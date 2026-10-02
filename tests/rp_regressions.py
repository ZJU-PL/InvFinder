#!/usr/bin/env python3
"""Independent finite-state BAT/Kleene oracle; no Python SMT bindings required."""
from __future__ import annotations
import itertools
import json
import math
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import time

BIN = Path(sys.argv[1]).resolve()
ROOT = Path(__file__).resolve().parents[1]
records: list[dict] = []


def bv(n: int, w: int) -> str:
    return f"(_ bv{n} {w})"


def write(path, width, initial, edges, ranges, flats, variables=None):
    variables = variables or [('x', 'xp', width)]
    def state_expr(s, prime=False):
        vals = s if isinstance(s, tuple) else (s,)
        terms = [f"(= {v[1 if prime else 0]} {bv(x,v[2])})" for v,x in zip(variables, vals)]
        return '(and ' + ' '.join(terms) + ')'
    init = '(or ' + ' '.join(state_expr(s) for s in sorted(initial)) + ')' if initial else 'false'
    trans = '(or ' + ' '.join(f'(and {state_expr(s)} {state_expr(t,True)})' for s,t in sorted(edges)) + ')' if edges else 'false'
    lines = ['RP1'] + ['\t'.join(map(str,('var', *v))) for v in variables]
    lines += ['pre\t'+init, 'trans\t'+trans]
    lines += ['\t'.join(map(str, ('range', f'r{i}', w, x, xp))) for i,(w,x,xp,_) in enumerate(ranges)]
    lines += ['\t'.join(map(str, ('flat', f'f{i}', w, x, xp))) for i,(w,x,xp,_) in enumerate(flats)]
    Path(path).write_text('\n'.join(lines)+'\n')


def abstract(states, ranges, flats):
    if not states:
        return None
    rs = [(min(f(s) for s in states), max(f(s) for s in states)) for _,_,_,f in ranges]
    fs = []
    for _,_,_,f in flats:
        values = {f(s) for s in states}
        fs.append(next(iter(values)) if len(values)==1 else None)
    return rs, fs


def concrete(a, universe, ranges, flats):
    if a is None:
        return set()
    rs,fs = a
    return {s for s in universe
            if all(l<=f(s)<=u for (l,u),(_,_,_,f) in zip(rs,ranges))
            and all(c is None or f(s)==c for c,(_,_,_,f) in zip(fs,flats))}


def oracle(universe, initial, edges, ranges, flats):
    a = abstract(initial, ranges, flats)
    while True:
        states = concrete(a, universe, ranges, flats)
        nxt = abstract(states | initial | {t for s,t in edges if s in states}, ranges, flats)
        if a==nxt:
            return a
        a = nxt


def actual(data):
    if data['bottom']:
        return None
    return ([(int(r['lower']),int(r['upper'])) for r in data['ranges']],
            [int(f['constant']) if f['enabled'] else None for f in data['flats']])


def run(path, opts=(), timeout=12, label=''):
    command=[str(BIN),str(path),'--timeout',str(timeout),*opts]
    cp=subprocess.run(command,text=True,capture_output=True,timeout=timeout+5)
    assert cp.returncode in (0,3), (command,cp.returncode,cp.stderr)
    data=json.loads(cp.stdout)
    record={'case':label or Path(path).stem,'options':list(opts),**data}
    records.append(record)
    return data


def assert_case(path, universe, initial, edges, ranges, flats, methods=('quantified','cegis'), label=''):
    expected=oracle(universe,initial,edges,ranges,flats)
    W=sum(r[0] for r in ranges); K=len(flats)
    for method in methods:
        data=run(path,('--method',method,'--certify'),label=label)
        assert data['complete'] and data['bestness_certified'], data
        a=actual(data)
        assert a==expected, (label,method,a,expected)
        states=concrete(a,universe,ranges,flats)
        assert initial<=states and all(s not in states or t in states for s,t in edges)
        assert data['stats']['proposals']<=2*W+K


def main():
    started=time.perf_counter()
    with tempfile.TemporaryDirectory() as td:
        td=Path(td)
        # Named mutual-support examples; standalone BIIs are TOP.
        U=set(range(16));init={0}
        t=lambda x:1 if x>=12 else 15 if x&1 else x+2 if x<10 else x
        edges={(x,t(x)) for x in U}
        ranges=[(4,'x','xp',lambda x:x)]
        flats=[(1,f'((_ extract {b} {b}) x)',f'((_ extract {b} {b}) xp)',lambda x,b=b:(x>>b)&1) for b in range(4)]
        for label,rs,fs in [('mutual_interval_bits',ranges,flats),('mutual_interval_only',ranges,[]),('mutual_bits_only',[],flats)]:
            assert_case(ROOT/'examples'/'reduced_product'/f'{label}.rp',U,init,edges,rs,fs,label=label)
        assert concrete(oracle(U,init,edges,ranges,flats),U,ranges,flats)=={0,2,4,6,8,10}
        # Modulus not a power of two. Residue domain is flat, not remainder intervals.
        t=lambda x:1 if x==15 else 15 if x%3 else x+3 if x<12 else x
        edges3={(x,t(x)) for x in U}
        mod=[(4,'(bvurem x #x3)','(bvurem xp #x3)',lambda x:x%3)]
        for label,rs,fs in [('mutual_interval_mod3',ranges,mod),('mutual_mod3_interval_only',ranges,[]),('mutual_mod3_only',[],mod)]:
            assert_case(ROOT/'examples'/'reduced_product'/f'{label}.rp',U,init,edges3,rs,fs,label=label)
        # Signed order is translated by XOR with the sign bit. Transition stays signed.
        signed=lambda x:x-16 if x&8 else x
        edges_s={(x,(x+1)&15 if signed(x)<3 else x) for x in U}
        rs=ranges+[(4,'(bvxor x #x8)','(bvxor xp #x8)',lambda x:x^8)]
        assert_case(ROOT/'examples/reduced_product/signed_cross_zero.rp',U,{9},edges_s,rs,[],label='signed_cross_zero')
        assert_case(ROOT/'examples/reduced_product/empty.rp',U,set(),set(itertools.product(U,U)),ranges,flats,label='empty')
        # Non-power-of-two congruence wraparound must not be treated as unbounded arithmetic.
        path=td/'wrap.rp';es={(x,(x+3)&15) for x in U}
        write(path,4,{0},es,ranges,mod)
        assert_case(path,U,{0},es,ranges,mod,label='mod3_wraparound')
        # Nondeterministic initiation forbids fixing a fact to just one sampled state.
        path=td/'multi_init.rp';es={(x,x) for x in U}
        write(path,4,{0,3,6},es,ranges,flats+mod)
        assert_case(path,U,{0,3,6},es,ranges,flats+mod,label='multiple_initial_states')
        # Abstract lower envelopes can contain unreachable states. With Pre={0,2}
        # and edge 1->6, a range and bit2 cannot exclude source 1, so the BII must
        # include 6. Adding parity excludes 1 and makes 6 unnecessary. This guards
        # against treating every consecution target as unconditionally positive.
        es={(x,6 if x==1 else x) for x in U}
        selected=[flats[2]]
        assert_case(ROOT/'examples/reduced_product/abstract_source_promotion.rp',U,{0,2},es,ranges,selected,label='abstract_source_promotion')
        assert_case(ROOT/'examples/reduced_product/excludable_source.rp',U,{0,2},es,ranges,selected+[flats[0]],label='excludable_source')
        # Full 128-bit bounds (no host-integer truncation); both symbolic backends.
        for method in ('quantified','cegis'):
            d=run(ROOT/'examples/reduced_product/counter128.rp',('--method',method,'--certify'),timeout=30)
            assert d['complete'] and actual(d)==([(5,6)],[None]),d
            assert d['stats']['proposals']<=257
        # Heterogeneous variable/row widths and a relational modular range.
        V=set(itertools.product(range(4),range(8)))
        es={(s,((s[0]+1)%4,(s[1]+2)%8)) for s in V}
        rs=[(2,'x','xp',lambda s:s[0]),(3,'y','yp',lambda s:s[1]),
            (3,'(bvsub y ((_ zero_extend 1) x))','(bvsub yp ((_ zero_extend 1) xp))',lambda s:(s[1]-s[0])%8)]
        fs=[(1,'((_ extract 0 0) y)','((_ extract 0 0) yp)',lambda s:s[1]&1)]
        path=td/'mixed.rp';write(path,0,{(0,0)},es,rs,fs,[('x','xp',2),('y','yp',3)])
        assert_case(path,V,{(0,0)},es,rs,fs,label='mixed_width_relational')
        # Seeded 3-bit nondeterministic transition systems, independently evaluated.
        rng=random.Random(20261002)
        for case in range(30):
            U8=set(range(8));ini={x for x in U8 if rng.random()<0.2}
            es={(x,y) for x in U8 for y in U8 if rng.random()<0.10}
            rs=[(3,'x','xp',lambda x:x),(3,'(bvxor x #b100)','(bvxor xp #b100)',lambda x:x^4)]
            fs=[(1,f'((_ extract {b} {b}) x)',f'((_ extract {b} {b}) xp)',lambda x,b=b:(x>>b)&1) for b in range(3)]
            fs += [(3,'(bvurem x #b011)','(bvurem xp #b011)',lambda x:x%3)]
            path=td/'random.rp';write(path,3,ini,es,rs,fs)
            assert_case(path,U8,ini,es,rs,fs,label=f'random_{case:02d}')
        # Interruptions: every published result must independently be inductive.
        U=set(range(16));es={(x,1 if x>=12 else 15 if x&1 else x+2 if x<10 else x) for x in U}
        for method in ('quantified','cegis'):
            for budget in (0,1,3,8,16):
                d=run(ROOT/'examples/reduced_product/mutual_interval_bits.rp',('--method',method,'--max-queries',str(budget)),label=f'budget_{method}_{budget}')
                states=concrete(actual(d),U,ranges,flats)
                assert {0}<=states and all(s not in states or t in states for s,t in es),d
                assert d['stats']['total_calls']<=budget
            d=run(ROOT/'examples/reduced_product/mutual_interval_bits.rp',('--method',method,'--timeout','0'),label=f'zero_timeout_{method}')
            assert not d['complete'] and d['stats']['total_calls']==0
        for flags in [('--no-reduction',),('--no-promotion',),('--no-reduction','--no-promotion'),('--range-first',)]:
            d=run(ROOT/'examples/reduced_product/mutual_interval_bits.rp',('--method','cegis','--certify',*flags),label='ablation')
            assert d['complete'] and actual(d)==([(0,10)],[0,None,None,None]),d
        # Ill-formed next-row or pre-state usage must be rejected explicitly.
        for text in ['RP1\nvar\tx\txp\t4\npre\ttrue\ntrans\ttrue\nrange\tx\t4\tx\tx\n',
                     'RP1\nvar\tx\txp\t4\npre\t(= xp #x0)\ntrans\ttrue\n',
                     'RP1\nvar\tx\txp\t4abc\npre\ttrue\ntrans\ttrue\n',
                     'RP1\nvar\tx\txp\t4294967300\npre\ttrue\ntrans\ttrue\n']:
            path=td/'invalid.rp';path.write_text(text)
            cp=subprocess.run([str(BIN),str(path)],capture_output=True,text=True)
            assert cp.returncode==2,(text,cp.stdout,cp.stderr)
    summary={'malformed_input_checks':4,'runs':len(records),'complete':sum(d['complete'] for d in records),
             'elapsed_seconds':time.perf_counter()-started,'z3':records[0]['z3'],
             'oracle':'finite concrete-state enumeration + exact product abstraction + Kleene iteration',
             'seed':20261002,'records':records}
    if len(sys.argv) > 2:
        Path(sys.argv[2]).write_text(json.dumps(summary, indent=2)+'\n')
    print(f"PASS: {len(records)} synthesis runs; finite-state oracle, certificates, wide BV, and interruption checks")

if __name__=='__main__':
    main()
