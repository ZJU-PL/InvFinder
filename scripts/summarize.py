#!/usr/bin/env python3
"""Summarize completed runs, common sets, width scaling, or differing-bit metrics."""
import argparse
import csv
import json
import math
import re
import sys
from collections import defaultdict
from pathlib import Path


def completed(row):
    return row['Bad Solve'] == '0'


def bounds(info):
    """Parse unsigned bound vectors, retaining widths and arbitrary precision."""
    if info == '[bottom][bottom]':
        return None
    match = re.fullmatch(r'\[([^\]]*)\]\[([^\]]*)\]', info.strip())
    if not match:
        raise ValueError('invalid invariant bound vectors: ' + info)
    vectors = []
    token = re.compile(r'\s*(#x[0-9a-fA-F]+|#b[01]+|\(_ bv\d+ \d+\))')
    for part in match.groups():
        values, pos = [], 0
        while part[pos:].strip():
            found = token.match(part, pos)
            if not found:
                raise ValueError('invalid bound numeral: ' + part[pos:])
            text = found.group(1)
            if text.startswith('#x'):
                value, width = int(text[2:], 16), 4 * (len(text) - 2)
            elif text.startswith('#b'):
                value, width = int(text[2:], 2), len(text) - 2
            else:
                value, width = map(int, re.fullmatch(r'\(_ bv(\d+) (\d+)\)', text).groups())
            if width < 1 or value >= 1 << width:
                raise ValueError('bound outside its bit width')
            values.append((value, width))
            pos = found.end()
        vectors.append(tuple(values))
    lower, upper = vectors
    if not lower or len(lower) != len(upper):
        raise ValueError('bounds must contain matching nonempty rows')
    if any(lw != uw or lo > hi for (lo, lw), (hi, uw) in zip(lower, upper)):
        raise ValueError('invalid unsigned interval bounds')
    return lower, upper


def differing_bit(info):
    parsed = bounds(info)
    if parsed is None:
        return None  # Bottom has no lower/upper interval metric.
    lower, upper = parsed
    return max((lo ^ hi).bit_length() for (lo, _), (hi, _) in zip(lower, upper))


def width_identity(filename):
    """EFMC width directory/suffix conventions; no guessing from invariant bounds."""
    widths = set()
    parts = []
    for part in Path(filename).parts:
        match = re.fullmatch(r'(\d+)bits?', part)
        if match:
            widths.add(int(match.group(1)))
        else:
            for value in re.findall(r'_(\d+)bits_unsigned', part):
                widths.add(int(value))
            parts.append(re.sub(r'_\d+bits_unsigned', '', part))
    if len(widths) != 1:
        raise ValueError('expected one width in EFMC directory/filename: ' + filename)
    return next(iter(widths)), '/'.join(parts)


def collect(rows):
    groups = defaultdict(dict)
    for row in rows:
        key = (row['Mode'], row['Domain'], row.get('Iteration Limit') or 'unlimited')
        task = (row['Method'], row['File'])
        if task in groups[key]:
            raise ValueError('duplicate method/input run: ' + str(task))
        time, calls = float(row['Time Cost']), int(row['Calls'])
        if not math.isfinite(time) or time < 0 or calls < 0:
            raise ValueError('invalid runtime or solver-call count')
        groups[key][task] = row
    return groups


def common_files(data, methods):
    sets = [{file for (method, file), row in data.items()
             if method == wanted and completed(row)} for wanted in methods]
    common = set.intersection(*sets) if sets else set()
    for file in common:
        selected = [data[(method, file)] for method in methods]
        if selected[0]['Mode'] == 'synthesis':
            expected = bounds(selected[0]['Info'])
            if any(bounds(row['Info']) != expected for row in selected[1:]):
                raise ValueError('completed methods disagree on bounds: ' + file)
        elif selected[0]['Mode'] == 'reduced-product':
            expected = product_tuple(selected[0]['Info'])
            if any(product_tuple(row['Info']) != expected for row in selected[1:]):
                raise ValueError('completed methods disagree on reduced-product bounds/facts: ' + file)
    return common


def product_tuple(info):
    """Ignore disabled anchor constants: they do not constrain the invariant."""
    result = json.loads(info)
    if result['bottom']:
        return None
    return (tuple((r['label'], int(r['lower']), int(r['upper'])) for r in result['ranges']),
            tuple((f['label'], int(f['constant']) if f['enabled'] else None) for f in result['flats']))


def totals(rows):
    seconds = sum(float(row['Time Cost']) for row in rows)
    calls = sum(int(row['Calls']) for row in rows)
    count = len(rows)
    return [count, f'{seconds:.6f}', f'{seconds/count:.6f}' if count else '', calls,
            f'{calls/count:.6f}' if count else '', f'{1000*seconds/calls:.6f}' if calls else '']


def selected_methods(data, requested):
    return requested or sorted({method for method, _ in data})


def summarize(rows, analysis='overall', methods=None, widths=(32, 64, 128)):
    if analysis in ('common', 'width') and not methods:
        raise ValueError('common/width analysis requires explicit --methods to define the comparison')
    groups = collect(rows)
    output = []
    if analysis == 'overall':
        header = ['mode', 'domain', 'method', 'iteration_limit', 'completed', 'total',
                  'completed_seconds', 'completed_calls']
        for (mode, domain, limit), data in sorted(groups.items()):
            for method in selected_methods(data, methods):
                chosen = [row for (m, _), row in data.items() if m == method]
                done = [row for row in chosen if completed(row)]
                stats = totals(done)
                output.append([mode, domain, method, limit, len(done), len(chosen), stats[1], stats[3]])
    elif analysis == 'common':
        header = ['mode', 'domain', 'method', 'iteration_limit', 'common_completed',
                  'completed_seconds', 'average_seconds', 'completed_calls', 'average_calls', 'milliseconds_per_call']
        for (mode, domain, limit), data in sorted(groups.items()):
            chosen_methods = selected_methods(data, methods)
            common = common_files(data, chosen_methods)
            for method in chosen_methods:
                output.append([mode, domain, method, limit] + totals([data[(method, file)] for file in sorted(common)]))
    elif analysis == 'width':
        header = ['domain', 'method', 'iteration_limit', 'width', 'common_benchmarks',
                  'completed_seconds', 'average_seconds', 'completed_calls', 'average_calls', 'milliseconds_per_call']
        for (mode, domain, limit), data in sorted(groups.items()):
            if mode != 'synthesis':
                raise ValueError('width analysis requires synthesis results')
            chosen_methods = selected_methods(data, methods)
            common_files(data, chosen_methods)  # Check same-domain bound agreement.
            indexed = {}
            for (method, file), row in data.items():
                width, identity = width_identity(file)
                if width not in widths or method not in chosen_methods:
                    continue
                key = (method, width, identity)
                if key in indexed:
                    raise ValueError('duplicate width-normalized input: ' + identity)
                indexed[key] = row
            sets = [{identity for (m, w, identity), row in indexed.items()
                     if m == method and w == width and completed(row)}
                    for method in chosen_methods for width in widths]
            common = set.intersection(*sets) if sets else set()
            for method in chosen_methods:
                for width in widths:
                    output.append([domain, method, limit, width] + totals([
                        indexed[(method, width, identity)] for identity in sorted(common)]))
    else:
        header = ['file', 'domain', 'method', 'iteration_limit', 'differing_bit', 'calls', 'seconds', 'metric_status']
        for (mode, domain, limit), data in sorted(groups.items()):
            if mode != 'synthesis':
                raise ValueError('differing-bit analysis requires synthesis results')
            chosen_methods = selected_methods(data, methods)
            common_files(data, chosen_methods)
            for (method, file), row in sorted(data.items()):
                if method not in chosen_methods or not completed(row):
                    continue
                metric = differing_bit(row['Info'])
                output.append([file, domain, method, limit, '' if metric is None else metric,
                               int(row['Calls']), row['Time Cost'], 'bottom' if metric is None else 'defined'])
    return header, output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('csv', type=Path)
    parser.add_argument('--analysis', choices=['overall', 'common', 'width', 'differing-bit'], default='overall')
    parser.add_argument('--domains', help='Comma-separated domains to include')
    parser.add_argument('--methods', help='Comma-separated methods; common sets require every selected method')
    parser.add_argument('--widths', default='32,64,128', help='Widths required together by width analysis')
    parser.add_argument('--plot', type=Path, help='Optional overall cactus PDF/PNG (requires matplotlib)')
    args = parser.parse_args()
    if args.plot and args.analysis != 'overall':
        parser.error('--plot is supported for overall cactus summaries')
    methods = list(dict.fromkeys(item.strip() for item in args.methods.split(',') if item.strip())) if args.methods else None
    domains = {item.strip() for item in args.domains.split(',') if item.strip()} if args.domains else None
    try:
        widths = tuple(dict.fromkeys(int(value) for value in args.widths.split(',')))
        if not widths or any(width < 1 for width in widths):
            raise ValueError('widths must be positive integers')
        with args.csv.open(newline='') as stream:
            rows = [row for row in csv.DictReader(stream)
                    if (not domains or row['Domain'] in domains) and (not methods or row['Method'] in methods)]
        if not rows:
            raise ValueError('no matching result rows')
        header, output = summarize(rows, args.analysis, methods, widths)
    except (ValueError, KeyError) as error:
        parser.error(str(error))
    writer = csv.writer(sys.stdout, lineterminator='\n')
    writer.writerow(header)
    writer.writerows(output)
    if args.plot:
        import matplotlib
        matplotlib.use('Agg')
        import matplotlib.pyplot as plt
        for (mode, domain, limit), data in sorted(collect(rows).items()):
            for method in selected_methods(data, methods):
                times = sorted(float(row['Time Cost']) for (m, _), row in data.items()
                               if m == method and completed(row))
                plt.plot(range(1, len(times) + 1), times, label='/'.join((mode, domain, method, limit)))
        plt.xlabel('Completed instances')
        plt.ylabel('Runtime per instance (seconds)')
        plt.yscale('log')
        plt.legend(fontsize='small')
        plt.tight_layout()
        args.plot.parent.mkdir(parents=True, exist_ok=True)
        plt.savefig(args.plot)


if __name__ == '__main__':
    main()
