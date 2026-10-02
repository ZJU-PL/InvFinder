#!/usr/bin/env python3
"""Replay SMT-LIB obligations with libz3 through its documented C API.

No Z3 Python package is needed. This is an independent solver invocation, not a
proof-object checker and not an independent implementation of the SMT theory.
"""
from __future__ import annotations
import ctypes as C
import ctypes.util
import argparse
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--library', help='Use the exact Z3 library selected by CMake')
    parser.add_argument('files', nargs='+', type=Path)
    args = parser.parse_args()
    lib = args.library or ctypes.util.find_library('z3')
    if not lib:
        raise SystemExit('libz3 not found')
    z=C.CDLL(lib)
    signatures={
        'Z3_mk_config':([],C.c_void_p),
        'Z3_del_config':([C.c_void_p],None),
        'Z3_mk_context':([C.c_void_p],C.c_void_p),
        'Z3_del_context':([C.c_void_p],None),
        'Z3_eval_smtlib2_string':([C.c_void_p,C.c_char_p],C.c_char_p),
    }
    for name,(argument_types,res) in signatures.items():
        f=getattr(z,name);f.argtypes=argument_types;f.restype=res
    for arg in args.files:
        data=arg.read_bytes()
        cfg=z.Z3_mk_config();ctx=z.Z3_mk_context(cfg);z.Z3_del_config(cfg)
        try:
            result=z.Z3_eval_smtlib2_string(ctx,data).decode().strip()
        finally:
            z.Z3_del_context(ctx)
        print(f'{arg}: {result}')
        if result!='unsat':
            raise SystemExit(1)

if __name__=='__main__':
    main()
