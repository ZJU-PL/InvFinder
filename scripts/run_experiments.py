#!/usr/bin/env python3
"""Run independent native-Z3 processes; incomplete results never count as solved."""
import argparse
import csv
import hashlib
import json
import math
import subprocess
import time
from pathlib import Path

COLUMNS = ["File", "Domain", "Method", "Bad Solve", "Time Cost", "Calls", "Info",
           "Mode", "Result", "K_needed", "Proved", "Iterations", "Iteration Limit", "Auxiliary Status"]
SUITES = {
    "rq1": ("interval,octagon,polyhedra", "efsolve,optimal,fixbsrh,bilater"),
    "rq2": ("interval", "bilater,efsolve,optimal"),
    "rq3": ("interval", "efsolve,bitwise,bounded,optimal"),
}


def iteration_limit(value):
    if value in ("unlimited", "-1"):
        return -1
    if not value.isascii() or not value.isdecimal() or int(value) > (1 << 63) - 1:
        raise argparse.ArgumentTypeError("iterations must be a nonnegative integer, -1, or unlimited")
    return int(value)


def fields(text):
    return dict(line.split(": ", 1) for line in text.splitlines() if ": " in line)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("-P", "--program", required=True, type=Path)
    parser.add_argument("-D", "--data-dir", required=True, type=Path)
    parser.add_argument("-A", "--domains", help="Comma-separated domains (default: interval)")
    parser.add_argument("-M", "--methods", help="Comma-separated synthesis tactics")
    parser.add_argument("--suite", choices=SUITES,
                        help="Synthesis configuration: rq1 comparisons, rq2 widths, or rq3 ablation; uses every supplied input")
    parser.add_argument("-O", "--output", required=True, type=Path)
    parser.add_argument("-T", "--timeout", type=float, default=60)
    parser.add_argument("--mode", choices=["synthesis", "verification"], default="synthesis")
    parser.add_argument("--max-k", type=int, default=64)
    parser.add_argument("--synthesis-timeout", type=float, default=10)
    parser.add_argument("-I", "--inv-iterations", "--iterations", type=iteration_limit, default=-1,
                        help="Synthesis iteration limit: N, -1, or unlimited (default unlimited)")
    parser.add_argument("--limit", type=int, help="Run only the first N sorted inputs (smoke test)")
    args = parser.parse_args()
    if args.suite:
        if args.mode != "synthesis" or args.domains is not None or args.methods is not None:
            parser.error("--suite requires synthesis mode and cannot be combined with --domains/--methods")
        args.domains, args.methods = SUITES[args.suite]
    else:
        args.domains = args.domains or "interval"
        args.methods = args.methods or "efsolve,bitwise,bounded,optimal,fixbsrh,bilater"
    if not math.isfinite(args.timeout) or (args.timeout < 0 and args.timeout != -1):
        parser.error("timeout must be nonnegative or -1")
    if not math.isfinite(args.synthesis_timeout) or (args.synthesis_timeout < 0 and args.synthesis_timeout != -1):
        parser.error("synthesis timeout must be nonnegative or -1")
    if args.max_k < 0:
        parser.error("maximum induction depth must be nonnegative")
    program = args.program.resolve(strict=True)
    files = sorted(args.data_dir.resolve().rglob("*.smt2"))
    if args.limit is not None:
        if args.limit < 1:
            parser.error("--limit must be positive")
        files = files[:args.limit]
    domains = list(dict.fromkeys(x.strip() for x in args.domains.split(",") if x.strip()))
    methods = list(dict.fromkeys(x.strip() for x in args.methods.split(",") if x.strip()))
    if not files or not domains or not methods:
        parser.error("select at least one input, domain, and method")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    version = subprocess.run([str(program), "--version"], capture_output=True, text=True, check=True).stdout.strip()
    metadata = {"version": version, "binary_sha256": hashlib.sha256(program.read_bytes()).hexdigest(),
                "options": {k: str(v) if isinstance(v, Path) else v for k, v in vars(args).items()},
                "files": {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}}
    args.output.with_suffix(args.output.suffix + ".json").write_text(json.dumps(metadata, indent=2) + "\n")
    with args.output.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=COLUMNS)
        writer.writeheader()
        for file in files:
            for domain in domains:
                selected = ["none"] if args.mode == "verification" and domain == "none" else methods
                for method in selected:
                    command = [str(program), "-F", str(file), "-D", domain, "-M", method, "-T", str(args.timeout)]
                    if args.mode == "verification":
                        command += ["--max-k", str(args.max_k), "--synthesis-timeout", str(args.synthesis_timeout)]
                        if domain != "none":
                            command += ["--inv-iterations", str(args.inv_iterations)]
                    else:
                        command += ["--iterations", str(args.inv_iterations)]
                    row = dict.fromkeys(COLUMNS, "")
                    row.update(File=str(file), Domain=domain, Method=method, Mode=args.mode)
                    row.update({"Bad Solve": 1, "Calls": 0, "Proved": 0, "Result": "unknown"})
                    if args.mode == "synthesis" or domain != "none":
                        row["Iteration Limit"] = "unlimited" if args.inv_iterations < 0 else args.inv_iterations
                    started = time.monotonic()
                    try:
                        proc = subprocess.run(command, capture_output=True, text=True,
                                              timeout=None if args.timeout == -1 else args.timeout + 5)
                        parsed = fields(proc.stdout)
                        if proc.returncode:
                            row["Info"] = "ERROR: " + proc.stderr.strip()
                        elif args.mode == "synthesis":
                            row["Bad Solve"] = int(parsed.get("Synthesis status") != "good")
                            row["Calls"] = int(parsed.get("SMT(OMT) calls", 0))
                            row["Info"] = parsed.get("Invariant", "Missing result")
                            row["Iterations"] = parsed.get("Iterations", "")
                            row["Result"] = "complete" if row["Bad Solve"] == 0 else "partial"
                        else:
                            row["Result"] = parsed.get("Result", "unknown")
                            row["Bad Solve"] = int(row["Result"] not in ("safe", "unsafe"))
                            row["Proved"] = int(row["Result"] == "safe")
                            row["K_needed"] = parsed.get("Required K", "")
                            row["Info"] = parsed.get("Reason", "Missing result")
                            row["Iterations"] = parsed.get("Invariant iterations", "")
                            row["Auxiliary Status"] = parsed.get("Auxiliary synthesis", "")
                        row["Time Cost"] = float(parsed["Time used"].removesuffix("s")) if "Time used" in parsed else time.monotonic() - started
                    except subprocess.TimeoutExpired:
                        row["Info"] = "TIMEOUT: process exceeded deadline"
                        row["Time Cost"] = time.monotonic() - started
                    writer.writerow(row)
                    stream.flush()
                    print(f"{file.name} [{domain}/{method}]: {row['Result']}", flush=True)


if __name__ == "__main__":
    main()
