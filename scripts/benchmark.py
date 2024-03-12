#!/usr/bin/env python3
import pathlib
import subprocess
import sys
import os
import argparse
import typing
import time
import re
from pathlib import Path
from enum import Enum


class Result(Enum):
    SAT = 1
    UNSAT = 2
    ERROR = 3
    TIMEOUT = 4


class ResultData:
    def __init__(self, status: Result, time: float = 0, conflicts: int = 0, decisions: int = 0):
        self.status = status
        self.time = time
        self.conflicts = conflicts
        self.decisions = decisions


def run_ivasat(path: str, filename: Path, timeout: int) -> ResultData:
    try:
        start = time.time()
        captured_output = subprocess.run([path, str(filename)], stdout=subprocess.PIPE, timeout=timeout)
        stop = time.time()
        ivasat_stdout = captured_output.stdout.decode()

        if 'Sat' == ivasat_stdout.splitlines(keepends=False)[-1]:
            m = re.search(r"Decisions: (\d+)", ivasat_stdout)
            num_decisions = int(m.group(1))
            m = re.search(r'Conflicts: (\d+)', ivasat_stdout)
            num_conflicts = int(m.group(1))

            return ResultData(Result.SAT, stop - start, conflicts=num_conflicts, decisions=num_decisions)
        elif 'Unsat' == ivasat_stdout.splitlines(keepends=False)[-1]:
            m = re.search(r'Decisions: (\d+)', ivasat_stdout)
            num_decisions = int(m.group(1))
            m = re.search(r'Conflicts: (\d+)', ivasat_stdout)
            num_conflicts = int(m.group(1))

            return ResultData(Result.UNSAT, stop - start, conflicts=num_conflicts, decisions=num_decisions)

    except subprocess.TimeoutExpired:
        return ResultData(Result.TIMEOUT, timeout)
    except Exception as ex:
        print(ex, file=sys.stderr)

    return ResultData(Result.ERROR, 0)


def run_minisat(path: str, filename: Path, timeout: int) -> ResultData:
    try:
        start = time.time()
        captured_output = subprocess.run([path, '-no-elim', str(filename)], stdout=subprocess.PIPE, timeout=timeout)
        stop = time.time()
        ivasat_stdout = captured_output.stdout.decode()

        if 'SATISFIABLE' == ivasat_stdout.splitlines(keepends=False)[-1]:
            m = re.search('decisions\s+: (\\d+)', ivasat_stdout)
            num_decisions = int(m.group(1))
            m = re.search('conflicts\s+: (\\d+)', ivasat_stdout)
            num_conflicts = int(m.group(1))
            return ResultData(Result.SAT, stop - start, conflicts=num_conflicts, decisions=num_decisions)
        elif 'UNSATISFIABLE' == ivasat_stdout.splitlines(keepends=False)[-1]:
            m = re.search('decisions\s+: (\\d+)', ivasat_stdout)
            num_decisions = int(m.group(1))
            m = re.search('conflicts\s+: (\\d+)', ivasat_stdout)
            num_conflicts = int(m.group(1))
            return ResultData(Result.UNSAT, stop - start, conflicts=num_conflicts, decisions=num_decisions)

    except subprocess.TimeoutExpired:
        return ResultData(Result.TIMEOUT, timeout)
    except Exception as ex:
        print(ex, file=sys.stderr)

    return ResultData(Result.ERROR, 0)


def discover_tests(path: Path):
    result = []
    for root, dirs, files in os.walk(path):
        for fname in files:
            if fname.endswith('.cnf'):
                result.append(pathlib.Path(root, fname))
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(prog='benchmark.py')
    parser.add_argument('directory')
    parser.add_argument('--tool-path', default='cmake-build-release/src/ivasat')
    parser.add_argument('--minisat', action='store_true')
    parser.add_argument('--minisat-path', default='minisat')
    parser.add_argument('--timeout', default=60)

    args = parser.parse_args()
    tests_dir = args.directory
    tool = args.tool_path
    timeout_value = int(args.timeout)

    tests = sorted(discover_tests(tests_dir))
    max_len = len(max(map(str, tests), key=len))
    num_timeouts = 0
    num_errors = 0

    total_solver_time = 0
    for test in tests:
        test_name = str(test)
        result = run_ivasat(tool, test, timeout_value)

        num_timeouts += 1 if result.status == Result.TIMEOUT else 0
        num_errors += 1 if result.status == Result.ERROR else 0

        total_solver_time += result.time
        if args.minisat:
            minisat_result = run_minisat('minisat', test, timeout_value)
            print(f'{test_name};{result.status};{result.time:.2f};{result.decisions};{result.conflicts};{minisat_result.status};{minisat_result.time:.2f};{minisat_result.decisions};{minisat_result.conflicts};',
                  flush=True)
        else:
            print(f'{test_name};{result.status};{result.time:.2f};{result.decisions};{result.conflicts};', flush=True)
