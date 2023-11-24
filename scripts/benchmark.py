#!/usr/bin/env python3
import pathlib
import subprocess
import sys
import os
import argparse
import typing
import time
from pathlib import Path
from enum import Enum


class Result(Enum):
    SAT = 1
    UNSAT = 2
    ERROR = 3
    TIMEOUT = 4


def run_ivasat(path: str, filename: Path, timeout: int) -> typing.Tuple[Result, float]:
    try:
        start = time.time()
        captured_output = subprocess.run([path, str(filename)], stdout=subprocess.PIPE, timeout=timeout)
        stop = time.time()
        ivasat_stdout = captured_output.stdout.decode()

        if 'Sat' == ivasat_stdout.splitlines(keepends=False)[-1]:
            return Result.SAT, stop - start
        elif 'Unsat' == ivasat_stdout.splitlines(keepends=False)[-1]:
            return Result.UNSAT, stop - start

    except subprocess.TimeoutExpired:
        return Result.TIMEOUT, timeout
    except Exception as ex:
        print(ex, file=sys.stderr)

    return Result.ERROR, 0


def run_minisat(path: str, filename: Path, timeout: int) -> typing.Tuple[Result, float]:
    try:
        start = time.time()
        captured_output = subprocess.run([path, '-no-elim', str(filename)], stdout=subprocess.PIPE, timeout=timeout)
        stop = time.time()
        ivasat_stdout = captured_output.stdout.decode()

        if 'SATISFIABLE' == ivasat_stdout.splitlines(keepends=False)[-1]:
            return Result.SAT, stop - start
        elif 'UNSATISFIABLE' == ivasat_stdout.splitlines(keepends=False)[-1]:
            return Result.UNSAT, stop - start

    except subprocess.TimeoutExpired:
        return Result.TIMEOUT, timeout
    except Exception as ex:
        print(ex, file=sys.stderr)

    return Result.ERROR, 0


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
        print(f'{test_name:{max_len + 4}}', end='', flush=True)
        status = run_ivasat(tool, test, timeout_value)

        num_timeouts += 1 if status[0] == Result.TIMEOUT else 0
        num_errors += 1 if status[0] == Result.ERROR else 0

        total_solver_time += status[1]
        if args.minisat:
            minisat_status = run_minisat('minisat', test, timeout_value)
            print(f'[{status[0]}, {status[1]:.2f}s, {minisat_status[0]}, {minisat_status[1]:.2f}]')
        else:
            print(f'[{status[0]}, {status[1]:.2f}s]')

    print('================================')
    print(f'Total tests: {len(tests)}')
    print(f'Timeouts: {num_timeouts}')
    print(f'Errors: {num_errors}')
    print(f'Total time: {total_solver_time}')
