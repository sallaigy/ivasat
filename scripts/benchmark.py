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


def discover_tests(path: Path):
    result = []
    for root, dirs, files in os.walk(path):
        for fname in files:
            result.append(pathlib.Path(root, fname))
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(prog='benchmark.py')
    parser.add_argument('directory')
    parser.add_argument('--tool-path', default='cmake-build-release/src/ivasat')
    parser.add_argument('--timeout', default=60)

    args = parser.parse_args()
    tests_dir = args.directory
    tool = args.tool_path
    timeout_value = int(args.timeout)

    tests = discover_tests(tests_dir)
    max_len = len(max(map(str, tests), key=len))

    for test in tests:
        test_name = str(test)
        print(f'{test_name:{max_len + 4}}', end='', flush=True)
        status = run_ivasat(tool, test, timeout_value)
        print(f'[{status[0]}, {status[1]:.2f}s]')

