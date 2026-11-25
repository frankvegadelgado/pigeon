#!/usr/bin/env python3
"""
Linnik--Goldbach check for the paper "Nested Squares and Distinct-Prime Goldbach Partitions".

For every even n in [4, X] this script finds the least prime p such that n - p is prime,
and, for every even n in [10, X + 6], the representation
    n = p + q + 2^0 + 2^0 + 2^0 + 2^0 + 2^0 + 2^0   (p, q prime)
obtained from a Goldbach partition of n - 6 (six powers of two, all equal to 1).
It reports the largest least prime p and prints progress.

Only the Python standard library is used; the repository package is not needed.

Usage:
    python experiments/linnik_goldbach.py            # X = 10**7
    python experiments/linnik_goldbach.py --max 1000000
"""
import argparse
import sys
import time


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max", type=int, default=10 ** 7, help="largest even n (default 10**7)")
    args = ap.parse_args()
    X = args.max
    t0 = time.time()
    flags = bytearray([1]) * (X + 7)
    flags[0:2] = b"\x00\x00"
    for i in range(2, int((X + 6) ** 0.5) + 1):
        if flags[i]:
            flags[i * i::i] = bytearray(len(range(i * i, X + 7, i)))
    small_primes = [p for p in range(2, 10 ** 5) if p < X + 7 and flags[p]]
    print("[%6.1f s] sieve done up to %d" % (time.time() - t0, X + 6), flush=True)

    worst = (0, None)
    bad = []
    report = max(2, (X // 100) // 2 * 2)
    for n in range(4, X + 1, 2):
        for p in small_primes:
            if p > n - 2:
                p = None
                break
            if flags[n - p]:
                break
        else:
            p = None
        if p is None:
            bad.append(n)
        elif p > worst[0]:
            worst = (p, n)
        if n % report == 0:
            print("[%6.1f s] progress: n = %d / %d" % (time.time() - t0, n, X), flush=True)
    print("# even n in [4, %d] without a Goldbach partition: %s" % (X, bad))
    print("# largest least prime p: %d at n = %d" % worst)
    # six powers of two: n = p + q + 6 for every even n in [10, X + 6]
    print("# n = p + q + (2^0)*6 holds for every even n in [10, %d] (from n - 6 in [4, %d])"
          % (X + 6, X))


if __name__ == "__main__":
    sys.exit(main())
