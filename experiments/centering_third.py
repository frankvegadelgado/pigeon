#!/usr/bin/env python3
"""
The centered witnesses with M <= N/3 for the paper "Nested Squares and Distinct-Prime Goldbach
Partitions".

For every N in [4, X] (default X = 10**6) it computes
    m_min(N) = the least M in [1, N/3] with N - M and N + M both prime,
that is, the least M in C_N & D_N, and reports

  Table 1: on each dyadic interval I_m, the largest m_min(N), the N attaining it and the ratio
           m_min(N) / log^2(2N);
  Table 2: the N in [4, X] with no such M (the statement "there is M <= N/3 with N - M and
           N + M prime" fails for them), if any;
  Table 3: for the values of N given with --count, the number R3(N) of M in [1, N/3] with
           N - M and N + M prime, the number R(2N) of all M in [1, N-3], and R3(N)/R(2N).

Requires only Python 3 and NumPy; it does not need the repository package.

Usage:
    python experiments/centering_third.py
    python experiments/centering_third.py --max 100000 --count 1000 10000 100000
"""
import argparse
import math
import sys
import time

import numpy as np


def prime_sieve(limit):
    flags = np.ones(limit + 1, dtype=bool)
    flags[:2] = False
    flags[4::2] = False
    for i in range(3, int(limit ** 0.5) + 1, 2):
        if flags[i]:
            flags[i * i::2 * i] = False
    return flags


def dyadic_index(N):
    if N <= 8:
        return 2
    return (N - 1).bit_length() - 1


def interval_label(m):
    return "[4,8]" if m == 2 else "(2^%d,2^%d]" % (m, m + 1)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max", type=int, default=10 ** 6)
    ap.add_argument("--count", type=int, nargs="*", default=[1000, 10000, 100000])
    args = ap.parse_args()
    X = args.max
    if X < 16:
        sys.exit("--max must be at least 16")
    t0 = time.time()

    def log(msg):
        print("[%7.1f s] %s" % (time.time() - t0, msg), file=sys.stderr, flush=True)

    log("sieve up to %d" % (2 * X))
    flags = prime_sieve(2 * X)
    N = np.arange(4, X + 1, dtype=np.int64)
    limit = N // 3
    mmin = np.zeros(len(N), dtype=np.int64)
    pending = np.ones(len(N), dtype=bool)

    log("least M")
    M = 1
    while pending.any() and M <= X // 3:
        cand = pending & (limit >= M)
        idx = np.nonzero(cand)[0]
        if len(idx) == 0:
            break
        hit = flags[N[idx] - M] & flags[N[idx] + M]
        found = idx[hit]
        mmin[found] = M
        pending[found] = False
        if M % 1000 == 0:
            log("M = %d, %d values of N without a witness so far" % (M, int(pending.sum())))
        M += 1

    print("# N in [4, %d]; elapsed %.1f s" % (X, time.time() - t0))
    print("\n# Table 1: the largest least M <= N/3 with N - M and N + M prime, on I_m")
    print("%-14s %-8s %-10s %-12s" % ("interval", "max M", "N", "M/log^2(2N)"))
    m = 2
    while True:
        lo = 4 if m == 2 else 2 ** m + 1
        hi = 8 if m == 2 else 2 ** (m + 1)
        if lo > X:
            break
        hi = min(hi, X)
        seg = mmin[lo - 4:hi - 4 + 1]
        seg_pending = pending[lo - 4:hi - 4 + 1]
        seg2 = np.where(seg_pending, -1, seg)
        k = int(np.argmax(seg2))
        n = lo + k
        print("%-14s %-8d %-10d %-12.4f" % (interval_label(m), seg2[k], n,
                                             seg2[k] / math.log(2.0 * n) ** 2))
        m += 1

    bad = N[pending]
    print("\n# Table 2: N in [4, %d] with no M <= N/3 such that N - M and N + M are prime" % X)
    print(", ".join(str(int(b)) for b in bad) if len(bad) else "none")

    print("\n# Table 3: R3(N) = #{M <= N/3}, R(2N) = #{M <= N-3} with N - M and N + M prime")
    print("%-10s %-8s %-8s %-8s" % ("N", "R3(N)", "R(2N)", "R3/R"))
    for n in args.count:
        if n < 4 or n > X:
            print("N = %d outside [4, %d]" % (n, X))
            continue
        Ms = np.arange(1, n - 2, dtype=np.int64)
        ok = flags[n - Ms] & flags[n + Ms]
        R = int(ok.sum())
        R3 = int(ok[:n // 3].sum())
        print("%-10d %-8d %-8d %-8.4f" % (n, R3, R, R3 / R if R else float("nan")))
    log("done")


if __name__ == "__main__":
    main()
