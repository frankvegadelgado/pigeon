#!/usr/bin/env python3
"""
Behaviour of J_R(N) = F_c(N) - ((N - 3) - R(2N)) with F_c(N) = N - 3 - c * w * (2N - 4) / log^2(2N),
for the paper "Nested Squares and Distinct-Prime Goldbach Partitions".

Here w is the Hardy--Littlewood constant omega, and
    J_R(N) = R(2N) - c * w * (2N - 4) / log^2(2N),
so J_R(N) > 0 if and only if rho(N) > c, where rho(N) = R(2N) / (w * (2N - 4) / log^2(2N)).

For every N in [4, X] (default X = 10**6) the script computes R(2N) and rho(N), and prints:
  Table 1: on each dyadic interval I_m, the minimum of rho(N) (the largest c for which
           J_R > 0 on I_m) and the N attaining it;
  Table 2: for each requested c, the last N <= X with J_R(N) <= 0 and the threshold
           N_0(c) = that N + 1, so that J_R(N) > 0 for all N_0(c) <= N <= X;
  Table 3: for N = 2^k, the minimum of rho(n) over n in [N, X]: the largest c with
           J_R(n) > 0 for all N <= n <= X.

Requires only Python 3 and NumPy; it does not need the repository package.

Usage:
    python experiments/centering_jr.py
    python experiments/centering_jr.py --max 100000 --c 0.25 0.5 0.75 0.9
"""
import argparse
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
    ap.add_argument("--c", type=float, nargs="*", default=[0.25, 0.5, 0.75, 0.9, 0.95])
    args = ap.parse_args()
    X = args.max
    if X < 16:
        sys.exit("--max must be at least 16")
    t0 = time.time()

    def log(msg):
        print("[%7.1f s] %s" % (time.time() - t0, msg), file=sys.stderr, flush=True)

    log("sieve and autocorrelation of the odd primes up to %d" % (2 * X))
    flags = prime_sieve(2 * X)
    odd_flags = flags.copy()
    odd_flags[2] = False
    size = 1
    while size < 4 * X + 2:
        size *= 2
    ind = np.zeros(size, dtype=np.float64)
    ind[:2 * X + 1] = odd_flags[:2 * X + 1]
    F = np.fft.rfft(ind)
    conv = np.rint(np.fft.irfft(F * F, size)).astype(np.int64)
    del F, ind

    log("R(2N) and rho(N)")
    N = np.arange(4, X + 1)
    corr = odd_flags[4:X + 1].astype(np.int64)
    R = (conv[8:2 * X + 1:2] - corr) // 2
    odd_primes = np.nonzero(odd_flags)[0]
    omega = 1.0
    for p in odd_primes[odd_primes <= 2 * 10 ** 6]:
        omega *= 1.0 - 1.0 / (int(p) - 1) ** 2
    x = omega * (2.0 * N - 4.0) / np.log(2.0 * N) ** 2
    rho = R / x

    print("# N in [4, %d]; elapsed %.1f s; omega = %.10f" % (X, time.time() - t0, omega))
    print("\n# Table 1: min rho(N) = min R(2N) / (omega (2N-4) / log^2(2N)) on I_m")
    print("%-14s %-10s %-10s" % ("interval", "min rho", "N"))
    m = 2
    while True:
        lo = 4 if m == 2 else 2 ** m + 1
        hi = 8 if m == 2 else 2 ** (m + 1)
        if lo > X:
            break
        hi = min(hi, X)
        seg = rho[lo - 4:hi - 4 + 1]
        k = int(np.argmin(seg))
        print("%-14s %-10.4f %-10d" % (interval_label(m), seg[k], lo + k))
        m += 1

    print("\n# Table 2: for each c, the last N <= X with J_R(N) <= 0 and N_0(c)")
    print("%-8s %-14s %-10s" % ("c", "last N", "N_0(c)"))
    for c in args.c:
        bad = np.nonzero(rho <= c)[0]
        if len(bad) == 0:
            print("%-8.3f %-14s %-10d" % (c, "none", 4))
        else:
            last = int(N[bad[-1]])
            print("%-8.3f %-14d %-10d" % (c, last, last + 1))

    print("\n# Table 3: for N = 2^k, min rho(n) over N <= n <= X")
    print("%-10s %-10s %-10s" % ("N", "min rho", "n"))
    tail = np.minimum.accumulate(rho[::-1])[::-1]
    arg = np.zeros(len(rho), dtype=np.int64)
    best = len(rho) - 1
    for i in range(len(rho) - 1, -1, -1):
        if rho[i] <= rho[best]:
            best = i
        arg[i] = best
    k = 3
    while 2 ** k <= X:
        i = 2 ** k - 4
        print("%-10d %-10.4f %-10d" % (2 ** k, tail[i], int(N[arg[i]])))
        k += 1
    log("done")


if __name__ == "__main__":
    main()
