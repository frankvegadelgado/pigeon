#!/usr/bin/env python3
"""
Centering statistics for the paper "Nested Squares and Distinct-Prime Goldbach Partitions".

For every N in [4, X] (default X = 10**6) it computes R(2N) = |C_N & D_N| and reports, on the
dyadic intervals I_m of the computational section:

  Table A: min R(2N)/HL(2N) over all N, and over the N with at most one odd prime divisor p,
           where N = 2^k, N = p or N = 2p, so that kappa(N) is 1 or (p - 1)/(p - 2);
  Table B: the least centered prime p_min(N) = N - max(C_N & D_N), the smallest odd prime
           p < N such that 2N - p is prime; the maximum of p_min(N) per interval, and
           the ratio p_min(N) / log^2(2N);
  Table C: for the values of N given with --defect, the defect t = (P' + Q')/2 - N of the
           straddling pairs P' < N < Q' < 2N of primes with Q' - P' = 2M, M in C_N:
           the number of M in C_N with a witness of defect t = 0 (these are the M in C_N & D_N)
           and the distribution of min |t| over M in C_N.

Requires only Python 3 and NumPy; it does not need the repository package.

Usage:
    python experiments/centering_stats.py                       # X = 10**6
    python experiments/centering_stats.py --max 100000
    python experiments/centering_stats.py --max 100000 --defect 1000 5000 20000
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


def smallest_prime_factor(limit):
    spf = np.zeros(limit + 1, dtype=np.int32)
    for i in range(2, int(limit ** 0.5) + 1):
        if spf[i] == 0:
            block = spf[i * i::i]
            block[block == 0] = i
    idx = np.nonzero(spf == 0)[0]
    spf[idx] = idx
    return spf


def odd_prime_divisors(n, spf):
    ps = []
    while n > 1:
        p = int(spf[n])
        if p > 2:
            ps.append(p)
        while n % p == 0:
            n //= p
    return ps


def dyadic_index(N):
    if N <= 8:
        return 2
    return (N - 1).bit_length() - 1


def interval_label(m):
    return "[4,8]" if m == 2 else "(2^%d,2^%d]" % (m, m + 1)


def defect_table(N, flags, out):
    """Defects of the straddling pairs for M in C_N (flags is the prime sieve up to 2N)."""
    primes = [p for p in range(3, N) if flags[p]]
    upper = [q for q in range(N + 1, 2 * N) if flags[q]]
    upper_set = set(upper)
    CN = [N - p for p in primes]
    best = {}
    zero = 0
    for M in CN:
        d = 2 * M
        m = None
        for P in primes:
            if P + d in upper_set:
                t = P - (N - M)
                if m is None or abs(t) < m:
                    m = abs(t)
                    if m == 0:
                        break
        best[M] = m
    nowit = sum(1 for v in best.values() if v is None)
    vals = [v for v in best.values() if v is not None]
    zero = sum(1 for v in vals if v == 0)
    out("N = %d: |C_N| = %d, with t = 0 (M in C_N & D_N): %d, no straddling witness: %d" %
        (N, len(CN), zero, nowit))
    if vals:
        vals.sort()
        out("    min|t| over M in C_N with a witness: median %d, 90th percentile %d, maximum %d" %
            (vals[len(vals) // 2], vals[(9 * len(vals)) // 10], vals[-1]))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max", type=int, default=10 ** 6)
    ap.add_argument("--defect", type=int, nargs="*", default=[])
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
    while size < 4 * X + 2:  # no wrap-around: the sums of two primes up to 2X reach 4X
        size *= 2
    ind = np.zeros(size, dtype=np.float64)
    ind[:2 * X + 1] = odd_flags[:2 * X + 1]
    F = np.fft.rfft(ind)
    conv = np.rint(np.fft.irfft(F * F, size)).astype(np.int64)
    del F, ind
    Rvals = np.zeros(X + 1, dtype=np.int64)
    for N in range(4, X + 1):
        Rvals[N] = (int(conv[2 * N]) - (1 if (N % 2 == 1 and flags[N]) else 0)) // 2
    del conv

    log("Hardy-Littlewood constant and smallest prime factors")
    odd_primes = np.nonzero(flags)[0]
    odd_primes = odd_primes[odd_primes > 2]
    omega = 1.0
    for p in odd_primes[odd_primes <= 2 * 10 ** 6]:
        omega *= 1.0 - 1.0 / (int(p) - 1) ** 2
    spf = smallest_prime_factor(X)
    nodes, weights = np.polynomial.legendre.leggauss(64)

    def hl_value(N):
        a, b = 2.0, 2.0 * N - 2.0
        t = 0.5 * (b - a) * nodes + 0.5 * (b + a)
        integral = 0.5 * (b - a) * float(np.sum(weights / (np.log(t) * np.log(2.0 * N - t))))
        S = omega
        for p in odd_prime_divisors(N, spf):
            S *= (p - 1.0) / (p - 2.0)
        return S * integral

    def kappa_one(N):
        return len(odd_prime_divisors(N, spf)) == 0 or \
            (len(odd_prime_divisors(N, spf)) == 1 and (N % 2 == 1 and flags[N] or
                                                       (N % 2 == 0 and flags[N // 2])))

    odd_prime_list = [int(p) for p in odd_primes if p < X]
    M_max = dyadic_index(X)
    all_min = {}
    fam_min = {}
    pmin_max = {}
    log("per-N statistics")
    step = max(1, X // 20)
    for N in range(4, X + 1):
        if N % step == 0:
            log("N = %d of %d" % (N, X))
        m = dyadic_index(N)
        ratio = Rvals[N] / hl_value(N)
        if m not in all_min or ratio < all_min[m][0]:
            all_min[m] = (ratio, N)
        if kappa_one(N):
            if m not in fam_min or ratio < fam_min[m][0]:
                fam_min[m] = (ratio, N)
        pm = None
        for p in odd_prime_list:
            if p >= N:
                break
            if flags[2 * N - p]:
                pm = p
                break
        if pm is None:
            print("no centered prime for N = %d" % N)
            continue
        val = pm / math.log(2.0 * N) ** 2
        if m not in pmin_max or pm > pmin_max[m][0]:
            pmin_max[m] = (pm, N, val)

    print("# N in [4, %d]; elapsed %.1f s; omega = %.10f" % (X, time.time() - t0, omega))
    print("\n# Table A: min R(2N)/HL(2N) on I_m, over all N and over N = 2^k, p, 2p")
    print("%-14s %-10s %-10s %-10s %-10s" % ("interval", "min(all)", "N", "min(fam.)", "N"))
    for m in range(2, M_max + 1):
        if m in all_min:
            f = fam_min.get(m)
            print("%-14s %-10.4f %-10d %-10s %-10s" % (
                interval_label(m), all_min[m][0], all_min[m][1],
                "%.4f" % f[0] if f else "-", f[1] if f else "-"))
    print("\n# Table B: the largest least centered prime p_min(N) on I_m")
    print("%-14s %-10s %-10s %-12s" % ("interval", "max p_min", "N", "p_min/log^2(2N)"))
    for m in range(2, M_max + 1):
        if m in pmin_max:
            print("%-14s %-10d %-10d %-12.4f" % (interval_label(m), pmin_max[m][0],
                                                 pmin_max[m][1], pmin_max[m][2]))
    if args.defect:
        print("\n# Table C: defects of the straddling pairs")
        for N in args.defect:
            if 2 * N > 2 * X:
                print("N = %d exceeds --max" % N)
                continue
            defect_table(N, flags, print)
    log("done")


if __name__ == "__main__":
    main()
