#!/usr/bin/env python3
"""
Large-range experiment for the paper "Nested Squares and Distinct-Prime Goldbach Partitions".

For every N in [4, X] (default X = 10**6) it computes
    |E_N|, H(N), R(2N) = |C_N & D_N|, H_R(N),
    the Hardy--Littlewood ratio R(2N)/HL(2N),
    the number F(N) of missing values forced by the prime gaps around N and below 2N
    (Lemmas "gap" and "gap-top") and U(N) = |A_N \\ E_N| - F(N),
and prints the dyadic-interval tables of the computational section.

Requires only Python 3 and NumPy; it does not need the repository package.

Method
  * cnt[d] = number of pairs (P, Q) of primes with P odd, P < N < Q < 2N, Q - P = d.
    When N increases by one, only P = N (if prime), Q = N+1 (leaving) and Q = 2N+1
    (entering) change, so cnt is updated by vectorised additions; nz = #{d : cnt[d] > 0}.
    Since 4 <= 2M <= 2N-4 for the half-differences, |E_N| = nz - [cnt[2N-4] > 0].
  * R(2N) = (conv[2N] - [N odd prime]) / 2, with conv the autocorrelation of the
    indicator of the odd primes, obtained from a single FFT.

Usage:
    python experiments/large_range.py             # X = 10**6
    python experiments/large_range.py --max 100000
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


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max", type=int, default=10 ** 6, help="largest N (default 10**6)")
    args = ap.parse_args()
    X = args.max
    t0 = time.time()

    def log(msg):
        print("[%7.1f s] %s" % (time.time() - t0, msg), flush=True)

    limit = 2 * X + 2
    log("sieving primes up to %d" % limit)
    flags = prime_sieve(limit)
    primes = np.nonzero(flags)[0].astype(np.int64)          # all primes <= limit
    odd_primes = primes[1:]                                  # drop 2

    log("FFT for R(2N)")
    # ---- R(2N) from one FFT of the indicator of the odd primes -------------
    ind = np.zeros(limit + 1)
    ind[odd_primes] = 1.0
    size = 1 << (2 * limit + 1).bit_length()
    F = np.fft.rfft(ind, size)
    conv = np.rint(np.fft.irfft(F * F, size)).astype(np.int64)   # ordered pairs (p, q)
    Rvals = np.zeros(X + 1, dtype=np.int64)
    for N in range(4, X + 1):
        Rvals[N] = (int(conv[2 * N]) - (1 if (N % 2 == 1 and flags[N]) else 0)) // 2
    del F

    log("Hardy-Littlewood constant and smallest prime factors")
    # ---- Hardy--Littlewood constant and quadrature --------------------------
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

    # ---- incremental computation of |E_N| ------------------------------------
    cnt = np.zeros(2 * X + 4, dtype=np.int32)
    nz = 0

    def add_pairs(idx):
        nonlocal nz
        nz += int(np.count_nonzero(cnt[idx] == 0))
        cnt[idx] += 1

    def remove_pairs(idx):
        nonlocal nz
        cnt[idx] -= 1
        nz -= int(np.count_nonzero(cnt[idx] == 0))

    # state at N = 4: P in {3}; Q in (4, 8) = {5, 7}
    P_arr = odd_primes[odd_primes < 4]
    for Q in (5, 7):
        add_pairs(Q - P_arr)

    log("main loop N = 4 .. %d" % X)
    report = max(1, X // 100)
    stats = {}
    sum_F = {}
    sum_miss = {}
    sum_U = {}
    cnt_N = {}
    min_E_ratio_all = (1e18, 0)
    N = 4
    while True:
        if N % report == 0:
            log("progress: N = %d / %d (%.0f%%)" % (N, X, 100.0 * N / X))
        # --- statistics for the current N ---
        Ncur = N
        E = nz - (1 if cnt[2 * Ncur - 4] > 0 else 0)
        miss = (Ncur - 3) - E
        H = math.log(2 * Ncur) ** 2 - miss
        R = int(Rvals[Ncur])
        HR = math.log(2 * Ncur) ** 2 - ((Ncur - 3) - R)
        # forced missing values
        i_lo = int(np.searchsorted(primes, Ncur, side="left"))       # primes[i_lo-1] < N
        p_minus = int(primes[i_lo - 1])
        j = i_lo + (1 if primes[i_lo] == Ncur else 0)
        p_plus = int(primes[j])
        k = int(np.searchsorted(primes, 2 * Ncur, side="left"))
        q = int(primes[k - 1])
        g = p_plus - p_minus
        lh = min(Ncur - 3, (g - 1) // 2)
        hl = max(1, (q - 3) // 2 + 1)
        if hl > Ncur - 3:                      # no value above (q-3)/2 in A_N
            Fn = lh
        elif lh >= hl - 1:                     # the two runs cover A_N
            Fn = Ncur - 3
        else:
            Fn = lh + (Ncur - 3 - hl + 1)
        U = miss - Fn
        ratio = R / hl_value(Ncur)

        m = dyadic_index(Ncur)
        s = stats.setdefault(m, {
            "H": (1e18, 0), "miss": (-1, 0), "E": (1e18, 0), "HR": (1e18, 0),
            "R": (10 ** 9, 0), "rmin": 1e18, "rmax": -1e18, "rsum": 0.0,
            "Fmax": -1, "Umax": (-1, 0), "Fbad": 0})
        if H < s["H"][0]:
            s["H"] = (H, Ncur)
        if miss > s["miss"][0]:
            s["miss"] = (miss, Ncur)
        if E / Ncur < s["E"][0]:
            s["E"] = (E / Ncur, Ncur)
        if HR < s["HR"][0]:
            s["HR"] = (HR, Ncur)
        if R < s["R"][0]:
            s["R"] = (R, Ncur)
        s["rmin"] = min(s["rmin"], ratio)
        s["rmax"] = max(s["rmax"], ratio)
        s["rsum"] += ratio
        s["Fmax"] = max(s["Fmax"], Fn)
        if U > s["Umax"][0]:
            s["Umax"] = (U, Ncur)
        if Fn > miss:
            s["Fbad"] += 1
        sum_F[m] = sum_F.get(m, 0) + Fn
        sum_miss[m] = sum_miss.get(m, 0) + miss
        sum_U[m] = sum_U.get(m, 0) + U
        cnt_N[m] = cnt_N.get(m, 0) + 1
        if Ncur >= 3275 and E / Ncur < min_E_ratio_all[0]:
            min_E_ratio_all = (E / Ncur, Ncur)

        if N == X:
            break
        # --- advance N -> N+1 ---
        if flags[N + 1]:                                   # Q = N+1 leaves the upper window
            lo = int(np.searchsorted(odd_primes, N, side="left"))
            remove_pairs(N + 1 - odd_primes[:lo])
        if N % 2 == 1 and flags[N]:                        # P = N joins the lower set
            a = int(np.searchsorted(primes, N + 1, side="right"))
            b = int(np.searchsorted(primes, 2 * N, side="left"))
            if b > a:
                add_pairs(primes[a:b] - N)
        if flags[2 * N + 1]:                               # Q = 2N+1 enters the upper window
            hi = int(np.searchsorted(odd_primes, N + 1, side="left"))
            add_pairs(2 * N + 1 - odd_primes[:hi])
        N += 1

    print("# N in [4, %d]; elapsed %.1f s; omega = %.10f" % (X, time.time() - t0, omega))
    print("\n# Table 1: min H(N) (N), max |A\\E| (N), min |E|/N (N) on I_m")
    for m in sorted(stats):
        s = stats[m]
        print("%-2d %-15s minH %.6f (%d)  max|A\\E| %d (%d)  min|E|/N %.6f (%d)" % (
            m, interval_label(m), s["H"][0], s["H"][1], s["miss"][0], s["miss"][1],
            s["E"][0], s["E"][1]))
    print("\n# min |E_N|/N over 3275 <= N <= X: %.6f at N=%d" % min_E_ratio_all)
    print("\n# Table 2: min H_R(N) (N) on I_m")
    for m in sorted(stats):
        s = stats[m]
        print("%-2d %-15s %.2f (%d)" % (m, interval_label(m), s["HR"][0], s["HR"][1]))
    print("\n# Table 3: min R(2N) (N); min, max, mean of R(2N)/HL(2N) on I_m")
    for m in sorted(stats):
        s = stats[m]
        print("%-2d %-15s minR %d (%d)  ratio min %.4f max %.4f mean %.4f" % (
            m, interval_label(m), s["R"][0], s["R"][1], s["rmin"], s["rmax"],
            s["rsum"] / cnt_N[m]))
    print("\n# Table 4: max |A\\E|, max F, max U (N), mean U, share sum F / sum |A\\E| on I_m")
    for m in sorted(stats):
        s = stats[m]
        print("%-2d %-15s max|A\\E| %d  maxF %d  maxU %d (%d)  meanU %.3f  share %.4f  F>miss: %d" % (
            m, interval_label(m), s["miss"][0], s["Fmax"], s["Umax"][0], s["Umax"][1],
            sum_U[m] / cnt_N[m], sum_F[m] / sum_miss[m] if sum_miss[m] else 1.0, s["Fbad"]))


if __name__ == "__main__":
    sys.exit(main())
