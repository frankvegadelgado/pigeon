#!/usr/bin/env python3
"""
Experiment for the paper "Nested Squares and Distinct-Prime Goldbach Partitions".

Computes, for every N in [4, 2**14],
    E_N, H(N) = log^2(2N) - ((N-3) - |E_N|), C_N, R(2N) = |C_N & D_N|,
    the set (C_N & E_N) \\ D_N and the pigeonhole count |C_N| > |A_N \\ E_N|,
and prints the dyadic-interval tables of the computational section.

Only the Python standard library is used; the script is self-contained and does
not need the repository package to be installed.

Usage:
    python experiments/experiment.py            # full run, N in [4, 2**14]
    python experiments/experiment.py --max 4096 # smaller range
    python experiments/experiment.py --missing 1327   # list A_N \\ E_N for one N
"""
import argparse
import math
import sys
import time


def sieve(limit):
    """Boolean list is_prime[0..limit]."""
    flags = bytearray([1]) * (limit + 1)
    flags[0:2] = b"\x00\x00"
    for i in range(2, int(limit ** 0.5) + 1):
        if flags[i]:
            flags[i * i::i] = bytearray(len(range(i * i, limit + 1, i)))
    return flags


def sets_for(N, is_prime):
    """Return (A, C, D, E) as Python sets for the integer N >= 4."""
    A = range(1, N - 2)  # 1..N-3
    C = {M for M in A if is_prime[N - M]}
    D = {M for M in A if is_prime[N + M]}
    # E_N: half-differences (Q-P)/2 of odd primes P < N < Q < 2N.
    low = [P for P in range(3, N) if is_prime[P]]
    high = [Q for Q in range(N + 1, 2 * N) if is_prime[Q]]
    rev = 0
    for P in low:
        rev |= 1 << (2 * N - P)          # bit at 2N - P
    diff = 0
    for Q in high:
        diff |= rev >> (2 * N - Q)       # bits at Q - P
    E = set()
    d = diff
    while d:
        low_bit = d & -d
        pos = low_bit.bit_length() - 1
        if pos % 2 == 0 and 1 <= pos // 2 <= N - 3:
            E.add(pos // 2)
        d ^= low_bit
    return set(A), C, D, E


def dyadic_index(N):
    """m with N in I_2 = [4,8] or I_m = (2^m, 2^(m+1)]."""
    if N <= 8:
        return 2
    return (N - 1).bit_length() - 1


def interval_label(m):
    return "[4,8]" if m == 2 else "(2^%d,2^%d]" % (m, m + 1)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max", type=int, default=2 ** 14, help="largest N (default 2**14)")
    ap.add_argument("--missing", type=int, default=None,
                    help="print A_N \\ E_N for this N and exit")
    args = ap.parse_args()

    top = args.max
    is_prime = sieve(2 * top + 2)

    if args.missing is not None:
        N = args.missing
        A, C, D, E = sets_for(N, is_prime if 2 * N + 2 <= len(is_prime) - 1 else sieve(2 * N + 2))
        miss = sorted(A - E)
        print("N =", N, "|A_N \\ E_N| =", len(miss))
        print(miss)
        return

    t0 = time.time()
    print("Sieve done (limit %d)" % len(is_prime), flush=True)
    stats = {}
    fails_pigeon = []
    no_CE_minus_D = []
    first_CE_minus_D = {}
    min_R = (10 ** 9, None)
    print("Running N = 4 .. %d" % top, flush=True)
    step = max(1, top // 100)
    for N in range(4, top + 1):
        if N % step == 0 or N == top:
            print("  progress: N = %d / %d (%.0f%%), elapsed %.1f s" % (
                N, top, 100.0 * N / top, time.time() - t0), flush=True)
        A, C, D, E = sets_for(N, is_prime)
        miss = len(A) - len(E)
        H = math.log(2 * N) ** 2 - ((N - 3) - len(E))
        R = len(C & D)
        HR = math.log(2 * N) ** 2 - ((N - 3) - R)
        if R < min_R[0]:
            min_R = (R, N)
        if not len(C) > miss:
            fails_pigeon.append(N)
        diffset = (C & E) - D
        if diffset:
            first_CE_minus_D[N] = min(diffset) if N <= 12 else None
        else:
            no_CE_minus_D.append(N)
        m = dyadic_index(N)
        s = stats.setdefault(m, {"H": (1e18, 0), "miss": (-1, 0), "ratio": (1e18, 0),
                                  "HR": (1e18, 0), "R0": (10 ** 9, 0)})
        if H < s["H"][0]:
            s["H"] = (H, N)
        if miss > s["miss"][0]:
            s["miss"] = (miss, N)
        if len(E) / N < s["ratio"][0]:
            s["ratio"] = (len(E) / N, N)
        if HR < s["HR"][0]:
            s["HR"] = (HR, N)
        if R < s["R0"][0]:
            s["R0"] = (R, N)

    print("# N in [4, %d]; elapsed %.1f s" % (top, time.time() - t0))
    print("\n# Table: min H(N), largest |A_N \\ E_N| (N), min |E_N|/N on I_m")
    print("m  interval        N(minH)  min H(N)    max|A\\E| (N)     min|E|/N")
    for m in sorted(stats):
        s = stats[m]
        print("%-2d %-15s %-8d %-11.6f %4d (%d)%s %.6f" % (
            m, interval_label(m), s["H"][1], s["H"][0], s["miss"][0], s["miss"][1],
            " " * 4, s["ratio"][0]))
    print("\n# Table: min H_R(N) = log^2(2N) - ((N-3) - R(2N)) on I_m")
    for m in sorted(stats):
        s = stats[m]
        print("%-2d %-15s N=%-6d min H_R = %.2f" % (m, interval_label(m), s["HR"][1], s["HR"][0]))
    print("\n# (1) minimum of R(2N) over N in [4,%d]: %d at N=%d" % (top, min_R[0], min_R[1]))
    print("# (2) N with |C_N| <= |A_N \\ E_N|:", fails_pigeon)
    print("# (3) N with (C_N & E_N) \\ D_N empty:", no_CE_minus_D,
          "; nonempty for", (top - 3) - len(no_CE_minus_D), "of", top - 3, "values")
    print("#     first elements for N <= 12:", {N: M for N, M in first_CE_minus_D.items() if M is not None})

    # (4) Lemma elementary: x/(log x + 2) - 2 > log^2(2x), integers 2 <= N <= 10**6.
    print("Checking the elementary inequality for 2 <= x <= 10^6 ...", flush=True)
    bad = [x for x in range(2, 10 ** 6 + 1)
           if not (x / (math.log(x) + 2) - 2 > math.log(2 * x) ** 2)]
    print("# (4) integers 2 <= x <= 10^6 where the inequality fails: largest =", max(bad),
          "; holds for all x >=", max(bad) + 1)


if __name__ == "__main__":
    sys.exit(main())
