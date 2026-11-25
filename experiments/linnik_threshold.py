#!/usr/bin/env python3
"""
Threshold check for the six-power (Linnik--Goldbach) representation, Proposition
\\ref{prop:six-powers-ext} of doc/paper.tex.

What is checked
---------------
Johnston--Trudgian (GRH): every sufficiently large even n is p + q + (six powers of 2)
with p, q prime.  Their theorem gives no explicit threshold n0.  The reach of the verified
Goldbach range [4, B], B = 4*10**18 (Oliveira e Silva--Herzog--Pardi) is
    every even n with 10 <= n <= B + 63 * 2**61 is p + q + (six powers of 2).
Hence, if n0 <= REACH + 1 (REACH = B + 63 * 2**61), every even n >= 10 has such a
representation under GRH.

  1. exact integer arithmetic for REACH, for the bound 1.49e20 and the window chain;
  2. a complete brute-force check of the same construction at a small scale: B_small is
     verified by a sieve, T_small = 2**k <= B_small - 3, and EVERY even n in
     [10, B_small + 63 * T_small] is written as p + q + (six powers of 2) explicitly;
  3. an optional threshold n0 (command line): reports whether n0 <= REACH + 1.

What is NOT checked
-------------------
* The GRH, and the Lean proof of it, are not used and not tested.
* The statement is about p + q + six powers of 2, with p, q not necessarily distinct.
  It is not the Goldbach conjecture and not the distinct-prime Goldbach conjecture: the
  six powers of 2 are part of the representation and cannot be removed by this argument.

Only the Python standard library is used; no package of the repository is needed.

Usage:
    python experiments/linnik_threshold.py            # steps 1 and 2
    python experiments/linnik_threshold.py N0         # also step 3, N0 an integer
                                                      # (e.g. 10**20 or 148000000000000000000)
"""
import sys

B = 4 * 10 ** 18
T = 2 ** 61
REACH = B + 63 * T


def six_powers(a, base):
    """Exponents e_1..e_6 with sum 2**e_i = a * 2**base, 1 <= a <= 63."""
    exps = [base + i for i in range(6) if (a >> i) & 1]
    while len(exps) < 6:
        exps.sort()
        e = exps.pop()
        exps += [e - 1, e - 1]
    assert len(exps) == 6 and sum(2 ** e for e in exps) == a * 2 ** base
    return exps


def check_exact():
    assert T <= B - 4
    assert REACH > 149 * 10 ** 18, REACH
    assert REACH < 150 * 10 ** 18, REACH
    prev_end = B + 6
    for a in range(1, 64):
        six_powers(a, 61)
        lo, hi = a * T + 4, a * T + B
        assert lo <= prev_end + 2, "gap before window %d" % a
        prev_end = max(prev_end, hi)
    assert prev_end >= REACH
    print("exact: REACH = B + 63*2^61 = %d  (%.6e)" % (REACH, REACH))
    print("exact: threshold condition is n0 <= REACH + 1 = %d" % (REACH + 1), flush=True)


def sieve(limit):
    s = bytearray([1]) * (limit + 1)
    s[0] = s[1] = 0
    for i in range(2, int(limit ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(range(i * i, limit + 1, i)))
    return s


def check_small(b_small=10 ** 6, k=19):
    """Brute-force analogue: all even n in [10, b_small + 63 * 2**k]."""
    t = 2 ** k
    assert t <= b_small - 4
    print("small scale: sieve up to %d ..." % b_small, flush=True)
    s = sieve(b_small)
    primes = [p for p in range(2, b_small // 2 + 1) if s[p]]
    # verified range: every even m in [4, b_small] is p + q (least prime p stored)
    least = {}
    for m in range(4, b_small + 1, 2):
        for p in primes:
            if p > m // 2:
                raise AssertionError("Goldbach fails at %d" % m)
            if s[m - p]:
                least[m] = p
                break
        if m % 100000 == 0:
            print("  verified range: m = %d / %d" % (m, b_small), flush=True)
    top = b_small + 63 * t
    total = (top - 10) // 2 + 1
    print("small scale: checking %d even n in [10, %d] ..." % (total, top), flush=True)
    count = 0
    for n in range(10, top + 1, 2):
        if n <= b_small + 6:
            m, exps = n - 6, [0] * 6
        else:
            a = -(-(n - b_small) // t)
            assert 1 <= a <= 63
            m = n - a * t
            exps = six_powers(a, k)
        assert 4 <= m <= b_small and m % 2 == 0
        p = least[m]
        q = m - p
        assert s[p] and s[q] and p + q + sum(2 ** e for e in exps) == n
        count += 1
        if count % 2000000 == 0:
            print("  n = %d  (%d / %d, %.0f%%)" % (n, count, total, 100.0 * count / total),
                  flush=True)
    print("small scale: B = %d, T = 2^%d: all %d even n in [10, %d] checked"
          % (b_small, k, count, top), flush=True)


def main():
    check_exact()
    check_small()
    if len(sys.argv) > 1:
        n0 = int(sys.argv[1])
        ok = n0 <= REACH + 1
        print("n0 = %d: %s REACH + 1" % (n0, "<=" if ok else ">"))
        print("six-power representation for every even n >= 10 under GRH: %s"
              % ("follows" if ok else "not implied"))
    print("# statement checked: p + q + six powers of 2; not the Goldbach conjecture")


if __name__ == "__main__":
    sys.exit(main())
