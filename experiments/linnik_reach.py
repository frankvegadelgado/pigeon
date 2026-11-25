#!/usr/bin/env python3
"""
Reach of the six-power representation from the verified Goldbach range [4, B], B = 4*10**18.

For T = 2**61 and a = 1, ..., 63 put s = a*T. Then
  * s is a sum of exactly six powers of two (the binary digits of a, each power split
    into two halves until six terms are reached);
  * if n is even and s + 4 <= n <= s + B, then n - s is an even integer in [4, B], hence
    n - s = p + q with p, q prime by the verification, and n = p + q + s.
The windows [a*T + 4, a*T + B] chain without gaps because T <= B - 3, so every even n in
[B + 7, B + 63*T] has such a representation. The script checks these facts with exact
integer arithmetic, and checks the construction on sample values of n.

Only the Python standard library is used; no package of the repository is needed.

Usage:
    python experiments/linnik_reach.py
"""
import random
import sys

B = 4 * 10 ** 18
T = 2 ** 61


def six_powers(a):
    """Exponents e_1..e_6 with sum 2**e_i = a * T, for 1 <= a <= 63."""
    exps = [61 + i for i in range(6) if (a >> i) & 1]
    while len(exps) < 6:
        exps.sort()
        e = exps.pop()          # split the largest power into two halves
        exps += [e - 1, e - 1]
    assert len(exps) == 6 and sum(2 ** e for e in exps) == a * T
    return exps


def main():
    assert T <= B - 3
    prev_end = B + 6            # n <= B + 6 is covered by the verification with 2^0 * 6
    for a in range(1, 64):
        exps = six_powers(a)
        lo, hi = a * T + 4, a * T + B
        assert lo <= prev_end + 2, "gap before window %d" % a
        prev_end = max(prev_end, hi)
        print("a = %2d  s = %d  exponents %s  window [%d, %d]" % (a, a * T, exps, lo, hi),
              flush=True)
    top = B + 63 * T
    print("# every even n in [10, %d] is p + q + (six powers of two): reach %.4e"
          % (top, top))
    assert prev_end >= top
    random.seed(1)
    for _ in range(100000):
        n = 2 * random.randint((B + 8) // 2, top // 2)
        a = -(-(n - B) // T)    # ceil((n - B) / T)
        assert 1 <= a <= 63
        m = n - a * T
        assert 4 <= m <= B and m % 2 == 0
    print("# construction checked on 100000 random even n up to %d" % top)


if __name__ == "__main__":
    sys.exit(main())
