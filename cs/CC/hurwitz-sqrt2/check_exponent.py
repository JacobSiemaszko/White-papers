#!/usr/bin/env python3
"""
Exact evaluation of the bound  P(N) <= sum_{s=-2h}^{2h} min(R_s^row, R_s^col)
from the pieces of Theorem B (ETH paper, Appendix B), where
  R_s^row = sum_{i=0}^{2h} p(s+i),   R_s^col = sum_{i=0}^{2h} p(2h-s-i),
h = least integer >= 2 with p(h) >= 2^lambda, p = partition function.
Prints log2(sum)/lambda, which converges to sqrt(2) ~ 1.4142 (see note.md, section 6).
Standard library only.  Run:  python3 check_exponent.py [lambda ...]
"""
import math, sys

def partitions_upto(M):
    """p(0..M) by Euler's pentagonal recurrence (exact integers)."""
    p = [0] * (M + 1); p[0] = 1
    for n in range(1, M + 1):
        s = 0; k = 1
        while True:
            g1 = k * (3 * k - 1) // 2; g2 = k * (3 * k + 1) // 2
            if g1 > n: break
            sign = 1 if k % 2 else -1
            s += sign * p[n - g1]
            if g2 <= n: s += sign * p[n - g2]
            k += 1
        p[n] = s
    return p

def main(lams):
    cHR = math.pi * math.sqrt(2 / 3) / math.log(2)
    hmax = int((max(lams) / cHR) ** 2 * 1.3) + 50
    P = partitions_upto(4 * hmax)
    pre = [0] * (len(P) + 1)
    for i, v in enumerate(P): pre[i + 1] = pre[i] + v
    def S(a, b):  # sum p(j), max(a,0) <= j <= b
        a = max(a, 0)
        return pre[b + 1] - pre[a] if b >= a else 0
    print(f"{'lambda':>7} {'h':>7} {'log2(sum)':>10} {'exponent':>9}   (Hrubes 2024: 1.615, limit: {math.sqrt(2):.4f})")
    for lam in lams:
        h = 2
        while P[h] < 2 ** lam: h += 1
        tot = 0
        for s in range(-2 * h, 2 * h + 1):
            tot += min(S(s, s + 2 * h), S(-s, -s + 2 * h))
        lb = math.log2(tot)
        print(f"{lam:7d} {h:7d} {lb:10.1f} {lb / lam:9.4f}")

if __name__ == "__main__":
    lams = [int(a) for a in sys.argv[1:]] or [20, 40, 60, 80, 120, 200, 300, 400, 500, 600]
    main(lams)
