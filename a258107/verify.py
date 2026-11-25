#!/usr/bin/env python3
"""Rigorous resolver for one magnitude L (integer arithmetic only, no floats in proofs).

Question: is there an integer N with TOP^L <= N < 2*TOP^L whose digits are all
0/1 in every base 3..TOP?   (base 2 is automatic)

  verify.py TOP L [--mode exact|interval] [--all] [--dump-s]

Prints one of:
  DEAD                 no such N exists (proved)
  SOLUTION n [n ...]   exact solutions (exact mode)
  UNRESOLVED           interval mode could not kill it at ~260 bits of depth
"""
import sys
from itertools import product
from math import log

EXACT_LIMIT = 2000  # use exact integers up to this L
P = 320  # fixed-point fraction bits for interval mode
Q = P + 64  # mantissa bits for power intervals
STOP_BITS = P - 60


def exact(TOP, L, want_all=False):
    bases = [TOP] + list(range(3, TOP))
    loN = TOP**L
    hiN = (TOP ** (L + 1) - 1) // (TOP - 1)
    cands = [[L]]
    for b in bases[1:]:
        ms, m = [], 0
        while b**m <= hiN:
            if (b ** (m + 1) - 1) // (b - 1) >= loN:
                ms.append(m)
            m += 1
        cands.append(ms)
    sols = []
    for ms in product(*cands):
        pw = [[b**j for j in range(m + 1)] for b, m in zip(bases, ms)]
        tail = [[(x - 1) // (b - 1) for x in row] for b, row in zip(bases, pw)]
        # node: per base (lo, k) ; interval [lo, lo + tail[m-k]]
        root = tuple((pw[i][ms[i]], 0) for i in range(len(bases)))
        stack = [root]
        while stack:
            st = stack.pop()
            lo = max(n[0] for n in st)
            hi = min(n[0] + tail[i][ms[i] - n[1]] for i, n in enumerate(st))
            if lo > hi:
                continue
            w, wi = -1, -1
            for i, n in enumerate(st):
                wd = tail[i][ms[i] - n[1]]
                if wd > w:
                    w, wi = wd, i
            if w == 0:
                sols.append(lo)
                if not want_all:
                    return sols
                continue
            nlo, k = st[wi]
            for d in (1, 0):
                c = (nlo + d * pw[wi][ms[wi] - k - 1], k + 1)
                stack.append(st[:wi] + (c,) + st[wi + 1 :])
    return sorted(set(sols))


def ipow(b, n):
    """(lo, hi, e) with lo*2^e <= b^n <= hi*2^e, mantissas ~Q bits."""

    def norm(lo, hi, e):
        sh = hi.bit_length() - Q
        if sh > 0:
            lo >>= sh
            hi = -((-hi) >> sh)
            e += sh
        return lo, hi, e

    r = (1, 1, 0)
    x = (b, b, 0)
    while n:
        if n & 1:
            r = norm(r[0] * x[0], r[1] * x[1], r[2] + x[2])
        n >>= 1
        if n:
            x = norm(x[0] * x[0], x[1] * x[1], x[2] + x[2])
    return r


def scales(TOP, L):
    """For each other base b: list of (m, slo, shi), enclosures of b^m/TOP^L * 2^P
    for every m that could be the top digit position."""
    dlo, dhi, de = ipow(TOP, L)
    one = 1 << P
    res = []
    for b in range(3, TOP):
        m0 = int(L * log(TOP) / log(b))
        lst = []
        for m in range(max(0, m0 - 3), m0 + 4):
            nlo, nhi, ne = ipow(b, m)
            sh = P + ne - de
            if sh >= 0:
                slo = (nlo << sh) // dhi
                shi = -((-(nhi << sh)) // dlo)
            else:
                slo = nlo // (dhi << -sh)
                shi = -((-nhi) // (dlo << -sh))
            # need s*[1, b/(b-1)] to meet [1, TOP/(TOP-1)]
            if shi * b >= one * (b - 1) and slo * (TOP - 1) <= one * TOP:
                lst.append((m, slo, shi))
        res.append((b, lst))
    return res


def interval(TOP, L):
    sc = scales(TOP, L)
    one = 1 << P
    bases = [TOP] + [b for b, _ in sc]
    stop = 1 << (P - STOP_BITS)
    for combo in product(*[lst for _, lst in sc]):
        slo = [one] + [c[1] for c in combo]
        shi = [one] + [c[2] for c in combo]

        def iv(i, p, k):
            b = bases[i]
            bk = b**k
            return (slo[i] * p) // bk, -((-(shi[i] * (p * (b - 1) + 1))) // ((b - 1) * bk))

        stack = [tuple((1, 0) for _ in bases)]
        while stack:
            st = stack.pop()
            ivs = [iv(i, p, k) for i, (p, k) in enumerate(st)]
            lo = max(a for a, _ in ivs)
            hi = min(b for _, b in ivs)
            if lo > hi:
                continue
            w, wi = -1, -1
            for i, (a, b) in enumerate(ivs):
                if b - a > w:
                    w, wi = b - a, i
            if w < stop:
                return False
            p, k = st[wi]
            for d in (1, 0):
                stack.append(st[:wi] + ((p * bases[wi] + d, k + 1),) + st[wi + 1 :])
    return True


def main():
    a = sys.argv[1:]
    TOP, L = int(a[0]), int(a[1])
    mode = None
    if "--mode" in a:
        mode = a[a.index("--mode") + 1]
    if "--dump-s" in a:
        for b, lst in scales(TOP, L):
            for m, slo, shi in lst:
                print(b, "%x" % (slo >> (P - 192)))
        return
    if mode is None:
        mode = "exact" if L <= EXACT_LIMIT else "interval"
    if mode == "exact":
        s = exact(TOP, L, "--all" in a)
        print("SOLUTION " + " ".join(map(str, s)) if s else "DEAD")
    else:
        print("DEAD" if interval(TOP, L) else "UNRESOLVED")


if __name__ == "__main__":
    main()
