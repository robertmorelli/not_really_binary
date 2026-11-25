#!/usr/bin/env python3
"""Correctness tests: brute force vs verify.py vs the C scanners."""
import subprocess, sys, os
from verify import exact, interval

def ok01(n, b):
    while n:
        if n % b > 1: return False
        n //= b
    return True

def brute(TOP, L):
    out = []
    for bits in range(1 << L):
        n, x, p = TOP**L, bits, 1
        while x:
            if x & 1: n += p
            p *= TOP; x >>= 1
        if all(ok01(n, b) for b in range(3, TOP)): out.append(n)
    return sorted(out)

fail = 0
# 1. exact resolver == brute force
for TOP, Lmax in ((4, 14), (5, 14), (6, 13)):
    for L in range(1, Lmax + 1):
        if brute(TOP, L) != exact(TOP, L, True):
            print("MISMATCH exact", TOP, L); fail = 1
print("exact resolver matches brute force")
assert exact(5, 7, True) == [82000]

# 2. interval resolver never kills an L that has a solution; agrees with exact otherwise
for TOP in (4, 5, 6):
    for L in range(1, 120):
        has = bool(exact(TOP, L)); dead = interval(TOP, L)
        if has and dead: print("UNSOUND interval", TOP, L); fail = 1
        if not has and not dead: print("note: interval unresolved w/o solution", TOP, L)
print("interval resolver sound on L<120")

# 3. C scanner: final verdicts must equal exact for all L < 400
for TOP in (4, 5, 6):
    for f in ("candidates_b%d.log" % TOP,):
        if os.path.exists(f): os.remove(f)
    r = subprocess.run(["./scan%d" % TOP, "--start", "1", "--end", "400", "--no-state", "--quiet", "--threads", "2"],
                       capture_output=True, text=True)
    found = {int(l.split()[1][2:-1]) for l in r.stdout.splitlines() if l.startswith("***")}
    truth = {L for L in range(1, 400) if exact(TOP, L)}
    print("TOP=%d: scanner reports %d magnitudes with solutions, truth %d" % (TOP, len(found), len(truth)))
    if found != truth: print("  MISMATCH", sorted(found ^ truth)[:20]); fail = 1
    print("  ", r.stdout.strip().splitlines()[-1])
sys.exit(fail)
