#!/usr/bin/env python3
"""Generate the range modules and NRB/Bound.lean.

  gen_ranges.py COUNT [BLOCKS_PER_RANGE]

Each range module proves, by one native_decide run, that no solution has between
A and A + BLOCKS*16384 base-6 digits.  Ranges start at length 3000 (below that is
`a6_gt_big`).  Re-running with a larger COUNT only adds modules; `lake build`
reuses the ones already checked.
"""
import os, sys

BLK = 16384
START = 3000
count = int(sys.argv[1])
blocks = int(sys.argv[2]) if len(sys.argv) > 2 else 65536
os.makedirs("NRB/Ranges", exist_ok=True)
span = blocks * BLK
for i in range(count):
    a = START + i * span
    with open("NRB/Ranges/R%d.lean" % i, "w") as f:
        f.write("import NRB.Sweep\n\n")
        f.write("theorem r%d_ok : blocks %d %d %d = true := by native_decide\n\n" % (i, BLK, blocks, a))
        f.write("theorem r%d : cover %d %d := blocks_sound %d %d %d r%d_ok\n" % (i, a, a + span, BLK, blocks, a, i))
end = START + count * span
chain = "r%d" % (count - 1)
for i in range(count - 2, -1, -1):
    chain = "cover_trans r%d (%s)" % (i, chain)
with open("NRB/Bound.lean", "w") as f:
    for i in range(count):
        f.write("import NRB.Ranges.R%d\n" % i)
    f.write("\n/-- No solution has between 3000 and %d base-6 digits. -/\n" % end)
    f.write("theorem cover_all : cover %d %d := %s\n\n" % (START, end, chain))
    f.write("/-- Verified lower bound: a(6), if it exists, is at least 6^%d. -/\n" % end)
    f.write("theorem a6_bound : ∀ N, 1 < N → N < 6 ^ %d → good 6 N = false :=\n  below_of_cover cover_all\n\n" % end)
    f.write("#print axioms a6_bound\n")
print("ranges: %d, lengths per range: %d, bound exponent: %d" % (count, span, end))
