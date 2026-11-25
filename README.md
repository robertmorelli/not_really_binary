# not_really_binary

A fast search for numbers whose digits are all 0 or 1 in several bases at once.

- **OEIS A258107**: a(n) is the smallest number > 1 whose representation in every base 2..n uses only the digits 0 and 1. Known terms: 2, 3, 4, 82000. a(6) is unknown and conjectured not to exist.
- **OEIS A146025**: numbers that are all-0/1 in bases 2, 3, 4 and 5. Known terms: 0, 1, 82000. Any a(6) would also be a term here.

The scanner does not find new terms (none are expected). It raises the lower bound below which no further term exists.

## Idea

The leading digits of N in base b depend only on the fractional part of log_b(N). So instead of testing candidate numbers, the scanner tests *lengths*.

Fix the top base B (5 or 6) and a length L. Any solution with L+1 base-B digits is N = B^L · u, where u lies in a Cantor-like set inside [1, B/(B−1)]. For each smaller base b, the same N must satisfy u ∈ s_b · C_b, where s_b = b^m / B^L is determined by the fractional part of L · log_b(B). If those sets cannot intersect, no number of that length is a solution.

The work per length is constant, regardless of how many digits the numbers have. Earlier searches worked on explicit candidates, where each step costs time proportional to the size of the number.

## Stages

Each stage only rejects a length when padded intervals are disjoint. Lengths that survive move to the next, more expensive stage.

| Stage | What it does | Arithmetic |
|---|---|---|
| 1. Arcs | The phase frac(L · log_b B) must fall in a fixed arc for every base b | 64-bit add and compare |
| 2. Bitmaps | Per-base table of phases compatible with base B to several digits | table lookup |
| 3. `ddfs` | Joint refinement of all bases down to interval width 2e-12 | doubles |
| 4. `mdfs` | Joint refinement down to width 2^-150 | 192-bit fixed point |
| 5. `verify.py` | Exact search for L ≤ 2000, otherwise 320-bit integer intervals | Python integers |

For top base 6, stages 1 and 2 reject about 99.9% of lengths.

## Files

All code is in `a258107/`.

| File | Purpose |
|---|---|
| `scan.c` | The scanner: all four in-process stages, threading, checkpointing |
| `verify.py` | Rigorous resolver for a single length, called for stage-4 survivors |
| `gen_consts.py` | Generates `consts.h` (256-bit logarithm constants) |
| `consts.h` | Generated constants, checked in so no generation step is needed |
| `test.py` | Correctness tests |

## Build and run

Needs a C compiler with `__int128` (clang or gcc on a 64-bit target) and `python3`.

```sh
cd a258107
for B in 4 5 6; do cc -O3 -DTOPBASE=$B scan.c -o scan$B -lpthread -lm; done
python3 test.py        # about 10 seconds
./scan6                # a(6); runs until stopped
./scan5                # bases 2..5
```

`TOPBASE=4` exists only for testing, since bases 3 and 4 have many common solutions.

Options:

| Option | Meaning |
|---|---|
| `--start L` | First length to scan (default: resume from the state file, else 1) |
| `--end L` | Stop before this length (default and maximum: 2^56) |
| `--threads T` | Worker threads (default 8) |
| `--no-state` | Do not read or write the state file |
| `--quiet` | No progress lines |
| `--dump-s L` | Print the 192-bit scale factors for length L and exit |

Progress is written to `state_b<B>.txt` every few seconds, and a stopped run resumes from it. Ctrl-C stops cleanly after the current batch.

Lengths that survive stage 4 are passed to `verify.py` and logged to `candidates_b<B>.log`. Anything not proved dead is printed as a line starting with `***`. With `scan5` this happens once, at L=7, which resolves to 82000.

## Results so far

Measured on an 8-core Apple Silicon laptop (November 2026):

| Scan | Lengths covered | No new term below about | Rate |
|---|---|---|---|
| Top base 6 | L < 6×10^10 | 10^(4.7×10^10) | 3.7×10^9 lengths/s |
| Top base 5 | L < 3×10^9 | 10^(2.1×10^9) | 3.2×10^8 lengths/s |

For comparison, the A146025 page records a 2015 search of bases 2..5 to about 11 million decimal digits.

## How far to trust the bounds

What has been checked:

- `verify.py` in exact mode matches brute-force enumeration for small L with top base 4, 5 and 6.
- The scanner's final verdicts match the exact resolver for every L < 400. With top base 4 it flags exactly the 210 lengths that contain a solution.
- The scale factors computed in C agree with an independent Python integer computation to about 185 bits.

What has not:

- Stages 1 to 3 rely on the platform `exp` being accurate to a few ulp and on hand-chosen padding margins. There is no written error analysis, so the bounds are careful engineering rather than a formal proof.
- The padding analysis assumes L < 2^56, which is why the scan stops there.
