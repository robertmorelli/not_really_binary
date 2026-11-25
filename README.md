# not_really_binary

A fast search and Lean 4 formalization for numbers whose digits are all `0` or `1` in several bases at once.

- **OEIS A258107**: $a(n)$ is the smallest number $> 1$ whose representation in every base $2 \dots n$ uses only the digits `0` and `1`. Known terms: `2, 3, 4, 82000`. $a(6)$ is unknown and conjectured not to exist.
- **OEIS A146025**: numbers that are all-0/1 in bases `2, 3, 4, 5`. Known terms: `0, 1, 82000`. Any $a(6)$ would also be a term here.

The scanners do not expect to find new terms; they raise the lower bound below which no further term exists.

## Idea

The leading digits of $N$ in base $b$ depend only on the fractional part of $\log_b(N)$. Instead of testing candidate numbers, the scanner tests *lengths*.

Fix the top base $B$ (5 or 6) and a length $L$. Any solution with $L+1$ base-$B$ digits has the form $N = B^L \cdot u$, where $u$ lies in a Cantor-like set $C_B \subset [1, B/(B-1)]$. For each smaller base $b$, the same $N$ must satisfy $u \in s_b \cdot C_b$, where $s_b = b^m / B^L$ is determined by $\operatorname{frac}(L \log_b B)$. If those sets cannot intersect, no number of length $L$ is a solution.

Work per length is $O(1)$, regardless of how many digits $N$ has. Earlier searches worked on explicit candidates, where each step costs time proportional to the size of the number.

## Stages

Each stage only rejects a length when padded intervals are disjoint. Survivors move to the next, more expensive stage.

| Stage | What it does | Arithmetic |
|---|---|---|
| 1. Arcs | $\operatorname{frac}(L \log_b B)$ must fall in a fixed arc for every base $b$ | 64-bit add and compare |
| 2. Bitmaps | Per-base table of phases compatible with base $B$ to several digits | table lookup |
| 3. `ddfs` | Joint refinement of all bases down to interval width `2e-12` | IEEE 754 doubles |
| 4. `mdfs` | Joint refinement down to width $2^{-150}$ | 192-bit fixed point |
| 5. `verify.py` | Exact search for $L \le 2000$, otherwise 320-bit integer intervals | Python integers |

For top base 6, stages 1 and 2 reject ~99.95% of lengths. The GPU front-ends (`gpuscan.m` for Metal, `gpuscan_cl.c` for OpenCL) run stages 1–2 on the GPU and stream survivors to the CPU for stages 3–5 in parallel.

## Repository layout

```text
a258107/
  scan.c          CPU scanner (all four in-process stages, threading, checkpointing)
  gpuscan.m       Metal GPU front-end (stages 1–2 on GPU, stages 3–5 on CPU)
  gpuscan_cl.c    OpenCL GPU front-end (for non-Apple GPUs)
  verify.py       Rigorous integer resolver for a single length (stage 5)
  gen_consts.py   Generates consts.h (256-bit logarithm constants)
  consts.h        Pre-generated constants (checked in)
  test.py         Correctness tests against brute force and exact resolution
  Makefile        Build targets for CPU, Metal, OpenCL, and tests
proof/
  NRB/            Lean 4 formalization (no dependencies beyond core Lean 4)
  gen_ranges.py   Generates parallel range-checking modules for NRB.Bound
  not_really_binary.typ / .pdf
                  Writeup of what is proved, what is computed, and what remains open
```

## Build and run

Requires a C compiler with `__int128` (clang or gcc on a 64-bit target) and `python3`.

```sh
cd a258107
make test       # builds scan4, scan5, scan6 and runs test.py (~10 s)
./scan6         # CPU scan for a(6); runs until stopped
./scan5         # CPU scan for bases 2..5
```

`TOPBASE=4` (`scan4`) exists only for testing, since bases 3 and 4 have many common solutions.

### GPU scanner (top base 6)

```sh
cd a258107
make gpu        # macOS (Apple Silicon / Metal) -> ./gpuscan
./gpuscan --batches 1 --no-state --check   # verify GPU matches CPU on first batch
./gpuscan       # runs until stopped

make opencl     # Linux / non-Apple GPUs (OpenCL) -> ./gpuscan_cl
```

### CPU scanner options (`scan4`, `scan5`, `scan6`)

| Option | Meaning |
|---|---|
| `--start L` | First length to scan (default: resume from state file, else 1) |
| `--end L` | Stop before this length (default and maximum: $2^{56}$) |
| `--threads T` | Worker threads (default 8) |
| `--no-state` | Do not read or write the state file |
| `--quiet` | Suppress progress lines |
| `--dump-s L` | Print the 192-bit scale factors for length $L$ and exit |

Progress is written to `state_b<B>.txt` (or `state_gpu_b6.txt` / `state_cl_b6.txt`) every few seconds, and a stopped run resumes from it. `Ctrl-C` stops cleanly after the current batch.

Lengths that survive stage 4 are passed to `verify.py` and logged to `candidates_*.log`. Anything not proved dead is printed as a line starting with `***`. With `scan5` this happens once, at $L = 7$, which resolves to `82000`.

## Results so far

Measured on an Apple Silicon laptop (November 2026):

| Scan | Lengths covered | No new term below about | Throughput |
|---|---|---|---|
| Top base 6 (Metal GPU + CPU) | $L < 8.9 \times 10^{13}$ | $10^{6.9 \times 10^{13}}$ | $4.1 \times 10^{10}$ lengths/s |
| Top base 6 (CPU, 8 cores) | — | — | $3.7 \times 10^{9}$ lengths/s |
| Top base 5 (CPU, 8 cores) | $L < 3 \times 10^{9}$ | $10^{2.1 \times 10^{9}}$ | $3.2 \times 10^{8}$ lengths/s |

For comparison, the OEIS A146025 page records a 2015 search of bases 2..5 to about 11 million decimal digits.

## Machine-checked proof (Lean 4)

`proof/` is a standalone Lake project with no dependencies beyond core Lean 4. It formalizes the same interval criterion in natural-number arithmetic, proves the checker sound, and runs it.

| Theorem | Statement |
|---|---|
| `ok_iff_dec` | A number has only 0/1 digits in base $b$ iff the base-$b$ decoder outputs it |
| `a5` | $a(5) = 82000$ |
| `a6_gt_big` | $a(6) \ge 6^{3000}$, from a search on the low digits |
| `blocks_sound` | Soundness of the magnitude sweep |
| `a6_bound` | $a(6) \ge 6^{17179872184} \approx 10^{1.3 \times 10^{10}}$ |

```sh
cd proof
lake build NRB                # verify the core theorems (~seconds)
lake build NRB.Bound          # verify the full bound (~16 minutes on 8 cores)
python3 gen_ranges.py 32      # extend to more ranges, then rebuild
```

The final finite evaluations use `native_decide`, which trusts the Lean compiler. The Lean checker takes about $0.56\ \mu\text{s}$ per length, roughly $1000\times$ slower than the C scanner. See [proof/not_really_binary.typ](proof/not_really_binary.typ) (and [proof/not_really_binary.pdf](proof/not_really_binary.pdf)) for what is proved, what is only computed, and why none of it proves that $a(6)$ does not exist.

## How far to trust the bounds

What has been checked:

- `verify.py` in exact mode matches brute-force enumeration for small $L$ with top base 4, 5, and 6.
- The CPU scanner's final verdicts match the exact resolver for every $L < 400$. With top base 4 it flags exactly the 210 lengths that contain a solution.
- The GPU scanner's `--check` mode confirms exact agreement with the CPU scanner's stage-1 and stage-2 survivor counts on the same batch.
- The scale factors computed in C agree with an independent Python integer computation to about 185 bits.

What has not:

- Stages 1–3 of the C/GPU scanners rely on the platform `exp` being accurate to a few ulp and on hand-chosen padding margins. There is no written error analysis, so the C/GPU bounds are careful engineering rather than a formal proof.
- The padding analysis assumes $L < 2^{56}$, which is where the scan stops.
