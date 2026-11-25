#set document(title: "Numbers that are binary in every base up to 6")
#set page(margin: 2.4cm, numbering: "1")
#set text(size: 10.5pt)
#set par(justify: true)
#set heading(numbering: "1.")
#let thm(kind, name, body) = block(inset: (left: 0.9em), stroke: (left: 1.5pt + gray), spacing: 1.1em)[
  *#kind* #if name != none [(#name).] #body
]
#let lean(name) = text(size: 9pt, fill: rgb("#555"))[Lean: #raw(name)]

#align(center)[
  #text(size: 16pt, weight: "bold")[Numbers that are binary in every base up to 6]
  #v(0.2em)
  #text(size: 10pt)[What is proved, what is computed, and what is still open (OEIS A258107, A146025)]
]

#block(fill: rgb("#fff4e5"), inset: 0.9em, radius: 3pt, width: 100%)[
  *Status.* This note does *not* prove that $a(6)$ does not exist. That statement is an open problem.
  It contains (i) results that are fully proved and machine-checked in the Lean project `NRB/`, including $a(6) > 6^(17179872184) approx 10^(1.3 times 10^10)$,
  (ii) a search criterion that is proved here on paper but whose large-scale use rests on unverified C code,
  and (iii) a heuristic for non-existence. Section 6 says exactly where a proof is missing.
]

= The decoder framing

For a base $b >= 2$, the *base-$b$ decoder* reads a finite string of bits as a base-$b$ numeral:
$ D_b (d_(m) dots d_1 d_0) = sum_(i=0)^m d_i b^i, quad d_i in {0, 1}. $
A number $N$ is an output of $D_b$ exactly when every base-$b$ digit of $N$ is 0 or 1 (Theorem 1).
$D_2$ outputs every natural number, so base 2 imposes nothing.

*Definition.* $a(n)$ is the smallest $N > 1$ that is an output of every decoder $D_2, dots, D_n$.
Known values are $a(2), dots, a(5) = 2, 3, 4, 82000$.

This is the picture from arithmetic coding. Each base is a decoder over the alphabet ${0, dots, b-1}$
that subdivides an interval once per symbol. Here only the symbols 0 and 1 are valid, so each
subdivision leaves gaps, and the question is whether one number can be valid for several decoders at once.

= Machine-checked results

#thm("Theorem 1", "digits and decoding agree")[
  For $b >= 2$: every base-$b$ digit of $N$ is 0 or 1 if and only if $N = D_b (w)$ for some bit string $w$.
  #lean("ok_iff_dec")
]

#thm("Theorem 2", "window lemma")[
  For $b >= 1$ and any bit string $w$ of length $m$: $(b - 1) D_b (w) + 1 <= b^m$.
  Equivalently $D_b (w) <= (b^m - 1) \/ (b - 1)$, the value of the numeral $11 dots 1$.
  #lean("window")
]

_Proof._ Induction on $w$. For the empty string both sides are 1. If $w = d dot w'$ with $D_b (w) = d + b D_b (w')$ and $d <= 1$, then
$ (b-1)(d + b D_b (w')) + 1 <= (b - 1) + b (b-1) D_b (w') + 1 = b ((b-1) D_b (w') + 1) <= b dot b^(m-1). $ #h(1fr) $square$

#thm("Theorem 3", [$a(5) = 82000$])[
  82000 is an output of $D_3$, $D_4$ and $D_5$, and no $N$ with $1 < N < 82000$ is.
  #lean("a5")
]

#thm("Theorem 4", "verified bound")[
  No $N$ with $1 < N < 10^7$ is an output of all of $D_3, D_4, D_5, D_6$. So $a(6) >= 10^7$ if it exists.
  #lean("a6_gt")
]

#thm("Theorem 4b", "verified bound from the low digits")[
  No $N$ with $1 < N < 6^3000 approx 10^2334$ is an output of all of $D_3, D_4, D_5, D_6$.
  #lean("a6_gt_big")
]

_Proof idea._ Since $3^k$ and $4^(floor(k\/2))$ divide $6^k$, the residue $N mod 6^k$ determines the low $k$ base-3 digits and the low
$floor(k\/2)$ base-4 digits of $N$. So if $N$ is a solution, every truncation $N mod 6^k$ must have only 0/1 digits in base 6, and its
residues mod $3^k$ and mod $4^(floor(k\/2))$ must have only 0/1 digits in bases 3 and 4. Build the list of residues mod $6^k$ that pass,
extending one base-6 digit at a time; the list never exceeds 62 entries up to $k = 3000$. Lean proves that no solution can be missing
from the list (`run_complete`), then checks that the list at $k = 3000$ contains no solution other than 0 and 1. #h(1fr) $square$

Theorems 1 and 2 depend only on Lean's standard axioms. Theorems 3, 4 and 4b are finite checks run with
`native_decide`, which additionally trusts the Lean compiler; the reasoning that makes the check in 4b sufficient is proved in full.

= The interval criterion

Fix the top base $B$ and a length $L$. Suppose $N$ has $L + 1$ base-$B$ digits, all 0 or 1, and write $u = N \/ B^L$.

#thm("Lemma 5", "prefix intervals")[
  Let $b >= 3$ and let $N$ have $m + 1$ base-$b$ digits, all 0 or 1, the first $k + 1$ of which spell the bit string $p$
  (read as the integer $P = D_b (p)$). Then
  $ P b^(m-k) <= N <= P b^(m-k) + (b^(m-k) - 1) / (b - 1) < (P + 1/(b-1)) b^(m-k). $
]

_Proof._ $N = P b^(m-k) + D_b (t)$ where $t$ is the remaining $m - k$ digits; apply Theorem 2 to $t$. #h(1fr) $square$

Dividing by $B^L$ and writing $s_b = b^m \/ B^L$, Lemma 5 says $u$ lies in the interval
$ I_b (p) = [ s_b P b^(-k), thick s_b (P + 1/(b-1)) b^(-k) ]. $

#thm("Proposition 6", "criterion")[
  If for some depth $k$, every choice of prefixes $p_3, dots, p_B$ of length $k + 1$ (one per base, each starting with 1)
  gives $inter.big_b I_b (p_b) = emptyset$, then no $N$ with $L + 1$ base-$B$ digits is an output of all of $D_3, dots, D_B$.
]

_Proof._ Such an $N$ would have some prefix in each base, and $u = N \/ B^L$ would lie in all the corresponding intervals. #h(1fr) $square$

The factor $s_b$ is fixed by the fractional part of $L log_b B$: with $theta = "frac"(L log_b B)$, $s_b = b^(-theta)$ or $b^(1 - theta)$.
At depth 0 the criterion says that $[s_b, s_b b\/(b-1)]$ must meet $[1, B\/(B-1)]$ for every $b$, which confines $theta$ to an arc. This is the first stage of the scanner.

#thm("Theorem 7", "verified magnitude sweep")[
  No $N$ with $1 < N < 6^(17179872184) approx 10^(1.3 times 10^10)$ is an output of all of $D_3, D_4, D_5, D_6$.
  #lean("a6_bound")
]

_How it is proved._ Proposition 6 is formalized in `NRB/Sweep.lean` using natural numbers only. For each base $b$ the checker keeps
integers $s_"lo" <= s_"hi"$ with $s_"lo" \/ S <= b^m \/ 6^L <= s_"hi" \/ S$ for a fixed scale $S$, and every rounding goes outward.
Lean proves:
- the enclosure stays valid when $L$ increases by one (`stepEnc_valid`), and a fresh enclosure can be computed for any $L$ from
  interval powers by repeated squaring (`ipow_sound`, `jump_sound`);
- a solution of length $L$ is consistent with the root node of every base (`root`), and with one of the two children of any node
  it is consistent with (`split`);
- a node confines $N S \/ 6^L$ to the interval the checker computes (`iv_sound`), so an empty intersection is a contradiction
  (`kill_sound`, `checkL_sound`).
The checker works at scale $S = 2^56$, which fits machine words, and falls back to $S = 2^220$ for any length the small scale cannot
decide. The range of lengths is split into 16 modules of $2^30$ lengths each, checked independently and chained by `cover_trans`.
As with Theorems 3 to 4b, the final evaluations use `native_decide`.

This is the same criterion the C scanner uses, at about 0.56 microseconds per length instead of about 0.5 nanoseconds.

= Computed bounds (not machine-verified)

The C program `a258107/scan.c` (and its Metal GPU front-end `a258107/gpuscan.m`) applies Proposition 6 to each $L$ in turn, using floating point with outward padding and then 192-bit
fixed point. Its output so far:

#table(
  columns: 3,
  table.header[*Top base*][*Lengths covered*][*Consequence, if the program is correct*],
  [6], [$L < 8.9 times 10^13$], [no $a(6)$ below about $10^(6.9 times 10^13)$],
  [5], [$L < 3 times 10^9$], [no term of A146025 between 82000 and about $10^(2.1 times 10^9)$],
)

These rest on the correctness of the C/GPU code, of the platform's `exp`, and of hand-chosen error margins. The code is tested against brute
force for small $L$, but there is no formal error analysis. Compare Theorem 7, which is machine-verified and reaches $10^(1.3 times 10^10)$. Extending Theorem 7 to the scanner's range is a matter of compute.

= Heuristic for non-existence

There are $2^L$ outputs of $D_6$ with $L + 1$ digits. If the digits of a number in bases 3, 4 and 5 behaved like independent uniform digits,
the chance that all of them are 0 or 1 would be
$ (2/3)^(L log_3 6) (2/4)^(L log_4 6) (2/5)^(L log_5 6). $
The expected number of solutions of length $L$ is then about $c^L$ with
$ c = 2 dot (2/3)^(log_3 6) dot (1/2)^(log_4 6) dot (2/5)^(log_5 6) approx 0.152. $
Since $sum_(L > L_0) c^L$ is finite and tiny for large $L_0$, one expects no solutions beyond the searched range. For bases up to 5 the
same calculation gives a ratio of about $0.494$, still below 1.

= Why this is not a proof

- The heuristic assumes digits in different bases are independent. They are not independent in any proved sense; this is the whole difficulty.
- Proposition 6 kills one length at a time. A proof needs all lengths at once, and the phases $"frac"(L log_b 6)$ are expected to be
  equidistributed, so there is no reason for any fixed depth to work uniformly in $L$.
- Statements of this kind, about digit expansions of one number in multiplicatively independent bases, are related to conjectures of
  Furstenberg and to a question of Erdős on base-3 digits of powers of 2, which remain open. The papers linked from the A146025 entry
  (arXiv:1905.00832, arXiv:2007.05480) prove results in this direction but do not settle the question.

- Reading from the low digits instead (Theorem 4b) turns the problem into a recursion: with $q$ the part of the number above $3^k$,
  appending base-6 digit $d$ gives $q' = (q + d dot 2^k) \/ 3$, allowed only when the remainder is 0 or 1. Showing this never returns
  to 0 after a nonzero digit, for every $k$, is a question of the same kind as whether $2^k$ can avoid the digit 2 in base 3 for large $k$.
  Already the single-digit case $N = 6^k$ asks for $2^k$ to be 0/1 in base 3, $3^k$ to be 0/1 in base 4 and $6^k$ to be 0/1 in base 5
  simultaneously, and no method is known that rules this out for all $k$.

Theorem 7 can be pushed further by running more ranges, which strengthens the bound but does not prove the conjecture. In the Lean
project the conjecture is stated as `A6DoesNotExist` and left unproved.
