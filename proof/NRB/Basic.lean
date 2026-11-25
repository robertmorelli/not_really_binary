/-
  Numbers whose digits are all 0 or 1 in several bases (OEIS A258107, A146025),
  in the "decoder" framing.  Core Lean 4 only, no Mathlib.

  Proved here:
    * `ok_iff_dec`      digit definition  <->  decoder definition
    * `window`          every output of the base-b decoder on m symbols is at most
                        (b^m - 1)/(b - 1): the interval used by stage 1 of the scanner
    * `a5`              a(5) = 82000
    * `a6_gt`           a(6), if it exists, is at least 10^7
    * `a6_gt_big`       a(6), if it exists, is at least 6^3000 (low-digit search)
  The magnitude sweep that reaches much larger bounds is in `NRB/Sweep.lean`.
  NOT proved (open problem): `A6DoesNotExist`.
-/

/-- The base-`b` decoder: read a string of bits (least significant first) as a base-`b` numeral. -/
def dec (b : Nat) : List Bool → Nat
  | [] => 0
  | d :: ds => d.toNat + b * dec b ds

/-- `ok b n`: every base-`b` digit of `n` is 0 or 1. -/
def ok (b n : Nat) : Bool :=
  if h : n = 0 then true
  else if hb : b < 2 then false
  else decide (n % b ≤ 1) && ok b (n / b)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega)

theorem toNat_le_one (d : Bool) : d.toNat ≤ 1 := by cases d <;> decide

/-- Everything the decoder outputs has only 0/1 digits. -/
theorem ok_dec (b : Nat) (hb : 2 ≤ b) : ∀ w : List Bool, ok b (dec b w) = true
  | [] => by unfold ok; simp [dec]
  | d :: ds => by
    have ih := ok_dec b hb ds
    have hd := toNat_le_one d
    unfold ok
    by_cases h : dec b (d :: ds) = 0
    · simp [h]
    · have hmod : dec b (d :: ds) % b = d.toNat := by
        simp only [dec]
        rw [Nat.add_mul_mod_self_left]
        exact Nat.mod_eq_of_lt (by omega)
      have hdiv : dec b (d :: ds) / b = dec b ds := by
        simp only [dec]
        rw [Nat.add_mul_div_left _ _ (by omega : 0 < b)]
        rw [Nat.div_eq_of_lt (by omega)]
        omega
      have hb' : ¬ b < 2 := by omega
      simp only [h, hb', dite_false]
      rw [hmod, hdiv, ih]
      simp [hd]

/-- Every number with only 0/1 digits is an output of the decoder. -/
theorem dec_of_ok (b : Nat) : ∀ n : Nat, ok b n = true → ∃ w, dec b w = n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro h
    by_cases hn : n = 0
    · exact ⟨[], by simp [dec, hn]⟩
    · unfold ok at h
      simp only [hn, dite_false] at h
      by_cases hb : b < 2
      · simp [hb] at h
      · simp only [hb, dite_false, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hm, hq⟩ := h
        have hlt : n / b < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by omega)
        obtain ⟨w, hw⟩ := ih (n / b) hlt hq
        refine ⟨decide (n % b = 1) :: w, ?_⟩
        have hbit : (decide (n % b = 1)).toNat = n % b := by
          by_cases h1 : n % b = 1
          · simp [h1]
          · have : n % b = 0 := by omega
            simp [this]
        simp only [dec, hw, hbit]
        exact Nat.mod_add_div n b

/-- The two definitions agree. -/
theorem ok_iff_dec (b : Nat) (hb : 2 ≤ b) (n : Nat) : ok b n = true ↔ ∃ w, dec b w = n :=
  ⟨dec_of_ok b n, fun ⟨w, hw⟩ => hw ▸ ok_dec b hb w⟩

/-- Window lemma: the decoder on `m` symbols outputs at most `(b^m - 1)/(b - 1)`,
    i.e. the numeral 11…1.  Stated without division or subtraction of the result. -/
theorem window (b : Nat) (hb : 1 ≤ b) : ∀ w : List Bool, (b - 1) * dec b w + 1 ≤ b ^ w.length
  | [] => by simp [dec]
  | d :: ds => by
    have ih := window b hb ds
    have hd := toNat_le_one d
    have h1 : (b - 1) * dec b (d :: ds) + 1 ≤ (b - 1) * 1 + (b - 1) * (b * dec b ds) + 1 := by
      simp only [dec, Nat.mul_add]
      have := Nat.mul_le_mul_left (b - 1) hd
      omega
    have h2 : (b - 1) * (b * dec b ds) = b * ((b - 1) * dec b ds) := by
      rw [← Nat.mul_assoc, Nat.mul_comm (b - 1) b, Nat.mul_assoc]
    have h3 : (b - 1) * 1 + b * ((b - 1) * dec b ds) + 1 = b * ((b - 1) * dec b ds + 1) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_one]
      omega
    have h4 : b * ((b - 1) * dec b ds + 1) ≤ b * b ^ ds.length := Nat.mul_le_mul_left b ih
    have h5 : b * b ^ ds.length = b ^ (d :: ds).length := by
      rw [List.length_cons, Nat.pow_succ, Nat.mul_comm]
    omega

/-- `good top n`: all digits of `n` are 0/1 in every base 3..top (base 2 is automatic). -/
def good (top n : Nat) : Bool := (List.range' 3 (top - 2)).all (fun b => ok b n)

/-- No `n` with `1 < n < bound` is good. -/
def noneBelow (top bound : Nat) : Bool := (List.range bound).all (fun n => decide (n ≤ 1) || !good top n)

theorem noneBelow_spec {top bound : Nat} (h : noneBelow top bound = true) :
    ∀ n, 1 < n → n < bound → good top n = false := by
  intro n h1 hn
  have := List.all_eq_true.mp h n (List.mem_range.mpr hn)
  have h1' : ¬ n ≤ 1 := by omega
  simpa [h1'] using this

/-- 82000 is all-0/1 in bases 2..5 and is the smallest such number above 1: a(5) = 82000. -/
theorem a5 : good 5 82000 = true ∧ ∀ n, 1 < n → n < 82000 → good 5 n = false :=
  ⟨by native_decide, noneBelow_spec (by native_decide)⟩

/-- Verified lower bound: a(6), if it exists, is at least 10^7. -/
theorem a6_gt : ∀ n, 1 < n → n < 10000000 → good 6 n = false :=
  noneBelow_spec (by native_decide)

/-! ## A verified bound from the low digits

`N mod 6^k` determines `N mod 3^k` and `N mod 4^(k/2)`, so the low `k` base-6 digits of a
solution must already look right in bases 3 and 4.  `run k` lists every residue mod `6^k`
that passes; `run_complete` proves no solution is missed. -/

theorem ok_zero (b : Nat) : ok b 0 = true := by unfold ok; simp

theorem ok_inv (b n : Nat) (hb : 2 ≤ b) (h : ok b n = true) : n % b ≤ 1 ∧ ok b (n / b) = true := by
  by_cases hn : n = 0
  · subst hn; simp [ok_zero]
  · unfold ok at h
    have hb' : ¬ b < 2 := by omega
    simp only [hn, hb', dite_false, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h

theorem ok_cons (b d m : Nat) (hb : 2 ≤ b) (hd : d ≤ 1) (hm : ok b m = true) :
    ok b (d + b * m) = true := by
  by_cases h : d + b * m = 0
  · rw [h]; exact ok_zero b
  · have hmod : (d + b * m) % b = d := by
      rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt (by omega)
    have hdiv : (d + b * m) / b = m := by
      rw [Nat.add_mul_div_left _ _ (by omega : 0 < b), Nat.div_eq_of_lt (by omega)]; omega
    unfold ok
    have hb' : ¬ b < 2 := by omega
    simp only [h, hb', dite_false]
    rw [hmod, hdiv, hm]
    simp [hd]

/-- Dropping high digits keeps a 0/1 numeral 0/1. -/
theorem ok_mod_pow (b : Nat) (hb : 2 ≤ b) : ∀ (k n : Nat), ok b n = true → ok b (n % b ^ k) = true
  | 0, n, _ => by simp [Nat.mod_one, ok_zero]
  | k + 1, n, h => by
    obtain ⟨hd, hq⟩ := ok_inv b n hb h
    have ih := ok_mod_pow b hb k (n / b) hq
    rw [Nat.pow_succ', Nat.mod_mul]
    exact ok_cons b _ _ hb hd ih

/-- Every base-`b` digit of a 0/1 numeral is at most 1. -/
theorem ok_digit (b : Nat) (hb : 2 ≤ b) : ∀ (k n : Nat), ok b n = true → n / b ^ k % b ≤ 1
  | 0, n, h => by simpa using (ok_inv b n hb h).1
  | k + 1, n, h => by
    have ih := ok_digit b hb k (n / b) (ok_inv b n hb h).2
    rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul]
    exact ih

theorem three_dvd_six (k : Nat) : 3 ^ k ∣ 6 ^ k := by
  have : (6 : Nat) ^ k = 3 ^ k * 2 ^ k := by rw [← Nat.mul_pow]
  exact ⟨2 ^ k, this⟩

theorem four_dvd_six (k : Nat) : 4 ^ (k / 2) ∣ 6 ^ k := by
  have h4 : (4 : Nat) ^ (k / 2) = 2 ^ (2 * (k / 2)) := by rw [Nat.pow_mul]
  have h2 : (2 : Nat) ^ (2 * (k / 2)) ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega)
  have h6 : (2 : Nat) ^ k ∣ 6 ^ k := by
    have : (6 : Nat) ^ k = 2 ^ k * 3 ^ k := by rw [← Nat.mul_pow]
    exact ⟨3 ^ k, this⟩
  rw [h4]; exact Nat.dvd_trans h2 h6

/-- The test applied to a residue `c` mod `6^k`. -/
def P (k c : Nat) : Bool := ok 3 (c % 3 ^ k) && ok 4 (c % 4 ^ (k / 2))

def step (k : Nat) (live : List Nat) : List Nat :=
  live.flatMap (fun r => [r, r + 6 ^ k].filter (P (k + 1)))

def run : Nat → List Nat
  | 0 => [0]
  | k + 1 => step k (run k)

theorem P_of_ok (k N : Nat) (h3 : ok 3 N = true) (h4 : ok 4 N = true) : P k (N % 6 ^ k) = true := by
  unfold P
  rw [Nat.mod_mod_of_dvd _ (three_dvd_six k), Nat.mod_mod_of_dvd _ (four_dvd_six k)]
  rw [ok_mod_pow 3 (by omega) k N h3, ok_mod_pow 4 (by omega) (k / 2) N h4]
  rfl

/-- Completeness of the search: the residue of any solution is on the list. -/
theorem run_complete (N : Nat) (h3 : ok 3 N = true) (h4 : ok 4 N = true) (h6 : ok 6 N = true) :
    ∀ k, N % 6 ^ k ∈ run k
  | 0 => by simp [run, Nat.mod_one]
  | k + 1 => by
    have ih := run_complete N h3 h4 h6 k
    have hd := ok_digit 6 (by omega) k N h6
    have hsplit : N % 6 ^ (k + 1) = N % 6 ^ k + 6 ^ k * (N / 6 ^ k % 6) := by
      rw [Nat.pow_succ, Nat.mod_mul]
    have hP := P_of_ok (k + 1) N h3 h4
    simp only [run, step, List.mem_flatMap, List.mem_filter]
    refine ⟨N % 6 ^ k, ih, ?_, hP⟩
    rw [hsplit]
    have : N / 6 ^ k % 6 = 0 ∨ N / 6 ^ k % 6 = 1 := by omega
    rcases this with h | h <;> simp [h]

def check (K : Nat) : Bool := (run K).all (fun r => decide (r ≤ 1) || !good 6 r)

theorem check_spec (K : Nat) (h : check K = true) :
    ∀ N, 1 < N → N < 6 ^ K → good 6 N = false := by
  intro N h1 hlt
  cases hg : good 6 N with
  | false => rfl
  | true =>
    have hall : ok 3 N = true ∧ ok 4 N = true ∧ ok 5 N = true ∧ ok 6 N = true := by
      simpa [good, List.range'] using hg
    have hmem := run_complete N hall.1 hall.2.1 hall.2.2.2 K
    rw [Nat.mod_eq_of_lt hlt] at hmem
    have := List.all_eq_true.mp h N hmem
    have h1' : ¬ N ≤ 1 := by omega
    simp [h1', hg] at this

/-- Verified lower bound: a(6), if it exists, is at least 6^3000 (about 10^2334). -/
theorem a6_gt_big : ∀ N, 1 < N → N < 6 ^ 3000 → good 6 N = false :=
  check_spec 3000 (by native_decide)

/-- The conjecture.  This is an OPEN PROBLEM and is deliberately not proved here. -/
def A6DoesNotExist : Prop := ∀ n, 1 < n → good 6 n = false

#print axioms ok_iff_dec
#print axioms window
#print axioms a5
#print axioms a6_gt
#print axioms run_complete
#print axioms a6_gt_big
