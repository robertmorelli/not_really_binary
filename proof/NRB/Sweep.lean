import NRB.Basic

/-!
# A verified magnitude sweep (the arithmetic-coding criterion)

For a length `L` we keep, for every base `b`, integers `slo ≤ shi` with
`slo/S ≤ b^m / 6^L ≤ shi/S` (`S` is a fixed-point scale).  A node `(P, k)` says "the top
`k+1` base-`b` digits of `N` spell `P`"; it confines `N·S/6^L` to an integer interval.
If the intervals of the current nodes have empty intersection, no such `N` exists; otherwise
we split a node into its two children.  Everything is natural-number arithmetic with
rounding directed outward, so a successful run is a proof.

Main result: `blocks_sound`.
-/

/-- Numbers below `b^j` with 0/1 digits are at most `11…1`. -/
theorem ok_window (b : Nat) (hb : 2 ≤ b) :
    ∀ (j t : Nat), ok b t = true → t < b ^ j → (b - 1) * t + 1 ≤ b ^ j
  | 0, t, _, h => by
    have : t = 0 := by simpa using h
    subst this; simp
  | j + 1, t, h, hlt => by
    obtain ⟨hd, hq⟩ := ok_inv b t hb h
    have hqlt : t / b < b ^ j := by
      apply Nat.div_lt_of_lt_mul
      rw [Nat.pow_succ, Nat.mul_comm] at hlt
      exact hlt
    have ih := ok_window b hb j (t / b) hq hqlt
    have ht := (Nat.div_add_mod t b).symm
    generalize t / b = q at *
    generalize t % b = d at *
    have e : (b - 1) * (b * q + d) = b * ((b - 1) * q) + (b - 1) * d := by
      rw [Nat.mul_add]; congr 1; ac_rfl
    have hd' : (b - 1) * d ≤ (b - 1) * 1 := Nat.mul_le_mul_left _ hd
    have ih' : b * ((b - 1) * q + 1) ≤ b * b ^ j := Nat.mul_le_mul_left b ih
    rw [Nat.mul_add, Nat.mul_one] at ih'
    rw [Nat.mul_one] at hd'
    rw [Nat.pow_succ, Nat.mul_comm (b ^ j) b, ht, e]
    omega

theorem ceil_ge (x D : Nat) (hD : 0 < D) : x ≤ (x + (D - 1)) / D * D := by
  have h1 := Nat.div_add_mod (x + (D - 1)) D
  have h2 := Nat.mod_lt (x + (D - 1)) hD
  rw [Nat.mul_comm] at h1
  omega

/-! ## Enclosures and nodes -/

structure Enc where
  b : Nat
  m : Nat
  slo : Nat
  shi : Nat

/-- `slo/S ≤ b^m/6^L ≤ shi/S`. -/
def Valid (S L : Nat) (e : Enc) : Prop :=
  e.slo * 6 ^ L ≤ e.b ^ e.m * S ∧ e.b ^ e.m * S ≤ e.shi * 6 ^ L

structure Node where
  e : Enc
  P : Nat
  k : Nat
  /-- cached `b^k` -/
  d : Nat
  /-- width hint used only to choose which node to split; carries no proof obligation -/
  w : Nat

/-- `N` has 0/1 digits in the node's base and its digits above position `m-k` spell `P`. -/
def Cons (n : Node) (N : Nat) : Prop :=
  ok n.e.b N = true ∧ n.k ≤ n.e.m ∧ N / n.e.b ^ (n.e.m - n.k) = n.P ∧ n.d = n.e.b ^ n.k

def iv (n : Node) : Nat × Nat :=
  ((n.e.slo * n.P) / n.d,
   (n.e.shi * ((n.e.b - 1) * n.P + 1) + ((n.e.b - 1) * n.d - 1)) / ((n.e.b - 1) * n.d))

def In (S L N : Nat) (p : Nat × Nat) : Prop := p.1 * 6 ^ L ≤ N * S ∧ N * S < p.2 * 6 ^ L

theorem iv_sound (S L N : Nat) (hS : 0 < S) (n : Node) (hv : Valid S L n.e) (hb : 2 ≤ n.e.b)
    (hc : Cons n N) : In S L N (iv n) := by
  obtain ⟨e, P, k, d, w⟩ := n
  obtain ⟨b, m, slo, shi⟩ := e
  simp only [Valid] at hv
  simp only [Cons] at hc
  simp only at hb
  obtain ⟨hv1, hv2⟩ := hv
  obtain ⟨hok, hk, hP, hd⟩ := hc
  subst hd
  simp only [iv, In]
  have hbm : b ^ m = b ^ (m - k) * b ^ k := by rw [← Nat.pow_add, Nat.sub_add_cancel hk]
  have hbk : 0 < b ^ k := Nat.pow_pos (by omega)
  have hX : 0 < b ^ (m - k) := Nat.pow_pos (by omega)
  have hlow : P * b ^ (m - k) ≤ N := by rw [← hP]; exact Nat.div_mul_le_self N _
  have hupp : (b - 1) * N + 1 ≤ ((b - 1) * P + 1) * b ^ (m - k) := by
    have ht := (Nat.div_add_mod N (b ^ (m - k))).symm
    have htl := Nat.mod_lt N hX
    have hokt := ok_mod_pow b hb (m - k) N hok
    have hw := ok_window b hb (m - k) _ hokt htl
    rw [hP] at ht
    generalize N % b ^ (m - k) = t at ht hw
    generalize b ^ (m - k) = X at ht hw ⊢
    have e1 : (b - 1) * (X * P + t) = (b - 1) * P * X + (b - 1) * t := by
      rw [Nat.mul_add]; congr 1; ac_rfl
    have e2 : ((b - 1) * P + 1) * X = (b - 1) * P * X + X := by rw [Nat.add_mul, Nat.one_mul]
    rw [ht, e1, e2]; omega
  rw [hbm] at hv1 hv2
  generalize b ^ (m - k) = X at hv1 hv2 hlow hupp
  generalize b ^ k = Y at hv1 hv2 hbk ⊢
  generalize (6 : Nat) ^ L = Z at hv1 hv2 ⊢
  constructor
  · have h1 : slo * P / Y * Y ≤ slo * P := Nat.div_mul_le_self _ _
    have h2 : slo * P / Y * Z * Y ≤ N * S * Y := by
      calc slo * P / Y * Z * Y = slo * P / Y * Y * Z := by ac_rfl
        _ ≤ slo * P * Z := Nat.mul_le_mul_right Z h1
        _ = slo * Z * P := by ac_rfl
        _ ≤ X * Y * S * P := Nat.mul_le_mul_right P hv1
        _ = P * X * (S * Y) := by ac_rfl
        _ ≤ N * (S * Y) := Nat.mul_le_mul_right _ hlow
        _ = N * S * Y := by ac_rfl
    exact Nat.le_of_mul_le_mul_right h2 hbk
  · have hD : 0 < (b - 1) * Y := Nat.mul_pos (by omega) hbk
    have hc := ceil_ge (shi * ((b - 1) * P + 1)) ((b - 1) * Y) hD
    generalize (shi * ((b - 1) * P + 1) + ((b - 1) * Y - 1)) / ((b - 1) * Y) = H at hc ⊢
    have hSY : 0 < S * Y := Nat.mul_pos hS hbk
    have h3 : N * S * ((b - 1) * Y) < H * Z * ((b - 1) * Y) := by
      calc N * S * ((b - 1) * Y) = (b - 1) * N * (S * Y) := by ac_rfl
        _ < ((b - 1) * N + 1) * (S * Y) := Nat.mul_lt_mul_of_pos_right (by omega) hSY
        _ ≤ ((b - 1) * P + 1) * X * (S * Y) := Nat.mul_le_mul_right _ hupp
        _ = ((b - 1) * P + 1) * (X * Y * S) := by ac_rfl
        _ ≤ ((b - 1) * P + 1) * (shi * Z) := Nat.mul_le_mul_left _ hv2
        _ = shi * ((b - 1) * P + 1) * Z := by ac_rfl
        _ ≤ H * ((b - 1) * Y) * Z := Nat.mul_le_mul_right Z hc
        _ = H * Z * ((b - 1) * Y) := by ac_rfl
    exact Nat.lt_of_mul_lt_mul_right h3

theorem In_dead (S L N lo hi : Nat) (h : In S L N (lo, hi)) (hle : hi ≤ lo) : False := by
  have := Nat.mul_le_mul_right (6 ^ L) hle
  have := h.1
  have := h.2
  simp only at *
  omega

theorem In_inter (S L N : Nat) (p q : Nat × Nat) (hp : In S L N p) (hq : In S L N q) :
    In S L N (max p.1 q.1, min p.2 q.2) := by
  simp only [In] at *
  constructor
  · rcases Nat.le_total p.1 q.1 with h | h
    · rw [Nat.max_eq_right h]; exact hq.1
    · rw [Nat.max_eq_left h]; exact hp.1
  · rcases Nat.le_total p.2 q.2 with h | h
    · rw [Nat.min_eq_left h]; exact hp.2
    · rw [Nat.min_eq_right h]; exact hq.2

def child (n : Node) (dg : Nat) : Node :=
  { n with P := n.e.b * n.P + dg, k := n.k + 1, d := n.d * n.e.b, w := n.w / n.e.b }

theorem split (N : Nat) (n : Node) (hb : 2 ≤ n.e.b) (hc : Cons n N) (hk : n.k < n.e.m) :
    Cons (child n 0) N ∨ Cons (child n 1) N := by
  obtain ⟨e, P, k, d, w⟩ := n
  obtain ⟨b, m, slo, shi⟩ := e
  simp only [Cons, child] at *
  obtain ⟨hok, _, hP, hd⟩ := hc
  have hd' : d * b = b ^ (k + 1) := by rw [hd, Nat.pow_succ]
  have hj : m - k = (m - (k + 1)) + 1 := by omega
  have hdig := ok_digit b hb (m - (k + 1)) N hok
  have hp : b ^ (m - (k + 1)) * b = b ^ (m - k) := by rw [hj, Nat.pow_succ]
  have hdiv : N / b ^ (m - (k + 1)) / b = P := by
    rw [Nat.div_div_eq_div_mul, hp]; exact hP
  have hdm := (Nat.div_add_mod (N / b ^ (m - (k + 1))) b).symm
  rw [hdiv] at hdm
  have : N / b ^ (m - (k + 1)) % b = 0 ∨ N / b ^ (m - (k + 1)) % b = 1 := by omega
  rcases this with h | h
  · left; exact ⟨hok, by omega, by rw [hdm, h], hd'⟩
  · right; exact ⟨hok, by omega, by rw [hdm, h], hd'⟩

/-- index of the node with the largest width hint (any index would be sound) -/
def pick (ns : List Node) : Nat :=
  (ns.foldl (fun (acc : Nat × Nat × Nat) n =>
    if n.w > acc.2.1 then (acc.1 + 1, n.w, acc.1) else (acc.1 + 1, acc.2.1, acc.2.2)) (0, 0, 0)).2.2

/-- `kill f ns lo hi = true` certifies that no `N` with `N·S/6^L` in `[lo, hi)` is
    consistent with all the nodes. -/
def kill : Nat → List Node → Nat → Nat → Bool
  | 0, _, _, _ => false
  | f + 1, ns, lo, hi =>
    match ns[pick ns]? with
    | none => false
    | some n =>
      if n.k < n.e.m then
        (decide (min hi (iv (child n 0)).2 ≤ max lo (iv (child n 0)).1) ||
          kill f (ns.set (pick ns) (child n 0)) (max lo (iv (child n 0)).1) (min hi (iv (child n 0)).2)) &&
        (decide (min hi (iv (child n 1)).2 ≤ max lo (iv (child n 1)).1) ||
          kill f (ns.set (pick ns) (child n 1)) (max lo (iv (child n 1)).1) (min hi (iv (child n 1)).2))
      else false

theorem kill_sound (S L N : Nat) (hS : 0 < S) : ∀ (f : Nat) (ns : List Node) (lo hi : Nat),
    kill f ns lo hi = true → (∀ n ∈ ns, Valid S L n.e ∧ 2 ≤ n.e.b) → (∀ n ∈ ns, Cons n N) →
    In S L N (lo, hi) → False
  | 0, _, _, _, h, _, _, _ => by simp [kill] at h
  | f + 1, ns, lo, hi, h, hv, hc, hin => by
    simp only [kill] at h
    split at h
    · simp at h
    · rename_i n hn
      have hmem : n ∈ ns := List.mem_of_getElem? hn
      split at h
      · rename_i hk
        simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
        have hset : ∀ d, ∀ x ∈ ns.set (pick ns) (child n d), (Valid S L x.e ∧ 2 ≤ x.e.b) := by
          intro d x hx
          rcases List.mem_or_eq_of_mem_set hx with hx | hx
          · exact hv x hx
          · subst hx; exact hv n hmem
        have hcons : ∀ d, Cons (child n d) N → ∀ x ∈ ns.set (pick ns) (child n d), Cons x N := by
          intro d hd x hx
          rcases List.mem_or_eq_of_mem_set hx with hx | hx
          · exact hc x hx
          · subst hx; exact hd
        have hbox : ∀ d, Cons (child n d) N →
            In S L N (max lo (iv (child n d)).1, min hi (iv (child n d)).2) := by
          intro d hd
          exact In_inter S L N (lo, hi) (iv (child n d)) hin
            (iv_sound S L N hS (child n d) (hv n hmem).1 (hv n hmem).2 hd)
        rcases split N n (hv n hmem).2 (hc n hmem) hk with h0 | h1
        · rcases h.1 with hd | hkk
          · exact In_dead S L N _ _ (hbox 0 h0) hd
          · exact kill_sound S L N hS f _ _ _ hkk (hset 0) (hcons 0 h0) (hbox 0 h0)
        · rcases h.2 with hd | hkk
          · exact In_dead S L N _ _ (hbox 1 h1) hd
          · exact kill_sound S L N hS f _ _ _ hkk (hset 1) (hcons 1 h1) (hbox 1 h1)
      · simp at h

/-! ## One length -/

/-- Root fact: with `0.6 ≤ s ≤ b-1`, a 0/1 numeral `N` in `[6^L, 6^(L+1)/5)` has its top digit at `m`. -/
theorem root (S L N : Nat) (hS : 0 < S) (e : Enc) (w : Nat) (hv : Valid S L e) (hb : 2 ≤ e.b)
    (c1 : 6 * S ≤ 10 * e.slo) (c2 : e.shi ≤ (e.b - 1) * S)
    (hlo : 6 ^ L ≤ N) (hhi : 5 * N + 1 ≤ 6 ^ (L + 1)) (hok : ok e.b N = true) :
    Cons ⟨e, 1, 0, 1, w⟩ N := by
  obtain ⟨b, m, slo, shi⟩ := e
  simp only [Valid] at hv
  simp only at hb c1 c2 hok
  obtain ⟨hv1, hv2⟩ := hv
  refine ⟨hok, Nat.zero_le _, ?_, by simp⟩
  simp only [Nat.sub_zero]
  have hX : 0 < b ^ m := Nat.pow_pos (by omega)
  have hge : b ^ m ≤ N := by
    apply Nat.le_of_not_lt
    intro hlt
    have hw := ok_window b hb m N hok hlt
    have h1 : (b - 1) * N * S + S ≤ b ^ m * S := by
      have := Nat.mul_le_mul_right S hw
      rw [Nat.add_mul, Nat.one_mul] at this; exact this
    have h2 : shi * 6 ^ L ≤ (b - 1) * S * N := by
      calc shi * 6 ^ L ≤ (b - 1) * S * 6 ^ L := Nat.mul_le_mul_right _ c2
        _ ≤ (b - 1) * S * N := Nat.mul_le_mul_left _ hlo
    have h3 : (b - 1) * S * N = (b - 1) * N * S := by ac_rfl
    omega
  have hlt2 : N < 2 * b ^ m := by
    apply Nat.lt_of_not_le
    intro hle
    have h1 : 10 * slo * 6 ^ L ≤ 10 * (b ^ m * S) := by
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 10 hv1
    have h2 : 6 * S * 6 ^ L ≤ 10 * slo * 6 ^ L := Nat.mul_le_mul_right _ c1
    have h3 : 6 * S * 6 ^ L = S * 6 ^ (L + 1) := by rw [Nat.pow_succ]; ac_rfl
    have h4 : S * (5 * N + 1) ≤ S * 6 ^ (L + 1) := Nat.mul_le_mul_left S hhi
    have h5 : S * (5 * N + 1) = 5 * (N * S) + S := by rw [Nat.mul_add, Nat.mul_one]; congr 1; ac_rfl
    have h6 : 2 * b ^ m * S ≤ N * S := Nat.mul_le_mul_right S hle
    have h7 : 2 * b ^ m * S = 2 * (b ^ m * S) := by ac_rfl
    omega
  have h1 : N / b ^ m < 2 := by
    apply Nat.div_lt_of_lt_mul; rw [Nat.mul_comm]; exact hlt2
  have h2 : 0 < N / b ^ m := Nat.div_pos hge hX
  omega

def encOk (S : Nat) (e : Enc) : Bool :=
  decide (2 ≤ e.b) && decide (6 * S ≤ 10 * e.slo) && decide (e.shi ≤ (e.b - 1) * S)

def rootNode (e : Enc) : Node := ⟨e, 1, 0, 1, e.shi / (e.b - 1)⟩

def box (ns : List Node) (p : Nat × Nat) : Nat × Nat :=
  ns.foldl (fun acc n => (max acc.1 (iv n).1, min acc.2 (iv n).2)) p

theorem box_sound (S L N : Nat) : ∀ (ns : List Node) (p : Nat × Nat), In S L N p →
    (∀ n ∈ ns, In S L N (iv n)) → In S L N (box ns p)
  | [], p, hp, _ => by simpa [box] using hp
  | n :: ns, p, hp, h => by
    have h1 := In_inter S L N p (iv n) hp (h n (List.mem_cons_self ..))
    have := box_sound S L N ns _ h1 (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simpa [box] using this

/-- Certifies: no `N` in `[6^L, 6^(L+1))` has 0/1 digits in base 6 and in every base of `es`. -/
def checkL (S L : Nat) (es : List Enc) : Bool :=
  ((⟨6, L, S, S⟩ : Enc) :: es).all (encOk S) &&
  (decide ((box (((⟨6, L, S, S⟩ : Enc) :: es).map rootNode) (iv (rootNode ⟨6, L, S, S⟩))).2 ≤
           (box (((⟨6, L, S, S⟩ : Enc) :: es).map rootNode) (iv (rootNode ⟨6, L, S, S⟩))).1) ||
   kill 300 (((⟨6, L, S, S⟩ : Enc) :: es).map rootNode)
     (box (((⟨6, L, S, S⟩ : Enc) :: es).map rootNode) (iv (rootNode ⟨6, L, S, S⟩))).1
     (box (((⟨6, L, S, S⟩ : Enc) :: es).map rootNode) (iv (rootNode ⟨6, L, S, S⟩))).2)

theorem checkL_sound (S L N : Nat) (hS : 0 < S) (es : List Enc) (h : checkL S L es = true)
    (hv : ∀ e ∈ es, Valid S L e) (hlo : 6 ^ L ≤ N) (hhi : N < 6 ^ (L + 1))
    (h6 : ok 6 N = true) (hoks : ∀ e ∈ es, ok e.b N = true) : False := by
  simp only [checkL, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨hcond, hkill⟩ := h
  have hw := ok_window 6 (by omega) (L + 1) N h6 hhi
  have hhi' : 5 * N + 1 ≤ 6 ^ (L + 1) := by simpa using hw
  have hv' : ∀ e ∈ (⟨6, L, S, S⟩ : Enc) :: es, Valid S L e := by
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · simp only [Valid]; constructor
      · rw [Nat.mul_comm]; exact Nat.le_refl _
      · rw [Nat.mul_comm]; exact Nat.le_refl _
    · exact hv e he
  have hok' : ∀ e ∈ (⟨6, L, S, S⟩ : Enc) :: es, ok e.b N = true := by
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact h6
    · exact hoks e he
  have hnodes : ∀ n ∈ ((⟨6, L, S, S⟩ : Enc) :: es).map rootNode,
      (Valid S L n.e ∧ 2 ≤ n.e.b) ∧ Cons n N := by
    intro n hn
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hn
    have hc := hcond e he
    simp only [encOk, Bool.and_eq_true, decide_eq_true_eq] at hc
    exact ⟨⟨hv' e he, hc.1.1⟩,
      root S L N hS e _ (hv' e he) hc.1.1 hc.1.2 hc.2 hlo hhi' (hok' e he)⟩
  have hroot6 : In S L N (iv (rootNode ⟨6, L, S, S⟩)) := by
    have := hnodes (rootNode ⟨6, L, S, S⟩) (by simp)
    exact iv_sound S L N hS _ this.1.1 this.1.2 this.2
  have hbox := box_sound S L N _ _ hroot6
    (fun n hn => iv_sound S L N hS n (hnodes n hn).1.1 (hnodes n hn).1.2 (hnodes n hn).2)
  rcases hkill with hd | hk
  · exact In_dead S L N _ _ hbox hd
  · exact kill_sound S L N hS 300 _ _ _ hk (fun n hn => (hnodes n hn).1)
      (fun n hn => (hnodes n hn).2) hbox

/-! ## Stepping an enclosure from `L` to `L+1` -/

def bump (S : Nat) (e : Enc) : Enc :=
  if 10 * e.slo < 6 * S then { e with m := e.m + 1, slo := e.slo * e.b, shi := e.shi * e.b } else e

def stepEnc (S : Nat) (e : Enc) : Enc :=
  bump S (bump S { e with slo := e.slo / 6, shi := (e.shi + 5) / 6 })

theorem bump_valid (S L : Nat) (e : Enc) (h : Valid S L e) : Valid S L (bump S e) := by
  unfold bump
  split
  · obtain ⟨h1, h2⟩ := h
    simp only [Valid]
    constructor
    · calc e.slo * e.b * 6 ^ L = e.slo * 6 ^ L * e.b := by ac_rfl
        _ ≤ e.b ^ e.m * S * e.b := Nat.mul_le_mul_right _ h1
        _ = e.b ^ (e.m + 1) * S := by rw [Nat.pow_succ]; ac_rfl
    · calc e.b ^ (e.m + 1) * S = e.b ^ e.m * S * e.b := by rw [Nat.pow_succ]; ac_rfl
        _ ≤ e.shi * 6 ^ L * e.b := Nat.mul_le_mul_right _ h2
        _ = e.shi * e.b * 6 ^ L := by ac_rfl
  · exact h

theorem bump_b (S : Nat) (e : Enc) : (bump S e).b = e.b := by unfold bump; split <;> rfl

theorem stepEnc_valid (S L : Nat) (e : Enc) (h : Valid S L e) : Valid S (L + 1) (stepEnc S e) := by
  unfold stepEnc
  apply bump_valid; apply bump_valid
  obtain ⟨h1, h2⟩ := h
  simp only [Valid]
  constructor
  · have : e.slo / 6 * 6 ≤ e.slo := Nat.div_mul_le_self _ _
    calc e.slo / 6 * 6 ^ (L + 1) = e.slo / 6 * 6 * 6 ^ L := by rw [Nat.pow_succ]; ac_rfl
      _ ≤ e.slo * 6 ^ L := Nat.mul_le_mul_right _ this
      _ ≤ e.b ^ e.m * S := h1
  · have : e.shi ≤ (e.shi + 5) / 6 * 6 := by omega
    calc e.b ^ e.m * S ≤ e.shi * 6 ^ L := h2
      _ ≤ (e.shi + 5) / 6 * 6 * 6 ^ L := Nat.mul_le_mul_right _ this
      _ = (e.shi + 5) / 6 * 6 ^ (L + 1) := by rw [Nat.pow_succ]; ac_rfl

theorem stepEnc_b (S : Nat) (e : Enc) : (stepEnc S e).b = e.b := by
  unfold stepEnc; rw [bump_b, bump_b]

/-! ## Jumping straight to any `L`: interval powers -/

structure Tri where
  lo : Nat
  hi : Nat
  e : Nat

/-- `lo·2^e ≤ x ≤ hi·2^e` -/
def Encl (t : Tri) (x : Nat) : Prop := t.lo * 2 ^ t.e ≤ x ∧ x ≤ t.hi * 2 ^ t.e

def mulT (a c : Tri) : Tri := ⟨a.lo * c.lo, a.hi * c.hi, a.e + c.e⟩

theorem mulT_sound (a c : Tri) (x y : Nat) (ha : Encl a x) (hc : Encl c y) : Encl (mulT a c) (x * y) := by
  simp only [Encl, mulT] at *
  constructor
  · calc a.lo * c.lo * 2 ^ (a.e + c.e) = a.lo * 2 ^ a.e * (c.lo * 2 ^ c.e) := by rw [Nat.pow_add]; ac_rfl
      _ ≤ x * y := Nat.mul_le_mul ha.1 hc.1
  · calc x * y ≤ a.hi * 2 ^ a.e * (c.hi * 2 ^ c.e) := Nat.mul_le_mul ha.2 hc.2
      _ = a.hi * c.hi * 2 ^ (a.e + c.e) := by rw [Nat.pow_add]; ac_rfl

/-- keep about `W` bits of mantissa -/
def normT (W : Nat) (t : Tri) : Tri :=
  if t.hi.log2 + 1 ≤ W then t
  else ⟨t.lo / 2 ^ (t.hi.log2 + 1 - W), (t.hi + (2 ^ (t.hi.log2 + 1 - W) - 1)) / 2 ^ (t.hi.log2 + 1 - W),
        t.e + (t.hi.log2 + 1 - W)⟩

theorem normT_sound (W : Nat) (t : Tri) (x : Nat) (h : Encl t x) : Encl (normT W t) x := by
  unfold normT
  split
  · exact h
  · simp only [Encl] at *
    generalize t.hi.log2 + 1 - W = sh
    have hp : 0 < 2 ^ sh := Nat.pow_pos (by decide)
    constructor
    · have : t.lo / 2 ^ sh * 2 ^ sh ≤ t.lo := Nat.div_mul_le_self _ _
      calc t.lo / 2 ^ sh * 2 ^ (t.e + sh) = t.lo / 2 ^ sh * 2 ^ sh * 2 ^ t.e := by rw [Nat.pow_add]; ac_rfl
        _ ≤ t.lo * 2 ^ t.e := Nat.mul_le_mul_right _ this
        _ ≤ x := h.1
    · have := ceil_ge t.hi (2 ^ sh) hp
      calc x ≤ t.hi * 2 ^ t.e := h.2
        _ ≤ (t.hi + (2 ^ sh - 1)) / 2 ^ sh * 2 ^ sh * 2 ^ t.e := Nat.mul_le_mul_right _ this
        _ = (t.hi + (2 ^ sh - 1)) / 2 ^ sh * 2 ^ (t.e + sh) := by rw [Nat.pow_add]; ac_rfl

/-- enclosure of `b^n` by repeated squaring -/
def ipow (W b : Nat) (n : Nat) : Tri :=
  if h : n = 0 then ⟨1, 1, 0⟩
  else if n % 2 = 1 then
    normT W (mulT (normT W (mulT (ipow W b (n / 2)) (ipow W b (n / 2)))) ⟨b, b, 0⟩)
  else normT W (mulT (ipow W b (n / 2)) (ipow W b (n / 2)))
termination_by n
decreasing_by all_goals omega

theorem ipow_sound (W b : Nat) : ∀ n : Nat, Encl (ipow W b n) (b ^ n) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold ipow
    by_cases h : n = 0
    · subst h; simp [Encl]
    · simp only [h, dite_false]
      have ihh := ih (n / 2) (by omega)
      have hsq : Encl (normT W (mulT (ipow W b (n / 2)) (ipow W b (n / 2)))) (b ^ (n / 2) * b ^ (n / 2)) :=
        normT_sound W _ _ (mulT_sound _ _ _ _ ihh ihh)
      by_cases hodd : n % 2 = 1
      · simp only [hodd, ite_true]
        have hb : Encl ⟨b, b, 0⟩ b := by simp [Encl]
        have hp : b ^ n = b ^ (n / 2) * b ^ (n / 2) * b := by
          rw [← Nat.pow_add, ← Nat.pow_succ]; congr 1; omega
        rw [hp]
        exact normT_sound W _ _ (mulT_sound _ _ _ _ hsq hb)
      · simp only [hodd, ite_false]
        have hp : b ^ n = b ^ (n / 2) * b ^ (n / 2) := by
          rw [← Nat.pow_add]; congr 1; omega
        rw [hp]; exact hsq

/-- enclosure of `b^m / 6^L` at scale `S` from enclosures of numerator and denominator -/
def quot (S b m : Nat) (tn td : Tri) : Enc :=
  if td.e ≤ tn.e then
    ⟨b, m, tn.lo * S * 2 ^ (tn.e - td.e) / td.hi,
      (tn.hi * S * 2 ^ (tn.e - td.e) + (td.lo - 1)) / td.lo⟩
  else
    ⟨b, m, tn.lo * S / (td.hi * 2 ^ (td.e - tn.e)),
      (tn.hi * S + (td.lo * 2 ^ (td.e - tn.e) - 1)) / (td.lo * 2 ^ (td.e - tn.e))⟩

theorem quot_sound (S L b m : Nat) (tn td : Tri) (hn : Encl tn (b ^ m)) (hd : Encl td (6 ^ L))
    (hpos : 0 < td.lo) : Valid S L (quot S b m tn td) := by
  obtain ⟨nlo, nhi, ne⟩ := tn
  obtain ⟨dlo, dhi, de⟩ := td
  simp only [Encl] at hn hd
  simp only at hpos
  unfold quot
  simp only
  split
  · rename_i hle
    have he : ne = de + (ne - de) := by omega
    generalize ne - de = t at he
    subst he
    rw [Nat.pow_add] at hn
    simp only [Valid]
    generalize b ^ m = B at hn ⊢
    generalize (6 : Nat) ^ L = Z at hd ⊢
    constructor
    · have h1 : nlo * S * 2 ^ t / dhi * dhi ≤ nlo * S * 2 ^ t := Nat.div_mul_le_self _ _
      calc nlo * S * 2 ^ t / dhi * Z ≤ nlo * S * 2 ^ t / dhi * (dhi * 2 ^ de) := Nat.mul_le_mul_left _ hd.2
        _ = nlo * S * 2 ^ t / dhi * dhi * 2 ^ de := by ac_rfl
        _ ≤ nlo * S * 2 ^ t * 2 ^ de := Nat.mul_le_mul_right _ h1
        _ = nlo * (2 ^ de * 2 ^ t) * S := by ac_rfl
        _ ≤ B * S := Nat.mul_le_mul_right _ hn.1
    · have h1 := ceil_ge (nhi * S * 2 ^ t) dlo hpos
      calc B * S ≤ nhi * (2 ^ de * 2 ^ t) * S := Nat.mul_le_mul_right _ hn.2
        _ = nhi * S * 2 ^ t * 2 ^ de := by ac_rfl
        _ ≤ (nhi * S * 2 ^ t + (dlo - 1)) / dlo * dlo * 2 ^ de := Nat.mul_le_mul_right _ h1
        _ = (nhi * S * 2 ^ t + (dlo - 1)) / dlo * (dlo * 2 ^ de) := by ac_rfl
        _ ≤ (nhi * S * 2 ^ t + (dlo - 1)) / dlo * Z := Nat.mul_le_mul_left _ hd.1
  · rename_i hle
    have he : de = ne + (de - ne) := by omega
    generalize de - ne = t at he
    subst he
    rw [Nat.pow_add] at hd
    simp only [Valid]
    generalize b ^ m = B at hn ⊢
    generalize (6 : Nat) ^ L = Z at hd ⊢
    have hD : 0 < dlo * 2 ^ t := Nat.mul_pos hpos (Nat.pow_pos (by decide))
    constructor
    · have h1 : nlo * S / (dhi * 2 ^ t) * (dhi * 2 ^ t) ≤ nlo * S := Nat.div_mul_le_self _ _
      calc nlo * S / (dhi * 2 ^ t) * Z ≤ nlo * S / (dhi * 2 ^ t) * (dhi * (2 ^ ne * 2 ^ t)) :=
            Nat.mul_le_mul_left _ hd.2
        _ = nlo * S / (dhi * 2 ^ t) * (dhi * 2 ^ t) * 2 ^ ne := by ac_rfl
        _ ≤ nlo * S * 2 ^ ne := Nat.mul_le_mul_right _ h1
        _ = nlo * 2 ^ ne * S := by ac_rfl
        _ ≤ B * S := Nat.mul_le_mul_right _ hn.1
    · have h1 := ceil_ge (nhi * S) (dlo * 2 ^ t) hD
      calc B * S ≤ nhi * 2 ^ ne * S := Nat.mul_le_mul_right _ hn.2
        _ = nhi * S * 2 ^ ne := by ac_rfl
        _ ≤ (nhi * S + (dlo * 2 ^ t - 1)) / (dlo * 2 ^ t) * (dlo * 2 ^ t) * 2 ^ ne :=
            Nat.mul_le_mul_right _ h1
        _ = (nhi * S + (dlo * 2 ^ t - 1)) / (dlo * 2 ^ t) * (dlo * (2 ^ ne * 2 ^ t)) := by ac_rfl
        _ ≤ (nhi * S + (dlo * 2 ^ t - 1)) / (dlo * 2 ^ t) * Z := Nat.mul_le_mul_left _ hd.1

theorem quot_b (S b m : Nat) (tn td : Tri) : (quot S b m tn td).b = b := by
  unfold quot; split <;> rfl

/-- mantissa bits used for interval powers -/
def WBITS : Nat := 320

/-- A lower approximation of `log_b 6` times `10^30`.  Only used to guess `m`; a bad guess
    makes the check fail, it cannot make it wrong. -/
def logNum (b : Nat) : Nat :=
  if b = 3 then 1630929753571457437099527114342
  else if b = 4 then 1292481250360578090726869471973
  else 1113282752559378345804672928035

/-- enclosure of `b^m / 6^L` for the `m` with `0.6 ≤ b^m/6^L`, computed from scratch -/
def jump (S b L : Nat) (td : Tri) : Option Enc :=
  if td.lo = 0 then none
  else
    some (bump S (bump S (bump S (bump S
      (quot S b (L * logNum b / 10 ^ 30 - 1) (ipow WBITS b (L * logNum b / 10 ^ 30 - 1)) td)))))

theorem jump_sound (S b L : Nat) (td : Tri) (e : Enc) (hd : Encl td (6 ^ L))
    (h : jump S b L td = some e) : Valid S L e ∧ e.b = b := by
  unfold jump at h
  split at h
  · cases h
  · rename_i hne
    have hpos : 0 < td.lo := Nat.pos_of_ne_zero hne
    injection h with h
    subst h
    refine ⟨?_, ?_⟩
    · apply bump_valid; apply bump_valid; apply bump_valid; apply bump_valid
      exact quot_sound S L b _ _ td (ipow_sound WBITS b _) hd hpos
    · rw [bump_b, bump_b, bump_b, bump_b, quot_b]

def jumpAll (S L : Nat) : Option (List Enc) :=
  match jump S 3 L (ipow WBITS 6 L), jump S 4 L (ipow WBITS 6 L), jump S 5 L (ipow WBITS 6 L) with
  | some a, some b, some c => some [a, b, c]
  | _, _, _ => none

/-- the bases of the enclosures are among 3, 4, 5 -/
def Bases (es : List Enc) : Prop := ∀ e ∈ es, e.b = 3 ∨ e.b = 4 ∨ e.b = 5

theorem jumpAll_sound (S L : Nat) (es : List Enc) (h : jumpAll S L = some es) :
    (∀ e ∈ es, Valid S L e) ∧ Bases es := by
  unfold jumpAll at h
  split at h
  · rename_i a b c ha hb hc
    injection h with h
    subst h
    have h6 := ipow_sound WBITS 6 L
    have sa := jump_sound S 3 L _ a h6 ha
    have sb := jump_sound S 4 L _ b h6 hb
    have sc := jump_sound S 5 L _ c h6 hc
    constructor
    · intro e he
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
      rcases he with rfl | rfl | rfl
      · exact sa.1
      · exact sb.1
      · exact sc.1
    · intro e he
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
      rcases he with rfl | rfl | rfl
      · exact Or.inl sa.2
      · exact Or.inr (Or.inl sb.2)
      · exact Or.inr (Or.inr sc.2)
  · cases h

/-! ## Sweeping -/

/-- small scale: fits machine words -/
def S2 : Nat := 2 ^ 56
/-- large scale: used only when the small scale cannot decide -/
def SB : Nat := 2 ^ 220

theorem S2_pos : 0 < S2 := Nat.pow_pos (by decide)
theorem SB_pos : 0 < SB := Nat.pow_pos (by decide)

/-- slow, high-precision check of one length -/
def checkBig (L : Nat) : Bool :=
  match jumpAll SB L with
  | some es => checkL SB L es
  | none => false

/-- `cover A B`: no solution `N` with `6^A ≤ N < 6^B`. -/
def cover (A B : Nat) : Prop := ∀ N, 6 ^ A ≤ N → N < 6 ^ B → good 6 N = false

theorem good6 (N : Nat) (h : good 6 N = true) :
    ok 3 N = true ∧ ok 4 N = true ∧ ok 5 N = true ∧ ok 6 N = true := by
  simpa [good, List.range'] using h

theorem oks_of_bases (N : Nat) (h : good 6 N = true) (es : List Enc) (hb : Bases es) :
    ∀ e ∈ es, ok e.b N = true := by
  intro e he
  have := good6 N h
  rcases hb e he with h3 | h4 | h5
  · rw [h3]; exact this.1
  · rw [h4]; exact this.2.1
  · rw [h5]; exact this.2.2.1

theorem checkBig_sound (L N : Nat) (h : checkBig L = true) (hlo : 6 ^ L ≤ N) (hhi : N < 6 ^ (L + 1))
    (hg : good 6 N = true) : False := by
  unfold checkBig at h
  split at h
  · rename_i es hes
    have := jumpAll_sound SB L es hes
    exact checkL_sound SB L N SB_pos es h this.1 hlo hhi (good6 N hg).2.2.2
      (oks_of_bases N hg es this.2)
  · cases h

/-- check lengths `L, …, L+f-1`, stepping small-scale enclosures -/
def sweepF : Nat → Nat → List Enc → Bool
  | 0, _, _ => true
  | f + 1, L, es => (checkL S2 L es || checkBig L) && sweepF f (L + 1) (es.map (stepEnc S2))

theorem sweepF_sound : ∀ (f L : Nat) (es : List Enc), sweepF f L es = true →
    (∀ e ∈ es, Valid S2 L e) → Bases es → cover L (L + f)
  | 0, L, _, _, _, _ => by
    intro N hlo hhi
    simp at hhi; omega
  | f + 1, L, es, h, hv, hb => by
    intro N hlo hhi
    simp only [sweepF, Bool.and_eq_true, Bool.or_eq_true] at h
    cases hg : good 6 N with
    | false => rfl
    | true =>
      exfalso
      by_cases hN : N < 6 ^ (L + 1)
      · rcases h.1 with h1 | h1
        · exact checkL_sound S2 L N S2_pos es h1 hv hlo hN (good6 N hg).2.2.2 (oks_of_bases N hg es hb)
        · exact checkBig_sound L N h1 hlo hN hg
      · have hv' : ∀ e ∈ es.map (stepEnc S2), Valid S2 (L + 1) e := by
          intro e he
          obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
          exact stepEnc_valid S2 L e' (hv e' he')
        have hb' : Bases (es.map (stepEnc S2)) := by
          intro e he
          obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
          rw [stepEnc_b]; exact hb e' he'
        have := sweepF_sound f (L + 1) _ h.2 hv' hb' N (by omega)
          (by have : L + 1 + f = L + (f + 1) := by omega
              rw [this]; exact hhi)
        rw [hg] at this; cases this

/-- `n` blocks of `blk` lengths starting at `L0`; enclosures are recomputed at every block start -/
def blocks (blk : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, L0 =>
    (match jumpAll S2 L0 with
     | some es => sweepF blk L0 es
     | none => false) && blocks blk n (L0 + blk)

theorem blocks_sound (blk : Nat) : ∀ (n L0 : Nat), blocks blk n L0 = true → cover L0 (L0 + n * blk)
  | 0, L0, _ => by
    intro N hlo hhi
    simp at hhi; omega
  | n + 1, L0, h => by
    simp only [blocks, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have ih := blocks_sound blk n (L0 + blk) h2
    have hfirst : cover L0 (L0 + blk) := by
      split at h1
      · rename_i es hes
        have := jumpAll_sound S2 L0 es hes
        exact sweepF_sound blk L0 es h1 this.1 this.2
      · cases h1
    intro N hlo hhi
    by_cases hN : N < 6 ^ (L0 + blk)
    · exact hfirst N hlo hN
    · refine ih N (by omega) ?_
      have : L0 + blk + n * blk = L0 + (n + 1) * blk := by rw [Nat.add_mul]; omega
      rw [this]; exact hhi

theorem cover_trans {A B C : Nat} (h1 : cover A B) (h2 : cover B C) : cover A C := by
  intro N hlo hhi
  by_cases hN : N < 6 ^ B
  · exact h1 N hlo hN
  · exact h2 N (by omega) hhi

/-- `a6_gt_big` restated: nothing between 2 and `6^3000`. -/
theorem below_of_cover {B : Nat} (h : cover 3000 B) : ∀ N, 1 < N → N < 6 ^ B → good 6 N = false := by
  intro N h1 hlt
  by_cases hN : N < 6 ^ 3000
  · exact a6_gt_big N h1 hN
  · exact h N (by omega) hlt
