import NRB.Sweep

/-!
# Ruling out a whole run of lengths with one test

Lengths `L, L+q, L+2q, …, L+Kq` behave almost alike when `6^q` is very close to a power of
every other base.  For such a run we widen each enclosure so that it is valid for every
member of the run, and call the same checker once.  If it succeeds, all `K+1` lengths are
ruled out.  If it fails we fall back to checking the members one at a time.

Main result: `rsweep_sound`.
-/

/-- Like `Valid`, but the enclosure's `m` is only a lower bound for the true exponent `M`. -/
def ValidM (S L : Nat) (e : Enc) (M : Nat) : Prop :=
  e.m ≤ M ∧ e.slo * 6 ^ L ≤ e.b ^ M * S ∧ e.b ^ M * S ≤ e.shi * 6 ^ L

/-- A node holds for `N` at length `L`, for some true exponent `M ≥ e.m`. -/
def Hold (S L N : Nat) (n : Node) : Prop :=
  ∃ M, ValidM S L n.e M ∧ 2 ≤ n.e.b ∧ ok n.e.b N = true ∧ n.k ≤ M ∧
    N / n.e.b ^ (M - n.k) = n.P ∧ n.d = n.e.b ^ n.k

theorem hold_iv (S L N : Nat) (hS : 0 < S) (n : Node) (h : Hold S L N n) : In S L N (iv n) := by
  obtain ⟨e, P, k, d, w⟩ := n
  obtain ⟨b, m, slo, shi⟩ := e
  simp only [Hold, ValidM] at h
  obtain ⟨M, ⟨_, v1, v2⟩, hb, hok, hk, hP, hd⟩ := h
  exact iv_sound S L N hS ⟨⟨b, M, slo, shi⟩, P, k, d, w⟩ ⟨v1, v2⟩ hb ⟨hok, hk, hP, hd⟩

theorem hold_split (S L N : Nat) (n : Node) (h : Hold S L N n) (hk : n.k < n.e.m) :
    Hold S L N (child n 0) ∨ Hold S L N (child n 1) := by
  obtain ⟨e, P, k, d, w⟩ := n
  obtain ⟨b, m, slo, shi⟩ := e
  simp only [Hold, ValidM] at h
  obtain ⟨M, ⟨hm, v1, v2⟩, hb, hok, hkM, hP, hd⟩ := h
  simp only at hk
  have hkM' : k < M := by omega
  have := split N ⟨⟨b, M, slo, shi⟩, P, k, d, w⟩ hb ⟨hok, hkM, hP, hd⟩ hkM'
  simp only [Cons, child] at this
  rcases this with ⟨_, c2, c3, c4⟩ | ⟨_, c2, c3, c4⟩
  · left; exact ⟨M, ⟨hm, v1, v2⟩, hb, hok, c2, c3, c4⟩
  · right; exact ⟨M, ⟨hm, v1, v2⟩, hb, hok, c2, c3, c4⟩

theorem kill_soundH (S L N : Nat) (hS : 0 < S) : ∀ (f : Nat) (ns : List Node) (lo hi : Nat),
    kill f ns lo hi = true → (∀ n ∈ ns, Hold S L N n) → In S L N (lo, hi) → False
  | 0, _, _, _, h, _, _ => by simp [kill] at h
  | f + 1, ns, lo, hi, h, hh, hin => by
    simp only [kill] at h
    split at h
    · simp at h
    · rename_i n hn
      have hmem : n ∈ ns := List.mem_of_getElem? hn
      split at h
      · rename_i hk
        simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
        have hset : ∀ d, Hold S L N (child n d) →
            ∀ x ∈ ns.set (pick ns) (child n d), Hold S L N x := by
          intro d hd x hx
          rcases List.mem_or_eq_of_mem_set hx with hx | hx
          · exact hh x hx
          · subst hx; exact hd
        have hbox : ∀ d, Hold S L N (child n d) →
            In S L N (max lo (iv (child n d)).1, min hi (iv (child n d)).2) := by
          intro d hd
          exact In_inter S L N (lo, hi) (iv (child n d)) hin (hold_iv S L N hS _ hd)
        rcases hold_split S L N n (hh n hmem) hk with h0 | h1
        · rcases h.1 with hd | hkk
          · exact In_dead S L N _ _ (hbox 0 h0) hd
          · exact kill_soundH S L N hS f _ _ _ hkk (hset 0 h0) (hbox 0 h0)
        · rcases h.2 with hd | hkk
          · exact In_dead S L N _ _ (hbox 1 h1) hd
          · exact kill_soundH S L N hS f _ _ _ hkk (hset 1 h1) (hbox 1 h1)
      · simp at h

theorem rootH (S L N : Nat) (hS : 0 < S) (e : Enc) (w M : Nat) (hv : ValidM S L e M) (hb : 2 ≤ e.b)
    (c1 : 6 * S ≤ 10 * e.slo) (c2 : e.shi ≤ (e.b - 1) * S)
    (hlo : 6 ^ L ≤ N) (hhi : 5 * N + 1 ≤ 6 ^ (L + 1)) (hok : ok e.b N = true) :
    Hold S L N ⟨e, 1, 0, 1, w⟩ := by
  obtain ⟨b, m, slo, shi⟩ := e
  obtain ⟨hm, v1, v2⟩ := hv
  have := root S L N hS ⟨b, M, slo, shi⟩ w ⟨v1, v2⟩ hb c1 c2 hlo hhi hok
  simp only [Cons] at this
  exact ⟨M, ⟨hm, v1, v2⟩, hb, this.1, this.2.1, this.2.2.1, this.2.2.2⟩

/-- `checkL S L es` run at length `L` also rules out any longer length `L'` for which the
    same enclosures are valid with larger exponents. -/
theorem checkL_soundG (S L L' N : Nat) (hS : 0 < S) (hLL : L ≤ L') (es : List Enc)
    (h : checkL S L es = true) (hv : ∀ e ∈ es, ∃ M, ValidM S L' e M)
    (hlo : 6 ^ L' ≤ N) (hhi : N < 6 ^ (L' + 1))
    (h6 : ok 6 N = true) (hoks : ∀ e ∈ es, ok e.b N = true) : False := by
  simp only [checkL, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨hcond, hkill⟩ := h
  have hw := ok_window 6 (by omega) (L' + 1) N h6 hhi
  have hhi' : 5 * N + 1 ≤ 6 ^ (L' + 1) := by simpa using hw
  have hv' : ∀ e ∈ (⟨6, L, S, S⟩ : Enc) :: es, ∃ M, ValidM S L' e M := by
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · refine ⟨L', hLL, ?_, ?_⟩
      · rw [Nat.mul_comm]; exact Nat.le_refl _
      · rw [Nat.mul_comm]; exact Nat.le_refl _
    · exact hv e he
  have hok' : ∀ e ∈ (⟨6, L, S, S⟩ : Enc) :: es, ok e.b N = true := by
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact h6
    · exact hoks e he
  have hnodes : ∀ n ∈ ((⟨6, L, S, S⟩ : Enc) :: es).map rootNode, Hold S L' N n := by
    intro n hn
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hn
    have hc := hcond e he
    simp only [encOk, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨M, hM⟩ := hv' e he
    exact rootH S L' N hS e _ M hM hc.1.1 hc.1.2 hc.2 hlo hhi' (hok' e he)
  have hroot6 : In S L' N (iv (rootNode ⟨6, L, S, S⟩)) :=
    hold_iv S L' N hS _ (hnodes (rootNode ⟨6, L, S, S⟩) (by simp))
  have hbox := box_sound S L' N _ _ hroot6 (fun n hn => hold_iv S L' N hS n (hnodes n hn))
  rcases hkill with hd | hk
  · exact In_dead S L' N _ _ hbox hd
  · exact kill_soundH S L' N hS 300 _ _ _ hk hnodes hbox

/-! ## A refinement that stops when splitting can no longer help

With a widened enclosure a band cannot be located more precisely than the enclosure's own
slack `shi - slo`.  `killW` is `kill` with one extra exit: give up once the widest band is
within a small multiple of that slack. -/

def killW : Nat → List Node → Nat → Nat → Bool
  | 0, _, _, _ => false
  | f + 1, ns, lo, hi =>
    match ns[pick ns]? with
    | none => false
    | some n =>
      if n.k < n.e.m then
        if n.w < 4 * (n.e.shi - n.e.slo) then false
        else
          (decide (min hi (iv (child n 0)).2 ≤ max lo (iv (child n 0)).1) ||
            killW f (ns.set (pick ns) (child n 0)) (max lo (iv (child n 0)).1) (min hi (iv (child n 0)).2)) &&
          (decide (min hi (iv (child n 1)).2 ≤ max lo (iv (child n 1)).1) ||
            killW f (ns.set (pick ns) (child n 1)) (max lo (iv (child n 1)).1) (min hi (iv (child n 1)).2))
      else false

theorem killW_sound (S L N : Nat) (hS : 0 < S) : ∀ (f : Nat) (ns : List Node) (lo hi : Nat),
    killW f ns lo hi = true → (∀ n ∈ ns, Hold S L N n) → In S L N (lo, hi) → False
  | 0, _, _, _, h, _, _ => by simp [killW] at h
  | f + 1, ns, lo, hi, h, hh, hin => by
    simp only [killW] at h
    split at h
    · simp at h
    · rename_i n hn
      have hmem : n ∈ ns := List.mem_of_getElem? hn
      split at h
      · rename_i hk
        split at h
        · simp at h
        · simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
          have hset : ∀ d, Hold S L N (child n d) →
              ∀ x ∈ ns.set (pick ns) (child n d), Hold S L N x := by
            intro d hd x hx
            rcases List.mem_or_eq_of_mem_set hx with hx | hx
            · exact hh x hx
            · subst hx; exact hd
          have hbox : ∀ d, Hold S L N (child n d) →
              In S L N (max lo (iv (child n d)).1, min hi (iv (child n d)).2) := by
            intro d hd
            exact In_inter S L N (lo, hi) (iv (child n d)) hin (hold_iv S L N hS _ hd)
          rcases hold_split S L N n (hh n hmem) hk with h0 | h1
          · rcases h.1 with hd | hkk
            · exact In_dead S L N _ _ (hbox 0 h0) hd
            · exact killW_sound S L N hS f _ _ _ hkk (hset 0 h0) (hbox 0 h0)
          · rcases h.2 with hd | hkk
            · exact In_dead S L N _ _ (hbox 1 h1) hd
            · exact killW_sound S L N hS f _ _ _ hkk (hset 1 h1) (hbox 1 h1)
      · simp at h

/-- `checkL` with `killW` in place of `kill` -/
def checkLW (S L : Nat) (es : List Enc) : Bool :=
  ((⟨6, L, S, S⟩ : Enc) :: es).all (encOk S) &&
  (decide ((box (((⟨6, L, S, S⟩ : Enc) :: es).map rootNode) (iv (rootNode ⟨6, L, S, S⟩))).2 ≤
           (box (((⟨6, L, S, S⟩ : Enc) :: es).map rootNode) (iv (rootNode ⟨6, L, S, S⟩))).1) ||
   killW 60 (((⟨6, L, S, S⟩ : Enc) :: es).map rootNode)
     (box (((⟨6, L, S, S⟩ : Enc) :: es).map rootNode) (iv (rootNode ⟨6, L, S, S⟩))).1
     (box (((⟨6, L, S, S⟩ : Enc) :: es).map rootNode) (iv (rootNode ⟨6, L, S, S⟩))).2)

theorem checkLW_sound (S L L' N : Nat) (hS : 0 < S) (hLL : L ≤ L') (es : List Enc)
    (h : checkLW S L es = true) (hv : ∀ e ∈ es, ∃ M, ValidM S L' e M)
    (hlo : 6 ^ L' ≤ N) (hhi : N < 6 ^ (L' + 1))
    (h6 : ok 6 N = true) (hoks : ∀ e ∈ es, ok e.b N = true) : False := by
  simp only [checkLW, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨hcond, hkill⟩ := h
  have hw := ok_window 6 (by omega) (L' + 1) N h6 hhi
  have hhi' : 5 * N + 1 ≤ 6 ^ (L' + 1) := by simpa using hw
  have hv' : ∀ e ∈ (⟨6, L, S, S⟩ : Enc) :: es, ∃ M, ValidM S L' e M := by
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · refine ⟨L', hLL, ?_, ?_⟩
      · rw [Nat.mul_comm]; exact Nat.le_refl _
      · rw [Nat.mul_comm]; exact Nat.le_refl _
    · exact hv e he
  have hok' : ∀ e ∈ (⟨6, L, S, S⟩ : Enc) :: es, ok e.b N = true := by
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact h6
    · exact hoks e he
  have hnodes : ∀ n ∈ ((⟨6, L, S, S⟩ : Enc) :: es).map rootNode, Hold S L' N n := by
    intro n hn
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hn
    have hc := hcond e he
    simp only [encOk, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨M, hM⟩ := hv' e he
    exact rootH S L' N hS e _ M hM hc.1.1 hc.1.2 hc.2 hlo hhi' (hok' e he)
  have hroot6 : In S L' N (iv (rootNode ⟨6, L, S, S⟩)) :=
    hold_iv S L' N hS _ (hnodes (rootNode ⟨6, L, S, S⟩) (by simp))
  have hbox := box_sound S L' N _ _ hroot6 (fun n hn => hold_iv S L' N hS n (hnodes n hn))
  rcases hkill with hd | hk
  · exact In_dead S L' N _ _ hbox hd
  · exact killW_sound S L' N hS 60 _ _ _ hk hnodes hbox

/-! ## Arithmetic of composed enclosures -/

theorem comp_arith (S A X B Y a1 a2 x1 x2 : Nat) (hS : 0 < S)
    (h1 : a1 * A ≤ B * S) (h2 : B * S ≤ a2 * A) (g1 : x1 * X ≤ Y * S) (g2 : Y * S ≤ x2 * X) :
    a1 * x1 / S * (A * X) ≤ B * Y * S ∧ B * Y * S ≤ (a2 * x2 + (S - 1)) / S * (A * X) := by
  constructor
  · have hw : a1 * x1 / S * S ≤ a1 * x1 := Nat.div_mul_le_self _ _
    have : a1 * x1 / S * (A * X) * S ≤ B * Y * S * S := by
      calc a1 * x1 / S * (A * X) * S = a1 * x1 / S * S * (A * X) := by ac_rfl
        _ ≤ a1 * x1 * (A * X) := Nat.mul_le_mul_right _ hw
        _ = a1 * A * (x1 * X) := by ac_rfl
        _ ≤ B * S * (Y * S) := Nat.mul_le_mul h1 g1
        _ = B * Y * S * S := by ac_rfl
    exact Nat.le_of_mul_le_mul_right this hS
  · have hw := ceil_ge (a2 * x2) S hS
    have : B * Y * S * S ≤ (a2 * x2 + (S - 1)) / S * (A * X) * S := by
      calc B * Y * S * S = B * S * (Y * S) := by ac_rfl
        _ ≤ a2 * A * (x2 * X) := Nat.mul_le_mul h2 g2
        _ = a2 * x2 * (A * X) := by ac_rfl
        _ ≤ (a2 * x2 + (S - 1)) / S * S * (A * X) := Nat.mul_le_mul_right _ hw
        _ = (a2 * x2 + (S - 1)) / S * (A * X) * S := by ac_rfl
    exact Nat.le_of_mul_le_mul_right this hS

/-- Step ratio at least 1: the lower bound stays, the upper bound grows by at most the K-step ratio. -/
theorem run_up (S A B X Y slo shi rhi W K k : Nat) (hS : 0 < S) (hX : 0 < X) (F : X ≤ Y)
    (e1 : slo * A ≤ B * S) (e2 : B * S ≤ shi * A) (hK : Y ^ K * S ≤ rhi * X ^ K) (hk : k ≤ K)
    (hW : shi * rhi ≤ W * S) :
    slo * (A * X ^ k) ≤ B * Y ^ k * S ∧ B * Y ^ k * S ≤ W * (A * X ^ k) := by
  obtain ⟨j, rfl⟩ : ∃ j, K = k + j := ⟨K - k, by omega⟩
  rw [Nat.pow_add, Nat.pow_add] at hK
  have hXk : X ^ k ≤ Y ^ k := Nat.pow_le_pow_left F k
  have hXj : X ^ j ≤ Y ^ j := Nat.pow_le_pow_left F j
  have hXjpos : 0 < X ^ j := Nat.pow_pos hX
  generalize X ^ k = Xk at *
  generalize Y ^ k = Yk at *
  generalize X ^ j = Xj at *
  generalize Y ^ j = Yj at *
  have T : Yk * S ≤ rhi * Xk := by
    have : Yk * S * Xj ≤ rhi * Xk * Xj := by
      calc Yk * S * Xj ≤ Yk * S * Yj := Nat.mul_le_mul_left _ hXj
        _ = Yk * Yj * S := by ac_rfl
        _ ≤ rhi * (Xk * Xj) := hK
        _ = rhi * Xk * Xj := by ac_rfl
    exact Nat.le_of_mul_le_mul_right this hXjpos
  constructor
  · calc slo * (A * Xk) = slo * A * Xk := by ac_rfl
      _ ≤ B * S * Xk := Nat.mul_le_mul_right _ e1
      _ ≤ B * S * Yk := Nat.mul_le_mul_left _ hXk
      _ = B * Yk * S := by ac_rfl
  · have : B * Yk * S * S ≤ W * (A * Xk) * S := by
      calc B * Yk * S * S = B * S * (Yk * S) := by ac_rfl
        _ ≤ shi * A * (rhi * Xk) := Nat.mul_le_mul e2 T
        _ = shi * rhi * (A * Xk) := by ac_rfl
        _ ≤ W * S * (A * Xk) := Nat.mul_le_mul_right _ hW
        _ = W * (A * Xk) * S := by ac_rfl
    exact Nat.le_of_mul_le_mul_right this hS

/-- Step ratio at most 1: the upper bound stays, the lower bound shrinks by at most the K-step ratio. -/
theorem run_dn (S A B X Y slo shi rlo W K k : Nat) (hS : 0 < S) (hX : 0 < X) (F : Y ≤ X)
    (e1 : slo * A ≤ B * S) (e2 : B * S ≤ shi * A) (hK : rlo * X ^ K ≤ Y ^ K * S) (hk : k ≤ K)
    (hW : W * S ≤ slo * rlo) :
    W * (A * X ^ k) ≤ B * Y ^ k * S ∧ B * Y ^ k * S ≤ shi * (A * X ^ k) := by
  obtain ⟨j, rfl⟩ : ∃ j, K = k + j := ⟨K - k, by omega⟩
  rw [Nat.pow_add, Nat.pow_add] at hK
  have hYk : Y ^ k ≤ X ^ k := Nat.pow_le_pow_left F k
  have hYj : Y ^ j ≤ X ^ j := Nat.pow_le_pow_left F j
  have hXjpos : 0 < X ^ j := Nat.pow_pos hX
  generalize X ^ k = Xk at *
  generalize Y ^ k = Yk at *
  generalize X ^ j = Xj at *
  generalize Y ^ j = Yj at *
  have T : rlo * Xk ≤ Yk * S := by
    have : rlo * Xk * Xj ≤ Yk * S * Xj := by
      calc rlo * Xk * Xj = rlo * (Xk * Xj) := by ac_rfl
        _ ≤ Yk * Yj * S := hK
        _ ≤ Yk * Xj * S := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hYj)
        _ = Yk * S * Xj := by ac_rfl
    exact Nat.le_of_mul_le_mul_right this hXjpos
  constructor
  · have : W * (A * Xk) * S ≤ B * Yk * S * S := by
      calc W * (A * Xk) * S = W * S * (A * Xk) := by ac_rfl
        _ ≤ slo * rlo * (A * Xk) := Nat.mul_le_mul_right _ hW
        _ = slo * A * (rlo * Xk) := by ac_rfl
        _ ≤ B * S * (Yk * S) := Nat.mul_le_mul e1 T
        _ = B * Yk * S * S := by ac_rfl
    exact Nat.le_of_mul_le_mul_right this hS
  · calc B * Yk * S = B * S * Yk := by ac_rfl
      _ ≤ B * S * Xk := Nat.mul_le_mul_left _ hYk
      _ ≤ shi * A * Xk := Nat.mul_le_mul_right _ e2
      _ = shi * (A * Xk) := by ac_rfl

/-! ## Composed and widened enclosures -/

/-- enclosure at `L + q` from one at `L` and one for the step `q` -/
def compE (S : Nat) (e r : Enc) : Enc :=
  ⟨e.b, e.m + r.m, e.slo * r.slo / S, (e.shi * r.shi + (S - 1)) / S⟩

theorem comp_sound (S L q : Nat) (hS : 0 < S) (e r : Enc) (he : Valid S L e) (hr : Valid S q r)
    (hb : r.b = e.b) : Valid S (L + q) (compE S e r) := by
  simp only [Valid, compE] at *
  rw [hb] at hr
  rw [Nat.pow_add, Nat.pow_add]
  exact comp_arith S _ _ _ _ _ _ _ _ hS he.1 he.2 hr.1 hr.2

/-- the step ratio is provably on one side of 1 -/
def wideOk (S : Nat) (r1 : Enc) : Bool := decide (S ≤ r1.slo) || decide (r1.shi ≤ S)

/-- one enclosure valid for every member `L + q·k`, `k ≤ K`, of a run -/
def wideE (S : Nat) (e r1 rK : Enc) : Enc :=
  if S ≤ r1.slo then ⟨e.b, e.m, e.slo, (e.shi * rK.shi + (S - 1)) / S⟩
  else ⟨e.b, e.m, e.slo * rK.slo / S, e.shi⟩

theorem wideE_b (S : Nat) (e r1 rK : Enc) : (wideE S e r1 rK).b = e.b := by
  unfold wideE; split <;> rfl

theorem wide_sound (S L q p K k : Nat) (hS : 0 < S) (e r1 rK : Enc)
    (he : Valid S L e) (h1 : Valid S (q * 1) r1) (hK : Valid S (q * K) rK)
    (b1 : r1.b = e.b) (m1 : r1.m = p * 1) (bK : rK.b = e.b) (mK : rK.m = p * K)
    (hk : k ≤ K) (hok : wideOk S r1 = true) :
    ValidM S (L + q * k) (wideE S e r1 rK) (e.m + p * k) := by
  obtain ⟨b, m, slo, shi⟩ := e
  obtain ⟨b1', m1', rlo1, rhi1⟩ := r1
  obtain ⟨bK', mK', rloK, rhiK⟩ := rK
  simp only at b1 m1 bK mK
  simp only [Valid] at he h1 hK
  rw [b1, m1] at h1
  rw [bK, mK] at hK
  simp only [Nat.mul_one] at h1
  simp only [wideOk, Bool.or_eq_true, decide_eq_true_eq] at hok
  rw [Nat.pow_mul, Nat.pow_mul] at hK
  have hX : 0 < 6 ^ q := Nat.pow_pos (by decide)
  unfold wideE
  simp only
  split
  · rename_i hA
    have F : 6 ^ q ≤ b ^ p := by
      have : 6 ^ q * S ≤ b ^ p * S := by
        calc 6 ^ q * S = S * 6 ^ q := Nat.mul_comm _ _
          _ ≤ rlo1 * 6 ^ q := Nat.mul_le_mul_right _ hA
          _ ≤ b ^ p * S := h1.1
      exact Nat.le_of_mul_le_mul_right this hS
    have hW := ceil_ge (shi * rhiK) S hS
    have := run_up S (6 ^ L) (b ^ m) (6 ^ q) (b ^ p) slo shi rhiK _ K k hS hX F he.1 he.2 hK.2 hk hW
    refine ⟨Nat.le_add_right _ _, ?_, ?_⟩
    · simp only; rw [Nat.pow_add, Nat.pow_add, Nat.pow_mul, Nat.pow_mul]; exact this.1
    · simp only; rw [Nat.pow_add, Nat.pow_add, Nat.pow_mul, Nat.pow_mul]; exact this.2
  · rename_i hA
    have hB : rhi1 ≤ S := by
      rcases hok with h | h
      · exact absurd h hA
      · exact h
    have F : b ^ p ≤ 6 ^ q := by
      have : b ^ p * S ≤ 6 ^ q * S := by
        calc b ^ p * S ≤ rhi1 * 6 ^ q := h1.2
          _ ≤ S * 6 ^ q := Nat.mul_le_mul_right _ hB
          _ = 6 ^ q * S := Nat.mul_comm _ _
      exact Nat.le_of_mul_le_mul_right this hS
    have hW : slo * rloK / S * S ≤ slo * rloK := Nat.div_mul_le_self _ _
    have := run_dn S (6 ^ L) (b ^ m) (6 ^ q) (b ^ p) slo shi rloK _ K k hS hX F he.1 he.2 hK.1 hk hW
    refine ⟨Nat.le_add_right _ _, ?_, ?_⟩
    · simp only; rw [Nat.pow_add, Nat.pow_add, Nat.pow_mul, Nat.pow_mul]; exact this.1
    · simp only; rw [Nat.pow_add, Nat.pow_add, Nat.pow_mul, Nat.pow_mul]; exact this.2

/-! ## Tables of step ratios -/

structure Row where
  r3 : Enc
  r4 : Enc
  r5 : Enc

def selR (row : Row) (b : Nat) : Enc := if b = 3 then row.r3 else if b = 4 then row.r4 else row.r5

/-- the power of `b` closest to `6^q` (a guess; a bad guess only makes checks fail) -/
def pOf (q b : Nat) : Nat := (q * logNum b + 5 * 10 ^ 29) / 10 ^ 30

/-- row `k` encloses `b^(p·k) / 6^(q·k)` for each base -/
def RowOK (S q k : Nat) (row : Row) : Prop :=
  ∀ b, (b = 3 ∨ b = 4 ∨ b = 5) →
    Valid S (q * k) (selR row b) ∧ (selR row b).b = b ∧ (selR row b).m = pOf q b * k

def mkEnc (S q k b : Nat) : Enc :=
  quot S b (pOf q b * k) (ipow WBITS b (pOf q b * k)) (ipow WBITS 6 (q * k))

def mkRow (S q k : Nat) : Option Row :=
  if (ipow WBITS 6 (q * k)).lo = 0 then none
  else some ⟨mkEnc S q k 3, mkEnc S q k 4, mkEnc S q k 5⟩

theorem quot_m (S b m : Nat) (tn td : Tri) : (quot S b m tn td).m = m := by
  unfold quot; split <;> rfl

theorem mkRow_sound (S q k : Nat) (row : Row) (h : mkRow S q k = some row) : RowOK S q k row := by
  unfold mkRow at h
  split at h
  · cases h
  · rename_i hne
    have hpos : 0 < (ipow WBITS 6 (q * k)).lo := Nat.pos_of_ne_zero hne
    injection h with h
    subst h
    intro b hb
    have key : ∀ c, Valid S (q * k) (mkEnc S q k c) ∧ (mkEnc S q k c).b = c ∧
        (mkEnc S q k c).m = pOf q c * k := by
      intro c
      unfold mkEnc
      exact ⟨quot_sound S (q * k) c _ _ _ (ipow_sound WBITS c _) (ipow_sound WBITS 6 _) hpos,
        quot_b _ _ _ _ _, quot_m _ _ _ _ _⟩
    rcases hb with rfl | rfl | rfl
    · simpa [selR] using key 3
    · simpa [selR] using key 4
    · simpa [selR] using key 5

def RowsOK (S q : Nat) : Nat → List Row → Prop
  | _, [] => True
  | k, row :: rest => RowOK S q k row ∧ RowsOK S q (k + 1) rest

def mkRows (S q : Nat) : Nat → Nat → Option (List Row)
  | 0, _ => some []
  | n + 1, k =>
    match mkRow S q k, mkRows S q n (k + 1) with
    | some r, some rs => some (r :: rs)
    | _, _ => none

theorem mkRows_sound (S q : Nat) : ∀ (n k : Nat) (rows : List Row), mkRows S q n k = some rows →
    RowsOK S q k rows ∧ rows.length = n
  | 0, k, rows, h => by
    simp only [mkRows] at h
    injection h with h
    subst h
    exact ⟨trivial, rfl⟩
  | n + 1, k, rows, h => by
    simp only [mkRows] at h
    split at h
    · rename_i r rs hr hrs
      injection h with h
      subst h
      have ih := mkRows_sound S q n (k + 1) rs hrs
      exact ⟨⟨mkRow_sound S q k r hr, ih.1⟩, by simp [ih.2]⟩
    · cases h

structure Tbl where
  rows : List Row
  r1 : Row
  rK : Row

def TOK (S q K : Nat) (T : Tbl) : Prop :=
  RowOK S q 1 T.r1 ∧ RowOK S q K T.rK ∧ RowsOK S q 0 T.rows ∧ T.rows.length = K + 1

def mkT (S q K : Nat) : Option Tbl :=
  match mkRow S q 1, mkRow S q K, mkRows S q (K + 1) 0 with
  | some a, some c, some rs => some ⟨rs, a, c⟩
  | _, _, _ => none

theorem mkT_sound (S q K : Nat) (T : Tbl) (h : mkT S q K = some T) : TOK S q K T := by
  unfold mkT at h
  split at h
  · rename_i a c rs ha hc hrs
    injection h with h
    subst h
    have := mkRows_sound S q (K + 1) 0 rs hrs
    exact ⟨mkRow_sound S q 1 a ha, mkRow_sound S q K c hc, this.1, this.2⟩
  · cases h

/-! ## Checking runs -/

/-- no solution has exactly `L+1` base-6 digits -/
def dead (L : Nat) : Prop := ∀ N, 6 ^ L ≤ N → N < 6 ^ (L + 1) → good 6 N = false

/-- check the members `L + q·k` one at a time, `k` running along the rows -/
def singles (S L q : Nat) (es : List Enc) : Nat → List Row → Bool
  | _, [] => true
  | k, row :: rest =>
    (checkL S (L + q * k) (es.map (fun e => bump S (compE S e (selR row e.b)))) || checkBig (L + q * k)) &&
    singles S L q es (k + 1) rest

theorem singles_sound (S L q : Nat) (hS : 0 < S) (es : List Enc) (hv : ∀ e ∈ es, Valid S L e)
    (hb : Bases es) : ∀ (rows : List Row) (k : Nat), RowsOK S q k rows →
    singles S L q es k rows = true → ∀ j, j < rows.length → dead (L + q * (k + j))
  | [], _, _, _, j, hj => by simp at hj
  | row :: rest, k, hr, h, j, hj => by
    simp only [singles, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨hrow, hrest⟩ := hr
    cases j with
    | zero =>
      intro N hlo hhi
      simp only [Nat.add_zero] at hlo hhi
      cases hg : good 6 N with
      | false => rfl
      | true =>
        exfalso
        rcases h.1 with h1 | h1
        · refine checkL_sound S (L + q * k) N hS _ h1 ?_ hlo hhi (good6 N hg).2.2.2 ?_
          · intro e he
            obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
            have := hrow e'.b (hb e' he')
            exact bump_valid S _ _ (comp_sound S L (q * k) hS e' _ (hv e' he') this.1 this.2.1)
          · intro e he
            obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
            rw [bump_b]
            exact oks_of_bases N hg es hb e' he'
        · exact checkBig_sound (L + q * k) N h1 hlo hhi hg
    | succ j =>
      have := singles_sound S L q hS es hv hb rest (k + 1) hrest h.2 j (by simpa using hj)
      have e : L + q * (k + 1 + j) = L + q * (k + (j + 1)) := by congr 2; omega
      rw [e] at this; exact this

/-- one widened test for the whole run, else the members one at a time -/
def runCheck (S L q : Nat) (T : Tbl) (es : List Enc) : Bool :=
  (es.all (fun e => wideOk S (selR T.r1 e.b)) &&
    checkLW S L (es.map (fun e => wideE S e (selR T.r1 e.b) (selR T.rK e.b)))) ||
  singles S L q es 0 T.rows

theorem run_sound (S L q K : Nat) (hS : 0 < S) (T : Tbl) (es : List Enc) (hT : TOK S q K T)
    (hv : ∀ e ∈ es, Valid S L e) (hb : Bases es) (h : runCheck S L q T es = true) :
    ∀ k, k ≤ K → dead (L + q * k) := by
  intro k hk
  simp only [runCheck, Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true] at h
  rcases h with ⟨hwide, hchk⟩ | hs
  · intro N hlo hhi
    cases hg : good 6 N with
    | false => rfl
    | true =>
      exfalso
      refine checkLW_sound S L (L + q * k) N hS (Nat.le_add_right _ _) _ hchk ?_ hlo hhi
        (good6 N hg).2.2.2 ?_
      · intro e he
        obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
        have h1 := hT.1 e'.b (hb e' he')
        have hKr := hT.2.1 e'.b (hb e' he')
        exact ⟨_, wide_sound S L q (pOf q e'.b) K k hS e' _ _ (hv e' he') h1.1 hKr.1
          h1.2.1 h1.2.2 hKr.2.1 hKr.2.2 hk (hwide e' he')⟩
      · intro e he
        obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
        rw [wideE_b]
        exact oks_of_bases N hg es hb e' he'
  · have := singles_sound S L q hS es hv hb T.rows 0 hT.2.2.1 hs k (by rw [hT.2.2.2]; omega)
    simpa using this

/-- runs starting at `L, L+1, …, L+f-1` -/
def runs (S q : Nat) (T : Tbl) : Nat → Nat → List Enc → Bool
  | 0, _, _ => true
  | f + 1, L, es => runCheck S L q T es && runs S q T f (L + 1) (es.map (stepEnc S))

theorem runs_sound (S q K : Nat) (hS : 0 < S) (T : Tbl) (hT : TOK S q K T) :
    ∀ (f L : Nat) (es : List Enc), runs S q T f L es = true → (∀ e ∈ es, Valid S L e) → Bases es →
    ∀ r, r < f → ∀ k, k ≤ K → dead (L + r + q * k)
  | 0, _, _, _, _, _, r, hr, _, _ => by omega
  | f + 1, L, es, h, hv, hb, r, hr, k, hk => by
    simp only [runs, Bool.and_eq_true] at h
    cases r with
    | zero => simpa using run_sound S L q K hS T es hT hv hb h.1 k hk
    | succ r =>
      have hv' : ∀ e ∈ es.map (stepEnc S), Valid S (L + 1) e := by
        intro e he
        obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
        exact stepEnc_valid S L e' (hv e' he')
      have hb' : Bases (es.map (stepEnc S)) := by
        intro e he
        obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
        rw [stepEnc_b]; exact hb e' he'
      have := runs_sound S q K hS T hT f (L + 1) _ h.2 hv' hb' r (by omega) k hk
      have e : L + 1 + r + q * k = L + (r + 1) + q * k := by omega
      rw [e] at this; exact this

theorem find_len : ∀ (n A N : Nat), 6 ^ A ≤ N → N < 6 ^ (A + n) →
    ∃ L', A ≤ L' ∧ L' < A + n ∧ 6 ^ L' ≤ N ∧ N < 6 ^ (L' + 1)
  | 0, A, N, hlo, hhi => by simp at hhi; omega
  | n + 1, A, N, hlo, hhi => by
    by_cases h : N < 6 ^ (A + 1)
    · exact ⟨A, Nat.le_refl _, by omega, hlo, h⟩
    · have e : A + 1 + n = A + (n + 1) := by omega
      obtain ⟨L', h1, h2, h3, h4⟩ := find_len n (A + 1) N (by omega) (by rw [e]; exact hhi)
      exact ⟨L', by omega, by omega, h3, h4⟩

theorem cover_of_dead (A n : Nat) (h : ∀ L', A ≤ L' → L' < A + n → dead L') : cover A (A + n) := by
  intro N hlo hhi
  obtain ⟨L', h1, h2, h3, h4⟩ := find_len n A N hlo hhi
  exact h L' h1 h2 N h3 h4

/-- `n` blocks of `q·(K+1)` lengths starting at `L0` -/
def rblocks (q K : Nat) (T : Tbl) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, L0 =>
    (match jumpAll S2 L0 with
     | some es => runs S2 q T q L0 es
     | none => false) && rblocks q K T n (L0 + q * (K + 1))

theorem rblocks_sound (q K : Nat) (hq : 0 < q) (T : Tbl) (hT : TOK S2 q K T) :
    ∀ (n L0 : Nat), rblocks q K T n L0 = true → cover L0 (L0 + n * (q * (K + 1)))
  | 0, L0, _ => by
    intro N hlo hhi
    simp at hhi; omega
  | n + 1, L0, h => by
    simp only [rblocks, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have ih := rblocks_sound q K hq T hT n (L0 + q * (K + 1)) h2
    have hfirst : cover L0 (L0 + q * (K + 1)) := by
      split at h1
      · rename_i es hes
        have hj := jumpAll_sound S2 L0 es hes
        apply cover_of_dead
        intro L' hA hB
        have hd : L' - L0 < q * (K + 1) := by omega
        have hk : (L' - L0) / q ≤ K := by
          have : (L' - L0) / q < K + 1 := Nat.div_lt_of_lt_mul hd
          omega
        have hr : (L' - L0) % q < q := Nat.mod_lt _ hq
        have := runs_sound S2 q K S2_pos T hT q L0 es h1 hj.1 hj.2 _ hr _ hk
        have e : L0 + (L' - L0) % q + q * ((L' - L0) / q) = L' := by
          have := Nat.div_add_mod (L' - L0) q
          omega
        rw [e] at this; exact this
      · cases h1
    have e : L0 + q * (K + 1) + n * (q * (K + 1)) = L0 + (n + 1) * (q * (K + 1)) := by
      rw [Nat.add_mul]; omega
    rw [← e]
    exact cover_trans hfirst ih

/-- the whole stripe sweep: tables are built once, then `n` blocks are checked -/
def rsweep (q K n L0 : Nat) : Bool :=
  match mkT S2 q K with
  | some T => decide (0 < q) && rblocks q K T n L0
  | none => false

theorem rsweep_sound (q K n L0 : Nat) (h : rsweep q K n L0 = true) :
    cover L0 (L0 + n * (q * (K + 1))) := by
  unfold rsweep at h
  split at h
  · rename_i T hT
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact rblocks_sound q K h.1 T (mkT_sound S2 q K T hT) n L0 h.2
  · cases h
