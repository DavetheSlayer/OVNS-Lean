import OddViscousNS.Closed.Forced.Moment.PairCheck
import OddViscousNS.Closed.Forced.Check.Sound

/-!
# Soundness of the pair checker

* `rawR`: the real pair value `½[g_l W/(u_l W + z_l) + g_h W/(u_h W + z_h)]` with real data;
  `rawq_cast` relates it to the rational checker, `rawR_mono` is monotonicity in `W`.
* `subdivOk_sound`: an accepted subdivision of `[lo, hi]` gives `rawR … W − λ(W − 1) < K` for every
  `W ∈ [lo, hi]`.
* `rangeOk_sound`: an accepted range gives the bound for every table pair `(C_l, C_h)` with
  `lo ≤ C_l < hi` and every `W` in the pair's interval, with the actual prices `gOVNS`.
* `gq_cast`, `gTable_eq_of_mem`, `mem_keys_of_rep3`: the table/representability glue.
-/

open Set

namespace OVNS

namespace Forced

namespace Mom

/-- The real pair value with prices `gl, gh`, weights `a, bL`. -/
noncomputable def rawR (a bL : ℝ) (Cl Ch : ℕ) (gl gh W : ℝ) : ℝ :=
  (gl * W / ((1 + bL / hmet Cl) * W + 4 * a * Cl / ((Cl : ℝ) + Ch)) +
    gh * W / ((1 + bL / hmet Ch) * W + 4 * a * Ch / ((Cl : ℝ) + Ch))) / 2

theorem rawq_cast (P : Params) (Cl Ch : ℕ) (gl gh W : ℚ) :
    ((rawq P Cl Ch gl gh W : ℚ) : ℝ) = rawR P.a P.bL Cl Ch gl gh W := by
  unfold rawq rawR
  push_cast
  rw [Chk.hq_cast, Chk.hq_cast]

/-- `h(j) ≥ 0`. -/
private lemma hmet_nonneg' (j : ℕ) : 0 ≤ hmet j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [hmet]
  · exact (hmet_pos hj).le

/-- One monotone summand `g W/(u W + z)`. -/
private lemma term_mono {g u z W W' : ℝ} (hg : 0 ≤ g) (hu : 1 ≤ u) (hz : 0 ≤ z) (hW : 0 ≤ W)
    (hWW : W ≤ W') : g * W / (u * W + z) ≤ g * W' / (u * W' + z) := by
  rcases hW.eq_or_lt with rfl | hW0
  · simp only [mul_zero, zero_add, zero_div]
    exact div_nonneg (mul_nonneg hg (by linarith)) (by nlinarith)
  · rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
    nlinarith [mul_le_mul_of_nonneg_left hWW (mul_nonneg hg hz)]

/-- Monotonicity in `W` (for `W ≥ 0`, nonnegative data, `1 ≤ C_l`). -/
theorem rawR_mono {a bL : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ bL) {Cl Ch : ℕ} (hCl : 1 ≤ Cl) {gl gh : ℝ}
    (hgl : 0 ≤ gl) (hgh : 0 ≤ gh) {W W' : ℝ} (hW : 0 ≤ W) (hWW : W ≤ W') :
    rawR a bL Cl Ch gl gh W ≤ rawR a bL Cl Ch gl gh W' := by
  have hJ : (0 : ℝ) ≤ (Cl : ℝ) + Ch := by positivity
  have hu : ∀ C : ℕ, 1 ≤ 1 + bL / hmet C := fun C ↦
    le_add_of_nonneg_right (div_nonneg hb (hmet_nonneg' C))
  have hz : ∀ C : ℕ, 0 ≤ 4 * a * C / ((Cl : ℝ) + Ch) := fun C ↦
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha) (Nat.cast_nonneg _)) hJ
  unfold rawR
  exact div_le_div_of_nonneg_right (add_le_add (term_mono hgl (hu Cl) (hz Cl) hW hWW)
    (term_mono hgh (hu Ch) (hz Ch) hW hWW)) (by norm_num)

/-- One accepted piece. -/
private lemma piece_sound {P : Params} (ha : 0 ≤ P.a) (hb : 0 ≤ P.bL) (hlam : 0 ≤ P.lam)
    {Cl Ch : ℕ} (hCl : 1 ≤ Cl) {gl gh : ℚ} (hgl : 0 ≤ gl) (hgh : 0 ≤ gh) {lo hi : ℚ}
    (hlo : 0 ≤ lo) (h : pieceOk P Cl Ch gl gh lo hi = true) {W : ℝ}
    (hW : W ∈ Icc (lo : ℝ) hi) :
    rawR P.a P.bL Cl Ch gl gh W - P.lam * (W - 1) < P.K := by
  have h' : rawq P Cl Ch gl gh hi - P.lam * (lo - 1) < P.K := by
    simpa only [pieceOk, decide_eq_true_eq] using h
  have h'' : ((rawq P Cl Ch gl gh hi - P.lam * (lo - 1) : ℚ) : ℝ) < (P.K : ℝ) := by
    exact_mod_cast h'
  rw [Rat.cast_sub, Rat.cast_mul, Rat.cast_sub, Rat.cast_one, rawq_cast] at h''
  have hm := rawR_mono (a := P.a) (bL := P.bL) (by exact_mod_cast ha) (by exact_mod_cast hb)
    (Ch := Ch) hCl
    (gl := gl) (gh := gh) (by exact_mod_cast hgl) (by exact_mod_cast hgh)
    (le_trans (by exact_mod_cast hlo) hW.1) hW.2
  have : (P.lam : ℝ) * (lo - 1) ≤ P.lam * (W - 1) :=
    mul_le_mul_of_nonneg_left (by linarith [hW.1]) (by exact_mod_cast hlam)
  linarith

theorem subdivOk_sound {P : Params} (ha : 0 ≤ P.a) (hb : 0 ≤ P.bL) (hlam : 0 ≤ P.lam)
    {Cl Ch : ℕ} (hCl : 1 ≤ Cl) {gl gh : ℚ} (hgl : 0 ≤ gl) (hgh : 0 ≤ gh) {n : ℕ} {lo hi : ℚ}
    (hlo : 0 ≤ lo) (h : subdivOk P Cl Ch gl gh n lo hi = true) {W : ℝ}
    (hW : W ∈ Icc (lo : ℝ) hi) :
    rawR P.a P.bL Cl Ch gl gh W - P.lam * (W - 1) < P.K := by
  induction n generalizing lo hi with
  | zero => exact piece_sound ha hb hlam hCl hgl hgh hlo h hW
  | succ n ih =>
    rw [subdivOk, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · exact piece_sound ha hb hlam hCl hgl hgh hlo h hW
    · have hlohi : (lo : ℝ) ≤ hi := hW.1.trans hW.2
      have hlohi' : lo ≤ hi := by exact_mod_cast hlohi
      rcases le_total W (((lo + hi) / 2 : ℚ) : ℝ) with hm | hm
      · exact ih hlo h1 ⟨hW.1, hm⟩
      · exact ih (by linarith) h2 ⟨hm, hW.2⟩

/-- `gq` is the rational version of `gOVNS`. -/
theorem gq_cast (C : ℕ) : ((gq C : ℚ) : ℝ) = gOVNS C := by
  unfold gq gOVNS gTable
  split_ifs
  · rcases hf : gTableN.find? (fun e => e.1 == C) with _ | e
    · simp only [hf, M₀]
      norm_num
    · simp only [hf]
      push_cast
      rfl
  · norm_num
  · norm_num

/-- Strictly increasing keys, as a `Bool`. -/
private def sortedB : List (ℕ × ℕ) → Bool
  | e :: f :: l => decide (e.1 < f.1) && sortedB (f :: l)
  | _ => true

private lemma sortedB_tail {e : ℕ × ℕ} {l : List (ℕ × ℕ)} (h : sortedB (e :: l) = true) :
    sortedB l = true := by
  rcases l with _ | ⟨f, l⟩
  · rfl
  · simp only [sortedB, Bool.and_eq_true] at h
    exact h.2

private lemma sortedB_head {e : ℕ × ℕ} {l : List (ℕ × ℕ)} (h : sortedB (e :: l) = true) :
    ∀ f ∈ l, e.1 < f.1 := by
  induction l generalizing e with
  | nil => simp
  | cons g l ih =>
    simp only [sortedB, Bool.and_eq_true, decide_eq_true_eq] at h
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact h.1
    · exact h.1.trans (ih h.2 f hf)

private lemma find_self {l : List (ℕ × ℕ)} (hs : sortedB l = true) {e : ℕ × ℕ} (he : e ∈ l) :
    l.find? (fun x => x.1 == e.1) = some e := by
  induction l with
  | nil => simp at he
  | cons a t ih =>
    rcases List.mem_cons.mp he with rfl | he'
    · simp
    · have hne : a.1 ≠ e.1 := (sortedB_head hs e he').ne
      rw [List.find?_cons_of_neg (by simpa using hne)]
      exact ih (sortedB_tail hs) he'

private lemma gTableN_sorted : sortedB gTableN = true := by decide +kernel

private lemma gTableN_lt : gTableN.all (fun e => decide (e.1 < 1024)) = true := by decide +kernel

/-- A table entry gives the price. -/
theorem gTable_eq_of_mem {e : ℕ × ℕ} (he : e ∈ gTableN) : gOVNS e.1 = (e.2 : ℝ) / 1000000000 := by
  have hlt : e.1 < 1024 := by
    simpa only [decide_eq_true_eq] using List.all_eq_true.mp gTableN_lt e he
  unfold gOVNS gTable
  simp only [hlt, ↓reduceIte, find_self gTableN_sorted he]

/-- The excluded values `4^a(8b+7)`, as a `Bool` with fuel. -/
private def exc : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, C => decide (C % 8 = 7) || (decide (C % 4 = 0) && decide (C ≠ 0) && exc f (C / 4))

/-- Merge check: every `D ∈ [C, C + n)` is excluded or a key of `l`. -/
private def cov : ℕ → ℕ → List (ℕ × ℕ) → Bool
  | _, 0, _ => true
  | C, n + 1, [] => exc 6 C && cov (C + 1) n []
  | C, n + 1, e :: l => if e.1 = C then cov (C + 1) n l else exc 6 C && cov (C + 1) n (e :: l)

private lemma cov_sound {n : ℕ} : ∀ {C : ℕ} {l : List (ℕ × ℕ)}, cov C n l = true →
    ∀ D, C ≤ D → D < C + n → exc 6 D = true ∨ ∃ e ∈ l, e.1 = D := by
  induction n with
  | zero => intro C l _ D h1 h2; omega
  | succ n ih =>
    intro C l h D h1 h2
    rcases l with _ | ⟨e, l⟩
    · simp only [cov, Bool.and_eq_true] at h
      rcases (show D = C ∨ C + 1 ≤ D by omega) with rfl | hD
      · exact Or.inl h.1
      · exact ih h.2 D hD (by omega)
    · simp only [cov] at h
      split_ifs at h with he
      · rcases (show D = C ∨ C + 1 ≤ D by omega) with rfl | hD
        · exact Or.inr ⟨e, List.mem_cons_self, he⟩
        · rcases ih h D hD (by omega) with h' | ⟨f, hf, hfD⟩
          · exact Or.inl h'
          · exact Or.inr ⟨f, List.mem_cons_of_mem _ hf, hfD⟩
      · rw [Bool.and_eq_true] at h
        rcases (show D = C ∨ C + 1 ≤ D by omega) with rfl | hD
        · exact Or.inl h.1
        · exact ih h.2 D hD (by omega)

private lemma gTableN_cov : cov 0 1024 gTableN = true := by decide +kernel

private lemma sq_mod8 (x : ℕ) : x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
  have h := Nat.mod_lt x (show 8 > 0 by norm_num)
  rw [Nat.pow_mod]
  interval_cases x % 8 <;> simp

private lemma half_sq (x : ℕ) : ∃ k, x = 2 * k ∧ x ^ 2 = 4 * k ^ 2 ∨
    x = 2 * k + 1 ∧ x ^ 2 = 4 * (k ^ 2 + k) + 1 := by
  rcases Nat.even_or_odd' x with ⟨k, rfl | rfl⟩
  · exact ⟨k, Or.inl ⟨rfl, by ring⟩⟩
  · exact ⟨k, Or.inr ⟨rfl, by ring⟩⟩

/-- Excluded values are not sums of three squares. -/
private lemma exc_not {f : ℕ} : ∀ {x y w : ℕ}, exc f (x ^ 2 + y ^ 2 + w ^ 2) = false := by
  induction f with
  | zero => intro x y w; rfl
  | succ f ih =>
    intro x y w
    simp only [exc, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    refine ⟨by rcases sq_mod8 x with h | h | h <;> rcases sq_mod8 y with h' | h' | h' <;>
      rcases sq_mod8 w with h'' | h'' | h'' <;> omega, ?_⟩
    obtain ⟨a, ha⟩ := half_sq x
    obtain ⟨b, hb⟩ := half_sq y
    obtain ⟨c, hc⟩ := half_sq w
    rcases ha with ⟨-, ha⟩ | ⟨-, ha⟩ <;> rcases hb with ⟨-, hb⟩ | ⟨-, hb⟩ <;>
      rcases hc with ⟨-, hc⟩ | ⟨-, hc⟩ <;> try (left; left; omega)
    right
    have : (x ^ 2 + y ^ 2 + w ^ 2) / 4 = a ^ 2 + b ^ 2 + c ^ 2 := by omega
    rw [this]
    exact ih

/-- Every `C < 1024` representable by three squares is a table key. -/
theorem mem_keys_of_rep3 {C : ℕ} (hC : C < 1024) (h : rep3 C = true) :
    ∃ e ∈ gTableN, e.1 = C := by
  rcases cov_sound gTableN_cov C (Nat.zero_le _) (by omega) with hx | hk
  · exfalso
    simp only [rep3, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨x, -, y, -, hxy, hs⟩ := h
    have hC : C = x ^ 2 + y ^ 2 + Nat.sqrt (C - x ^ 2 - y ^ 2) ^ 2 := by omega
    rw [hC, exc_not] at hx
    exact Bool.false_ne_true hx
  · exact hk

/-- `nsq` of a mode is representable. -/
theorem rep3_nsq {z : Mode} (hz : nsq z < 1024) : rep3 (nsq z) = true := by
  have hn : nsq z = (z 0).natAbs ^ 2 + (z 1).natAbs ^ 2 + (z 2).natAbs ^ 2 := by
    simp [nsq, Fin.sum_univ_three]
  rw [hn] at hz ⊢
  set x := (z 0).natAbs
  set y := (z 1).natAbs
  set w := (z 2).natAbs
  have hx : x < 32 := by nlinarith
  have hy : y < 32 := by nlinarith
  simp only [rep3, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨x, hx, y, hy, by omega, ?_⟩
  rw [show x ^ 2 + y ^ 2 + w ^ 2 - x ^ 2 - y ^ 2 = w ^ 2 by omega, Nat.sqrt_eq']

/-- Soundness of `rangeOk`: the bound on every table pair in the range, in the pair's
`W`-interval, with the real prices. -/
theorem rangeOk_sound {P : Params} (ha : 0 ≤ P.a) (hb : 0 ≤ P.bL) (hlam : 0 ≤ P.lam)
    (_hthi : 0 < P.thi) (_htlo : 0 ≤ P.tlo) (hwlo : 0 ≤ P.wlo) {lo hi : ℕ}
    (h : rangeOk P lo hi = true) {Cl Ch : ℕ} (hlo : lo ≤ Cl) (hhi : Cl < hi) (h1 : 1 ≤ Cl)
    (hle : Cl ≤ Ch) (hJ : Cl + Ch < P.Jmax) (hmod : (Ch - Cl) % 4 = 0)
    (hl : ∃ e ∈ gTableN, e.1 = Cl) (hh : ∃ e ∈ gTableN, e.1 = Ch) {W : ℝ}
    (hW : W ∈ Icc (wLo P Cl Ch : ℝ) (wHi P Cl Ch : ℝ)) :
    rawR P.a P.bL Cl Ch (gOVNS Cl) (gOVNS Ch) W - P.lam * (W - 1) < P.K := by
  obtain ⟨el, hel, rfl⟩ := hl
  obtain ⟨eh, heh, rfl⟩ := hh
  have h1' := List.all_eq_true.mp h el hel
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h1'
  rcases h1' with ((h' | h') | h') | h'
  · omega
  · omega
  · omega
  have h2' := List.all_eq_true.mp h' eh heh
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h2'
  rcases h2' with ((h'' | h'') | h'') | h''
  · omega
  · omega
  · omega
  unfold pairOk at h''
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h''
  rcases h'' with hc | hs
  · have hle' : (wLo P el.1 eh.1 : ℝ) ≤ wHi P el.1 eh.1 := hW.1.trans hW.2
    have : wLo P el.1 eh.1 ≤ wHi P el.1 eh.1 := by exact_mod_cast hle'
    exact absurd hc (not_lt.mpr this)
  · have key := subdivOk_sound ha hb hlam h1 (gl := (el.2 : ℚ) / 1000000000)
      (gh := (eh.2 : ℚ) / 1000000000) (by positivity) (by positivity)
      (le_max_of_le_left hwlo) hs hW
    rw [gTable_eq_of_mem hel, gTable_eq_of_mem heh]
    push_cast at key
    exact key

/-- Real version of the row-price check `subdivOkR`. -/
noncomputable def rawRr (a L H r W : ℝ) : ℝ :=
  (L * W / (W + 4 * a * r) + H * W / (W + 4 * a * (1 - r))) / 2

theorem subdivOkR_sound {a L H r lam K : ℚ} (ha : 0 ≤ a) (hL : 0 ≤ L) (hH : 0 ≤ H) (hr : 0 ≤ r)
    (hr1 : r ≤ 1) (hlam : 0 ≤ lam) {n : ℕ} {lo hi : ℚ} (hlo : 0 < lo)
    (h : subdivOkR a L H r lam K n lo hi = true) {W : ℝ} (hW : W ∈ Icc (lo : ℝ) hi) :
    rawRr a L H r W - lam * (W - 1) < K := by
  have hmono : ∀ {V V' : ℝ}, 0 ≤ V → V ≤ V' → rawRr a L H r V ≤ rawRr a L H r V' := by
    intro V V' hV hVV
    have hz1 : (0 : ℝ) ≤ 4 * a * r := by
      have : (0 : ℝ) ≤ a := by exact_mod_cast ha
      have : (0 : ℝ) ≤ r := by exact_mod_cast hr
      positivity
    have hz2 : (0 : ℝ) ≤ 4 * a * (1 - r) := by
      have : (0 : ℝ) ≤ a := by exact_mod_cast ha
      have : (r : ℝ) ≤ 1 := by exact_mod_cast hr1
      exact mul_nonneg (by positivity) (by linarith)
    have t1 := term_mono (u := 1) (g := (L : ℝ)) (by exact_mod_cast hL) le_rfl hz1 hV hVV
    have t2 := term_mono (u := 1) (g := (H : ℝ)) (by exact_mod_cast hH) le_rfl hz2 hV hVV
    simp only [one_mul] at t1 t2
    unfold rawRr
    exact div_le_div_of_nonneg_right (add_le_add t1 t2) (by norm_num)
  have piece : ∀ {lo hi : ℚ}, 0 < lo → pieceOkR a L H r lam K lo hi = true →
      W ∈ Icc (lo : ℝ) hi → rawRr a L H r W - lam * (W - 1) < K := by
    intro lo hi hlo h hW
    have h' : rawr a L H r hi - lam * (lo - 1) < K := by
      simpa only [pieceOkR, decide_eq_true_eq] using h
    have h'' : ((rawr a L H r hi - lam * (lo - 1) : ℚ) : ℝ) < (K : ℝ) := by exact_mod_cast h'
    rw [Rat.cast_sub, Rat.cast_mul, Rat.cast_sub, Rat.cast_one] at h''
    have hc : ((rawr a L H r hi : ℚ) : ℝ) = rawRr a L H r hi := by
      unfold rawr rawRr
      push_cast
      ring
    rw [hc] at h''
    have hm := hmono (le_trans (by exact_mod_cast hlo.le) hW.1) hW.2
    have : (lam : ℝ) * (lo - 1) ≤ lam * (W - 1) :=
      mul_le_mul_of_nonneg_left (by linarith [hW.1]) (by exact_mod_cast hlam)
    linarith
  induction n generalizing lo hi with
  | zero => exact piece hlo h hW
  | succ n ih =>
    rw [subdivOkR, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · exact piece hlo h hW
    · have hlohi : (lo : ℝ) ≤ hi := hW.1.trans hW.2
      have hlohi' : lo ≤ hi := by exact_mod_cast hlohi
      rcases le_total W (((lo + hi) / 2 : ℚ) : ℝ) with hm | hm
      · exact ih hlo h1 ⟨hW.1, hm⟩
      · exact ih (by linarith) h2 ⟨hm, hW.2⟩

end Mom

end Forced

end OVNS
