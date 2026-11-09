import OddViscousNS.Closed.Cond.Defs
import OddViscousNS.Closed.Triad

/-!
# The LLH class: kinetic cancellation and the first-shell amplitude bound

(iii)–(iv) of §3 of `OddViscousNS_data/reports/u785_unforced_graph.md`:
the LLH class of the weighted triad sum equals `(h₂ − 1)⟨B(w₁,w₁), P₂w⟩` (`w₁ = P₁w`), and
`‖P₂B(w₁,w₁)‖₀² ≤ ∑_{i<j} x_i x_j ≤ x²/3`, whence `|LLH| ≤ c₁ x √Y₂`.
Also the split `cubic = triadLLH + triadRest` (absolute convergence from `summable_triad`).
-/

open scoped ENNReal ComplexConjugate

namespace OVNS

/-! ### Algebraic helpers (re-derived; those of `Triad.lean` are private) -/

private lemma det3_eq' (a b c : V3) : det3 a b c = (a 1 * b 2 - a 2 * b 1) * c 0 +
    (a 2 * b 0 - a 0 * b 2) * c 1 + (a 0 * b 1 - a 1 * b 0) * c 2 := by
  simp [det3, dotV, cross, Fin.sum_univ_three]

private lemma det3_cyc' (a b c : V3) : det3 b c a = det3 a b c := by
  rw [det3_eq', det3_eq']; ring

private lemma det3_swap12' (a b c : V3) : det3 b a c = -det3 a b c := by
  rw [det3_eq', det3_eq']; ring

private lemma det3_swap23' (a b c : V3) : det3 a c b = -det3 a b c := by
  rw [det3_eq', det3_eq']; ring

private lemma det3_curlS' (p : Mode) (a b c : V3) :
    det3 (curlS p a) b c = Complex.I * (dotM b p * dotV a c - dotV a b * dotM c p) := by
  have h0 : curlS p a 0 = Complex.I * ((p 1 : ℂ) * a 2 - (p 2 : ℂ) * a 1) := by
    simp [curlS, cross, modeVec]
  have h1 : curlS p a 1 = Complex.I * ((p 2 : ℂ) * a 0 - (p 0 : ℂ) * a 2) := by
    simp [curlS, cross, modeVec]
  have h2 : curlS p a 2 = Complex.I * ((p 0 : ℂ) * a 1 - (p 1 : ℂ) * a 0) := by
    simp [curlS, cross, modeVec]
  rw [det3_eq', h0, h1, h2]
  simp only [dotM, dotV, Fin.sum_univ_three]
  ring

private lemma dotV_comm' (a b : V3) : dotV a b = dotV b a := by
  simp only [dotV, mul_comm]

private lemma dotM_add_sub' (c : V3) (k p : Mode) : dotM c p + dotM c (k - p) = dotM c k := by
  simp only [dotM, ← Finset.sum_add_distrib, Pi.sub_apply, Int.cast_sub]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

private lemma dotM_conjV'' (v : V3) (k : Mode) : dotM (conjV v) k = conj (dotM v k) := by
  simp [dotM, conjV, map_sum]

private lemma nsq_neg' (j : Mode) : nsq (-j) = nsq j := by
  simp [nsq]

private lemma lamVals_pos' (i : ℕ) : 0 < lamVals.getD i 100000 := by
  rcases lt_or_ge i 24 with h | h
  · interval_cases i <;> decide
  · rw [List.getD_eq_default]; · norm_num
    simpa [lamVals] using h

private lemma lamW_pos' (j : ℕ) : 0 < lamW j := by
  unfold lamW
  split
  · have := lamVals_pos' ‹ℕ›
    positivity
  · norm_num

private lemma Wk_nonneg' (k p : Mode) : 0 ≤ Wk lamW k p := by
  have h1 := lamW_pos' (nsq p)
  have h2 := lamW_pos' (nsq (k - p))
  have h3 := lamW_pos' (nsq k)
  unfold Wk; positivity

private lemma Wk_le' (k p : Mode) : Wk lamW k p ≤ 3 := by
  have h1 := lamW_pos' (nsq p)
  have h2 := lamW_pos' (nsq (k - p))
  have h3 := lamW_pos' (nsq k)
  unfold Wk
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-! ### Goal 1: the split -/

/-- The fixed-output weighted triad summand. -/
private noncomputable def Fw (u : Field) (kp : Mode × Mode) : ℝ :=
  Wk lamW kp.1 kp.2 * (triT kp.2 (kp.1 - kp.2) (-kp.1) (u kp.2) (u (kp.1 - kp.2))
    (conjV (u kp.1))).re

private lemma summable_Fw {u : Field} (hu : Adm 2 u) : Summable (Fw u) := by
  refine Summable.of_norm_bounded ((summable_triad hu).mul_left 3) fun kp => ?_
  rw [Fw, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Wk_nonneg' _ _)]
  exact mul_le_mul (Wk_le' _ _) (Complex.abs_re_le_norm _) (abs_nonneg _) (by norm_num)

theorem cubic_eq_LLH_add_rest {w : Field} (hw : Adm 2 w) : cubic w = triadLLH w + triadRest w := by
  have hF := summable_Fw hw
  have h1 : Summable fun kp : Mode × Mode =>
      if isLLH kp.2 (kp.1 - kp.2) (-kp.1) then Fw w kp else 0 :=
    hF.indicator {kp | isLLH kp.2 (kp.1 - kp.2) (-kp.1)} |>.congr fun kp => by
      simp [Set.indicator_apply]
  have h2 : Summable fun kp : Mode × Mode =>
      if isLLH kp.2 (kp.1 - kp.2) (-kp.1) then 0 else Fw w kp :=
    (hF.sub h1).congr fun kp => by split_ifs <;> simp
  have key : ∑' k, ∑' p, Wk lamW k p *
      (triT p (k - p) (-k) (w p) (w (k - p)) (conjV (w k))).re = ∑' kp, Fw w kp := by
    rw [show (Fw w) = fun kp => (fun k p => Fw w (k, p)) kp.1 kp.2 from rfl, hF.tsum_prod]
    rfl
  rw [cubic_eq_triad hw, key, triadLLH, triadRest, ← mul_add]
  change _ = 1 / 6 * ((∑' kp : Mode × Mode,
    if isLLH kp.2 (kp.1 - kp.2) (-kp.1) then Fw w kp else 0) + ∑' kp : Mode × Mode,
    if isLLH kp.2 (kp.1 - kp.2) (-kp.1) then 0 else Fw w kp)
  rw [← h1.tsum_add h2]
  congr 1
  exact tsum_congr fun kp => by split_ifs <;> simp

/-! ### Finite mode sets -/

/-- `|k|²` with explicit coordinates (decidable form). -/
private def nsq3 (k : Mode) : ℕ := (k 0).natAbs ^ 2 + (k 1).natAbs ^ 2 + (k 2).natAbs ^ 2

private lemma nsq_eq3 (k : Mode) : nsq k = nsq3 k := by simp [nsq, nsq3, Fin.sum_univ_three]

/-- The first shell `{±e_i}`. -/
private def S1 : Finset Mode :=
  {![1, 0, 0], ![-1, 0, 0], ![0, 1, 0], ![0, -1, 0], ![0, 0, 1], ![0, 0, -1]}

/-- The twelve unordered first-shell pairs with sum on the second shell. -/
private def P12 : Finset (Mode × Mode) :=
  {(![1, 0, 0], ![0, 1, 0]), (![1, 0, 0], ![0, -1, 0]), (![-1, 0, 0], ![0, 1, 0]),
   (![-1, 0, 0], ![0, -1, 0]), (![1, 0, 0], ![0, 0, 1]), (![1, 0, 0], ![0, 0, -1]),
   (![-1, 0, 0], ![0, 0, 1]), (![-1, 0, 0], ![0, 0, -1]), (![0, 1, 0], ![0, 0, 1]),
   (![0, 1, 0], ![0, 0, -1]), (![0, -1, 0], ![0, 0, 1]), (![0, -1, 0], ![0, 0, -1])}

private def boxF (r : ℤ) : Finset Mode := Fintype.piFinset fun _ => Finset.Icc (-r) r

private lemma coord_le_of_nsq {x : Mode} {n : ℕ} (hx : nsq x ≤ n) (hn : n ≤ 3) (i : Fin 3) :
    -1 ≤ x i ∧ x i ≤ 1 := by
  rw [nsq_eq3] at hx
  have h : (x i).natAbs ^ 2 ≤ 3 := by
    fin_cases i <;> simp only [nsq3] at hx <;> simp <;> omega
  have h' : (x i).natAbs ≤ 1 := by
    by_contra hc
    rw [not_le] at hc
    have : 2 ^ 2 ≤ (x i).natAbs ^ 2 := Nat.pow_le_pow_left hc 2
    omega
  omega

private lemma mem_box1 {x : Mode} {n : ℕ} (hx : nsq x ≤ n) (hn : n ≤ 3) : x ∈ boxF 1 := by
  simp only [boxF, Fintype.mem_piFinset, Finset.mem_Icc]
  exact fun i => coord_le_of_nsq hx hn i

private lemma mem_S1_iff (p : Mode) : p ∈ S1 ↔ nsq p = 1 := by
  constructor
  · intro h
    rw [nsq_eq3]
    revert p
    decide
  · intro h
    have hb := mem_box1 h.le (by norm_num)
    rw [nsq_eq3] at h
    have key : ∀ p ∈ boxF 1, nsq3 p = 1 → p ∈ S1 := by decide
    exact key p hb h

private lemma S1_par : ∀ p ∈ S1, ∀ l ∈ S1,
    nsq3 (p + l) = 1 ∨ nsq3 (p + l) = 2 ∨ l = p ∨ p + l = 0 := by
  decide

private lemma P12_spec : ∀ pr ∈ P12, pr.1 ∈ S1 ∧ pr.2 ∈ S1 ∧ pr.1 ≠ pr.2 ∧
    nsq3 (pr.1 + pr.2) = 2 ∧ ∀ p ∈ S1, pr.1 + pr.2 - p ∈ S1 → p = pr.1 ∨ p = pr.2 := by
  decide

private lemma P12_surj : ∀ k ∈ boxF 1, nsq3 k = 2 → ∃ pr ∈ P12, pr.1 + pr.2 = k := by
  decide

private lemma P12_inj : ∀ a ∈ P12, ∀ b ∈ P12, a.1 + a.2 = b.1 + b.2 → a = b := by
  decide

/-! ### The triple-sum framework, restricted to the LLH class -/

/-- `Re det(S_p u_p, u_l, u_q)`. -/
private noncomputable def Dl (u : Field) (p l q : Mode) : ℝ :=
  (det3 (curlS p (u p)) (u l) (u q)).re

/-- `h_q Re det(S_p u_p, u_l, u_q)`. -/
private noncomputable def Pl (u : Field) (p l q : Mode) : ℝ := hm q * Dl u p l q

/-- `Re T(p,l,q)(u_p,u_l,u_q)`. -/
private noncomputable def Tl (u : Field) (p l q : Mode) : ℝ := (triT p l q (u p) (u l) (u q)).re

/-- The cyclic weight of the third slot. -/
private noncomputable def Wl (p l q : Mode) : ℝ :=
  3 * lamW (nsq q) / (lamW (nsq p) + lamW (nsq l) + lamW (nsq q))

private lemma Tl_eq (u : Field) (p l q : Mode) : Tl u p l q =
    Pl u p l q + Pl u p q l + Pl u l q p + Pl u l p q + Pl u q p l + Pl u q l p := by
  have e1 := det3_swap23' (curlS p (u p)) (u l) (u q)
  have e2 := det3_cyc' (u p) (curlS l (u l)) (u q)
  have e3 := det3_swap12' (u p) (curlS l (u l)) (u q)
  have e4 := det3_cyc' (curlS q (u q)) (u p) (u l)
  have e5 : det3 (curlS q (u q)) (u l) (u p) = -det3 (u p) (u l) (curlS q (u q)) := by
    rw [det3_swap23', e4]
  simp only [Tl, triT, Pl, Dl, e1, e2, e3, ← e4, e5, Complex.add_re, Complex.re_ofReal_mul,
    Complex.neg_re]
  ring

private lemma Wl_cyc (p l q : Mode) : Wl p l q + Wl l q p + Wl q p l = 3 := by
  have h1 := lamW_pos' (nsq p)
  have h2 := lamW_pos' (nsq l)
  have h3 := lamW_pos' (nsq q)
  simp only [Wl]
  field_simp
  ring

private lemma isLLH_cyc (p l q : Mode) : isLLH l q p ↔ isLLH p l q := by
  unfold isLLH; tauto

private lemma isLLH_23 (p l q : Mode) : isLLH p q l ↔ isLLH p l q := by
  unfold isLLH; tauto

/-- The sum over ordered triples `p + l + q = 0`, parametrized by `(k, p) ↦ (p, k - p, -k)`. -/
private noncomputable def tL (Φ : Mode → Mode → Mode → ℝ) : ℝ :=
  ∑' kp : Mode × Mode, Φ kp.2 (kp.1 - kp.2) (-kp.1)

private lemma tL_perm (σ : Mode × Mode ≃ Mode × Mode) {Φ Ψ : Mode → Mode → Mode → ℝ}
    (h : ∀ kp : Mode × Mode, Ψ kp.2 (kp.1 - kp.2) (-kp.1) =
      Φ (σ kp).2 ((σ kp).1 - (σ kp).2) (-(σ kp).1)) : tL Ψ = tL Φ := by
  have hf : (fun kp : Mode × Mode => Ψ kp.2 (kp.1 - kp.2) (-kp.1)) =
      (fun kp : Mode × Mode => Φ kp.2 (kp.1 - kp.2) (-kp.1)) ∘ σ := funext h
  unfold tL; rw [hf]; exact σ.tsum_eq (fun kp : Mode × Mode => Φ kp.2 (kp.1 - kp.2) (-kp.1))

private def f12 : Mode × Mode ≃ Mode × Mode where
  toFun kp := (kp.1, kp.1 - kp.2)
  invFun kp := (kp.1, kp.1 - kp.2)
  left_inv kp := by ext <;> simp
  right_inv kp := by ext <;> simp

private def f23 : Mode × Mode ≃ Mode × Mode where
  toFun kp := (kp.2 - kp.1, kp.2)
  invFun kp := (kp.2 - kp.1, kp.2)
  left_inv kp := by ext <;> simp
  right_inv kp := by ext <;> simp

private def fCyc : Mode × Mode ≃ Mode × Mode where
  toFun kp := (-kp.2, kp.1 - kp.2)
  invFun kp := (kp.2 - kp.1, -kp.1)
  left_inv kp := by ext <;> simp
  right_inv kp := by ext <;> simp

private def fCyc2 : Mode × Mode ≃ Mode × Mode where
  toFun kp := (kp.2 - kp.1, -kp.1)
  invFun kp := (-kp.2, kp.1 - kp.2)
  left_inv kp := by ext <;> simp
  right_inv kp := by ext <;> simp

private def f13 : Mode × Mode ≃ Mode × Mode where
  toFun kp := (-kp.2, -kp.1)
  invFun kp := (-kp.2, -kp.1)
  left_inv kp := by ext <;> simp
  right_inv kp := by ext <;> simp

private lemma tL_12 (Φ : Mode → Mode → Mode → ℝ) : tL (fun p l q => Φ l p q) = tL Φ :=
  tL_perm f12 fun kp => by simp [f12]

private lemma tL_23 (Φ : Mode → Mode → Mode → ℝ) : tL (fun p l q => Φ p q l) = tL Φ :=
  tL_perm f23 fun kp => by simp [f23]

private lemma tL_cyc (Φ : Mode → Mode → Mode → ℝ) : tL (fun p l q => Φ l q p) = tL Φ :=
  tL_perm fCyc fun kp => by
    simp only [fCyc, Equiv.coe_fn_mk, neg_neg,
      show ∀ a b : Mode, -b - (a - b) = -a from fun a b => by abel]

private lemma tL_cyc2 (Φ : Mode → Mode → Mode → ℝ) : tL (fun p l q => Φ q p l) = tL Φ :=
  tL_perm fCyc2 fun kp => by simp [fCyc2]

private lemma tL_13 (Φ : Mode → Mode → Mode → ℝ) : tL (fun p l q => Φ q l p) = tL Φ :=
  tL_perm f13 fun kp => by
    simp only [f13, Equiv.coe_fn_mk, neg_neg,
      show ∀ a b : Mode, -b - -a = a - b from fun a b => by abel]

attribute [local irreducible] boxF in
private lemma boxF_mem_iff {r : ℤ} {x : Mode} : x ∈ boxF r ↔ ∀ i, -r ≤ x i ∧ x i ≤ r := by
  unfold boxF; simp only [Fintype.mem_piFinset, Finset.mem_Icc]

attribute [local irreducible] boxF

private lemma llh_mem {kp : Mode × Mode} (h : isLLH kp.2 (kp.1 - kp.2) (-kp.1)) :
    kp ∈ boxF 2 ×ˢ boxF 2 := by
  simp only [Finset.mem_product, boxF_mem_iff]
  have c1 : ∀ x : Mode, nsq x = 1 → ∀ i, -1 ≤ x i ∧ x i ≤ 1 :=
    fun x hx i => coord_le_of_nsq hx.le (by norm_num) i
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have a := c1 _ h1
    have b := c1 _ h2
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have := a i; have := b i; simp only [Pi.sub_apply] at *; omega
    · have := a i; omega
  · have a := c1 _ h1
    have b := c1 _ h2
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have := b i; simp only [Pi.neg_apply] at *; omega
    · have := a i; omega
  · have a := c1 _ h1
    have b := c1 _ h2
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have := b i; simp only [Pi.neg_apply] at *; omega
    · have := a i; have := b i; simp only [Pi.sub_apply, Pi.neg_apply] at *; omega

private lemma tLm_of_llh {Φ : Mode → Mode → Mode → ℝ} (h : ∀ p l q, ¬ isLLH p l q → Φ p l q = 0) :
    Summable fun kp : Mode × Mode => Φ kp.2 (kp.1 - kp.2) (-kp.1) :=
  summable_of_ne_finset_zero (s := boxF 2 ×ˢ boxF 2) fun kp hkp => by
    by_cases hl : isLLH kp.2 (kp.1 - kp.2) (-kp.1)
    · exact absurd (llh_mem hl) hkp
    · exact h _ _ _ hl

/-- Step A: `triadLLH` as an LLH-restricted triple sum. -/
private lemma triadLLH_eq_tL {w : Field} (hw : Adm 2 w) : triadLLH w =
    1 / 6 * tL (fun p l q => if isLLH p l q then Wl p l q * Tl w p l q else 0) := by
  unfold triadLLH tL
  refine congrArg _ (tsum_congr fun kp => ?_)
  rw [← hw.real kp.1]
  simp only [Wk, Wl, Tl, nsq_neg']

/-- Step C: the cyclic weights drop out. -/
private lemma tL_W (w : Field) :
    tL (fun p l q => if isLLH p l q then Wl p l q * Tl w p l q else 0) =
      tL (fun p l q => if isLLH p l q then Tl w p l q else 0) := by
  set Φ : Mode → Mode → Mode → ℝ := fun p l q => if isLLH p l q then Wl p l q * Tl w p l q
    else 0 with hΦ
  have h0 := tLm_of_llh (Φ := Φ) fun p l q h => by simp [hΦ, h]
  have s1 := tLm_of_llh (Φ := fun p l q => Φ l q p) fun p l q h => by
    simp [hΦ, (isLLH_cyc p l q).1.mt h]
  have s2 := tLm_of_llh (Φ := fun p l q => Φ q p l) fun p l q h => by
    have h' : ¬ isLLH q p l := fun h' => h ((isLLH_cyc p l q).1 ((isLLH_cyc l q p).1 h'))
    simp [hΦ, h']
  have e1 := tL_cyc Φ
  have e2 := tL_cyc2 Φ
  unfold tL at *
  have h := ((h0.hasSum.add s1.hasSum).add s2.hasSum).tsum_eq
  rw [e1, e2] at h
  have h' : ∑' kp : Mode × Mode, (Φ kp.2 (kp.1 - kp.2) (-kp.1) +
      Φ (kp.1 - kp.2) (-kp.1) kp.2 + Φ (-kp.1) kp.2 (kp.1 - kp.2)) =
      ∑' kp : Mode × Mode, 3 * (if isLLH kp.2 (kp.1 - kp.2) (-kp.1) then
        Tl w kp.2 (kp.1 - kp.2) (-kp.1) else 0) := by
    refine tsum_congr fun kp => ?_
    have c1 := isLLH_cyc kp.2 (kp.1 - kp.2) (-kp.1)
    have c2 := isLLH_cyc (-kp.1) kp.2 (kp.1 - kp.2)
    have t1 : Tl w (kp.1 - kp.2) (-kp.1) kp.2 = Tl w kp.2 (kp.1 - kp.2) (-kp.1) := by
      rw [Tl_eq, Tl_eq]; ring
    have t2 : Tl w (-kp.1) kp.2 (kp.1 - kp.2) = Tl w kp.2 (kp.1 - kp.2) (-kp.1) := by
      rw [Tl_eq, Tl_eq]; ring
    simp only [hΦ, c1, ← c2, t1, t2]
    split_ifs
    · rw [← Wl_cyc kp.2 (kp.1 - kp.2) (-kp.1)]; ring
    · ring
  rw [h', tsum_mul_left] at h
  linarith

/-- Step D: the six permutations of the curl form. -/
private lemma tL_T (w : Field) :
    tL (fun p l q => if isLLH p l q then Tl w p l q else 0) =
      6 * tL (fun p l q => if isLLH p l q then Pl w p l q else 0) := by
  set Φ : Mode → Mode → Mode → ℝ := fun p l q => if isLLH p l q then Pl w p l q else 0
    with hΦ
  have inv : ∀ p l q, (isLLH l q p ↔ isLLH p l q) ∧ (isLLH p q l ↔ isLLH p l q) ∧
      (isLLH l p q ↔ isLLH p l q) ∧ (isLLH q p l ↔ isLLH p l q) ∧
      (isLLH q l p ↔ isLLH p l q) := fun p l q => by unfold isLLH; tauto
  have hP := tLm_of_llh (Φ := Φ) fun p l q h => by simp [hΦ, h]
  have s1 := tLm_of_llh (Φ := fun p l q => Φ p q l) fun p l q h => by
    simp [hΦ, (inv p l q).2.1.not.2 h]
  have s2 := tLm_of_llh (Φ := fun p l q => Φ l q p) fun p l q h => by
    simp [hΦ, (inv p l q).1.not.2 h]
  have s3 := tLm_of_llh (Φ := fun p l q => Φ l p q) fun p l q h => by
    simp [hΦ, (inv p l q).2.2.1.not.2 h]
  have s4 := tLm_of_llh (Φ := fun p l q => Φ q p l) fun p l q h => by
    simp [hΦ, (inv p l q).2.2.2.1.not.2 h]
  have s5 := tLm_of_llh (Φ := fun p l q => Φ q l p) fun p l q h => by
    simp [hΦ, (inv p l q).2.2.2.2.not.2 h]
  have e1 := tL_23 Φ
  have e2 := tL_cyc Φ
  have e3 := tL_12 Φ
  have e4 := tL_cyc2 Φ
  have e5 := tL_13 Φ
  unfold tL at *
  have h := (((((hP.hasSum.add s1.hasSum).add s2.hasSum).add s3.hasSum).add s4.hasSum).add
    s5.hasSum).tsum_eq
  rw [e1, e2, e3, e4, e5] at h
  have h' : ∑' kp : Mode × Mode, (if isLLH kp.2 (kp.1 - kp.2) (-kp.1) then
      Tl w kp.2 (kp.1 - kp.2) (-kp.1) else 0) = ∑' kp : Mode × Mode,
      (Φ kp.2 (kp.1 - kp.2) (-kp.1) +
      Φ kp.2 (-kp.1) (kp.1 - kp.2) + Φ (kp.1 - kp.2) (-kp.1) kp.2 +
      Φ (kp.1 - kp.2) kp.2 (-kp.1) + Φ (-kp.1) kp.2 (kp.1 - kp.2) +
      Φ (-kp.1) (kp.1 - kp.2) kp.2) := by
    refine tsum_congr fun kp => ?_
    obtain ⟨i1, i2, i3, i4, i5⟩ := inv kp.2 (kp.1 - kp.2) (-kp.1)
    simp only [hΦ, i1, i2, i3, i4, i5]
    split_ifs
    · rw [Tl_eq]
    · simp
  rw [h', h]
  ring

/-! ### Step E: only the `{1,1,2}` configurations survive -/

/-- The surviving configurations: first two legs on shell 1, third on shell 2. -/
private noncomputable def Ps (u : Field) (p l q : Mode) : ℝ :=
  if nsq p = 1 ∧ nsq l = 1 ∧ nsq q = 2 then (hmet 2 - 1) * Dl u p l q else 0

private lemma Dl_swap (u : Field) (p l q : Mode) : Dl u p q l = -Dl u p l q := by
  unfold Dl; rw [det3_swap23', Complex.neg_re]

private lemma det3_zero3 (a b : V3) : det3 a b 0 = 0 := by simp [det3_eq']

private lemma det3_zero2 (a c : V3) : det3 a 0 c = 0 := by simp [det3_eq']

private lemma curlS_zero (p : Mode) : curlS p 0 = 0 := by
  ext i; fin_cases i <;> simp [curlS, cross]

private lemma det3_zero1 (b c : V3) : det3 0 b c = 0 := by simp [det3_eq']

private lemma dotM_add' (c : V3) (p l : Mode) : dotM c (p + l) = dotM c p + dotM c l := by
  simp only [dotM, ← Finset.sum_add_distrib, Pi.add_apply, Int.cast_add, mul_add]

private lemma dotM_neg (c : V3) (p : Mode) : dotM c (-p) = -dotM c p := by
  simp only [dotM, Pi.neg_apply, Int.cast_neg, mul_neg, Finset.sum_neg_distrib]

private lemma Dl_van {w : Field} (hw : Adm 2 w) {p l q : Mode} (hp : nsq p = 1) (hl : nsq l = 1)
    (hs : p + l + q = 0) (h1 : nsq q ≠ 1) (h2 : nsq q ≠ 2) : Dl w p l q = 0 := by
  have hq : q = -(p + l) := by rw [eq_neg_iff_add_eq_zero, ← hs]; abel
  subst hq
  rw [nsq_neg', nsq_eq3] at h1 h2
  rcases S1_par p ((mem_S1_iff p).2 hp) l ((mem_S1_iff l).2 hl) with h | h | h | h
  · exact absurd h h1
  · exact absurd h h2
  · rw [h]
    have e1 := hw.sol p
    have e2 := hw.sol (-(p + p))
    rw [dotM_neg, dotM_add'] at e2
    have e3 : dotM (w (-(p + p))) p = 0 := by linear_combination (-1 / 2 : ℂ) * e2
    simp only [Dl, det3_curlS', e1, e3]
    simp
  · simp only [Dl, h, neg_zero, hw.mean, det3_zero3, Complex.zero_re]

private lemma Ps_pt {w : Field} (hw : Adm 2 w) {p l q : Mode} (hs : p + l + q = 0) :
    (if isLLH p l q then Pl w p l q else 0) + (if isLLH p q l then Pl w p q l else 0) =
      Ps w p l q + Ps w p q l := by
  have van1 : nsq p = 1 → nsq l = 1 → nsq q ≠ 1 → nsq q ≠ 2 → Dl w p l q = 0 :=
    fun a b c d => Dl_van hw a b hs c d
  have van2 : nsq p = 1 → nsq q = 1 → nsq l ≠ 1 → nsq l ≠ 2 → Dl w p l q = 0 := by
    intro a b c d
    have := Dl_van hw a b (show p + q + l = 0 by rw [← hs]; abel) c d
    rw [Dl_swap] at this; linarith
  simp only [Ps, Pl, Dl_swap w p q l, hm, isLLH]
  by_cases hp : nsq p = 1 <;> by_cases hl : nsq l = 1 <;> by_cases hq : nsq q = 1 <;>
    simp [hp, hl, hq]
  all_goals
    have e := Dl_swap w p l q
    rw [hmet_one]
    split_ifs with h2
    · rw [h2]; ring
    · have : Dl w p l q = 0 := by
        first | exact van1 hp hl hq h2 | exact van2 hp hq hl h2
      rw [e, this]; ring

private lemma tL_E {w : Field} (hw : Adm 2 w) :
    tL (fun p l q => if isLLH p l q then Pl w p l q else 0) = tL (Ps w) := by
  set Φ : Mode → Mode → Mode → ℝ := fun p l q => if isLLH p l q then Pl w p l q else 0
    with hΦ
  have hPs : ∀ p l q, ¬ isLLH p l q → Ps w p l q = 0 := fun p l q h => by
    unfold Ps; rw [ite_eq_right]; exact fun h' => h (Or.inl ⟨h'.1, h'.2.1⟩)
  have s0 := tLm_of_llh (Φ := Φ) fun p l q h => by simp [hΦ, h]
  have s1 := tLm_of_llh (Φ := fun p l q => Φ p q l) fun p l q h => by
    simp [hΦ, (isLLH_23 p l q).not.2 h]
  have r0 := tLm_of_llh hPs
  have r1 := tLm_of_llh (Φ := fun p l q => Ps w p q l) fun p l q h =>
    hPs p q l ((isLLH_23 p l q).not.2 h)
  have e1 := tL_23 Φ
  have e2 := tL_23 (Ps w)
  unfold tL at *
  have h1 := (s0.hasSum.add s1.hasSum).tsum_eq
  have h2 := (r0.hasSum.add r1.hasSum).tsum_eq
  rw [e1] at h1
  rw [e2] at h2
  have h3 : ∑' kp : Mode × Mode, (Φ kp.2 (kp.1 - kp.2) (-kp.1) + Φ kp.2 (-kp.1) (kp.1 - kp.2)) =
      ∑' kp : Mode × Mode, (Ps w kp.2 (kp.1 - kp.2) (-kp.1) + Ps w kp.2 (-kp.1) (kp.1 - kp.2)) :=
    tsum_congr fun kp => Ps_pt hw (by abel)
  linarith

/-! ### Step F: identification with `⟨P₂w, B(w₁,w₁)⟩` -/

private lemma dotV_zero_left (c : V3) : dotV 0 c = 0 := by simp [dotV]

private lemma dotV_zero_right (c : V3) : dotV c 0 = 0 := by simp [dotV]

private lemma dotM_zero (k : Mode) : dotM 0 k = 0 := by simp [dotM]

private lemma inner_eq_dotV' (x y : V3) : inner ℂ x y = dotV (conjV x) y := by
  simp [dotV, conjV, PiLp.inner_apply, mul_comm]

private lemma swap_fin (v : Field) (s : Finset Mode) (hv : ∀ p ∉ s, v p = 0) (k : Mode)
    (c : V3) (hc : dotM c k = 0) :
    ∑' p, Complex.I * dotM (v p) (k - p) * dotV (v (k - p)) c =
      ∑' p, det3 (curlS p (v p)) (v (k - p)) c := by
  set g : Mode → ℂ := fun p => dotM (v (k - p)) p * dotV (v p) c with hgdef
  set h : Mode → ℂ := fun p => dotV (v p) (v (k - p)) * dotM c p with hhdef
  have hg : Summable g := summable_of_ne_finset_zero (s := s) fun p hp => by
    simp [hgdef, hv p hp, dotV_zero_left]
  have hh : Summable h := summable_of_ne_finset_zero (s := s) fun p hp => by
    simp [hhdef, hv p hp, dotV_zero_left]
  have hgσ : ∑' p, g (k - p) = ∑' p, g p := (Equiv.subLeft k).tsum_eq g
  have hhσ : ∑' p, h (k - p) = ∑' p, h p := (Equiv.subLeft k).tsum_eq h
  have hh' : Summable fun p => h (k - p) := (Equiv.subLeft k).summable_iff.2 hh
  have hh0 : ∑' p, h p = 0 := by
    have e : ∑' p, (h p + h (k - p)) = 0 := by
      rw [← tsum_zero]
      refine tsum_congr fun p => ?_
      simp only [hhdef, sub_sub_cancel, dotV_comm' (v (k - p)) (v p)]
      rw [← mul_add, dotM_add_sub', hc, mul_zero]
    rw [hh.tsum_add hh', hhσ] at e
    linear_combination e / 2
  have lhs : ∀ p, Complex.I * dotM (v p) (k - p) * dotV (v (k - p)) c =
      Complex.I * g (k - p) := fun p => by
    simp only [hgdef, sub_sub_cancel]; ring
  have rhs : ∀ p, det3 (curlS p (v p)) (v (k - p)) c = Complex.I * (g p - h p) := fun p => by
    rw [det3_curlS']
  simp only [lhs, rhs]
  rw [tsum_mul_left, tsum_mul_left, hg.tsum_sub hh, hh0, hgσ, sub_zero]

private lemma inner_convec_fin (v : Field) (s : Finset Mode) (hv : ∀ p ∉ s, v p = 0) (a : V3)
    {k : Mode} (hk : k ≠ 0) (ha : dotM a k = 0) :
    inner ℂ a (convec v k) = ∑' p, det3 (curlS p (v p)) (v (k - p)) (conjV a) := by
  have hf : Summable fun p => (Complex.I * dotM (v p) (k - p)) • v (k - p) :=
    summable_of_ne_finset_zero (s := s) fun p hp => by simp [hv p hp, dotM_zero]
  have h0 : inner ℂ a (modeVec k) = 0 := by
    rw [inner_eq_dotV']
    have : dotV (conjV a) (modeVec k) = dotM (conjV a) k := by
      simp [dotV, dotM, modeVec]
    rw [this, dotM_conjV'', ha, map_zero]
  have hc : dotM (conjV a) k = 0 := by rw [dotM_conjV'', ha, map_zero]
  rw [convec, leray, ite_eq_right hk, inner_sub_right, inner_smul_right, h0, mul_zero, sub_zero,
    advect, ← swap_fin v s hv k (conjV a) hc]
  have := (innerSL ℂ a).map_tsum hf
  simp only [innerSL_apply_apply] at this
  rw [this]
  refine tsum_congr fun p => ?_
  rw [inner_smul_right, inner_eq_dotV', dotV_comm']

private lemma shell1_eq_zero (w : Field) {p : Mode} (hp : p ∉ S1) : shell 1 w p = 0 := by
  rw [mem_S1_iff] at hp
  simp [shell, hp]

private lemma termF {w : Field} (hw : Adm 2 w) (k : Mode) :
    ∑' p, Ps w p (k - p) (-k) =
      (hmet 2 - 1) * (inner ℂ (shell 2 w k) (convec (shell 1 w) k)).re := by
  by_cases hk : nsq k = 2
  · have hk0 : k ≠ 0 := by
      rintro rfl; simp [nsq] at hk
    have hs : shell 2 w k = w k := by simp [shell, hk]
    rw [hs, inner_convec_fin (shell 1 w) S1 (fun p hp => shell1_eq_zero w hp) (w k) hk0
      (hw.sol k), ← hw.real k]
    have hsum : Summable fun p =>
        det3 (curlS p (shell 1 w p)) (shell 1 w (k - p)) (w (-k)) :=
      summable_of_ne_finset_zero (s := S1) fun p hp => by
        rw [shell1_eq_zero w hp, curlS_zero, det3_zero1]
    have hre := Complex.reCLM.map_tsum hsum
    simp only [Complex.reCLM_apply] at hre
    rw [hre, ← tsum_mul_left]
    refine tsum_congr fun p => ?_
    simp only [Ps, Dl, shell, nsq_neg', hk, and_true]
    by_cases h1 : nsq p = 1 <;> by_cases h2 : nsq (k - p) = 1 <;>
      simp [h1, h2, curlS_zero, det3_zero1, det3_zero2]
  · have hs : shell 2 w k = 0 := by simp [shell, hk]
    rw [hs, inner_zero_left, Complex.zero_re, mul_zero]
    refine (tsum_congr fun p => ?_).trans tsum_zero
    simp [Ps, nsq_neg', hk]

private lemma tL_F {w : Field} (hw : Adm 2 w) :
    tL (Ps w) = (hmet 2 - 1) * ∑' k, (inner ℂ (shell 2 w k) (convec (shell 1 w) k)).re := by
  have hPs : ∀ p l q, ¬ isLLH p l q → Ps w p l q = 0 := fun p l q h => by
    unfold Ps; rw [ite_eq_right]; exact fun h' => h (Or.inl ⟨h'.1, h'.2.1⟩)
  have hS := tLm_of_llh hPs
  unfold tL
  rw [show (fun kp : Mode × Mode => Ps w kp.2 (kp.1 - kp.2) (-kp.1)) =
      fun kp => (fun k p => Ps w p (k - p) (-k)) kp.1 kp.2 from rfl, hS.tsum_prod,
    ← tsum_mul_left]
  exact tsum_congr fun k => termF hw k

/-- Kinetic cancellation: the LLH class is `(h₂ − 1)⟨B(w₁,w₁), P₂w⟩`. -/
theorem triadLLH_eq {w : Field} (hw : Adm 2 w) :
    triadLLH w = (hmet 2 - 1) * ∑' k, (inner ℂ (shell 2 w k) (convec (shell 1 w) k)).re := by
  rw [triadLLH_eq_tL hw, tL_W, tL_T, tL_E hw, tL_F hw]
  ring

/-! ### Goal 3: the first-shell amplitude bound -/

private lemma sos_hint (x y z u : ℂ) (s : ℝ) :
    0 ≤ (x.re * y.re + x.im * y.im - s * (z.re * u.re + z.im * u.im)) ^ 2 +
      (x.im * y.re - x.re * y.im - s * (z.im * u.re - z.re * u.im)) ^ 2 := by
  positivity

/-- The Leray-projected two-term amplitude on each of the twelve second-shell outputs. -/
private lemma amp_sq : ∀ pr ∈ P12, ∀ a b : V3, dotM a pr.1 = 0 → dotM b pr.2 = 0 →
    ‖leray (pr.1 + pr.2) ((Complex.I * dotM a pr.2) • b + (Complex.I * dotM b pr.1) • a)‖ ^ 2
      ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  intro pr hpr a b ha hb
  simp only [P12, Finset.mem_insert, Finset.mem_singleton] at hpr
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  rcases hpr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [dotM, Fin.sum_univ_three] at ha hb
    simp [Fin.sum_univ_three, leray, dotM, modeVec, absSq, ha, hb]
    ring_nf
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.sub_re,
      Complex.sub_im, Complex.I_re, Complex.I_im, Complex.zero_re, Complex.zero_im]
    linarith [sos_hint (a 1) (b 0) (a 2) (b 2) 1, sos_hint (a 1) (b 0) (a 2) (b 2) (-1),
      sos_hint (a 2) (b 0) (a 1) (b 1) 1, sos_hint (a 2) (b 0) (a 1) (b 1) (-1),
      sos_hint (a 2) (b 1) (a 0) (b 0) 1, sos_hint (a 2) (b 1) (a 0) (b 0) (-1)]

private lemma advect_pair (w : Field) {pr : Mode × Mode} (hpr : pr ∈ P12) :
    advect (shell 1 w) (shell 1 w) (pr.1 + pr.2) =
      (Complex.I * dotM (w pr.1) pr.2) • w pr.2 + (Complex.I * dotM (w pr.2) pr.1) • w pr.1 := by
  obtain ⟨h1, h2, hne, -, huniq⟩ := P12_spec pr hpr
  unfold advect
  rw [tsum_eq_sum (s := {pr.1, pr.2}), Finset.sum_pair hne, add_sub_cancel_left,
    add_sub_cancel_right]
  · have e1 : shell 1 w pr.1 = w pr.1 := by simp [shell, (mem_S1_iff _).1 h1]
    have e2 : shell 1 w pr.2 = w pr.2 := by simp [shell, (mem_S1_iff _).1 h2]
    rw [e1, e2]
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
    by_cases hp1 : p ∈ S1
    · by_cases hp2 : pr.1 + pr.2 - p ∈ S1
      · rcases huniq p hp1 hp2 with h | h
        · exact absurd h hp.1
        · exact absurd h hp.2
      · rw [shell1_eq_zero w hp2, smul_zero]
    · rw [shell1_eq_zero w hp1, dotM_zero, mul_zero, zero_smul]

private lemma convec_pair_sq {w : Field} (hw : Adm 2 w) {pr : Mode × Mode} (hpr : pr ∈ P12) :
    ‖convec (shell 1 w) (pr.1 + pr.2)‖ ^ 2 ≤ ‖w pr.1‖ ^ 2 * ‖w pr.2‖ ^ 2 := by
  rw [convec, advect_pair w hpr]
  exact amp_sq pr hpr (w pr.1) (w pr.2) (hw.sol _) (hw.sol _)

private lemma sum_S2 (φ : Mode → ℝ) :
    ∑' k, (if nsq k = 2 then φ k else 0) = ∑ pr ∈ P12, φ (pr.1 + pr.2) := by
  rw [tsum_eq_sum (s := P12.image fun pr => pr.1 + pr.2)]
  · rw [Finset.sum_image fun a ha b hb h => P12_inj a ha b hb h]
    refine Finset.sum_congr rfl fun pr hpr => ?_
    rw [ite_eq_left]
    rw [nsq_eq3]; exact (P12_spec pr hpr).2.2.2.1
  · intro k hk
    rw [ite_eq_right]
    intro h2
    obtain ⟨pr, hpr, he⟩ := P12_surj k (mem_box1 h2.le (by norm_num)) (by rw [← nsq_eq3]; exact h2)
    exact hk (Finset.mem_image.2 ⟨pr, hpr, he⟩)

private lemma x1_eq (w : Field) : x1 w = ∑ p ∈ S1, ‖w p‖ ^ 2 := by
  unfold x1
  rw [tsum_eq_sum (s := S1)]
  · exact Finset.sum_congr rfl fun p hp => by rw [ite_eq_left ((mem_S1_iff p).1 hp)]
  · intro p hp; rw [ite_eq_right (by rwa [mem_S1_iff] at hp)]

private lemma sum_S1_eq (f : Mode → ℝ) : ∑ p ∈ S1, f p = f ![1, 0, 0] + f ![-1, 0, 0] +
    f ![0, 1, 0] + f ![0, -1, 0] + f ![0, 0, 1] + f ![0, 0, -1] := by
  simp only [S1]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

private lemma sum_P12_eq (f : Mode → Mode → ℝ) : ∑ pr ∈ P12, f pr.1 pr.2 =
    f ![1, 0, 0] ![0, 1, 0] + f ![1, 0, 0] ![0, -1, 0] + f ![-1, 0, 0] ![0, 1, 0] +
    f ![-1, 0, 0] ![0, -1, 0] + f ![1, 0, 0] ![0, 0, 1] + f ![1, 0, 0] ![0, 0, -1] +
    f ![-1, 0, 0] ![0, 0, 1] + f ![-1, 0, 0] ![0, 0, -1] + f ![0, 1, 0] ![0, 0, 1] +
    f ![0, 1, 0] ![0, 0, -1] + f ![0, -1, 0] ![0, 0, 1] + f ![0, -1, 0] ![0, 0, -1] := by
  simp only [P12]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

private lemma pair_sum_le (w : Field) :
    ∑ pr ∈ P12, ‖w pr.1‖ ^ 2 * ‖w pr.2‖ ^ 2 ≤ (x1 w) ^ 2 / 3 := by
  rw [x1_eq, sum_S1_eq, sum_P12_eq (fun p l => ‖w p‖ ^ 2 * ‖w l‖ ^ 2)]
  set x0 := ‖w ![1, 0, 0]‖ ^ 2 + ‖w ![-1, 0, 0]‖ ^ 2
  set y0 := ‖w ![0, 1, 0]‖ ^ 2 + ‖w ![0, -1, 0]‖ ^ 2
  set z0 := ‖w ![0, 0, 1]‖ ^ 2 + ‖w ![0, 0, -1]‖ ^ 2
  have : x0 * y0 + x0 * z0 + y0 * z0 ≤ (x0 + y0 + z0) ^ 2 / 3 := by
    nlinarith [sq_nonneg (x0 - y0), sq_nonneg (x0 - z0), sq_nonneg (y0 - z0)]
  simp only [x0, y0, z0] at this
  linarith

/-- The first-shell amplitude bound: `|LLH| ≤ c₁ x √Y₂`. -/
theorem triadLLH_le {w : Field} (hw : Adm 2 w) :
    |triadLLH w| ≤ c1 * x1 w * Real.sqrt (Y2r w) := by
  set B := convec (shell 1 w)
  have hR : ∑' k, (inner ℂ (shell 2 w k) (B k)).re =
      ∑ pr ∈ P12, (inner ℂ (w (pr.1 + pr.2)) (B (pr.1 + pr.2))).re := by
    rw [← sum_S2 (fun k => (inner ℂ (w k) (B k)).re)]
    refine tsum_congr fun k => ?_
    by_cases hk : nsq k = 2 <;> simp [shell, hk]
  have hm : m2 w = ∑ pr ∈ P12, ‖w (pr.1 + pr.2)‖ ^ 2 := by
    unfold m2; rw [sum_S2]
  have hx0 : 0 ≤ x1 w := by rw [x1_eq]; positivity
  have hm0 : 0 ≤ m2 w := by rw [hm]; positivity
  have h2 : 1 < hmet 2 := by norm_num [hmet, hmetTable]
  -- Cauchy–Schwarz
  have hCS : |∑ pr ∈ P12, (inner ℂ (w (pr.1 + pr.2)) (B (pr.1 + pr.2))).re| ≤
      Real.sqrt (m2 w) * (x1 w / Real.sqrt 3) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun pr _ => (Complex.abs_re_le_norm _).trans
      (norm_inner_le_norm (𝕜 := ℂ) _ _)).trans ?_
    refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans ?_
    rw [← hm]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    have hB : ∑ pr ∈ P12, ‖B (pr.1 + pr.2)‖ ^ 2 ≤ (x1 w) ^ 2 / 3 :=
      (Finset.sum_le_sum fun pr hpr => convec_pair_sq hw hpr).trans (pair_sum_le w)
    calc Real.sqrt (∑ pr ∈ P12, ‖B (pr.1 + pr.2)‖ ^ 2) ≤ Real.sqrt ((x1 w) ^ 2 / 3) :=
          Real.sqrt_le_sqrt hB
      _ = x1 w / Real.sqrt 3 := by rw [Real.sqrt_div' _ (by norm_num), Real.sqrt_sq hx0]
  rw [triadLLH_eq hw, hR, abs_mul, abs_of_pos (by linarith)]
  have e : c1 * x1 w * Real.sqrt (Y2r w) =
      (hmet 2 - 1) * (Real.sqrt (m2 w) * (x1 w / Real.sqrt 3)) := by
    have hh : 0 < hmet 2 := by linarith
    have s3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    have sh : 0 < Real.sqrt (hmet 2) := Real.sqrt_pos.2 hh
    rw [c1, Y2r, Real.sqrt_mul (by norm_num), Real.sqrt_mul hh.le]
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left hCS (by linarith)

end OVNS
