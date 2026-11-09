import OddViscousNS.Filtered

/-! # Triad representation, antisymmetry, resonant energy conservation, selection rules
(`Lemma lem:anti`, `lem:energy`, `lem:FFS`, `lem:sel`, `lem:cat`).

The proofs avoid time averaging.  For real fields the pairing `⟨Z, Qm m X Y⟩` is an absolutely
convergent sum over `(p, q)` (with `r = -(p + q)`) of the permutation-friendly triad `tau`, and the
cancellations are pointwise identities on the orbits of `(p, q, r) ↦ (q, r, p)` or
`(q ↔ r)`. -/

open scoped ComplexConjugate

noncomputable section
namespace OVNS

variable {f h s : Field}

/-! ### Coordinates -/

lemma v3_ext {a b : V3} (h0 : a 0 = b 0) (h1 : a 1 = b 1) (h2 : a 2 = b 2) : a = b := by
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

lemma cross_apply_zero (a b : V3) : cross a b 0 = a 1 * b 2 - a 2 * b 1 := by
  simp [cross]

lemma cross_apply_one (a b : V3) : cross a b 1 = a 2 * b 0 - a 0 * b 2 := by
  simp [cross]

lemma cross_apply_two (a b : V3) : cross a b 2 = a 0 * b 1 - a 1 * b 0 := by
  simp [cross]

lemma modeVec_apply (k : Mode) (i : Fin 3) : modeVec k i = (k i : ℂ) := by
  simp [modeVec]

lemma dotM_eq (v : V3) (k : Mode) :
    dotM v k = v 0 * (k 0 : ℂ) + v 1 * (k 1 : ℂ) + v 2 * (k 2 : ℂ) := by
  simp [dotM, Fin.sum_univ_three]

lemma absSq_cast (k : Mode) :
    (absSq k : ℂ) = (k 0 : ℂ) ^ 2 + (k 1 : ℂ) ^ 2 + (k 2 : ℂ) ^ 2 := by
  simp [absSq, Fin.sum_univ_three]

lemma absSq_cast_ne {k : Mode} (hk : k ≠ 0) : (absSq k : ℂ) ≠ 0 := by
  have h := one_le_absSq hk
  have h0 : absSq k ≠ 0 := ne_of_gt (by linarith)
  exact_mod_cast h0

lemma conjV_apply (v : V3) (i : Fin 3) : conjV v i = conj (v i) := by
  simp [conjV]

lemma inner_eq (v w : V3) :
    inner ℂ v w = conj (v 0) * w 0 + conj (v 1) * w 1 + conj (v 2) * w 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

/-- The bilinear dot product on `ℂ³`. -/
def bd (a b : V3) : ℂ := a 0 * b 0 + a 1 * b 1 + a 2 * b 2

lemma bd_comm (a b : V3) : bd a b = bd b a := by
  simp only [bd]
  ring

lemma bd_zero_left (a : V3) : bd 0 a = 0 := by
  simp [bd]

lemma bd_zero_right (a : V3) : bd a 0 = 0 := by
  simp [bd]

lemma inner_eq_bd (v w : V3) : inner ℂ v w = bd (conjV v) w := by
  simp only [inner_eq, bd, conjV_apply]

lemma norm_bd_le (a b : V3) : ‖bd a b‖ ≤ ‖a‖ * ‖b‖ := by
  have h : bd a b = inner ℂ (conjV a) b := by
    rw [inner_eq_bd]
    simp only [bd, conjV_apply, Complex.conj_conj]
  rw [h, ← norm_conjV a]
  exact norm_inner_le_norm _ _

lemma dotM_neg_mode (v : V3) (k : Mode) : dotM v (-k) = -dotM v k := by
  simp only [dotM_eq, Pi.neg_apply, Int.cast_neg]
  ring

lemma dotM_add_mode (v : V3) (p q : Mode) : dotM v (p + q) = dotM v p + dotM v q := by
  simp only [dotM_eq, Pi.add_apply, Int.cast_add]
  ring

lemma dotM_zero_left (k : Mode) : dotM 0 k = 0 := by
  simp [dotM]

lemma hel_zero_right (a : Sgn) (k : Mode) : hel a k 0 = 0 := by
  have h := hel_smul a k 0 0
  simpa using h

lemma vert_zero_left (p q : Mode) (B : V3) : vert p q 0 B = 0 := by
  have h := leray_smul (p + q) 0 0
  simpa [vert, dotM_zero_left] using h

lemma vert_zero_right (p q : Mode) (A : V3) : vert p q A 0 = 0 := by
  have h := leray_smul (p + q) 0 0
  simpa [vert, dotM_zero_left] using h

/-! ### The vertex -/

/-- `C · ½[i(A·q)B + i(B·p)A]`, the bilinear form of the vertex against a transverse `C`. -/
def tau (p q : Mode) (A B C : V3) : ℂ :=
  (1 / 2) * Complex.I * (dotM A q * bd B C + dotM B p * bd A C)

lemma tau_comm (p q : Mode) (A B C : V3) : tau p q A B C = tau q p B A C := by
  simp only [tau]
  ring

lemma tau_zero_right (p q : Mode) (A B : V3) : tau p q A B 0 = 0 := by
  simp [tau, bd_zero_right]

lemma tau_zero_left (p q : Mode) (B C : V3) : tau p q 0 B C = 0 := by
  simp [tau, bd_zero_left, dotM_zero_left]

lemma tau_zero_mid (p q : Mode) (A C : V3) : tau p q A 0 C = 0 := by
  simp [tau, bd_zero_left, dotM_zero_left]

lemma leray_of_ne {k : Mode} (hk : k ≠ 0) (v : V3) :
    leray k v = v - (dotM v k / (absSq k : ℂ)) • modeVec k := by
  simp [leray, hk]

lemma bd_leray {k : Mode} {C : V3} (hk : k ≠ 0) (hC : dotM C k = 0) (V : V3) :
    bd C (leray k V) = bd C V := by
  rw [dotM_eq] at hC
  simp only [leray_of_ne hk, bd, PiLp.sub_apply, PiLp.smul_apply, modeVec_apply, smul_eq_mul]
  linear_combination (-(dotM V k / (absSq k : ℂ))) * hC

lemma bd_vert {p q : Mode} {A B C : V3} (hC : dotM C (p + q) = 0)
    (h0 : p + q = 0 → C = 0) : bd C (vert p q A B) = tau p q A B C := by
  by_cases hk : p + q = 0
  · simp [h0 hk, bd_zero_left, tau_zero_right]
  have hsm : ∀ (c : ℂ) (V : V3), bd C (c • V) = c * bd C V := fun c V => by
    simp only [bd, PiLp.smul_apply, smul_eq_mul]
    ring
  have hadd : ∀ V W : V3, bd C (V + W) = bd C V + bd C W := fun V W => by
    simp only [bd, PiLp.add_apply]
    ring
  rw [vert, hsm, bd_leray hk hC, hadd, hsm, hsm, tau, bd_comm C B, bd_comm C A]
  ring

/-- `lem:coef` at the level of vectors: the convective identity on a pair of helical waves. -/
lemma vert_hel (a b : Sgn) (p q : Mode) (v w : V3) :
    vert p q (hel a p v) (hel b q w) =
      (((sg a * absk p - sg b * absk q) / 2 : ℝ) : ℂ) •
        leray (p + q) (cross (hel a p v) (hel b q w)) := by
  set A := hel a p v with hA
  set B := hel b q w with hB
  have h1 : Complex.I • cross (modeVec p) A = ((sg a * absk p : ℝ) : ℂ) • A := cross_hel a p v
  have h2 : Complex.I • cross (modeVec q) B = ((sg b * absk q : ℝ) : ℂ) • B := cross_hel b q w
  have hkey : (Complex.I * dotM A q) • B + (Complex.I * dotM B p) • A =
      ((sg a * absk p - sg b * absk q : ℝ) : ℂ) • cross A B +
        (Complex.I * bd A B) • modeVec (p + q) := by
    have e0 := congrArg (fun V : V3 => V 0) h1
    have e1 := congrArg (fun V : V3 => V 1) h1
    have e2 := congrArg (fun V : V3 => V 2) h1
    have e0' := congrArg (fun V : V3 => V 0) h2
    have e1' := congrArg (fun V : V3 => V 1) h2
    have e2' := congrArg (fun V : V3 => V 2) h2
    simp only [PiLp.smul_apply, smul_eq_mul, cross_apply_zero, cross_apply_one, cross_apply_two,
      modeVec_apply] at e0 e1 e2 e0' e1' e2'
    apply v3_ext <;>
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, cross_apply_zero, cross_apply_one,
        cross_apply_two, modeVec_apply, dotM_eq, bd, Pi.add_apply, Int.cast_add, Complex.ofReal_sub]
    · linear_combination (B 2) * e1 - (B 1) * e2 + (A 2) * e1' - (A 1) * e2'
    · linear_combination (B 0) * e2 - (B 2) * e0 + (A 0) * e2' - (A 2) * e0'
    · linear_combination (B 1) * e0 - (B 0) * e1 + (A 1) * e0' - (A 0) * e1'
  have hgrad : ∀ c : ℂ, leray (p + q) (c • modeVec (p + q)) = 0 := fun c => by
    rw [leray_smul]
    by_cases hk : p + q = 0
    · simp [leray, hk]
    · apply v3_ext <;>
        · simp only [leray_of_ne hk, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, dotM_eq,
            modeVec_apply, absSq_cast, PiLp.zero_apply]
          have := absSq_cast_ne hk
          rw [absSq_cast] at this
          field_simp
          ring
  rw [vert, hkey, leray_add, hgrad, add_zero, leray_smul, smul_smul]
  congr 1
  push_cast
  ring

/-- Vanishing of the vertex under the helical resonance. -/
lemma vert_hel_zero {a b : Sgn} {p q : Mode} (v w : V3)
    (h : sg a * absk p = sg b * absk q) : vert p q (hel a p v) (hel b q w) = 0 := by
  rw [vert_hel, h]
  simp

/-! ### Absolutely convergent triple sums -/

lemma cs_equiv {a c : Mode → ℝ} (ha : ∀ k, 0 ≤ a k) (hc : ∀ k, 0 ≤ c k)
    (ha2 : Summable fun k => a k ^ 2) (hc2 : Summable fun k => c k ^ 2) (e : Mode ≃ Mode) :
    Summable (fun k => a k * c (e k)) ∧
      ∑' k, a k * c (e k) ≤ Real.sqrt (∑' k, a k ^ 2) * Real.sqrt (∑' k, c k ^ 2) := by
  have hc2' : Summable fun k => c (e k) ^ 2 := e.summable_iff.mpr hc2
  have h := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
    ha (fun k => hc (e k)) (by simpa only [Real.rpow_two] using ha2)
    (by simpa only [Real.rpow_two] using hc2')
  have he : ∑' k, c (e k) ^ 2 = ∑' k, c k ^ 2 := e.tsum_eq fun k => c k ^ 2
  simp only [Real.rpow_two, he] at h
  simpa only [Real.sqrt_eq_rpow] using h

lemma triple_bound {b a c : Mode → ℝ} (hb0 : ∀ k, 0 ≤ b k) (ha : ∀ k, 0 ≤ a k)
    (hc : ∀ k, 0 ≤ c k) (hb : Summable b) (ha2 : Summable fun k => a k ^ 2)
    (hc2 : Summable fun k => c k ^ 2) :
    Summable (fun x : Mode × Mode => b x.1 * a x.2 * c (x.1 + x.2)) ∧
      ∑' x : Mode × Mode, b x.1 * a x.2 * c (x.1 + x.2) ≤
        (∑' k, b k) * (Real.sqrt (∑' k, a k ^ 2) * Real.sqrt (∑' k, c k ^ 2)) := by
  set K := Real.sqrt (∑' k, a k ^ 2) * Real.sqrt (∑' k, c k ^ 2)
  have hcs := fun p : Mode => cs_equiv ha hc ha2 hc2 (Equiv.addLeft p)
  have hin : ∀ p : Mode, Summable fun q => b p * a q * c (p + q) := fun p => by
    have := (hcs p).1.mul_left (b p)
    simpa only [Equiv.coe_addLeft, mul_assoc] using this
  have hval : ∀ p : Mode, ∑' q, b p * a q * c (p + q) ≤ b p * K := fun p => by
    have e : ∑' q, b p * a q * c (p + q) = b p * ∑' q, a q * c (p + q) := by
      rw [← tsum_mul_left]
      exact tsum_congr fun q => mul_assoc _ _ _
    rw [e]
    exact mul_le_mul_of_nonneg_left (hcs p).2 (hb0 p)
  have hout : Summable fun p : Mode => ∑' q, b p * a q * c (p + q) :=
    Summable.of_nonneg_of_le (fun p => tsum_nonneg fun q =>
      mul_nonneg (mul_nonneg (hb0 p) (ha q)) (hc _)) hval (hb.mul_right K)
  have hs : Summable (fun x : Mode × Mode => b x.1 * a x.2 * c (x.1 + x.2)) :=
    (summable_prod_of_nonneg (fun x => mul_nonneg (mul_nonneg (hb0 _) (ha _)) (hc _))).mpr
      ⟨hin, hout⟩
  refine ⟨hs, ?_⟩
  rw [hs.tsum_prod, ← tsum_mul_right]
  exact hout.tsum_le_tsum hval (hb.mul_right K)

lemma sobWeight_one (k : Mode) : sobWeight 1 k = absSq k := by
  unfold sobWeight
  split_ifs with hk
  · subst hk
    simp [absSq]
  · have : absk k ^ (2 * 1 : ℝ) = absk k ^ (2 : ℕ) := by
      rw [mul_one, Real.rpow_two]
    rw [this, absk_sq]

lemma sobWeight_two (k : Mode) : sobWeight 2 k = absSq k ^ 2 := by
  unfold sobWeight
  split_ifs with hk
  · subst hk
    simp [absSq]
  · have : absk k ^ (2 * 2 : ℝ) = absk k ^ (4 : ℕ) := by
      rw [show (2 * 2 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast]
    rw [this, ← absk_sq]
    ring

lemma summable_grad_sq {X : Field} (hX : MZ 2 X) :
    Summable fun k => (absk k * ‖X k‖) ^ 2 := by
  have h := (InH.mono (s := 1) (by norm_num) hX.inH : InH 1 X)
  refine h.congr fun k => ?_
  rw [sobWeight_one, mul_pow, absk_sq]

lemma summable_hess_sq {Z : Field} (hZ : MZ 2 Z) :
    Summable fun k => (absSq k * ‖Z (-k)‖) ^ 2 := by
  have h : Summable fun k => sobWeight 2 (-k) * ‖Z (-k)‖ ^ 2 :=
    Summable.comp_injective (i := fun k : Mode => -k) hZ.inH neg_injective
  refine h.congr fun k => ?_
  rw [sobWeight_neg, sobWeight_two, mul_pow]

lemma summable_sq {X : Field} (hX : MZ 2 X) : Summable fun k => ‖X k‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (summable_grad_sq hX)
  by_cases hk : k = 0
  · subst hk
    simp [hX.mean]
  · rw [mul_pow, absk_sq]
    nlinarith [one_le_absSq hk, sq_nonneg ‖X k‖]

/-- The absolute majorant of all the triple sums. -/
def triM (σ : ℝ) (X Y Z : Field) (x : Mode × Mode) : ℝ :=
  sobWeight σ (x.1 + x.2) *
    ((absk x.1 + absk x.2) * ‖X x.1‖ * ‖Y x.2‖ * ‖Z (-(x.1 + x.2))‖)

lemma triM_nonneg (σ : ℝ) (X Y Z : Field) (x : Mode × Mode) : 0 ≤ triM σ X Y Z x := by
  have := absk_nonneg x.1
  have := absk_nonneg x.2
  have := sobWeight_nonneg σ (x.1 + x.2)
  unfold triM
  positivity

lemma summable_triM {σ : ℝ} (hσ : σ ≤ 1) {X Y Z : Field} (hX : MZ 2 X) (hY : MZ 2 Y)
    (hZ : MZ 2 Z) : Summable (triM σ X Y Z) := by
  have hc0 : ∀ k, 0 ≤ absSq k * ‖Z (-k)‖ := fun k => mul_nonneg (absSq_nonneg k) (norm_nonneg _)
  have h1 := (triple_bound (fun k => norm_nonneg (X k))
    (fun k => mul_nonneg (absk_nonneg k) (norm_nonneg (Y k))) hc0
    (summable_wiener hX.inH) (summable_grad_sq hY) (summable_hess_sq hZ)).1
  have h2 := (triple_bound (fun k => norm_nonneg (Y k))
    (fun k => mul_nonneg (absk_nonneg k) (norm_nonneg (X k))) hc0
    (summable_wiener hY.inH) (summable_grad_sq hX) (summable_hess_sq hZ)).1
  have h2' := (Equiv.prodComm Mode Mode).summable_iff.mpr h2
  refine Summable.of_nonneg_of_le (triM_nonneg σ X Y Z) (fun x => ?_) (h1.add h2')
  have hw := sobWeight_mono hσ (x.1 + x.2)
  rw [sobWeight_one] at hw
  have hrest : 0 ≤ (absk x.1 + absk x.2) * ‖X x.1‖ * ‖Y x.2‖ * ‖Z (-(x.1 + x.2))‖ := by
    have := absk_nonneg x.1
    have := absk_nonneg x.2
    positivity
  have hle := mul_le_mul_of_nonneg_right hw hrest
  simp only [triM, Function.comp, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap,
    add_comm x.2 x.1]
  calc _ ≤ _ := hle
    _ = _ := by ring

/-! ### Relabelling the triple sum -/

/-- The cyclic relabelling `(p, q) ↦ (q, r)`, `r = -(p + q)`. -/
def rho : Equiv.Perm (Mode × Mode) where
  toFun x := (x.2, -(x.1 + x.2))
  invFun x := (-(x.1 + x.2), x.1)
  left_inv x := Prod.ext (by simp) (by simp)
  right_inv x := Prod.ext (by simp) (by simp)

/-- The involution `(p, q) ↦ (p, r)`, `r = -(p + q)`. -/
def iota : Equiv.Perm (Mode × Mode) :=
  Function.Involutive.toPerm (fun x => (x.1, -(x.1 + x.2))) fun x => Prod.ext (by simp) (by simp)

lemma tsum_cyc {U : Mode × Mode → ℂ} (hU : Summable U)
    (h : ∀ p q, U (p, q) + U (q, -(p + q)) + U (-(p + q), p) = 0) : ∑' x, U x = 0 := by
  have h1 : ∑' x, U (rho x) = ∑' x, U x := rho.tsum_eq U
  have h2 : ∑' x, U (rho (rho x)) = ∑' x, U x := by
    rw [rho.tsum_eq fun y => U (rho y), h1]
  have hs1 : Summable fun x => U (rho x) := rho.summable_iff.mpr hU
  have hs2 : Summable fun x => U (rho (rho x)) := rho.summable_iff.mpr hs1
  have h3 : ∑' x, (U x + U (rho x) + U (rho (rho x))) = 0 := by
    rw [← tsum_zero (α := ℂ) (β := Mode × Mode)]
    refine tsum_congr fun x => ?_
    have e : rho (rho x) = (-(x.1 + x.2), x.1) := Prod.ext rfl (by simp [rho])
    rw [e]
    exact h x.1 x.2
  rw [(hU.add hs1).tsum_add hs2, hU.tsum_add hs1, h1, h2] at h3
  linear_combination (1 / 3 : ℂ) * h3

lemma tsum_anti {U : Mode × Mode → ℂ} (h : ∀ p q, U (p, -(p + q)) = -U (p, q)) :
    ∑' x, U x = 0 := by
  have h1 : ∑' x, U (iota x) = ∑' x, U x := iota.tsum_eq U
  have h2 : ∑' x, U (iota x) = -∑' x, U x := by
    rw [← tsum_neg]
    exact tsum_congr fun x => h x.1 x.2
  rw [h2] at h1
  linear_combination (-1 / 2 : ℂ) * h1

/-- The pairing against `W` as a sum over `(p, q)`. -/
lemma pair_eq_tsum {σ : ℝ} {Z W : Field} (T : Mode → Mode → ℂ)
    (hW : ∀ k, inner ℂ (Z k) (W k) = ∑' p, T p (k - p))
    (hT : Summable fun x : Mode × Mode => (sobWeight σ (x.1 + x.2) : ℂ) * T x.1 x.2) :
    pair σ Z W = (∑' x : Mode × Mode, (sobWeight σ (x.1 + x.2) : ℂ) * T x.1 x.2).re := by
  set F : Mode × Mode → ℂ := fun x => (sobWeight σ (x.1 + x.2) : ℂ) * T x.1 x.2 with hF
  let e : (Mode × Mode) ≃ (Mode × Mode) :=
    { toFun := fun x => (x.2, x.1 - x.2)
      invFun := fun x => (x.1 + x.2, x.1)
      left_inv := fun x => Prod.ext (by simp) rfl
      right_inv := fun x => Prod.ext rfl (by simp) }
  have hs : Summable fun x => F (e x) := e.summable_iff.mpr hT
  have hval : ∀ k, ∑' p, F (e (k, p)) = (sobWeight σ k : ℂ) * inner ℂ (Z k) (W k) := fun k => by
    rw [hW, ← tsum_mul_left]
    refine tsum_congr fun p => ?_
    simp only [hF, e, Equiv.coe_fn_mk, add_sub_cancel]
  have hsum : ∑' x, F x = ∑' k, (sobWeight σ k : ℂ) * inner ℂ (Z k) (W k) := by
    rw [← e.tsum_eq F, hs.tsum_prod]
    exact tsum_congr hval
  have hs' : Summable fun k => (sobWeight σ k : ℂ) * inner ℂ (Z k) (W k) := by
    have := hs.prod
    simpa only [Function.comp, hval] using this
  rw [hsum, Complex.re_tsum hs', pair]
  refine tsum_congr fun k => ?_
  simp

lemma weight_zero_mul {p q : Mode} {t : ℂ} (h : p + q = 0 → t = 0) :
    (sobWeight 0 (p + q) : ℂ) * t = t := by
  by_cases hk : p + q = 0
  · simp [h hk]
  · simp [sobWeight, hk]

/-- The cyclic cancellation for the pairing with weight `1`. -/
lemma pair_zero_of_cyc {Z W : Field} (T : Mode → Mode → ℂ)
    (hW : ∀ k, inner ℂ (Z k) (W k) = ∑' p, T p (k - p))
    (hT : Summable fun x : Mode × Mode => (sobWeight 0 (x.1 + x.2) : ℂ) * T x.1 x.2)
    (h0 : ∀ p q, p + q = 0 → T p q = 0)
    (hc : ∀ p q, T p q + T q (-(p + q)) + T (-(p + q)) p = 0) : pair 0 Z W = 0 := by
  rw [pair_eq_tsum T hW hT]
  have he : ∀ x : Mode × Mode, (sobWeight 0 (x.1 + x.2) : ℂ) * T x.1 x.2 = T x.1 x.2 :=
    fun x => weight_zero_mul (h0 _ _)
  simp only [he] at hT ⊢
  rw [tsum_cyc hT hc]
  simp

/-! ### The triad representation -/

lemma inner_tsum {v : Mode → V3} (x : V3) (hv : Summable v) :
    inner ℂ x (∑' p, v p) = ∑' p, inner ℂ x (v p) := by
  simpa using (innerSL ℂ x).map_tsum hv

lemma inner_hel_real {Z : Field} (hZ : IsReal Z) (c : Sgn) (k : Mode) (V : V3) :
    inner ℂ (Z k) (hel c k V) = bd (hel c (-k) (Z (-k))) V := by
  rw [inner_hel_right, inner_eq_bd, conjV_hel, ← hZ k]

/-- The triad summand of `⟨Z, Qm m X Y⟩`. -/
def tripT (m : Mult) (X Y Z : Field) (p q : Mode) : ℂ :=
  ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, m a b c p q *
    tau p q (hel a p (X p)) (hel b q (Y q)) (hel c (-(p + q)) (Z (-(p + q))))

lemma dotM_hel_neg (c : Sgn) (k : Mode) (v : V3) : dotM (hel c (-k) v) k = 0 := by
  have h := dotM_hel c (-k) v
  rw [dotM_neg_mode] at h
  exact neg_eq_zero.mp h

lemma bd_hel_vert (c : Sgn) (p q : Mode) (A B v : V3) :
    bd (hel c (-(p + q)) v) (vert p q A B) = tau p q A B (hel c (-(p + q)) v) :=
  bd_vert (dotM_hel_neg c _ v) fun h => by simp [h, hel_zero_mode]

lemma inner_Qm {m : Mult} (hm : m.Bdd) {X Y Z : Field} (hZ : IsReal Z) (hX : MZ 2 X)
    (hY : MZ 2 Y) (k : Mode) : inner ℂ (Z k) (Qm m X Y k) = ∑' p, tripT m X Y Z p (k - p) := by
  rw [Qm, inner_tsum _ (summable_Qm_term hm hX hY k)]
  refine tsum_congr fun p => ?_
  have hk : p + (k - p) = k := by abel
  simp only [inner_sum, inner_smul_right, tripT, hk, inner_hel_real hZ]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  have := bd_hel_vert c p (k - p) (hel a p (X p)) (hel b (k - p) (Y (k - p))) (Z (-k))
  rw [hk] at this
  rw [this]

lemma norm_tau_le (p q : Mode) (A B C : V3) :
    ‖tau p q A B C‖ ≤ (absk p + absk q) * ‖A‖ * ‖B‖ * ‖C‖ := by
  have h1 := norm_dotM_le A q
  have h2 := norm_dotM_le B p
  have h3 := norm_bd_le B C
  have h4 := norm_bd_le A C
  have hp := absk_nonneg p
  have hq := absk_nonneg q
  have hP : 0 ≤ ‖A‖ * ‖B‖ * ‖C‖ := by positivity
  have h5 : ‖dotM A q * bd B C + dotM B p * bd A C‖ ≤
      ‖A‖ * absk q * (‖B‖ * ‖C‖) + ‖B‖ * absk p * (‖A‖ * ‖C‖) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    gcongr
  have h6 : ‖(1 / 2 : ℂ) * Complex.I‖ = 1 / 2 := by simp
  rw [tau, norm_mul, h6]
  nlinarith [mul_nonneg hp hP, mul_nonneg hq hP]

lemma norm_tripT_le {m : Mult} (hm : m.Bdd) (X Y Z : Field) (p q : Mode) :
    ‖tripT m X Y Z p q‖ ≤
      8 * ((absk p + absk q) * ‖X p‖ * ‖Y q‖ * ‖Z (-(p + q))‖) := by
  set E := (absk p + absk q) * ‖X p‖ * ‖Y q‖ * ‖Z (-(p + q))‖ with hE
  have hterm : ∀ a b c, ‖m a b c p q *
      tau p q (hel a p (X p)) (hel b q (Y q)) (hel c (-(p + q)) (Z (-(p + q))))‖ ≤ E := by
    intro a b c
    have hp := absk_nonneg p
    have hq := absk_nonneg q
    rw [norm_mul]
    calc _ ≤ 1 * ‖tau p q (hel a p (X p)) (hel b q (Y q)) (hel c (-(p + q)) (Z (-(p + q))))‖ :=
          mul_le_mul_of_nonneg_right (hm a b c p q) (norm_nonneg _)
      _ ≤ _ := by
          rw [one_mul]
          refine (norm_tau_le _ _ _ _ _).trans ?_
          rw [hE]
          have h1 := norm_hel_le a p (X p)
          have h2 := norm_hel_le b q (Y q)
          have h3 := norm_hel_le c (-(p + q)) (Z (-(p + q)))
          gcongr
  have hbd : ‖tripT m X Y Z p q‖ ≤ ∑ _a : Sgn, ∑ _b : Sgn, ∑ _c : Sgn, E :=
    norm_sum_le_of_le _ fun a _ => norm_sum_le_of_le _ fun b _ =>
      norm_sum_le_of_le _ fun c _ => hterm a b c
  refine hbd.trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
  push_cast
  ring

lemma summable_tripT {m : Mult} (hm : m.Bdd) {σ : ℝ} (hσ : σ ≤ 1) {X Y Z : Field}
    (hX : MZ 2 X) (hY : MZ 2 Y) (hZ : MZ 2 Z) :
    Summable fun x : Mode × Mode => (sobWeight σ (x.1 + x.2) : ℂ) * tripT m X Y Z x.1 x.2 := by
  refine Summable.of_norm_bounded ((summable_triM hσ hX hY hZ).mul_left 8) fun x => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sobWeight_nonneg _ _)]
  have := mul_le_mul_of_nonneg_left (norm_tripT_le hm X Y Z x.1 x.2)
    (sobWeight_nonneg σ (x.1 + x.2))
  simp only [triM]
  linarith

lemma sum3_rot (g : Sgn → Sgn → Sgn → ℂ) :
    ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, g a b c = ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, g b c a := by
  simp only [Fintype.sum_bool]
  ring

lemma sum3_rot' (g : Sgn → Sgn → Sgn → ℂ) :
    ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, g a b c = ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, g c a b := by
  simp only [Fintype.sum_bool]
  ring

lemma sum3_swap (g : Sgn → Sgn → Sgn → ℂ) :
    ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, g a b c = ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, g a c b := by
  simp only [Fintype.sum_bool]
  ring

/-- The cyclic cancellation of the vertex on a triad with `A ⟂ p`, `B ⟂ q`, `C ⟂ r`. -/
lemma tau_cyc {p q : Mode} {A B C : V3} (hA : dotM A p = 0) (hB : dotM B q = 0)
    (hC : dotM C (-(p + q)) = 0) :
    tau p q A B C + tau q (-(p + q)) B C A + tau (-(p + q)) p C A B = 0 := by
  have e1 : dotM A (-(p + q)) = -dotM A p - dotM A q := by
    rw [dotM_neg_mode, dotM_add_mode]
    ring
  have e2 : dotM B (-(p + q)) = -dotM B p - dotM B q := by
    rw [dotM_neg_mode, dotM_add_mode]
    ring
  simp only [tau, e1, e2, hA, hB]
  rw [dotM_neg_mode, dotM_add_mode] at hC
  rw [bd_comm C A, bd_comm C B, bd_comm B A]
  linear_combination (-(1 / 2 : ℂ) * Complex.I * bd A B) * hC

lemma tripT_cyc {m : Mult} (hm : ∀ a b c p q, m a b c p q = m b c a q (-(p + q)))
    (F : Field) (p q : Mode) :
    tripT m F F F p q + tripT m F F F q (-(p + q)) + tripT m F F F (-(p + q)) p = 0 := by
  set r := -(p + q) with hr
  have h1 : -(q + r) = p := by rw [hr]; abel
  have h2 : -(r + p) = q := by rw [hr]; abel
  have e1 : tripT m F F F q r = ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, m b c a q r *
      tau q r (hel b q (F q)) (hel c r (F r)) (hel a p (F p)) := by
    simp only [tripT, h1]
    exact sum3_rot fun a b c => m a b c q r *
      tau q r (hel a q (F q)) (hel b r (F r)) (hel c p (F p))
  have e2 : tripT m F F F r p = ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, m c a b r p *
      tau r p (hel c r (F r)) (hel a p (F p)) (hel b q (F q)) := by
    simp only [tripT, h2]
    exact sum3_rot' fun a b c => m a b c r p *
      tau r p (hel a r (F r)) (hel b p (F p)) (hel c q (F q))
  rw [e1, e2, tripT, ← hr, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun c _ => ?_
  have hm1 := hm a b c p q
  have hm2 := hm b c a q r
  rw [h1] at hm2
  rw [← hr] at hm1
  rw [← hm2, ← hm1]
  have hc := tau_cyc (dotM_hel a p (F p)) (dotM_hel b q (F q)) (C := hel c r (F r))
    (by rw [← hr]; exact dotM_hel c r (F r))
  rw [← hr] at hc
  linear_combination (m a b c p q) * hc

lemma Phi_cyc (a b c : Sgn) (p q : Mode) : Phi a b c p q = Phi b c a q (-(p + q)) := by
  have h : q + -(p + q) = -p := by abel
  simp only [Phi, h, lam_neg]
  ring

lemma Phi_swap (a b c : Sgn) (p q : Mode) : Phi a b c p q = Phi a c b p (-(p + q)) := by
  have h : p + -(p + q) = -q := by abel
  simp only [Phi, h, lam_neg]
  ring

lemma resM_cyc (a b c : Sgn) (p q : Mode) :
    resM a b c p q = resM b c a q (-(p + q)) := by
  simp only [resM]
  rw [Phi_cyc]

lemma resM_swap (a b c : Sgn) (p q : Mode) :
    resM a b c p q = resM a c b p (-(p + q)) := by
  simp only [resM]
  rw [Phi_swap]

/-- `Lemma lem:energy`: `Q_res` conserves energy on real fields. -/
theorem pair_Qres_self (hf : Adm 2 f) : pair 0 f (Qres f f) = 0 := by
  refine pair_zero_of_cyc (tripT resM f f f) (inner_Qm resM_bdd hf.real hf.mz hf.mz)
    (summable_tripT resM_bdd (by norm_num) hf.mz hf.mz hf.mz) ?_ (tripT_cyc resM_cyc f)
  intro p q h
  simp [tripT, h, hel_zero_mode, tau_zero_right]

/-! ### Selection rules -/

lemma slow_zero (hs : PiS s = s) {k : Mode} (hk : k 2 ≠ 0) : s k = 0 := by
  rw [← hs]
  simp [PiS, hk]

lemma fast_zero (hf : PiF f = f) {k : Mode} (hk : k 2 = 0) : f k = 0 := by
  rw [← hf]
  simp [PiF, hk]

lemma lam_slow {k : Mode} (hk : k 2 = 0) (a : Sgn) : lam a k = 0 := by
  simp [lam, hk]

lemma res_null {a b c : Sgn} {p q : Mode} (hk : (p + q) 2 = 0) (hp : p 2 ≠ 0)
    (hΦ : Phi a b c p q = 0) : sg a * absk p = sg b * absk q := by
  have hq : (q 2 : ℝ) = -(p 2 : ℝ) := by
    have : q 2 = -p 2 := by
      simp only [Pi.add_apply] at hk
      omega
    rw [this]
    simp
  have hp' : (p 2 : ℝ) ≠ 0 := by exact_mod_cast hp
  rw [Phi, lam_slow hk, lam, lam, hq] at hΦ
  apply mul_left_cancel₀ hp'
  linear_combination hΦ

lemma res_cat {a b c : Sgn} {p q : Mode} (hp : p 2 = 0) (hq : q 2 ≠ 0)
    (hΦ : Phi a b c p q = 0) : sg b * absk q = sg c * absk (p + q) := by
  have hq' : (q 2 : ℝ) ≠ 0 := by exact_mod_cast hq
  have hk : (((p + q) 2 : ℤ) : ℝ) = (q 2 : ℝ) := by simp [hp]
  rw [Phi, lam_slow hp, lam, lam, hk] at hΦ
  apply mul_left_cancel₀ hq'
  linear_combination hΦ

lemma Qm_eq_zero {m : Mult} {X Y : Field} {k : Mode}
    (h : ∀ p, X p = 0 ∨ Y (k - p) = 0) : Qm m X Y k = 0 := by
  rw [Qm, ← tsum_zero (α := V3) (β := Mode)]
  refine tsum_congr fun p => ?_
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
    Finset.sum_eq_zero fun c _ => ?_
  rcases h p with h | h
  · simp [h, hel_zero_right, vert_zero_left]
  · simp [h, hel_zero_right, vert_zero_right]

/-- One summand of `Π_S Q_res` at a slow output. -/
lemma Qres_term_slow (f : Field) (a b c : Sgn) {k : Mode} (hk : k 2 = 0) (p : Mode) :
    resM a b c p (k - p) •
        hel c k (vert p (k - p) (hel a p (f p)) (hel b (k - p) (f (k - p)))) =
      (1 : ℂ) • hel c k
        (vert p (k - p) (hel a p (PiS f p)) (hel b (k - p) (PiS f (k - p)))) := by
  have hk' : p + (k - p) = k := by abel
  by_cases hp : p 2 = 0
  · have hq : (k - p) 2 = 0 := by simp [hk, hp]
    have hΦ : Phi a b c p (k - p) = 0 := by
      rw [Phi, hk', lam_slow hp, lam_slow hq, lam_slow hk]
      simp
    simp [resM, hΦ, PiS, hp, hq]
  · have hq : (k - p) 2 ≠ 0 := by
      simpa [hk] using hp
    have hr : PiS f p = 0 := by simp [PiS, hp]
    rw [hr, hel_zero_right, vert_zero_left, hel_zero_right]
    by_cases hΦ : Phi a b c p (k - p) = 0
    · have h := res_null (by rw [hk']; exact hk) hp hΦ
      rw [vert_hel_zero _ _ h, hel_zero_right]
      simp
    · simp [resM, hΦ]

lemma PiS_apply_slow (u : Field) {k : Mode} (hk : k 2 = 0) : PiS u k = u k := by
  simp [PiS, hk]

lemma PiS_apply_fast (u : Field) {k : Mode} (hk : k 2 ≠ 0) : PiS u k = 0 := by
  simp [PiS, hk]

lemma PiF_apply_slow (u : Field) {k : Mode} (hk : k 2 = 0) : PiF u k = 0 := by
  simp [PiF, hk]

lemma PiF_apply_fast (u : Field) {k : Mode} (hk : k 2 ≠ 0) : PiF u k = u k := by
  simp [PiF, hk]

/-- `Lemma lem:sel(a)` and `lem:FFS`/`sel(c)`: the slow projection of `Q_res(w,w)` is the closed
slow convection of the slow part. -/
theorem PiS_Qres (hw : Adm 2 f) : PiS (Qres f f) = Bsym (PiS f) (PiS f) := by
  funext k
  by_cases hk : k 2 = 0
  · rw [PiS_apply_slow _ hk, ← congrFun (Qm_one hw.PiS hw.PiS) k, Qres, Qm, Qm]
    refine tsum_congr fun p => ?_
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => ?_
    exact Qres_term_slow f a b c hk p
  · rw [PiS_apply_fast _ hk, Bsym, ← tsum_zero (α := V3) (β := Mode)]
    refine tsum_congr fun p => ?_
    by_cases hp : p 2 = 0
    · have hq : (k - p) 2 ≠ 0 := by simpa [hp] using hk
      rw [PiS_apply_fast f hq, vert_zero_right]
    · rw [PiS_apply_fast f hp, vert_zero_left]

/-- The weight-carrying cancellation on a catalytic triad. -/
lemma cat_term (hs' : PiS s = s) (hf' : PiF f = f) (σ : ℝ) (a b c : Sgn) (p q : Mode) :
    (sobWeight σ (p + -(p + q)) : ℂ) * (resM a c b p (-(p + q)) *
        tau p (-(p + q)) (hel a p (s p)) (hel c (-(p + q)) (f (-(p + q)))) (hel b q (f q))) +
      (sobWeight σ (p + q) : ℂ) * (resM a b c p q *
        tau p q (hel a p (s p)) (hel b q (f q)) (hel c (-(p + q)) (f (-(p + q))))) = 0 := by
  set r := -(p + q) with hr
  rw [hr, ← resM_swap, ← hr]
  by_cases hΦ : Phi a b c p q = 0
  swap
  · simp [resM, hΦ]
  by_cases hp : p 2 = 0
  swap
  · simp [slow_zero hs' hp, hel_zero_right, tau_zero_left]
  by_cases hq : q 2 = 0
  · simp [fast_zero hf' hq, hel_zero_right, tau_zero_right, tau_zero_mid]
  have hsg := res_cat hp hq hΦ
  have habs : absk q = absk (p + q) := by
    have h0 := absk_nonneg q
    have h1 := absk_nonneg (p + q)
    cases b <;> cases c <;> simp [sg] at hsg <;> linarith
  have hkq : p + q ≠ 0 := fun h => hq (by
    have := congrFun h 2
    simpa [hp] using this)
  have hq0 : q ≠ 0 := fun h => hq (by simp [h])
  have hrp : p + r = -q := by rw [hr]; abel
  have hw : sobWeight σ (p + r) = sobWeight σ (p + q) := by
    rw [hrp, sobWeight_neg]
    simp only [sobWeight, hkq, hq0, ↓reduceIte, habs]
  have hrabs : absk r = absk (p + q) := absk_neg _
  have hv : vert q r (hel b q (f q)) (hel c r (f r)) = 0 :=
    vert_hel_zero _ _ (by rw [hrabs]; exact hsg)
  have hqr : q + r = -p := by rw [hr]; abel
  have hbd : tau q r (hel b q (f q)) (hel c r (f r)) (hel a p (s p)) = 0 := by
    rw [← bd_vert (by rw [hqr, dotM_neg_mode, dotM_hel, neg_zero]) (fun h => ?_), hv, bd_zero_right]
    have : p = 0 := by
      rw [hqr] at h
      exact neg_eq_zero.mp h
    simp [this, hel_zero_mode]
  have hc := tau_cyc (dotM_hel a p (s p)) (dotM_hel b q (f q)) (C := hel c r (f r))
    (by rw [← hr]; exact dotM_hel c r (f r))
  rw [← hr, hbd, tau_comm r p] at hc
  rw [hw, show resM a b c p q = 1 by simp [resM, hΦ]]
  linear_combination (sobWeight σ (p + q) : ℂ) * hc

/-- `Lemma lem:sel(b)`: `Q_res(s,f)` is fast and its output at `k` involves only `|q| = |k|`, so
it preserves each sphere; hence catalytic neutrality at every weight (`Lemma lem:cat`). -/
theorem cat_neutral (hs : Adm 2 s) (hf : Adm 2 f) (hs' : PiS s = s) (hf' : PiF f = f)
    {σ : ℝ} (hσ : σ = 0 ∨ σ = 1) : pair σ f (Qres s f) = 0 := by
  have hσ' : σ ≤ 1 := by
    rcases hσ with rfl | rfl <;> norm_num
  rw [Qres, pair_eq_tsum (tripT resM s f f) (inner_Qm resM_bdd hf.real hs.mz hf.mz)
    (summable_tripT resM_bdd hσ' hs.mz hf.mz hf.mz)]
  have h0 : ∑' x : Mode × Mode, (sobWeight σ (x.1 + x.2) : ℂ) * tripT resM s f f x.1 x.2 = 0 := by
    refine tsum_anti fun p q => ?_
    simp only
    set r := -(p + q) with hr
    have hrq : -(p + r) = q := by rw [hr]; abel
    have e : tripT resM s f f p r = ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, resM a c b p r *
        tau p r (hel a p (s p)) (hel c r (f r)) (hel b q (f q)) := by
      simp only [tripT, hrq]
      exact sum3_swap fun a b c => resM a b c p r *
        tau p r (hel a p (s p)) (hel b r (f r)) (hel c q (f q))
    rw [eq_neg_iff_add_eq_zero, e, tripT, ← hr]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
      Finset.sum_eq_zero fun c _ => ?_
    exact cat_term hs' hf' σ a b c p q
  rw [h0]
  simp

/-- `Lemma lem:cat`, second half. -/
theorem pair_Qres_fast (hf : Adm 2 f) (_hf' : PiF f = f) :
    pair 0 f (Qres f f) = 0 := pair_Qres_self hf

/-- `PiF f`-tested fast self-interaction lands in the fast sector. -/
theorem PiS_Qres_fast (hf : Adm 2 f) (hf' : PiF f = f) : PiS (Qres f f) = 0 := by
  funext k
  by_cases hk : k 2 = 0
  · show PiS (Qres f f) k = (0 : V3)
    rw [congrFun (PiS_Qres hf) k, Bsym, ← tsum_zero (α := V3) (β := Mode)]
    refine tsum_congr fun p => ?_
    by_cases hp : p 2 = 0
    · rw [PiS_apply_slow f hp, fast_zero hf' hp, vert_zero_left]
    · rw [PiS_apply_fast f hp, vert_zero_left]
  · exact PiS_apply_fast _ hk

/-- The fast projection of `Q_res(w,w)`: catalytic plus fast-fast-fast. -/
theorem PiF_Qres (hw : Adm 2 f) :
    PiF (Qres f f) = (2 : ℂ) • Qres (PiS f) (PiF f) + Qres (PiF f) (PiF f) := by
  have hs := hw.PiS.mz
  have hF := hw.PiF.mz
  have hsum : MZ 2 (PiS f + PiF f) := by
    rw [PiS_add_PiF]
    exact hw.mz
  have hM := majorized_res
  have h1 : Qres (PiS f + PiF f) (PiS f + PiF f) =
      Qres (PiS f) (PiS f + PiF f) + Qres (PiF f) (PiS f + PiF f) :=
    hM.add_left 0 _ _ _ hs hF hsum
  have h2 : Qres (PiS f) (PiS f + PiF f) = Qres (PiS f) (PiS f) + Qres (PiS f) (PiF f) :=
    hM.add_right 0 _ _ _ hs hs hF
  have h3 : Qres (PiF f) (PiS f + PiF f) = Qres (PiF f) (PiS f) + Qres (PiF f) (PiF f) :=
    hM.add_right 0 _ _ _ hF hs hF
  have h4 : Qres (PiF f) (PiS f) = Qres (PiS f) (PiF f) := Qm_comm_of_symm resM_symm hF hs
  rw [h2, h3, h4, PiS_add_PiF] at h1
  have hslow : ∀ {k : Mode}, k 2 = 0 → Qres (PiS f) (PiF f) k = 0 := fun {k} hk =>
    Qm_eq_zero fun p => by
      by_cases hp : p 2 = 0
      · right
        exact PiF_apply_slow f (by simp [hk, hp])
      · left
        exact PiS_apply_fast f hp
  have hFF : ∀ {k : Mode}, k 2 = 0 → Qres (PiF f) (PiF f) k = 0 := fun {k} hk => by
    have hid : PiF (PiF f) = PiF f := by
      funext j
      by_cases hj : j 2 = 0 <;> simp [PiF, hj]
    have h := congrFun (PiS_Qres_fast hw.PiF hid) k
    rwa [PiS_apply_slow _ hk] at h
  have hss : ∀ {k : Mode}, k 2 ≠ 0 → Qres (PiS f) (PiS f) k = 0 := fun {k} hk =>
    Qm_eq_zero fun p => by
      by_cases hp : p 2 = 0
      · right
        exact PiS_apply_fast f (by simpa [hp] using hk)
      · left
        exact PiS_apply_fast f hp
  funext k
  have hk' := congrFun h1 k
  simp only [Pi.add_apply] at hk'
  simp only [Pi.add_apply, Pi.smul_apply]
  by_cases hk : k 2 = 0
  · rw [PiF_apply_slow _ hk, hslow hk, hFF hk]
    simp
  · rw [PiF_apply_fast _ hk, hk', hss hk, two_smul]
    abel

/-! ### The slow, 2D–3C block -/

lemma PiH_fast (u : Field) {k : Mode} (hk : k 2 ≠ 0) : PiH u k = 0 := by
  simp [PiH, hk]

lemma admPiH (hs : Adm 2 s) : Adm 2 (PiH s) := by
  have hr : ∀ k (i : Fin 3), s (-k) i = conj (s k i) := fun k i => by
    rw [hs.real k, conjV_apply]
  refine ⟨hs.inH.PiH, fun k => ?_, fun k => ?_, ?_⟩
  · by_cases h : k 2 = 0
    · apply v3_ext <;> simp [PiH, h, conjV_apply, hr]
    · apply v3_ext <;> simp [PiH, h, conjV_apply]
  · by_cases h : k 2 = 0
    · have := hs.sol k
      simp only [dotM_eq, h] at this ⊢
      simpa [PiH, h] using this
    · simp [PiH, h, dotM]
  · simp [PiH, hs.mean]

lemma admPiV (hs : Adm 2 s) : Adm 2 (PiV s) := by
  have hr : ∀ k (i : Fin 3), s (-k) i = conj (s k i) := fun k i => by
    rw [hs.real k, conjV_apply]
  refine ⟨hs.inH.PiV, fun k => ?_, fun k => ?_, ?_⟩
  · by_cases h : k 2 = 0
    · apply v3_ext <;> simp [PiV, h, conjV_apply, hr]
    · apply v3_ext <;> simp [PiV, h, conjV_apply]
  · by_cases h : k 2 = 0
    · simp [PiV, h, dotM_eq]
    · simp [PiV, h, dotM]
  · simp [PiV, hs.mean]

lemma pair_PiH (σ : ℝ) (W : Field) : pair σ (PiH s) (PiH W) = pair σ (PiH s) W := by
  simp only [pair]
  refine tsum_congr fun k => ?_
  by_cases h : k 2 = 0
  · simp [inner_eq, PiH, h]
  · simp [PiH, h]

lemma pair_PiV (σ : ℝ) (W : Field) : pair σ (PiV s) (PiV W) = pair σ (PiV s) W := by
  simp only [pair]
  refine tsum_congr fun k => ?_
  by_cases h : k 2 = 0
  · simp [inner_eq, PiV, h]
  · simp [PiV, h]

lemma bd_slow_PiH (hs' : PiS s = s) (q r : Mode) :
    bd (s q) (PiH s r) = bd (PiH s q) (PiH s r) := by
  by_cases hr : r 2 = 0
  · by_cases hq : q 2 = 0
    · simp [bd, PiH, hr, hq]
    · simp [slow_zero hs' hq, PiH, hq, bd]
  · simp [PiH, hr, bd]

lemma bd_slow_PiV (hs' : PiS s = s) (q r : Mode) :
    bd (s q) (PiV s r) = bd (PiV s q) (PiV s r) := by
  by_cases hr : r 2 = 0
  · by_cases hq : q 2 = 0
    · simp [bd, PiV, hr, hq]
    · simp [slow_zero hs' hq, PiV, hq, bd]
  · simp [PiV, hr, bd]

lemma summable_vert {X Y : Field} (hX : MZ 2 X) (hY : MZ 2 Y) (k : Mode) :
    Summable fun p => vert p (k - p) (X p) (Y (k - p)) := by
  have hA := fun k => mul_nonneg (absk_nonneg k) (norm_nonneg (X k))
  have hB := fun k => mul_nonneg (absk_nonneg k) (norm_nonneg (Y k))
  have h1 := (cs_equiv hA (fun k => norm_nonneg (Y k)) (summable_grad_sq hX) (summable_sq hY)
    (Equiv.subLeft k)).1
  have h2 := (cs_equiv (fun k => norm_nonneg (X k)) hB (summable_sq hX) (summable_grad_sq hY)
    (Equiv.subLeft k)).1
  refine Summable.of_norm_bounded (h1.add h2) fun p => ?_
  refine (norm_vert_le₁ _ _ _ _).trans ?_
  simp only [Equiv.subLeft_apply]
  have h3 := hA p
  have h4 := hB (k - p)
  nlinarith [norm_nonneg (X p), norm_nonneg (Y (k - p)),
    mul_nonneg h3 (norm_nonneg (Y (k - p))), mul_nonneg (norm_nonneg (X p)) h4]

/-- The triad summand of `⟨Z, B(X, Y)⟩`. -/
def tripB (X Y Z : Field) (p q : Mode) : ℂ := tau p q (X p) (Y q) (Z (-(p + q)))

lemma inner_Bsym {X Y Z : Field} (hZ : Adm 2 Z) (hX : MZ 2 X) (hY : MZ 2 Y) (k : Mode) :
    inner ℂ (Z k) (Bsym X Y k) = ∑' p, tripB X Y Z p (k - p) := by
  rw [Bsym, inner_tsum _ (summable_vert hX hY k)]
  refine tsum_congr fun p => ?_
  have hk : p + (k - p) = k := by abel
  rw [inner_eq_bd, ← hZ.real k, tripB, hk]
  refine bd_vert ?_ fun h => ?_
  · have := hZ.sol (-k)
    rw [dotM_neg_mode] at this
    rw [hk]
    exact neg_eq_zero.mp this
  · rw [hk] at h
    simp [h, hZ.mean]

lemma summable_tripB {σ : ℝ} (hσ : σ ≤ 1) {X Y Z : Field} (hX : MZ 2 X) (hY : MZ 2 Y)
    (hZ : MZ 2 Z) :
    Summable fun x : Mode × Mode => (sobWeight σ (x.1 + x.2) : ℂ) * tripB X Y Z x.1 x.2 := by
  refine Summable.of_norm_bounded (summable_triM hσ hX hY hZ) fun x => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sobWeight_nonneg _ _)]
  exact mul_le_mul_of_nonneg_left (norm_tau_le _ _ _ _ _) (sobWeight_nonneg σ _)

/-- The slow transport cancellation for a component `Z` of the slow field `s`. -/
lemma pair_slow_cyc (hs : Adm 2 s) {Z : Field} (hZ : Adm 2 Z)
    (hb : ∀ q r, bd (s q) (Z r) = bd (Z q) (Z r)) : pair 0 Z (Bsym s s) = 0 := by
  refine pair_zero_of_cyc (tripB s s Z) (inner_Bsym hZ hs.mz hs.mz)
    (summable_tripB (by norm_num) hs.mz hs.mz hZ.mz) ?_ ?_
  · intro p q h
    simp [tripB, h, hZ.mean, tau_zero_right]
  · intro p q
    set r := -(p + q) with hr
    have h1 : -(q + r) = p := by rw [hr]; abel
    have h2 : -(r + p) = q := by rw [hr]; abel
    have hp := hs.sol p
    have hq := hs.sol q
    have hrr := hs.sol r
    have e1 : dotM (s p) r = -dotM (s p) p - dotM (s p) q := by
      rw [hr, dotM_neg_mode, dotM_add_mode]
      ring
    have e2 : dotM (s q) r = -dotM (s q) p - dotM (s q) q := by
      rw [hr, dotM_neg_mode, dotM_add_mode]
      ring
    have e3 : dotM (s r) r = -dotM (s r) p - dotM (s r) q := by
      rw [hr, dotM_neg_mode, dotM_add_mode]
      ring
    rw [e3] at hrr
    simp only [tripB, tau, h1, h2, ← hr, hb, e1, e2, hp, hq]
    rw [bd_comm (Z r) (Z q), bd_comm (Z r) (Z p), bd_comm (Z q) (Z p)]
    linear_combination (-(1 / 2 : ℂ) * Complex.I * bd (Z p) (Z q)) * hrr

/-- The stream function of a horizontal slow field. -/
def streamPsi (s : Field) (p : Mode) : ℂ := (-(s p 0) * p 1 + s p 1 * p 0) / absSq p

lemma streamPsi_spec (hs : Adm 2 s) {p : Mode} (hp : p 2 = 0) :
    s p 0 = -streamPsi s p * p 1 ∧ s p 1 = streamPsi s p * p 0 := by
  by_cases h0 : p = 0
  · subst h0
    simp [hs.mean]
  have hne := absSq_cast_ne h0
  have hd := hs.sol p
  rw [dotM_eq, hp] at hd
  have hA := absSq_cast p
  rw [hp] at hA
  simp only [Int.cast_zero, mul_zero, add_zero] at hd
  simp only [streamPsi]
  constructor
  · field_simp
    rw [hA]
    push_cast
    linear_combination (p 0 : ℂ) * hd
  · field_simp
    rw [hA]
    push_cast
    linear_combination (p 1 : ℂ) * hd

/-- The triad in stream-function form: `T = ½ i ψ_p ψ_q ψ_r (p ∧ q)(|p|² - |q|²)`. -/
lemma tripB_eval (hs : Adm 2 s) {p q : Mode} (hp : p 2 = 0) (hq : q 2 = 0) :
    tripB s s (PiH s) p q = (1 / 2) * Complex.I * streamPsi s p * streamPsi s q * streamPsi s (-(p + q)) *
      ((p 0 : ℂ) * q 1 - p 1 * q 0) * ((p 0 : ℂ) ^ 2 + p 1 ^ 2 - q 0 ^ 2 - q 1 ^ 2) := by
  have hr : (-(p + q)) 2 = 0 := by simp [hp, hq]
  obtain ⟨p0, p1⟩ := streamPsi_spec hs hp
  obtain ⟨q0, q1⟩ := streamPsi_spec hs hq
  obtain ⟨r0, r1⟩ := streamPsi_spec hs hr
  have h0 : PiH s (-(p + q)) 0 = s (-(p + q)) 0 := by simp [PiH, hr]
  have h1 : PiH s (-(p + q)) 1 = s (-(p + q)) 1 := by simp [PiH, hr]
  have h2 : PiH s (-(p + q)) 2 = 0 := by simp [PiH, hr]
  simp only [tripB, tau, bd, dotM_eq, hp, hq, h0, h1, h2, p0, p1, q0, q1, r0, r1]
  simp only [Pi.neg_apply, Pi.add_apply, Int.cast_neg, Int.cast_add, Int.cast_zero]
  ring

/-- `⟨B(s,s), s⟩`-type cancellations on slow fields. -/
theorem pair_slow_horizontal (hs : Adm 2 s) (hs' : PiS s = s) {σ : ℝ} (hσ : σ = 0 ∨ σ = 1) :
    pair σ (PiH s) (PiH (Bsym s s)) = 0 := by
  rw [pair_PiH]
  rcases hσ with rfl | rfl
  · exact pair_slow_cyc hs (admPiH hs) (bd_slow_PiH hs')
  have hH := admPiH hs
  have hsum := summable_tripB (σ := 1) le_rfl hs.mz hs.mz hH.mz
  rw [pair_eq_tsum (tripB s s (PiH s)) (inner_Bsym hH hs.mz hs.mz) hsum, tsum_cyc hsum]
  · simp
  intro p q
  simp only [sobWeight_one]
  set r := -(p + q) with hr
  have hzero : ∀ p q : Mode, (p 2 ≠ 0 ∨ q 2 ≠ 0 ∨ (-(p + q)) 2 ≠ 0) →
      tripB s s (PiH s) p q = 0 := by
    intro p q h
    rcases h with h | h | h
    · simp [tripB, slow_zero hs' h, tau_zero_left]
    · simp [tripB, slow_zero hs' h, tau_zero_mid]
    · rw [tripB, PiH_fast s h, tau_zero_right]
  have h1 : -(q + r) = p := by rw [hr]; abel
  have h2 : -(r + p) = q := by rw [hr]; abel
  by_cases hp : p 2 = 0
  swap
  · rw [hzero p q (Or.inl hp), hzero q r (Or.inr (Or.inr (by rw [h1]; exact hp))),
      hzero r p (Or.inr (Or.inl hp))]
    simp
  by_cases hq : q 2 = 0
  swap
  · rw [hzero p q (Or.inr (Or.inl hq)), hzero q r (Or.inl hq),
      hzero r p (Or.inr (Or.inr (by rw [h2]; exact hq)))]
    simp
  have hrz : r 2 = 0 := by simp [hr, hp, hq]
  rw [tripB_eval hs hp hq, tripB_eval hs hq hrz, tripB_eval hs hrz hp, h1, h2, ← hr]
  simp only [absSq_cast, Pi.add_apply, hr, Pi.neg_apply, Int.cast_add, Int.cast_neg, hp, hq,
    Int.cast_zero, neg_add_rev, add_zero, neg_zero]
  ring

/-- Transport cancellation for the vertical scalar. -/
theorem pair_slow_vertical (hs : Adm 2 s) (hs' : PiS s = s) :
    pair 0 (PiV s) (PiV (Bsym s s)) = 0 := by
  rw [pair_PiV]
  exact pair_slow_cyc hs (admPiV hs) (bd_slow_PiV hs')

lemma dotM_PiH (hs' : PiS s = s) (p : Mode) {q : Mode} (hq : q 2 = 0) :
    dotM (s p) q = dotM (PiH s p) q := by
  by_cases hp : p 2 = 0
  · simp [dotM_eq, PiH, hp, hq]
  · simp [slow_zero hs' hp, PiH, hp, dotM_zero_left]

lemma norm_dot_bd_le (hs' : PiS s = s) (p q r : Mode) :
    ‖dotM (s p) q * bd (s q) (PiV s r)‖ ≤
      ‖PiH s p‖ * (absk q * ‖PiV s q‖) * ‖PiV s r‖ := by
  rw [bd_slow_PiV hs']
  by_cases hq : q 2 = 0
  · rw [dotM_PiH hs' p hq, norm_mul]
    have h1 := norm_dotM_le (PiH s p) q
    have h2 := norm_bd_le (PiV s q) (PiV s r)
    have h3 : 0 ≤ ‖PiH s p‖ * absk q := mul_nonneg (norm_nonneg _) (absk_nonneg q)
    calc _ ≤ (‖PiH s p‖ * absk q) * (‖PiV s q‖ * ‖PiV s r‖) :=
          mul_le_mul h1 h2 (norm_nonneg _) h3
      _ = _ := by ring
  · have h0 : PiV s q = 0 := by simp [PiV, hq]
    simp [h0, bd_zero_left]

/-- The Wiener transport bound at the `H¹` level. -/
theorem pair_slow_vertical_le (hs : Adm 2 s) (hs' : PiS s = s) :
    |pair 1 (PiV s) (PiV (Bsym s s))| ≤ wiener (PiH s) * hnorm 1 (PiV s) * hnorm 2 (PiV s) := by
  rw [pair_PiV]
  have hV := admPiV hs
  have hsum := summable_tripB (σ := 1) le_rfl hs.mz hs.mz hV.mz
  rw [pair_eq_tsum (tripB s s (PiV s)) (inner_Bsym hV hs.mz hs.mz) hsum]
  set G : Mode × Mode → ℝ := fun x => ‖PiH s x.1‖ * (absk x.2 * ‖PiV s x.2‖) *
    (absSq (x.1 + x.2) * ‖PiV s (-(x.1 + x.2))‖) with hGdef
  obtain ⟨hG, hGle⟩ := triple_bound (b := fun k => ‖PiH s k‖)
    (a := fun k => absk k * ‖PiV s k‖) (c := fun k => absSq k * ‖PiV s (-k)‖)
    (fun _ => norm_nonneg _) (fun k => mul_nonneg (absk_nonneg k) (norm_nonneg _))
    (fun k => mul_nonneg (absSq_nonneg k) (norm_nonneg _)) (summable_wiener (admPiH hs).inH)
    (summable_grad_sq hV.mz) (summable_hess_sq hV.mz)
  have ha : ∑' k, (absk k * ‖PiV s k‖) ^ 2 = ∑' k, sobWeight 1 k * ‖PiV s k‖ ^ 2 :=
    tsum_congr fun k => by rw [sobWeight_one, mul_pow, absk_sq]
  have hc : ∑' k, (absSq k * ‖PiV s (-k)‖) ^ 2 = ∑' k, sobWeight 2 k * ‖PiV s k‖ ^ 2 := by
    rw [← (Equiv.neg Mode).tsum_eq fun k => sobWeight 2 k * ‖PiV s k‖ ^ 2]
    refine tsum_congr fun k => ?_
    simp only [Equiv.neg_apply]
    rw [sobWeight_neg, sobWeight_two, mul_pow]
  rw [ha, hc] at hGle
  have hGs : Summable fun x : Mode × Mode => G x.swap :=
    (Equiv.prodComm Mode Mode).summable_iff.mpr hG
  have hG' : ∑' x : Mode × Mode, G x.swap = ∑' x, G x := (Equiv.prodComm Mode Mode).tsum_eq G
  have hpt : ∀ x : Mode × Mode, ‖(sobWeight 1 (x.1 + x.2) : ℂ) * tripB s s (PiV s) x.1 x.2‖ ≤
      (1 / 2) * G x + (1 / 2) * G x.swap := by
    rintro ⟨p, q⟩
    simp only [hGdef, Prod.swap_prod_mk, add_comm q p]
    have h1 := norm_dot_bd_le hs' p q (-(p + q))
    have h2 := norm_dot_bd_le hs' q p (-(p + q))
    have h3 : ‖tripB s s (PiV s) p q‖ ≤ (1 / 2) *
        (‖PiH s p‖ * (absk q * ‖PiV s q‖) * ‖PiV s (-(p + q))‖ +
          ‖PiH s q‖ * (absk p * ‖PiV s p‖) * ‖PiV s (-(p + q))‖) := by
      have h6 : ‖(1 / 2 : ℂ) * Complex.I‖ = 1 / 2 := by simp
      rw [tripB, tau, norm_mul, h6]
      exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add h1 h2)) (by norm_num)
    rw [norm_mul, Complex.norm_real, sobWeight_one, Real.norm_of_nonneg (absSq_nonneg _)]
    have := mul_le_mul_of_nonneg_left h3 (absSq_nonneg (p + q))
    refine this.trans (le_of_eq ?_)
    ring
  have hle : ‖∑' x : Mode × Mode, (sobWeight 1 (x.1 + x.2) : ℂ) * tripB s s (PiV s) x.1 x.2‖ ≤
      (1 / 2) * ∑' x, G x + (1 / 2) * ∑' x : Mode × Mode, G x.swap :=
    tsum_of_norm_bounded ((hG.hasSum.mul_left _).add (hGs.hasSum.mul_left _)) hpt
  rw [hG'] at hle
  refine (Complex.abs_re_le_norm _).trans (hle.trans ?_)
  have hfin : (1 / 2) * ∑' x, G x + (1 / 2) * ∑' x, G x = ∑' x, G x := by ring
  rw [hfin, mul_assoc]
  exact hGle

end OVNS
