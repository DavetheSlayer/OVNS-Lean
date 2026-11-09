import OddViscousNS.LocalTheory

/-! # The fast force corrector (`§ fg:sec:tr`, paragraph "Corrector") -/

open Set
open scoped ENNReal
noncomputable section
namespace OVNS

open Classical in
/-- `ψ(t)`, started at `0` at absolute time `t₀`, solving
`ψ' = -Aψ + Π_F R(-r(t+t₀)) g`. -/
def psi (r t₀ : ℝ) (g : Field) (t : ℝ) : Field := fun k =>
  if k 2 = 0 then 0 else ∑ a : Sgn,
    ((Complex.exp (-(Complex.I * (r * (t + t₀) * lam a k : ℝ))) -
        Complex.exp (-(absSq k * t : ℝ)) * Complex.exp (-(Complex.I * (r * t₀ * lam a k : ℝ)))) /
      ((absSq k : ℂ) - Complex.I * (r * lam a k : ℝ))) • hel a k (g k)

variable {r t₀ : ℝ} {g : Field}

/-- The denominator of the helical coefficient of the corrector. -/
private def den (r : ℝ) (a : Sgn) (k : Mode) : ℂ :=
  (absSq k : ℂ) - Complex.I * (r * lam a k : ℝ)

/-- The helical coefficient `φ` of the corrector. -/
private def phi (r t₀ : ℝ) (a : Sgn) (k : Mode) (t : ℝ) : ℂ :=
  (Complex.exp (-(Complex.I * (r * (t + t₀) * lam a k : ℝ))) -
      Complex.exp (-(absSq k * t : ℝ)) * Complex.exp (-(Complex.I * (r * t₀ * lam a k : ℝ)))) /
    den r a k

private lemma psi_of_fast {k : Mode} (hk : k 2 ≠ 0) (t : ℝ) :
    psi r t₀ g t k = ∑ a : Sgn, phi r t₀ a k t • hel a k (g k) := by
  simp only [psi, hk, ↓reduceIte]
  rfl

private lemma psi_of_slow {k : Mode} (hk : k 2 = 0) (t : ℝ) : psi r t₀ g t k = 0 := by
  simp only [psi, hk, ↓reduceIte]

private lemma ne_zero_of_fast {k : Mode} (hk : k 2 ≠ 0) : k ≠ 0 := by
  rintro rfl
  exact hk rfl

private lemma den_re (a : Sgn) (k : Mode) : (den r a k).re = absSq k := by
  simp [den]

private lemma den_im (a : Sgn) (k : Mode) : (den r a k).im = -(r * lam a k) := by
  simp [den]

private lemma absSq_le_norm_den (a : Sgn) (k : Mode) : absSq k ≤ ‖den r a k‖ := by
  have h := Complex.abs_re_le_norm (den r a k)
  rw [den_re] at h
  exact (le_abs_self _).trans h

private lemma den_ne_zero (a : Sgn) {k : Mode} (hk : k ≠ 0) : den r a k ≠ 0 := by
  have h := absSq_le_norm_den (r := r) a k
  have h1 := one_le_absSq hk
  intro h0
  rw [h0, norm_zero] at h
  linarith

private lemma abs_lam_ge (a : Sgn) {k : Mode} (hk : k 2 ≠ 0) : absk k ≤ |lam a k| := by
  have h1 : (1 : ℝ) ≤ |(k 2 : ℝ)| := by exact_mod_cast Int.one_le_abs hk
  have hs : |sg a| = 1 := by cases a <;> simp [sg]
  rw [lam, abs_mul, abs_mul, hs, one_mul, abs_of_nonneg (absk_nonneg k)]
  exact le_mul_of_one_le_left (absk_nonneg k) h1

private lemma abs_mul_absk_le_norm_den (a : Sgn) {k : Mode} (hk : k 2 ≠ 0) :
    |r| * absk k ≤ ‖den r a k‖ := by
  have h := Complex.abs_im_le_norm (den r a k)
  rw [den_im, abs_neg, abs_mul] at h
  exact (mul_le_mul_of_nonneg_left (abs_lam_ge a hk) (abs_nonneg r)).trans h

private lemma norm_exp_neg_I (x : ℝ) : ‖Complex.exp (-(Complex.I * (x : ℂ)))‖ = 1 := by
  rw [show -(Complex.I * (x : ℂ)) = ((-x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The numerator of the coefficient is at most `2` for nonnegative times. -/
private lemma norm_phi_le (a : Sgn) (k : Mode) {t : ℝ} (ht : 0 ≤ t) :
    ‖phi r t₀ a k t‖ ≤ 2 / ‖den r a k‖ := by
  rw [phi, norm_div]
  refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
  have h1 : ‖Complex.exp (-((absSq k * t : ℝ) : ℂ))‖ ≤ 1 := by
    rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal]
    exact Real.exp_le_one_iff.mpr (by have := mul_nonneg (absSq_nonneg k) ht; linarith)
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ 1 + 1 := by
      rw [norm_mul, norm_exp_neg_I, norm_exp_neg_I, mul_one]
      linarith
    _ = 2 := by norm_num

/-- Orthogonality of helical components: a helical multiplier bounded by `C` is bounded by `C`. -/
private lemma norm_sq_sum_hel_le (c : Sgn → ℂ) (C : ℝ) (hC : ∀ a, ‖c a‖ ≤ C) (k : Mode) (v : V3) :
    ‖∑ a : Sgn, c a • hel a k v‖ ^ 2 ≤ C ^ 2 * ‖v‖ ^ 2 := by
  have horth : inner ℂ (c true • hel true k v) (c false • hel false k v) = (0 : ℂ) := by
    rw [inner_smul_left, inner_smul_right, ← inner_hel_right true k, hel_orth (by decide),
      inner_zero_right]
    simp
  have hsq : ∀ a, ‖c a • hel a k v‖ ^ 2 ≤ C ^ 2 * ‖hel a k v‖ ^ 2 := fun a ↦ by
    rw [norm_smul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hC a) 2) (sq_nonneg _)
  have hsum := norm_sq_hel_sum k v
  rw [Fintype.sum_bool] at hsum ⊢
  rw [norm_add_sq (𝕜 := ℂ), horth]
  have hl : ‖leray k v‖ ^ 2 ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_leray_le k v) 2
  have hC2 : 0 ≤ C ^ 2 := sq_nonneg C
  have := hsq true
  have := hsq false
  simp only [map_zero, mul_zero, add_zero]
  nlinarith [mul_le_mul_of_nonneg_left hl hC2]

private lemma norm_sq_psi_le {k : Mode} {t : ℝ} (ht : 0 ≤ t) (C : ℝ)
    (hC : ∀ a, 2 / ‖den r a k‖ ≤ C) :
    ‖psi r t₀ g t k‖ ^ 2 ≤ C ^ 2 * ‖g k‖ ^ 2 := by
  by_cases hk : k 2 = 0
  · have hC0 := hC true
    rw [psi_of_slow hk, norm_zero]
    have : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [this]
    positivity
  · rw [psi_of_fast hk]
    exact norm_sq_sum_hel_le _ C (fun a ↦ (norm_phi_le a k ht).trans (hC a)) k _

private lemma sobWeight_two {k : Mode} (hk : k ≠ 0) : sobWeight 2 k = absSq k ^ 2 := by
  simp only [sobWeight, hk, ↓reduceIte]
  rw [← absk_sq, ← pow_mul, show (2 * 2 : ℝ) = ((2 * 2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

private lemma sobWeight_one {k : Mode} (hk : k ≠ 0) : sobWeight 1 k = absSq k := by
  simp only [sobWeight, hk, ↓reduceIte]
  rw [← absk_sq, show (2 * 1 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- Mode-wise size of the corrector, gaining one derivative with the factor `1 / |r|`. -/
private lemma term_le (hr : r ≠ 0) (k : Mode) {t : ℝ} (ht : 0 ≤ t) :
    sobWeight 2 k * ‖psi r t₀ g t k‖ ^ 2 ≤ (2 / |r|) ^ 2 * (sobWeight 1 k * ‖g k‖ ^ 2) := by
  by_cases hk : k 2 = 0
  · rw [psi_of_slow hk, norm_zero]
    have := mul_nonneg (sobWeight_nonneg 1 k) (sq_nonneg ‖g k‖)
    have h0 : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [h0, mul_zero]
    positivity
  have hk0 := ne_zero_of_fast hk
  have habs : 0 < absk k := lt_of_lt_of_le one_pos (one_le_absk hk0)
  have hrp : 0 < |r| := abs_pos.mpr hr
  have h := norm_sq_psi_le (r := r) (t₀ := t₀) (g := g) (k := k) ht (2 / (|r| * absk k)) fun a ↦
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (abs_mul_absk_le_norm_den a hk)
  rw [sobWeight_two hk0, sobWeight_one hk0]
  calc absSq k ^ 2 * ‖psi r t₀ g t k‖ ^ 2
      ≤ absSq k ^ 2 * ((2 / (|r| * absk k)) ^ 2 * ‖g k‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ = (2 / |r|) ^ 2 * (absSq k * ‖g k‖ ^ 2) := by
      rw [← absk_sq]
      field_simp

private lemma norm_le_two_mul (k : Mode) {t : ℝ} (ht : 0 ≤ t) :
    ‖psi r t₀ g t k‖ ^ 2 ≤ 2 ^ 2 * ‖g k‖ ^ 2 := by
  by_cases hk : k = 0
  · subst hk
    rw [psi_of_slow rfl, norm_zero]
    have h0 : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [h0]
    positivity
  · refine norm_sq_psi_le ht 2 fun a ↦ ?_
    have h1 := one_le_absSq hk
    have h2 := absSq_le_norm_den (r := r) a k
    exact div_le_self (by norm_num) (by linarith)

private lemma inH_psi (hg : InH 2 g) {t : ℝ} (ht : 0 ≤ t) : InH 2 (psi r t₀ g t) := by
  refine Summable.of_nonneg_of_le (fun k ↦ ?_) (fun k ↦ ?_) (hg.mul_left (2 ^ 2))
  · exact mul_nonneg (sobWeight_nonneg 2 k) (sq_nonneg _)
  · calc sobWeight 2 k * ‖psi r t₀ g t k‖ ^ 2
        ≤ sobWeight 2 k * (2 ^ 2 * ‖g k‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (norm_le_two_mul k ht) (sobWeight_nonneg 2 k)
      _ = 2 ^ 2 * (sobWeight 2 k * ‖g k‖ ^ 2) := by ring

private lemma exp_time_hasDerivAt (L x : ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ Complex.exp (-(Complex.I * ((r * (s + x) * L : ℝ) : ℂ))))
      (Complex.exp (-(Complex.I * ((r * (t + x) * L : ℝ) : ℂ))) *
        (-(Complex.I * ((r * L : ℝ) : ℂ)))) t := by
  have h : HasDerivAt (fun s : ℝ ↦ r * (s + x) * L) (r * L) t := by
    have := ((hasDerivAt_id t).add_const x).const_mul r |>.mul_const L
    simpa using this
  exact ((h.ofReal_comp.const_mul Complex.I).neg).cexp

private lemma phi_hasDerivAt (a : Sgn) {k : Mode} (hk : k ≠ 0) (t : ℝ) :
    HasDerivAt (fun s ↦ phi r t₀ a k s)
      ((-(absSq k : ℂ)) * phi r t₀ a k t +
        Complex.exp (Complex.I * ((-(r * (t + t₀)) * lam a k : ℝ) : ℂ))) t := by
  have h1 := exp_time_hasDerivAt (r := r) (lam a k) t₀ t
  have h2 : HasDerivAt (fun s : ℝ ↦ Complex.exp (-((absSq k * s : ℝ) : ℂ)))
      (Complex.exp (-((absSq k * t : ℝ) : ℂ)) * (-(absSq k : ℂ))) t := by
    have h : HasDerivAt (fun s : ℝ ↦ absSq k * s) (absSq k) t := by
      simpa using (hasDerivAt_id t).const_mul (absSq k)
    exact (h.ofReal_comp.neg).cexp
  have h3 := ((h1.sub (h2.mul_const
    (Complex.exp (-(Complex.I * ((r * t₀ * lam a k : ℝ) : ℂ)))))).div_const (den r a k))
  have hD := den_ne_zero (r := r) a hk
  refine h3.congr_deriv ?_
  have hE : Complex.exp (Complex.I * ((-(r * (t + t₀)) * lam a k : ℝ) : ℂ)) =
      Complex.exp (-(Complex.I * ((r * (t + t₀) * lam a k : ℝ) : ℂ))) := by
    congr 1
    push_cast
    ring
  rw [hE, phi]
  field_simp
  simp only [den]
  push_cast
  ring

lemma psi_zero : psi r t₀ g 0 = 0 := by
  funext k
  by_cases hk : k 2 = 0
  · exact psi_of_slow hk 0
  · rw [psi_of_fast hk]
    refine Finset.sum_eq_zero fun a _ ↦ ?_
    have : phi r t₀ a k 0 = 0 := by simp [phi]
    rw [this, zero_smul]

/-- The mode equation of the corrector. -/
theorem psi_mode (_hg : Adm 2 g) (k : Mode) (t : ℝ) :
    HasDerivAt (fun s => psi r t₀ g s k)
      ((-(absSq k : ℝ) : ℂ) • psi r t₀ g t k + PiF (filtG r t₀ g t) k) t := by
  by_cases hk : k 2 = 0
  · have h : (fun s ↦ psi r t₀ g s k) = fun _ ↦ 0 := funext fun s ↦ psi_of_slow hk s
    rw [h, psi_of_slow hk]
    simp only [PiF, hk, ↓reduceIte]
    simpa using hasDerivAt_const t (0 : V3)
  have h : (fun s ↦ psi r t₀ g s k) = fun s ↦ ∑ a : Sgn, phi r t₀ a k s • hel a k (g k) :=
    funext fun s ↦ psi_of_fast hk s
  have hd : HasDerivAt (fun s ↦ ∑ a : Sgn, phi r t₀ a k s • hel a k (g k))
      (∑ a : Sgn, ((-(absSq k : ℂ)) * phi r t₀ a k t +
        Complex.exp (Complex.I * ((-(r * (t + t₀)) * lam a k : ℝ) : ℂ))) • hel a k (g k)) t :=
    HasDerivAt.fun_sum fun a _ ↦ (phi_hasDerivAt a (ne_zero_of_fast hk) t).smul_const _
  rw [h]
  refine hd.congr_deriv ?_
  rw [psi_of_fast hk]
  simp only [PiF, hk, ↓reduceIte, filtG, rotF, rot, add_smul, Finset.sum_add_distrib, mul_smul,
    Finset.smul_sum]

/-- The size of the corrector. -/
theorem psi_bound (hr : r ≠ 0) (hg : Adm 2 g) (t : ℝ) (ht : 0 ≤ t) :
    InH 2 (psi r t₀ g t) ∧ hnorm 2 (psi r t₀ g t) ≤ 2 * hnorm 1 g / |r| := by
  have hg1 : InH 1 g := Summable.of_nonneg_of_le
    (fun k ↦ mul_nonneg (sobWeight_nonneg 1 k) (sq_nonneg _))
    (fun k ↦ mul_le_mul_of_nonneg_right (sobWeight_mono (by norm_num) k) (sq_nonneg _)) hg.inH
  have hpsi : InH 2 (psi r t₀ g t) := inH_psi hg.inH ht
  refine ⟨hpsi, ?_⟩
  have hrp : 0 < |r| := abs_pos.mpr hr
  have hsum : ∑' k, sobWeight 2 k * ‖psi r t₀ g t k‖ ^ 2 ≤
      (2 / |r|) ^ 2 * ∑' k, sobWeight 1 k * ‖g k‖ ^ 2 := by
    rw [← tsum_mul_left]
    exact hpsi.tsum_le_tsum (fun k ↦ term_le hr k ht) (hg1.mul_left _)
  have h0 : 0 ≤ ∑' k, sobWeight 1 k * ‖g k‖ ^ 2 :=
    tsum_nonneg fun k ↦ mul_nonneg (sobWeight_nonneg 1 k) (sq_nonneg _)
  rw [hnorm, hnorm]
  calc √(∑' k, sobWeight 2 k * ‖psi r t₀ g t k‖ ^ 2)
      ≤ √((2 / |r|) ^ 2 * ∑' k, sobWeight 1 k * ‖g k‖ ^ 2) := Real.sqrt_le_sqrt hsum
    _ = 2 * √(∑' k, sobWeight 1 k * ‖g k‖ ^ 2) / |r| := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
      ring

private lemma conj_phi (a : Sgn) (k : Mode) (t : ℝ) :
    (starRingEnd ℂ) (phi r t₀ a k t) = phi r t₀ a (-k) t := by
  have hden : (starRingEnd ℂ) (den r a k) = den r a (-k) := by
    simp only [den, map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal, lam_neg, absSq_neg]
    push_cast
    ring
  have hexp : ∀ x : ℝ, (starRingEnd ℂ) (Complex.exp (-(Complex.I * ((x * lam a k : ℝ) : ℂ)))) =
      Complex.exp (-(Complex.I * ((x * lam a (-k) : ℝ) : ℂ))) := fun x ↦ by
    rw [← Complex.exp_conj, lam_neg]
    congr 1
    simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  have hreal : (starRingEnd ℂ) (Complex.exp (-((absSq k * t : ℝ) : ℂ))) =
      Complex.exp (-((absSq (-k) * t : ℝ) : ℂ)) := by
    rw [← Complex.exp_conj, absSq_neg, map_neg, Complex.conj_ofReal]
  simp only [phi, map_div₀, map_sub, map_mul, hden, hexp, hreal]

private lemma conjV_sum_smul (c : Sgn → ℂ) (v : Sgn → V3) :
    conjV (∑ a : Sgn, c a • v a) = ∑ a : Sgn, (starRingEnd ℂ) (c a) • conjV (v a) := by
  ext i
  simp [conjV]

private lemma dotM_sum_smul (c : Sgn → ℂ) (v : Sgn → V3) (k : Mode) :
    dotM (∑ a : Sgn, c a • v a) k = ∑ a : Sgn, c a * dotM (v a) k := by
  rw [Fintype.sum_bool, Fintype.sum_bool, dotM_add, dotM_smul, dotM_smul]

theorem psi_adm (hg : Adm 2 g) (t : ℝ) (ht : 0 ≤ t) : Adm 2 (psi r t₀ g t) := by
  refine ⟨inH_psi hg.inH ht, fun k ↦ ?_, fun k ↦ ?_, psi_of_slow rfl t⟩
  · by_cases hk : k 2 = 0
    · have hk' : (-k) 2 = 0 := by simp [hk]
      rw [psi_of_slow hk, psi_of_slow hk']
      ext i
      simp [conjV]
    · have hk' : (-k) 2 ≠ 0 := by simpa using hk
      rw [psi_of_fast hk, psi_of_fast hk', conjV_sum_smul]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [conj_phi, conjV_hel, hg.real k]
  · by_cases hk : k 2 = 0
    · rw [psi_of_slow hk]
      simp [dotM]
    · rw [psi_of_fast hk, dotM_sum_smul]
      simp only [dotM_hel, mul_zero, Finset.sum_const_zero]

end OVNS
