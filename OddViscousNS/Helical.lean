import OddViscousNS.Sobolev

/-! # The Leray symbol, the odd symbol, helical projectors and the filter `R(τ)`
(`Lemma lem:symbol`, `Lemma lem:semigroup`, the "Helical basis" paragraph). -/

open scoped ComplexConjugate Topology
noncomputable section
namespace OVNS

variable {k : Mode} {v w : V3}

private lemma v3_ext {a b : V3} (h0 : a 0 = b 0) (h1 : a 1 = b 1) (h2 : a 2 = b 2) : a = b := by
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

private lemma cross_apply_zero (a b : V3) : cross a b 0 = a 1 * b 2 - a 2 * b 1 := by
  simp [cross]
private lemma cross_apply_one (a b : V3) : cross a b 1 = a 2 * b 0 - a 0 * b 2 := by
  simp [cross]
private lemma cross_apply_two (a b : V3) : cross a b 2 = a 0 * b 1 - a 1 * b 0 := by
  simp [cross]
private lemma modeVec_apply (k : Mode) (i : Fin 3) : modeVec k i = (k i : ℂ) := by
  simp [modeVec]
private lemma e3_apply_zero : e3 0 = 0 := by simp [e3]
private lemma e3_apply_one : e3 1 = 0 := by simp [e3]
private lemma e3_apply_two : e3 2 = 1 := by simp [e3]
private lemma dotM_eq (v : V3) (k : Mode) :
    dotM v k = v 0 * (k 0 : ℂ) + v 1 * (k 1 : ℂ) + v 2 * (k 2 : ℂ) := by
  simp [dotM, Fin.sum_univ_three]
private lemma absSq_cast (k : Mode) :
    (absSq k : ℂ) = (k 0 : ℂ) ^ 2 + (k 1 : ℂ) ^ 2 + (k 2 : ℂ) ^ 2 := by
  simp [absSq, Fin.sum_univ_three]
private lemma absSq_cast_ne (hk : k ≠ 0) : (absSq k : ℂ) ≠ 0 := by
  have h := one_le_absSq hk
  have h0 : absSq k ≠ 0 := ne_of_gt (by linarith)
  exact_mod_cast h0
private lemma conjV_apply (v : V3) (i : Fin 3) : conjV v i = conj (v i) := by
  simp [conjV]
private lemma leray_of_ne (hk : k ≠ 0) (v : V3) :
    leray k v = v - (dotM v k / (absSq k : ℂ)) • modeVec k := by
  simp [leray, hk]
private lemma hel_of_ne (a : Sgn) (hk : k ≠ 0) (v : V3) :
    hel a k v = (1 / 2 : ℂ) • (leray k v + (Complex.I * (sg a / absk k : ℝ)) •
      cross (modeVec k) v) := by
  simp [hel, hk]
private lemma leray_zero_mode (v : V3) : leray 0 v = 0 := by simp [leray]

lemma dotM_add (a b : V3) (k : Mode) : dotM (a + b) k = dotM a k + dotM b k := by
  simp only [dotM_eq, PiLp.add_apply]; ring
lemma dotM_smul (c : ℂ) (a : V3) (k : Mode) : dotM (c • a) k = c * dotM a k := by
  simp only [dotM_eq, PiLp.smul_apply, smul_eq_mul]; ring
private lemma dotM_sub (a b : V3) (k : Mode) : dotM (a - b) k = dotM a k - dotM b k := by
  simp only [dotM_eq, PiLp.sub_apply]; ring
lemma cross_add_right (a b c : V3) : cross a (b + c) = cross a b + cross a c := by
  apply v3_ext <;>
    simp only [cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.add_apply] <;> ring
private lemma cross_sub_right (a b c : V3) : cross a (b - c) = cross a b - cross a c := by
  apply v3_ext <;>
    simp only [cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.sub_apply] <;> ring
lemma cross_smul_right (c : ℂ) (a b : V3) : cross a (c • b) = c • cross a b := by
  apply v3_ext <;>
    simp only [cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.smul_apply,
      smul_eq_mul] <;> ring
lemma leray_add (k : Mode) (a b : V3) : leray k (a + b) = leray k a + leray k b := by
  by_cases hk : k = 0
  · subst hk; simp [leray_zero_mode]
  · simp only [leray_of_ne hk, dotM_add, add_div, add_smul]; abel
lemma leray_sub (k : Mode) (a b : V3) : leray k (a - b) = leray k a - leray k b := by
  by_cases hk : k = 0
  · subst hk; simp [leray_zero_mode]
  · simp only [leray_of_ne hk, dotM_sub, sub_div, sub_smul]; abel
lemma leray_smul (k : Mode) (c : ℂ) (a : V3) : leray k (c • a) = c • leray k a := by
  by_cases hk : k = 0
  · subst hk; simp [leray_zero_mode]
  · simp only [leray_of_ne hk, dotM_smul, smul_sub, smul_smul, mul_div_assoc]
lemma leray_of_perp (hk : k ≠ 0) (hv : dotM v k = 0) : leray k v = v := by
  simp [leray_of_ne hk, hv]
private lemma dotM_modeVec (k : Mode) : dotM (modeVec k) k = (absSq k : ℂ) := by
  simp only [dotM_eq, absSq_cast, modeVec_apply]; ring
lemma dotM_leray (k : Mode) (v : V3) : dotM (leray k v) k = 0 := by
  by_cases hk : k = 0
  · subst hk; simp [leray_zero_mode, dotM]
  · rw [leray_of_ne hk, dotM_sub, dotM_smul, dotM_modeVec, div_mul_cancel₀ _ (absSq_cast_ne hk),
      sub_self]
lemma leray_idem (k : Mode) (v : V3) : leray k (leray k v) = leray k v := by
  by_cases hk : k = 0
  · subst hk; simp [leray_zero_mode]
  · exact leray_of_perp hk (dotM_leray k v)

/-- Inner product of `ℂ³` in coordinates. -/
private lemma inner_eq (v w : V3) :
    inner ℂ v w = conj (v 0) * w 0 + conj (v 1) * w 1 + conj (v 2) * w 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

private lemma conj_natCast_int (n : ℤ) : conj (n : ℂ) = n := by simp

private lemma inner_modeVec_right (v : V3) (k : Mode) :
    inner ℂ v (modeVec k) = conj (dotM v k) := by
  simp only [inner_eq, dotM_eq, modeVec_apply, map_add, map_mul, conj_natCast_int]

private lemma inner_modeVec_left (v : V3) (k : Mode) :
    inner ℂ (modeVec k) v = dotM v k := by
  simp only [inner_eq, dotM_eq, modeVec_apply, conj_natCast_int]; ring

private lemma absSq_cast_conj (k : Mode) : conj (absSq k : ℂ) = (absSq k : ℂ) :=
  Complex.conj_ofReal _

/-- `P_k` is self-adjoint. -/
private lemma inner_leray_right (k : Mode) (v w : V3) :
    inner ℂ v (leray k w) = inner ℂ (leray k v) w := by
  by_cases hk : k = 0
  · subst hk; simp [leray_zero_mode]
  · simp only [leray_of_ne hk, inner_sub_right, inner_sub_left, inner_smul_right, inner_smul_left,
      inner_modeVec_right, inner_modeVec_left, map_div₀, absSq_cast_conj]
    ring

lemma norm_leray_le (k : Mode) (v : V3) : ‖leray k v‖ ≤ ‖v‖ := by
  by_cases h0 : ‖leray k v‖ = 0
  · rw [h0]; exact norm_nonneg v
  have hpos : 0 < ‖leray k v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
  have h1 : ‖leray k v‖ ^ 2 ≤ ‖v‖ * ‖leray k v‖ := by
    have h2 : inner ℂ (leray k v) (leray k v) = inner ℂ v (leray k v) := by
      rw [← inner_leray_right, leray_idem]
    have h3 : ‖inner ℂ (leray k v) (leray k v)‖ = ‖leray k v‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]; simp
    rw [← h3, h2]
    exact norm_inner_le_norm v _
  nlinarith

lemma conjV_leray (k : Mode) (v : V3) : conjV (leray k v) = leray (-k) (conjV v) := by
  by_cases hk : k = 0
  · subst hk
    apply v3_ext <;> simp [leray_zero_mode, conjV_apply]
  · have hk' : -k ≠ 0 := neg_ne_zero.mpr hk
    have hS : (absSq (-k) : ℂ) = absSq k := by rw [absSq_neg]
    have hd : dotM (conjV v) (-k) = - conj (dotM v k) := by
      simp only [dotM_eq, conjV_apply, map_add, map_mul, conj_natCast_int, Pi.neg_apply,
        Int.cast_neg]
      ring
    rw [leray_of_ne hk, leray_of_ne hk', hS, hd]
    apply v3_ext <;>
      simp only [conjV_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, modeVec_apply,
        map_sub, map_mul, map_div₀, absSq_cast_conj, conj_natCast_int, Pi.neg_apply,
        Int.cast_neg] <;>
      ring
lemma norm_conjV (v : V3) : ‖conjV v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp [conjV_apply]

private lemma oddSym_add (k : Mode) (a b : V3) : oddSym k (a + b) = oddSym k a + oddSym k b := by
  simp only [oddSym, smul_add, cross_add_right, leray_add]
private lemma oddSym_smul (k : Mode) (c : ℂ) (a : V3) : oddSym k (c • a) = c • oddSym k a := by
  simp only [oddSym, smul_comm _ c a, cross_smul_right, leray_smul]
private lemma cross_zero_right (a : V3) : cross a 0 = 0 := by
  apply v3_ext <;> simp [cross_apply_zero, cross_apply_one, cross_apply_two]
private lemma cross_self (a : V3) : cross a a = 0 := by
  apply v3_ext <;>
    simp only [cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.zero_apply, mul_comm,
      sub_self]
private lemma dotM_cross (k : Mode) (v : V3) : dotM (cross (modeVec k) v) k = 0 := by
  simp only [dotM_eq, cross_apply_zero, cross_apply_one, cross_apply_two, modeVec_apply]
  ring
/-- The double cross product identity `C² = -|k|² P_k`, before dividing by `|k|²`. -/
private lemma cross_cross (k : Mode) (v : V3) :
    cross (modeVec k) (cross (modeVec k) v) = dotM v k • modeVec k - (absSq k : ℂ) • v := by
  apply v3_ext <;>
    simp only [dotM_eq, absSq_cast, cross_apply_zero, cross_apply_one, cross_apply_two,
      modeVec_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] <;> ring
private lemma cross_cross_of_ne (hk : k ≠ 0) (v : V3) :
    cross (modeVec k) (cross (modeVec k) v) = (-(absSq k : ℂ)) • leray k v := by
  rw [cross_cross, leray_of_ne hk, smul_sub, smul_smul, neg_mul,
    mul_div_cancel₀ _ (absSq_cast_ne hk), neg_smul, neg_smul]
  abel
/-- `C P_k = C`. -/
private lemma cross_leray (hk : k ≠ 0) (v : V3) :
    cross (modeVec k) (leray k v) = cross (modeVec k) v := by
  have h : ∀ (c : ℂ) (a b : V3), cross a (b - c • a) = cross a b := by
    intro c a b
    rw [cross_sub_right, cross_smul_right, cross_self, smul_zero, sub_zero]
  rw [leray_of_ne hk, h]
/-- The polynomial form of `Lemma lem:symbol`. -/
private lemma absSq_smul_leray_cross (hk : k ≠ 0) (hv : dotM v k = 0) :
    (absSq k : ℂ) • leray k (cross e3 v) = (k 2 : ℂ) • cross (modeVec k) v := by
  rw [leray_of_ne hk, smul_sub, smul_smul, mul_div_cancel₀ _ (absSq_cast_ne hk)]
  rw [dotM_eq] at hv
  apply v3_ext <;>
    simp only [dotM_eq, absSq_cast, cross_apply_zero, cross_apply_one, cross_apply_two,
      modeVec_apply, e3_apply_zero, e3_apply_one, e3_apply_two, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul]
  · linear_combination (-(k 1 : ℂ)) * hv
  · linear_combination (k 0 : ℂ) * hv
  · ring

/-- `Lemma lem:symbol`: on `k^⊥`, `L` has symbol `-k₃ k×`. -/
theorem oddSym_eq (hk : k ≠ 0) (hv : dotM v k = 0) :
    oddSym k v = (-(k 2 : ℂ)) • cross (modeVec k) v := by
  rw [oddSym, cross_smul_right, leray_smul, neg_smul, absSq_smul_leray_cross hk hv, neg_smul]

private lemma sg_mul_self (a : Sgn) : sg a * sg a = 1 := by cases a <;> simp [sg]
private lemma absk_cast_ne (hk : k ≠ 0) : (absk k : ℂ) ≠ 0 := by
  exact_mod_cast (absk_eq_zero.not.mpr hk)
private lemma absSq_cast_eq (k : Mode) : (absSq k : ℂ) = (absk k : ℂ) ^ 2 := by
  rw [← absk_sq]; push_cast; rfl

lemma hel_add (a : Sgn) (k : Mode) (v w : V3) : hel a k (v + w) = hel a k v + hel a k w := by
  by_cases hk : k = 0
  · subst hk; simp [hel]
  · simp only [hel_of_ne a hk, leray_add, cross_add_right, smul_add]
    abel
lemma hel_sub (a : Sgn) (k : Mode) (v w : V3) : hel a k (v - w) = hel a k v - hel a k w := by
  by_cases hk : k = 0
  · subst hk; simp [hel]
  · simp only [hel_of_ne a hk, leray_sub, cross_sub_right, smul_sub, smul_add]
    abel
lemma hel_smul (a : Sgn) (k : Mode) (c : ℂ) (v : V3) : hel a k (c • v) = c • hel a k v := by
  by_cases hk : k = 0
  · subst hk; simp [hel]
  · simp only [hel_of_ne a hk, leray_smul, cross_smul_right, smul_add, smul_comm _ c]
lemma hel_zero_mode (a : Sgn) (v : V3) : hel a 0 v = 0 := by simp [hel]

/-- The curl eigenrelation `(i k ×) H_a = a |k| H_a`. -/
lemma cross_hel (a : Sgn) (k : Mode) (v : V3) :
    (Complex.I) • cross (modeVec k) (hel a k v) = ((sg a * absk k : ℝ) : ℂ) • hel a k v := by
  by_cases hk : k = 0
  · subst hk; simp [hel_zero_mode, cross_zero_right]
  have hr := absk_cast_ne hk
  have hs : (sg a : ℂ) * sg a = 1 := by exact_mod_cast sg_mul_self a
  rw [hel_of_ne a hk, cross_smul_right, cross_add_right, cross_leray hk, cross_smul_right,
    cross_cross_of_ne hk, absSq_cast_eq]
  set x := leray k v
  set y := cross (modeVec k) v
  simp only [smul_add, smul_smul]
  rw [add_comm]
  push_cast
  congr 2
  · field_simp
    linear_combination (-1 : ℂ) * Complex.I_sq * sg a
  · field_simp
    linear_combination (-1 : ℂ) * hs

lemma dotM_hel (a : Sgn) (k : Mode) (v : V3) : dotM (hel a k v) k = 0 := by
  by_cases hk : k = 0
  · subst hk; simp [hel, dotM]
  · rw [hel_of_ne a hk, dotM_smul, dotM_add, dotM_smul, dotM_leray, dotM_cross]
    simp
private lemma leray_hel (hk : k ≠ 0) (a : Sgn) (v : V3) : leray k (hel a k v) = hel a k v :=
  leray_of_perp hk (dotM_hel a k v)
/-- The product formula `H_a H_b = ½(1 + ab) H_b`. -/
private lemma hel_hel (a b : Sgn) (k : Mode) (v : V3) :
    hel a k (hel b k v) = ((1 + (sg a : ℂ) * sg b) / 2) • hel b k v := by
  by_cases hk : k = 0
  · subst hk; simp [hel_zero_mode]
  have hr := absk_cast_ne hk
  have h : (Complex.I * (sg a / absk k : ℝ)) • cross (modeVec k) (hel b k v) =
      ((sg a : ℂ) * sg b) • hel b k v := by
    have h1 := cross_hel b k v
    calc (Complex.I * (sg a / absk k : ℝ)) • cross (modeVec k) (hel b k v)
        = ((sg a / absk k : ℝ) : ℂ) • (Complex.I • cross (modeVec k) (hel b k v)) := by
          rw [smul_smul, mul_comm]
      _ = ((sg a : ℂ) * sg b) • hel b k v := by
          rw [h1, smul_smul]
          congr 1
          push_cast
          field_simp
  have e : ∀ (c : ℂ) (x : V3), (1 / 2 : ℂ) • (x + c • x) = ((1 + c) / 2) • x := by
    intro c x
    rw [show (1 + c) / 2 = 1 / 2 + 1 / 2 * c by ring, add_smul, smul_add, smul_smul]
  rw [hel_of_ne a hk (hel b k v), leray_hel hk, h, e]
lemma hel_idem (a : Sgn) (k : Mode) (v : V3) : hel a k (hel a k v) = hel a k v := by
  have hs : (sg a : ℂ) * sg a = 1 := by exact_mod_cast sg_mul_self a
  rw [hel_hel, hs]
  norm_num
lemma hel_orth {a b : Sgn} (h : a ≠ b) (k : Mode) (v : V3) : hel a k (hel b k v) = 0 := by
  have hs : (sg a : ℂ) * sg b = -1 := by
    cases a <;> cases b <;> simp_all [sg]
  rw [hel_hel, hs]
  simp
/-- `H₊ + H₋ = P_k`. -/
lemma hel_sum (k : Mode) (v : V3) : ∑ a : Sgn, hel a k v = leray k v := by
  by_cases hk : k = 0
  · subst hk; simp [hel_zero_mode, leray_zero_mode]
  have h1 : sg true = 1 := by simp [sg]
  have h2 : sg false = -1 := by simp [sg]
  rw [Fintype.sum_bool, hel_of_ne true hk, hel_of_ne false hk, h1, h2, ← smul_add]
  have h3 : ((-1 / absk k : ℝ) : ℂ) = -((1 / absk k : ℝ) : ℂ) := by push_cast; ring
  rw [h3, mul_neg, neg_smul, add_add_add_comm, add_neg_cancel, add_zero, ← two_smul ℂ, smul_smul]
  norm_num
private lemma conj_half : conj (1 / 2 : ℂ) = 1 / 2 := by
  rw [map_div₀, map_one, Complex.conj_ofNat]
private lemma inner_cross_right (k : Mode) (v w : V3) :
    inner ℂ v (cross (modeVec k) w) = -inner ℂ (cross (modeVec k) v) w := by
  simp only [inner_eq, cross_apply_zero, cross_apply_one, cross_apply_two, modeVec_apply, map_sub,
    map_mul, conj_natCast_int]
  ring
/-- `H_a(k)` is self-adjoint. -/
lemma inner_hel_right (a : Sgn) (k : Mode) (v w : V3) :
    inner ℂ v (hel a k w) = inner ℂ (hel a k v) w := by
  by_cases hk : k = 0
  · subst hk; simp [hel_zero_mode]
  have hc : conj (Complex.I * ((sg a / absk k : ℝ) : ℂ)) = -(Complex.I * (sg a / absk k : ℝ)) := by
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  simp only [hel_of_ne a hk, inner_smul_right, inner_smul_left, inner_add_right, inner_add_left,
    inner_leray_right, inner_cross_right k v w, hc, conj_half]
  ring
private lemma inner_hel_hel_of_ne {a b : Sgn} (h : a ≠ b) (k : Mode) (v w : V3) :
    inner ℂ (hel a k v) (hel b k w) = 0 := by
  rw [← inner_hel_right, hel_orth h, inner_zero_right]
/-- Orthogonal decomposition of the sesquilinear form of `P_k`. -/
private lemma inner_leray_leray (k : Mode) (v w : V3) :
    inner ℂ (leray k v) (leray k w) =
      inner ℂ (hel true k v) (hel true k w) + inner ℂ (hel false k v) (hel false k w) := by
  simp only [← hel_sum, Fintype.sum_bool, inner_add_left, inner_add_right,
    inner_hel_hel_of_ne (show true ≠ false by simp),
    inner_hel_hel_of_ne (show false ≠ true by simp)]
  ring
private lemma inner_self_cast (v : V3) : inner ℂ v v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]
  simp
/-- Orthogonal decomposition of `P_k v`. -/
lemma norm_sq_hel_sum (k : Mode) (v : V3) :
    ∑ a : Sgn, ‖hel a k v‖ ^ 2 = ‖leray k v‖ ^ 2 := by
  have h := inner_leray_leray k v v
  simp only [inner_self_cast] at h
  rw [Fintype.sum_bool]
  exact_mod_cast h.symm
lemma norm_hel_le (a : Sgn) (k : Mode) (v : V3) : ‖hel a k v‖ ≤ ‖v‖ := by
  have h1 := norm_sq_hel_sum k v
  have h2 : ‖hel a k v‖ ^ 2 ≤ ∑ a : Sgn, ‖hel a k v‖ ^ 2 :=
    Finset.single_le_sum (f := fun a => ‖hel a k v‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ a)
  have h3 : ‖leray k v‖ ^ 2 ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_leray_le k v) 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (by linarith)
private lemma conjV_add (a b : V3) : conjV (a + b) = conjV a + conjV b := by
  apply v3_ext <;> simp only [conjV_apply, PiLp.add_apply, map_add]
private lemma conjV_smul (c : ℂ) (a : V3) : conjV (c • a) = conj c • conjV a := by
  apply v3_ext <;> simp only [conjV_apply, PiLp.smul_apply, smul_eq_mul, map_mul]
private lemma conjV_cross (a b : V3) : conjV (cross a b) = cross (conjV a) (conjV b) := by
  apply v3_ext <;>
    simp only [conjV_apply, cross_apply_zero, cross_apply_one, cross_apply_two, map_sub, map_mul]
private lemma conjV_modeVec (k : Mode) : conjV (modeVec k) = modeVec k := by
  apply v3_ext <;> simp only [conjV_apply, modeVec_apply, conj_natCast_int]
private lemma cross_modeVec_neg (k : Mode) (v : V3) :
    cross (modeVec (-k)) v = -cross (modeVec k) v := by
  apply v3_ext <;>
    simp only [cross_apply_zero, cross_apply_one, cross_apply_two, modeVec_apply, PiLp.neg_apply,
      Pi.neg_apply, Int.cast_neg] <;> ring
lemma conjV_hel (a : Sgn) (k : Mode) (v : V3) :
    conjV (hel a k v) = hel a (-k) (conjV v) := by
  by_cases hk : k = 0
  · subst hk
    apply v3_ext <;> simp [hel_zero_mode, conjV_apply]
  have hc : conj (Complex.I * ((sg a / absk k : ℝ) : ℂ)) = -(Complex.I * (sg a / absk k : ℝ)) := by
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [hel_of_ne a hk, hel_of_ne a (neg_ne_zero.mpr hk), conjV_smul, conjV_add, conjV_smul,
    conjV_leray, conjV_cross, conjV_modeVec, absk_neg, cross_modeVec_neg, hc, conj_half, neg_smul,
    smul_neg]
lemma lam_neg (a : Sgn) (k : Mode) : lam a (-k) = -lam a k := by
  simp only [lam, absk_neg, Pi.neg_apply, Int.cast_neg]
  ring
/-- `L h_a = i λ_a h_a`. -/
lemma oddSym_hel (a : Sgn) (k : Mode) (v : V3) :
    oddSym k (hel a k v) = (Complex.I * (lam a k : ℝ)) • hel a k v := by
  by_cases hk : k = 0
  · subst hk; simp [hel_zero_mode, oddSym, leray_zero_mode]
  have h1 := cross_hel a k v
  have h2 : cross (modeVec k) (hel a k v) =
      (-Complex.I * ((sg a * absk k : ℝ) : ℂ)) • hel a k v := by
    rw [mul_smul, ← h1, smul_smul]
    simp
  rw [oddSym_eq hk (dotM_hel a k v), h2, smul_smul]
  congr 1
  simp only [lam]
  push_cast
  ring

/-! ### The filter -/
private lemma rot_eq (τ : ℝ) (k : Mode) (v : V3) : rot τ k v =
    Complex.exp (Complex.I * (τ * lam true k : ℝ)) • hel true k v +
      Complex.exp (Complex.I * (τ * lam false k : ℝ)) • hel false k v := by
  rw [rot, Fintype.sum_bool]
private lemma rot_zero_mode (τ : ℝ) (v : V3) : rot τ 0 v = 0 := by simp [rot, hel_zero_mode]
lemma rot_add (τ : ℝ) (k : Mode) (v w : V3) : rot τ k (v + w) = rot τ k v + rot τ k w := by
  simp only [rot_eq, hel_add, smul_add]
  abel
lemma rot_sub (τ : ℝ) (k : Mode) (v w : V3) : rot τ k (v - w) = rot τ k v - rot τ k w := by
  simp only [rot_eq, hel_sub, smul_sub]
  abel
lemma rot_smul (τ : ℝ) (k : Mode) (c : ℂ) (v : V3) : rot τ k (c • v) = c • rot τ k v := by
  simp only [rot_eq, hel_smul, smul_add, smul_comm _ c]
lemma hel_rot (τ : ℝ) (a : Sgn) (k : Mode) (v : V3) :
    hel a k (rot τ k v) = Complex.exp (Complex.I * (τ * lam a k : ℝ)) • hel a k v := by
  rw [rot_eq, hel_add, hel_smul, hel_smul]
  cases a
  · rw [hel_idem, hel_orth (by simp), smul_zero, zero_add]
  · rw [hel_idem, hel_orth (by simp), smul_zero, add_zero]
lemma rot_rot (s t : ℝ) (k : Mode) (v : V3) : rot s k (rot t k v) = rot (s + t) k v := by
  rw [rot]
  simp only [hel_rot, smul_smul, ← Complex.exp_add]
  rw [rot]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  congr 2
  push_cast
  ring
lemma rot_zero_time (k : Mode) (v : V3) : rot 0 k v = leray k v := by
  rw [← hel_sum]
  simp [rot]
lemma dotM_rot (τ : ℝ) (k : Mode) (v : V3) : dotM (rot τ k v) k = 0 := by
  simp only [rot_eq, dotM_add, dotM_smul, dotM_hel, mul_zero, add_zero]
private lemma phase_mul_conj (x : ℝ) :
    Complex.exp (Complex.I * x) * conj (Complex.exp (Complex.I * x)) = 1 := by
  rw [Complex.mul_conj', mul_comm, Complex.norm_exp_ofReal_mul_I]
  simp
lemma inner_rot (τ : ℝ) (k : Mode) (v w : V3) :
    inner ℂ (rot τ k v) (rot τ k w) = inner ℂ (leray k v) (leray k w) := by
  rw [inner_leray_leray]
  simp only [rot_eq, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    inner_hel_hel_of_ne (show true ≠ false by simp),
    inner_hel_hel_of_ne (show false ≠ true by simp), mul_zero, add_zero, zero_add, ← mul_assoc,
    phase_mul_conj, one_mul]
/-- Unitarity. -/
lemma norm_rot (τ : ℝ) (k : Mode) (v : V3) : ‖rot τ k v‖ = ‖leray k v‖ := by
  have h := inner_rot τ k v v
  simp only [inner_self_cast] at h
  have h' : ‖rot τ k v‖ ^ 2 = ‖leray k v‖ ^ 2 := by exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h'
private lemma conj_phase (τ : ℝ) (a : Sgn) (k : Mode) :
    conj (Complex.exp (Complex.I * (τ * lam a k : ℝ))) =
      Complex.exp (Complex.I * (τ * lam a (-k) : ℝ)) := by
  rw [← Complex.exp_conj, lam_neg]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring
lemma conjV_rot (τ : ℝ) (k : Mode) (v : V3) : conjV (rot τ k v) = rot τ (-k) (conjV v) := by
  simp only [rot_eq, conjV_add, conjV_smul, conjV_hel, conj_phase]
/-- On slow modes the filter is the Leray projector. -/
lemma rot_slow (τ : ℝ) (hk : k 2 = 0) (v : V3) : rot τ k v = leray k v := by
  rw [← hel_sum, rot]
  simp [lam, hk]
/-- `∂_τ R(τ) = L R(τ)`. -/
lemma hasDerivAt_rot (k : Mode) (v : V3) (τ : ℝ) :
    HasDerivAt (fun s => rot s k v) (oddSym k (rot τ k v)) τ := by
  have key : ∀ a : Sgn, HasDerivAt
      (fun s : ℝ ↦ Complex.exp (Complex.I * (s * lam a k : ℝ)) • hel a k v)
      ((Complex.exp (Complex.I * (τ * lam a k : ℝ)) * (Complex.I * (lam a k : ℝ))) • hel a k v)
      τ := by
    intro a
    have h1 : HasDerivAt (fun s : ℝ ↦ Complex.I * ((s * lam a k : ℝ) : ℂ))
        (Complex.I * (lam a k : ℝ)) τ := by
      have h0 := ((hasDerivAt_id τ).mul_const (lam a k)).ofReal_comp
      simpa using h0.const_mul Complex.I
    exact h1.cexp.smul_const _
  have h := (key true).fun_add (key false)
  have h' : oddSym k (rot τ k v) =
      (Complex.exp (Complex.I * (τ * lam true k : ℝ)) * (Complex.I * (lam true k : ℝ))) •
        hel true k v +
      (Complex.exp (Complex.I * (τ * lam false k : ℝ)) * (Complex.I * (lam false k : ℝ))) •
        hel false k v := by
    rw [rot_eq, oddSym_add, oddSym_smul, oddSym_smul, oddSym_hel, oddSym_hel, smul_smul, smul_smul]
  rw [h']
  simpa only [rot_eq] using h
/-- On a solenoidal vector, `R(-τ)R(τ) = id`. -/
lemma rot_neg_rot (τ : ℝ) (hk : k ≠ 0) (hv : dotM v k = 0) : rot (-τ) k (rot τ k v) = v := by
  rw [rot_rot, neg_add_cancel, rot_zero_time, leray_of_perp hk hv]

variable {s : ℝ} {u : Field}

lemma rotF_add (τ : ℝ) (u v : Field) : rotF τ (u + v) = rotF τ u + rotF τ v := by
  funext k
  exact rot_add τ k (u k) (v k)
lemma rotF_sub (τ : ℝ) (u v : Field) : rotF τ (u - v) = rotF τ u - rotF τ v := by
  funext k
  exact rot_sub τ k (u k) (v k)
lemma rotF_rotF_neg (τ : ℝ) (hu : IsSolenoidal u) (h0 : u 0 = 0) :
    rotF (-τ) (rotF τ u) = u := by
  funext k
  by_cases hk : k = 0
  · subst hk
    simp only [rotF, rot_zero_mode, h0]
  · exact rot_neg_rot τ hk (hu k)
private lemma norm_rot_le (τ : ℝ) (k : Mode) (v : V3) : ‖rot τ k v‖ ≤ ‖v‖ := by
  rw [norm_rot]
  exact norm_leray_le k v
lemma Adm.rotF (τ : ℝ) (hu : Adm s u) : Adm s (OVNS.rotF τ u) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun k ↦ ?_) (fun k ↦ ?_) hu.inH
    · exact mul_nonneg (sobWeight_nonneg s k) (by positivity)
    · exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (norm_rot_le τ k (u k)) 2) (sobWeight_nonneg s k)
  · intro k
    simp only [OVNS.rotF]
    rw [hu.real k, conjV_rot]
  · intro k
    exact dotM_rot τ k (u k)
  · exact rot_zero_mode τ (u 0)
lemma hnorm_rotF (τ : ℝ) (hu : IsSolenoidal u) : hnorm s (rotF τ u) = hnorm s u := by
  have h : (fun k ↦ sobWeight s k * ‖rotF τ u k‖ ^ 2) = fun k ↦ sobWeight s k * ‖u k‖ ^ 2 := by
    funext k
    by_cases hk : k = 0
    · subst hk
      simp [sobWeight]
    · rw [show rotF τ u k = rot τ k (u k) from rfl, norm_rot, leray_of_perp hk (hu k)]
  rw [hnorm, hnorm, h]
/-- Strong continuity of the filter on `H^s`. -/
lemma tendsto_hnorm_rotF (hu : InH s u) (_hsol : IsSolenoidal u) (τ₀ : ℝ) :
    Filter.Tendsto (fun τ => hnorm s (rotF τ u - rotF τ₀ u)) (𝓝 τ₀) (𝓝 0) := by
  have hcont : ∀ k, Continuous fun τ : ℝ ↦ rot τ k (u k) := fun k ↦
    continuous_iff_continuousAt.mpr fun τ ↦ (hasDerivAt_rot k (u k) τ).continuousAt
  have hbd : Summable fun k ↦ 4 * (sobWeight s k * ‖u k‖ ^ 2) := hu.mul_left 4
  have hsum : Filter.Tendsto
      (fun τ ↦ ∑' k, sobWeight s k * ‖rot τ k (u k) - rot τ₀ k (u k)‖ ^ 2) (𝓝 τ₀)
      (𝓝 (∑' _ : Mode, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence hbd (fun k ↦ ?_) (.of_forall fun τ k ↦ ?_)
    · have h1 : Filter.Tendsto (fun τ : ℝ ↦ rot τ k (u k) - rot τ₀ k (u k)) (𝓝 τ₀)
          (𝓝 (rot τ₀ k (u k) - rot τ₀ k (u k))) :=
        ((hcont k).tendsto τ₀).sub_const _
      simpa using (h1.norm.pow 2).const_mul (sobWeight s k)
    · have h2 : ‖rot τ k (u k) - rot τ₀ k (u k)‖ ≤ 2 * ‖u k‖ := by
        linarith [norm_sub_le (rot τ k (u k)) (rot τ₀ k (u k)), norm_rot_le τ k (u k),
          norm_rot_le τ₀ k (u k)]
      have hw := sobWeight_nonneg s k
      rw [Real.norm_of_nonneg (by positivity)]
      calc sobWeight s k * ‖rot τ k (u k) - rot τ₀ k (u k)‖ ^ 2
          ≤ sobWeight s k * (2 * ‖u k‖) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h2 2) hw
        _ = 4 * (sobWeight s k * ‖u k‖ ^ 2) := by ring
  have h := hsum.sqrt
  simpa [hnorm, rotF, Real.sqrt_zero] using h
private lemma Adm.one_of_two {g : Field} (hg : Adm 2 g) : Adm 1 g :=
  ⟨hg.inH.mono (by norm_num), hg.real, hg.sol, hg.mean⟩
/-- The filtered force is a good force. -/
theorem goodForce_filtG (r t₀ : ℝ) {g : Field} (hg : Adm 2 g) :
    GoodForce (filtG r t₀ g) (hnorm 1 g) := by
  have hg1 := hg.one_of_two
  refine ⟨fun t ↦ hg1.rotF _, fun t ↦ (hnorm_rotF _ hg.sol).le, fun t₁ ↦ ?_⟩
  have hc : Continuous fun t : ℝ ↦ -(r * (t + t₀)) := by fun_prop
  exact (tendsto_hnorm_rotF hg1.inH hg.sol (-(r * (t₁ + t₀)))).comp (hc.tendsto t₁)
/-- The (constant) slow force is a good force. -/
theorem goodForce_PiS {g : Field} (hg : Adm 2 g) :
    GoodForce (fun _ => PiS g) (hnorm 1 g) := by
  have hg1 := hg.one_of_two
  refine ⟨fun _ ↦ hg1.PiS, fun _ ↦ hnorm_PiS_le hg1.inH, fun t₀ ↦ ?_⟩
  simp only [sub_self, hnorm_zero]
  exact tendsto_const_nhds

end OVNS
