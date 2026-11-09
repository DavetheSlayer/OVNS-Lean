import OddViscousNS.Quant.Energy.Kinetic.Defs

/-!
# E4, the kinetic primitive: symbol bounds, summability, norm bounds

TeX: "The proper kinetic primitive … Its denominator is the actual nonzero outer phase" and the
fixed-slow-output Cauchy remark after eq. quant-kinetic-floor; Body 48 (N2)–(N3) via the survey
`t12_energy_derivation.md` §2.1 ("`vertex/(irΦ) = leray(A×B)/(2irp₃)`, a bounded multiplier").

* `norm_cross_le`: `‖A × B‖ ≤ ‖A‖ ‖B‖` on `ℂ³` (complex Lagrange identity
  `‖A×B‖² + |⟨A,B⟩|² = ‖A‖²‖B‖²`).
* `vert_hel_slow_out`: on a slow output the helical vertex is `Φ/(2p₃)·ℙ(A×B)`; hence
  `kinM • vert = kinSym • ℙ(A×B)` (`kinM_smul_vert`) and `‖kinSym‖ ≤ 1/(2q)` (`norm_kinSym_le`):
  the symbol `vertex/(irΦ)` is bounded by `1/(2q)` with no small divisor.
* (N3): the triad summand of `N(f,g)_k` is `≤ (2/q) ‖f_p‖ ‖g_{k−p}‖` (`norm_kinN_term_le`), so
  `‖N(f,g)_k‖ ≤ (2/q) ∑_p ‖f_p‖‖g_{k−p}‖ ≤ (2/q) ‖f‖_{ℓ²}‖g‖_{ℓ²}` (`norm_kinN_le`,
  `norm_kinN_le_l2`), `‖N(f,g)‖₀ ≤ (2/q) 𝒜(f) ‖g‖_{ℓ²}` (Young, `hnorm_kinN_le`), and the
  fixed-slow-output Cauchy bound `|⟨Z, N(f,g)⟩| ≤ (2/q) 𝒜(Z) ‖f‖_{ℓ²}‖g‖_{ℓ²}`
  (`abs_pair_kinN_le`).
* Structure: `N(f,g)` is slow (`kinN_fast`), mean-zero, solenoidal, real for real inputs and
  symmetric (`kinN_comm`); `Adm 2 f → Adm 2 g → Adm 0 (N(f,g))` (`kinN_adm`).
* `inner_kinN`: the triad expansion `⟨Z_k, N(X,Y)_k⟩ = ∑_p tripT (kinM) X Y Z p (k−p)` (mirror
  of `inner_Qm`, whose `Bdd` hypothesis the kinetic multiplier does not satisfy) and its
  bound `norm_tripT_kinM_le`, the inputs of the derivative lemma (`Derivative.lean`).

All bounds are stated for `ℓ²` inputs (`Summable (‖f ·‖²)`), since the derivative terms of the
kinetic functional involve `F' ∈ H⁰` only (`ℓ²` bookkeeping: `Defs.lean`).
-/

open scoped ComplexConjugate

noncomputable section

namespace OVNS

variable {r τ : ℝ}

/-! ### Vector algebra -/

/-- The complex Lagrange identity for the bilinear cross product and the sesquilinear inner
product: `‖A × B‖² + |⟨A, B⟩|² = ‖A‖² ‖B‖²`. -/
lemma norm_cross_sq_add_inner (a b : V3) :
    ‖cross a b‖ ^ 2 + ‖inner ℂ a b‖ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, cross_apply_zero, cross_apply_one,
    cross_apply_two, inner_eq, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.conj_re, Complex.conj_im]
  ring

lemma norm_cross_le (a b : V3) : ‖cross a b‖ ≤ ‖a‖ * ‖b‖ := by
  have h := norm_cross_sq_add_inner a b
  have h1 : ‖cross a b‖ ^ 2 ≤ (‖a‖ * ‖b‖) ^ 2 := by nlinarith [sq_nonneg ‖inner ℂ a b‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h1

/-- `∑_{a,b} ‖H_a A‖ ‖H_b B‖ ≤ 2 ‖A‖ ‖B‖` (Cauchy–Schwarz in the helicity pair). -/
lemma sum_norm_hel_mul_le (p q : Mode) (A B : V3) :
    (∑ a : Sgn, ‖hel a p A‖) * (∑ b : Sgn, ‖hel b q B‖) ≤ 2 * (‖A‖ * ‖B‖) := by
  have hsq : ∀ (k : Mode) (v : V3), (∑ a : Sgn, ‖hel a k v‖) ^ 2 ≤ 2 * ‖v‖ ^ 2 := by
    intro k v
    have h1 : ‖hel true k v‖ ^ 2 + ‖hel false k v‖ ^ 2 = ‖leray k v‖ ^ 2 := by
      rw [← norm_sq_hel_sum, Fintype.sum_bool]
    have h2 : ‖leray k v‖ ^ 2 ≤ ‖v‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_leray_le k v) 2
    rw [Fintype.sum_bool]
    nlinarith [sq_nonneg (‖hel true k v‖ - ‖hel false k v‖)]
  have hx : 0 ≤ ∑ a : Sgn, ‖hel a p A‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hy : 0 ≤ ∑ b : Sgn, ‖hel b q B‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h : ((∑ a : Sgn, ‖hel a p A‖) * (∑ b : Sgn, ‖hel b q B‖)) ^ 2 ≤
      (2 * (‖A‖ * ‖B‖)) ^ 2 := by
    calc _ = (∑ a : Sgn, ‖hel a p A‖) ^ 2 * (∑ b : Sgn, ‖hel b q B‖) ^ 2 := mul_pow _ _ _
      _ ≤ (2 * ‖A‖ ^ 2) * (2 * ‖B‖ ^ 2) :=
        mul_le_mul (hsq p A) (hsq q B) (sq_nonneg _) (by positivity)
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (mul_nonneg hx hy) (by positivity) two_ne_zero).mp h

/-- Summing a helicity-indexed family bounded by `κ ‖H_a A‖ ‖H_b B‖`. -/
lemma norm_sum3_le {E : Type*} [SeminormedAddCommGroup E] (T : Sgn → Sgn → Sgn → E) {κ : ℝ}
    (hκ : 0 ≤ κ) (p q : Mode) (A B : V3)
    (h : ∀ a b c, ‖T a b c‖ ≤ κ * (‖hel a p A‖ * ‖hel b q B‖)) :
    ‖∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, T a b c‖ ≤ 4 * κ * (‖A‖ * ‖B‖) := by
  calc _ ≤ ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, κ * (‖hel a p A‖ * ‖hel b q B‖) :=
        norm_sum_le_of_le _ fun a _ => norm_sum_le_of_le _ fun b _ =>
          norm_sum_le_of_le _ fun c _ => h a b c
    _ = 2 * κ * ((∑ a : Sgn, ‖hel a p A‖) * (∑ b : Sgn, ‖hel b q B‖)) := by
        simp only [Fintype.sum_bool]
        ring
    _ ≤ 2 * κ * (2 * (‖A‖ * ‖B‖)) :=
        mul_le_mul_of_nonneg_left (sum_norm_hel_mul_le _ _ _ _) (by positivity)
    _ = _ := by ring

/-! ### The symbol -/

/-- On a slow output `(p+q)₃ = 0` with fast inputs, the helical vertex is `Φ/(2p₃)` times the
bounded vector `ℙ_{p+q}(H_a v × H_b w)` (TeX: "use the slow output phase identity before
division"; survey §2.1, `/tmp/t12energy/KinPrim.lean`). -/
theorem vert_hel_slow_out (a b c : Sgn) (p q : Mode) (v w : V3) (hk : (p + q) 2 = 0)
    (hp : p 2 ≠ 0) :
    vert p q (hel a p v) (hel b q w) =
      ((Phi a b c p q / (2 * (p 2 : ℝ)) : ℝ) : ℂ) •
        leray (p + q) (cross (hel a p v) (hel b q w)) := by
  rw [vert_hel]
  congr 1
  have hq : (q 2 : ℝ) = -(p 2 : ℝ) := by
    have : q 2 = -p 2 := by simp only [Pi.add_apply] at hk; omega
    rw [this]; simp
  have hp' : (p 2 : ℝ) ≠ 0 := by exact_mod_cast hp
  have hl : lam c (p + q) = 0 := lam_slow hk c
  rw [Phi, hl, lam, lam, hq]
  congr 1
  field_simp
  ring

/-- The kinetic symbol: `kinM • vert = kinSym • ℙ(A × B)`, i.e. `vertex/(irΦ) = ℙ(A×B)/(2irp₃)`
(Body 48 (N2): `g/(2irn)`). -/
lemma kinM_smul_vert (hr : r ≠ 0) (a b c : Sgn) (p q : Mode) (A B : V3) :
    kinM r τ a b c p q • vert p q (hel a p A) (hel b q B) =
      kinSym r τ a b c p q • leray (p + q) (cross (hel a p A) (hel b q B)) := by
  by_cases h : (p + q) 2 = 0 ∧ p 2 ≠ 0
  · by_cases hΦ : Phi a b c p q = 0
    · have h' : ¬ ((p + q) 2 = 0 ∧ p 2 ≠ 0 ∧ Phi a b c p q ≠ 0) := fun h'' => h''.2.2 hΦ
      rw [kinM, kinSym, ite_eq_left h, ite_eq_right h', hΦ]
      simp
    · have h' : (p + q) 2 = 0 ∧ p 2 ≠ 0 ∧ Phi a b c p q ≠ 0 := ⟨h.1, h.2, hΦ⟩
      rw [vert_hel_slow_out a b c p q A B h.1 h.2, smul_smul, kinM, kinSym, ite_eq_left h,
        ite_eq_left h']
      congr 1
      have hp : (p 2 : ℂ) ≠ 0 := by exact_mod_cast h.2
      have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
      have hΦ' : (Phi a b c p q : ℂ) ≠ 0 := by exact_mod_cast hΦ
      push_cast
      field_simp
  · have h' : ¬ ((p + q) 2 = 0 ∧ p 2 ≠ 0 ∧ Phi a b c p q ≠ 0) := fun h'' => h ⟨h''.1, h''.2.1⟩
    rw [kinM, kinSym, ite_eq_right h, ite_eq_right h']
    simp

lemma norm_phaseM (τ : ℝ) (a b c : Sgn) (p q : Mode) : ‖phaseM τ a b c p q‖ = 1 := by
  rw [phaseM, mul_comm, Complex.norm_exp_ofReal_mul_I]

/-- The kinetic symbol is bounded by `1/(2q)`: no small divisors (`|p₃| ≥ 1`). -/
lemma norm_kinSym_le (a b c : Sgn) (p q : Mode) :
    ‖kinSym r τ a b c p q‖ ≤ 1 / (2 * |r|) := by
  unfold kinSym
  split_ifs with h
  · have hp : (1 : ℝ) ≤ |(p 2 : ℝ)| := by exact_mod_cast Int.one_le_abs h.2.1
    rw [norm_div, norm_phaseM, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, abs_mul]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2, mul_one]
    by_cases hr : r = 0
    · simp [hr]
    · have hr' : 0 < |r| := abs_pos.mpr hr
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
  · simp

/-- `‖vertex/(irΦ)‖ ≤ (1/(2q)) ‖H_a A‖ ‖H_b B‖` on every triad. -/
lemma norm_kinM_smul_vert_le (hr : r ≠ 0) (a b c : Sgn) (p q : Mode) (A B : V3) :
    ‖kinM r τ a b c p q • vert p q (hel a p A) (hel b q B)‖ ≤
      1 / (2 * |r|) * (‖hel a p A‖ * ‖hel b q B‖) := by
  rw [kinM_smul_vert hr, norm_smul]
  refine mul_le_mul (norm_kinSym_le a b c p q) ?_ (norm_nonneg _) (by positivity)
  exact (norm_leray_le _ _).trans (norm_cross_le _ _)

/-! ### (N3): pointwise bounds and summability of the primitive -/

/-- (N3): the triad summand of `N(f,g)_k` at `p` is at most `(2/q) ‖f_p‖ ‖g_{k−p}‖`. -/
lemma norm_kinN_term_le (hr : r ≠ 0) (f g : Field) (k p : Mode) :
    ‖∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, kinM r τ a b c p (k - p) •
        hel c k (vert p (k - p) (hel a p (f p)) (hel b (k - p) (g (k - p))))‖ ≤
      2 / |r| * (‖f p‖ * ‖g (k - p)‖) := by
  have h := norm_sum3_le (fun a b c => kinM r τ a b c p (k - p) •
      hel c k (vert p (k - p) (hel a p (f p)) (hel b (k - p) (g (k - p)))))
    (κ := 1 / (2 * |r|)) (by positivity) p (k - p) (f p) (g (k - p)) fun a b c => by
      rw [← hel_smul]
      exact (norm_hel_le _ _ _).trans (norm_kinM_smul_vert_le hr a b c p (k - p) (f p) (g (k - p)))
  refine h.trans (le_of_eq ?_)
  ring

lemma summable_kinN_term (hr : r ≠ 0) {f g : Field} (hf : Summable fun k => ‖f k‖ ^ 2)
    (hg : Summable fun k => ‖g k‖ ^ 2) (k : Mode) :
    Summable fun p => ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, kinM r τ a b c p (k - p) •
      hel c k (vert p (k - p) (hel a p (f p)) (hel b (k - p) (g (k - p)))) :=
  Summable.of_norm_bounded ((convR_le_of_l2 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    hf hg k).1.mul_left (2 / |r|)) (norm_kinN_term_le hr f g k)

/-- Pointwise (N3): `‖N(f,g)_k‖ ≤ (2/q) ∑_p ‖f_p‖ ‖g_{k−p}‖`. -/
lemma norm_kinN_le (hr : r ≠ 0) {f g : Field} (hf : Summable fun k => ‖f k‖ ^ 2)
    (hg : Summable fun k => ‖g k‖ ^ 2) (k : Mode) :
    ‖kinN r τ f g k‖ ≤ 2 / |r| * ∑' p, ‖f p‖ * ‖g (k - p)‖ := by
  rw [kinN, Qm, ← tsum_mul_left]
  exact tsum_of_norm_bounded ((convR_le_of_l2 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    hf hg k).1.mul_left (2 / |r|)).hasSum (norm_kinN_term_le hr f g k)

/-- Pointwise Cauchy–Schwarz: `‖N(f,g)_k‖ ≤ (2/q) ‖f‖_{ℓ²} ‖g‖_{ℓ²}` (the "fixed-slow-output
Cauchy" of the TeX, before the slow test is summed). -/
lemma norm_kinN_le_l2 (hr : r ≠ 0) {f g : Field} (hf : Summable fun k => ‖f k‖ ^ 2)
    (hg : Summable fun k => ‖g k‖ ^ 2) (k : Mode) :
    ‖kinN r τ f g k‖ ≤
      2 / |r| * (Real.sqrt (∑' k, ‖f k‖ ^ 2) * Real.sqrt (∑' k, ‖g k‖ ^ 2)) :=
  (norm_kinN_le hr hf hg k).trans (mul_le_mul_of_nonneg_left
    (convR_le_of_l2 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hf hg k).2
    (by positivity))

/-! ### Structure of the primitive -/

lemma kinN_zero_mode (f g : Field) : kinN r τ f g 0 = 0 := by
  simp [kinN, Qm, hel_zero_mode]

/-- `N(f,g)` is slow: it vanishes on fast outputs. -/
lemma kinN_fast (f g : Field) {k : Mode} (hk : k 2 ≠ 0) : kinN r τ f g k = 0 := by
  simp only [kinN, Qm]
  rw [← tsum_zero]
  refine tsum_congr fun p => ?_
  simp [kinM, hk]

lemma PiS_kinN (f g : Field) : PiS (kinN r τ f g) = kinN r τ f g := by
  funext k
  by_cases hk : k 2 = 0
  · rw [PiS_apply_slow _ hk]
  · rw [PiS_apply_fast _ hk, kinN_fast f g hk]

/-- The pairing with a fixed mode, as a continuous linear map. -/
private def dotL (k : Mode) : V3 →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => dotM v k, map_add' := fun a b => dotM_add a b k,
      map_smul' := fun c a => dotM_smul c a k }

/-- `N(f,g)` is solenoidal. -/
lemma kinN_sol (hr : r ≠ 0) {f g : Field} (hf : Summable fun k => ‖f k‖ ^ 2)
    (hg : Summable fun k => ‖g k‖ ^ 2) : IsSolenoidal (kinN r τ f g) := fun k => by
  have h := (dotL k).map_tsum (summable_kinN_term (τ := τ) hr hf hg k)
  change dotL k (kinN r τ f g k) = 0
  rw [kinN, Qm, h]
  simp [dotL, dotM_add, dotM_smul, dotM_hel]

lemma kinM_symm (a b c : Sgn) (p q : Mode) : kinM r τ a b c p q = kinM r τ b a c q p := by
  have hpq : (p + q) 2 = 0 ∧ p 2 ≠ 0 ↔ (q + p) 2 = 0 ∧ q 2 ≠ 0 := by
    rw [add_comm]
    constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, fun h3 => h2 ?_⟩ <;>
      simp only [Pi.add_apply] at h1 <;> omega
  unfold kinM
  rw [Phi_symm' a b c p q, phaseM_symm τ a b c p q]
  by_cases h : (p + q) 2 = 0 ∧ p 2 ≠ 0
  · rw [ite_eq_left h, ite_eq_left (hpq.1 h)]
  · rw [ite_eq_right h, ite_eq_right (hpq.not.1 h)]

/-- `N(f,g) = N(g,f)` (both advective orders are retained symmetrically). -/
lemma kinN_comm (f g : Field) : kinN r τ f g = kinN r τ g f := by
  funext k
  simp only [kinN, Qm]
  refine ((Equiv.subLeft k).tsum_eq _).symm.trans (tsum_congr fun p => ?_)
  simp only [Equiv.subLeft_apply, sub_sub_cancel]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun c _ => ?_
  rw [kinM_symm a b c, vert_comm]

/-- (N3) integrated by Young `ℓ¹ * ℓ² ⊂ ℓ²`: `‖N(f,g)‖₀ ≤ (2/q) 𝒜(f) ‖g‖_{ℓ²}`. -/
lemma hnorm_kinN_le (hr : r ≠ 0) {f g : Field} (hf : Summable fun k => ‖f k‖)
    (hg : Summable fun k => ‖g k‖ ^ 2) :
    InH 0 (kinN r τ f g) ∧
      hnorm 0 (kinN r τ f g) ≤ 2 / |r| * (wiener f * Real.sqrt (∑' k, ‖g k‖ ^ 2)) := by
  obtain ⟨-, h2, h3⟩ := young_l1_l2 (a := fun k => ‖f k‖) (b := fun k => ‖g k‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hf hg
  have hf2 := summable_sq_of_summable hf
  have hpt : ∀ k, ‖kinN r τ f g k‖ ^ 2 ≤
      (2 / |r|) ^ 2 * convR (fun k => ‖f k‖) (fun k => ‖g k‖) k ^ 2 := fun k => by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_kinN_le hr hf2 hg k) 2
  have hs : Summable fun k => ‖kinN r τ f g k‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun k => sq_nonneg _) hpt (h2.mul_left _)
  refine ⟨inH_zero_of_summable hs, ?_⟩
  have hg0 : 0 ≤ ∑' k, ‖g k‖ ^ 2 := tsum_nonneg fun k => sq_nonneg _
  rw [hnorm_zero_eq (kinN_zero_mode f g)]
  calc Real.sqrt (∑' k, ‖kinN r τ f g k‖ ^ 2)
      ≤ Real.sqrt ((2 / |r|) ^ 2 * ∑' k, convR (fun k => ‖f k‖) (fun k => ‖g k‖) k ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        rw [← tsum_mul_left]
        exact hs.tsum_le_tsum hpt (h2.mul_left _)
    _ ≤ Real.sqrt ((2 / |r|) ^ 2 * ((∑' k, ‖f k‖) ^ 2 * ∑' k, ‖g k‖ ^ 2)) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h3 (by positivity))
    _ = 2 / |r| * (wiener f * Real.sqrt (∑' k, ‖g k‖ ^ 2)) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
          Real.sqrt_sq (by positivity), Real.sqrt_sq (tsum_nonneg fun _ => norm_nonneg _)]
        rfl

/-- The fixed-slow-output Cauchy bound (TeX, after eq. quant-kinetic-floor: "use fixed-slow-output
Cauchy … before summing the slow test"): `|⟨Z, N(f,g)⟩| ≤ (2/q) 𝒜(Z) ‖f‖_{ℓ²} ‖g‖_{ℓ²}`. -/
lemma abs_pair_kinN_le (hr : r ≠ 0) {f g Z : Field} (hZ : Summable fun k => ‖Z k‖)
    (hf : Summable fun k => ‖f k‖ ^ 2) (hg : Summable fun k => ‖g k‖ ^ 2) :
    |pair 0 Z (kinN r τ f g)| ≤
      2 / |r| * (wiener Z * (Real.sqrt (∑' k, ‖f k‖ ^ 2) * Real.sqrt (∑' k, ‖g k‖ ^ 2))) := by
  set C := 2 / |r| * (Real.sqrt (∑' k, ‖f k‖ ^ 2) * Real.sqrt (∑' k, ‖g k‖ ^ 2)) with hC
  have hs : HasSum (fun k => ‖Z k‖ * C) (wiener Z * C) := hZ.hasSum.mul_right C
  rw [pair, ← Real.norm_eq_abs, show 2 / |r| * (wiener Z * (Real.sqrt (∑' k, ‖f k‖ ^ 2) *
    Real.sqrt (∑' k, ‖g k‖ ^ 2))) = wiener Z * C by rw [hC]; ring]
  refine tsum_of_norm_bounded hs fun k => ?_
  have h1 : sobWeight 0 k ≤ 1 := by
    unfold sobWeight
    split_ifs <;> simp
  have h2 : |(inner ℂ (Z k) (kinN r τ f g k)).re| ≤ ‖Z k‖ * ‖kinN r τ f g k‖ :=
    (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
  have h3 := norm_kinN_le_l2 (τ := τ) hr hf hg k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sobWeight_nonneg 0 k)]
  calc sobWeight 0 k * |(inner ℂ (Z k) (kinN r τ f g k)).re|
      ≤ 1 * (‖Z k‖ * ‖kinN r τ f g k‖) := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
    _ ≤ ‖Z k‖ * C := by rw [one_mul]; exact mul_le_mul_of_nonneg_left h3 (norm_nonneg _)

/-! ### The triad expansion of `⟨Z, N(X,Y)⟩` -/

/-- Mirror of `inner_Qm` for the kinetic multiplier (which is not `Bdd`):
`⟨Z_k, N(X,Y)_k⟩ = ∑_p tripT (kinM) X Y Z p (k − p)` for real `Z` and `ℓ²` inputs. -/
lemma inner_kinN (hr : r ≠ 0) {X Y Z : Field} (hZ : IsReal Z)
    (hX : Summable fun k => ‖X k‖ ^ 2) (hY : Summable fun k => ‖Y k‖ ^ 2) (k : Mode) :
    inner ℂ (Z k) (kinN r τ X Y k) = ∑' p, tripT (kinM r τ) X Y Z p (k - p) := by
  rw [kinN, Qm, inner_tsum _ (summable_kinN_term hr hX hY k)]
  refine tsum_congr fun p => ?_
  have hk : p + (k - p) = k := by abel
  simp only [inner_sum, inner_smul_right, tripT, hk, inner_hel_real hZ]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  have := bd_hel_vert c p (k - p) (hel a p (X p)) (hel b (k - p) (Y (k - p))) (Z (-k))
  rw [hk] at this
  rw [this]

/-- The triad summand of `⟨Z, N(X,Y)⟩` is at most `(2/q) ‖X_p‖ ‖Y_q‖ ‖Z_{−(p+q)}‖`. -/
lemma norm_tripT_kinM_le (hr : r ≠ 0) (X Y Z : Field) (p q : Mode) :
    ‖tripT (kinM r τ) X Y Z p q‖ ≤ 2 / |r| * (‖X p‖ * ‖Y q‖ * ‖Z (-(p + q))‖) := by
  have h := norm_sum3_le (fun a b c => kinM r τ a b c p q *
      tau p q (hel a p (X p)) (hel b q (Y q)) (hel c (-(p + q)) (Z (-(p + q)))))
    (κ := 1 / (2 * |r|) * ‖Z (-(p + q))‖) (by positivity) p q (X p) (Y q) fun a b c => by
      rw [← bd_hel_vert, ← bd_smul_right]
      refine (norm_bd_le _ _).trans ?_
      have h1 := norm_hel_le c (-(p + q)) (Z (-(p + q)))
      have h2 := norm_kinM_smul_vert_le (τ := τ) hr a b c p q (X p) (Y q)
      calc _ ≤ ‖Z (-(p + q))‖ * (1 / (2 * |r|) * (‖hel a p (X p)‖ * ‖hel b q (Y q)‖)) :=
            mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
        _ = _ := by ring
  refine h.trans (le_of_eq ?_)
  ring

/-! ### Reality and admissibility -/

/-- The kinetic multiplier respects reality. -/
lemma kinM_real : (kinM r τ).Real := fun a b c p q => by
  have hind : (-p + -q) 2 = 0 ∧ (-p) 2 ≠ 0 ↔ (p + q) 2 = 0 ∧ p 2 ≠ 0 := by
    simp only [Pi.add_apply, Pi.neg_apply, neg_eq_zero, ne_eq]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩
  unfold kinM
  by_cases h : (p + q) 2 = 0 ∧ p 2 ≠ 0
  · rw [ite_eq_left (hind.2 h), ite_eq_left h, map_div₀, ← phaseM_real τ a b c p q, Phi_neg']
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  · rw [ite_eq_right (hind.not.2 h), ite_eq_right h, map_zero]

private lemma conjV_add' (a b : V3) : conjV (a + b) = conjV a + conjV b := by
  ext i; simp [conjV]

private lemma conjV_smul' (c : ℂ) (a : V3) : conjV (c • a) = conj c • conjV a := by
  ext i; simp [conjV]

private lemma dotM_conjV (v : V3) (k : Mode) : dotM (conjV v) (-k) = -conj (dotM v k) := by
  simp [dotM, conjV, Finset.sum_neg_distrib]

private lemma conjV_vert (p q : Mode) (A B : V3) :
    conjV (vert p q A B) = vert (-p) (-q) (conjV A) (conjV B) := by
  have h2 : conj (1 / 2 : ℂ) = 1 / 2 := by
    rw [map_div₀, map_one, Complex.conj_ofNat]
  simp only [vert, conjV_smul', conjV_leray, conjV_add', h2, map_mul, Complex.conj_I, dotM_conjV,
    neg_add]
  simp only [mul_neg, neg_mul]

/-- Conjugation as an additive map. -/
private def conjHom : V3 →+ V3 := AddMonoidHom.mk' conjV conjV_add'

private lemma continuous_conjHom : Continuous conjHom :=
  (AddMonoidHomClass.isometry_of_norm conjHom norm_conjV).continuous

/-- `N(f,g)` is real for real `ℓ²` inputs. -/
lemma kinN_real (hr : r ≠ 0) {f g : Field} (hfr : IsReal f) (hgr : IsReal g)
    (hf : Summable fun k => ‖f k‖ ^ 2) (hg : Summable fun k => ‖g k‖ ^ 2) :
    IsReal (kinN r τ f g) := fun k => by
  have hs := summable_kinN_term (τ := τ) hr hf hg k
  have h1 := hs.map_tsum conjHom continuous_conjHom
  change kinN r τ f g (-k) = conjHom (kinN r τ f g k)
  simp only [kinN, Qm]
  rw [h1, ← (Equiv.neg Mode).tsum_eq]
  refine tsum_congr fun p => ?_
  have e : -k - -p = -(k - p) := by abel
  simp only [Equiv.neg_apply, conjHom, AddMonoidHom.mk'_apply, e, Fintype.sum_bool, conjV_add',
    conjV_smul', conjV_hel, conjV_vert, kinM_real _ _ _ p (k - p), hfr p, hgr (k - p)]

/-- `Adm 2 f → Adm 2 g → Adm 0 (N(f,g))`: the primitive preserves the admissible class. -/
theorem kinN_adm (hr : r ≠ 0) {f g : Field} (hf : Adm 2 f) (hg : Adm 2 g) :
    Adm 0 (kinN r τ f g) := by
  have hf1 : Summable fun k => ‖f k‖ := summable_wiener hf.inH
  have hg2 : Summable fun k => ‖g k‖ ^ 2 := summable_norm_sq_of_inH (hg.inH.mono (by norm_num))
  exact ⟨(hnorm_kinN_le hr hf1 hg2).1, kinN_real hr hf.real hg.real (summable_sq_of_summable hf1)
    hg2, kinN_sol hr (summable_sq_of_summable hf1) hg2, kinN_zero_mode f g⟩

end OVNS

end
