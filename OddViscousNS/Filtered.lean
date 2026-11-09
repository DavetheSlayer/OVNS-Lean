import OddViscousNS.Majorant

/-! # The filtered equation: `Q_τ = R(-τ) B(R(τ)·, R(τ)·)` and `B(u,u) = ℙ((u·∇)u)`
(`Lemma lem:coef`, `Definition def:Q`, `(eq:filt)`). -/

open scoped Topology
open Filter Set

noncomputable section
namespace OVNS

variable {f g u : Field}

/-! ### Continuous linear versions of the symbols -/

/-- The Leray symbol as a continuous linear map. -/
private def lerayL (k : Mode) : V3 →L[ℂ] V3 :=
  LinearMap.toContinuousLinearMap
    { toFun := leray k, map_add' := leray_add k, map_smul' := leray_smul k }

/-- The helical projector as a continuous linear map. -/
private def helL (a : Sgn) (k : Mode) : V3 →L[ℂ] V3 :=
  LinearMap.toContinuousLinearMap
    { toFun := hel a k, map_add' := hel_add a k, map_smul' := hel_smul a k }

/-- The filter as a continuous linear map. -/
private def rotL (τ : ℝ) (k : Mode) : V3 →L[ℂ] V3 :=
  LinearMap.toContinuousLinearMap
    { toFun := rot τ k, map_add' := rot_add τ k, map_smul' := rot_smul τ k }

/-! ### Bilinearity of the vertex -/

private lemma vert_add_left (p q : Mode) (A A' B : V3) :
    vert p q (A + A') B = vert p q A B + vert p q A' B := by
  simp only [vert, dotM_add, mul_add, add_smul, smul_add, leray_add]
  abel

private lemma vert_add_right (p q : Mode) (A B B' : V3) :
    vert p q A (B + B') = vert p q A B + vert p q A B' := by
  simp only [vert, dotM_add, mul_add, add_smul, smul_add, leray_add]
  abel

private lemma vert_smul_left (p q : Mode) (c : ℂ) (A B : V3) :
    vert p q (c • A) B = c • vert p q A B := by
  have h : (Complex.I * dotM (c • A) q) • B + (Complex.I * dotM B p) • (c • A) =
      c • ((Complex.I * dotM A q) • B + (Complex.I * dotM B p) • A) := by
    rw [dotM_smul]
    module
  rw [vert, vert, h, leray_smul, smul_comm]

private lemma vert_smul_right (p q : Mode) (c : ℂ) (A B : V3) :
    vert p q A (c • B) = c • vert p q A B := by
  have h : (Complex.I * dotM A q) • (c • B) + (Complex.I * dotM (c • B) p) • A =
      c • ((Complex.I * dotM A q) • B + (Complex.I * dotM B p) • A) := by
    rw [dotM_smul]
    module
  rw [vert, vert, h, leray_smul, smul_comm]

private lemma vert_comm (p q : Mode) (A B : V3) : vert p q A B = vert q p B A := by
  rw [vert, vert, add_comm p q, add_comm ((Complex.I * dotM A q) • B)]

private lemma leray_vert (k p : Mode) (A B : V3) :
    leray k (vert p (k - p) A B) = vert p (k - p) A B := by
  simp only [vert, add_sub_cancel, leray_smul, leray_idem]

/-- The helical expansion of the vertex, with arbitrary coefficients. -/
private lemma sum_hel_vert (z x y : Sgn → ℂ) (k p q : Mode) (A B : V3) :
    ∑ a, ∑ b, ∑ c, (z c * (x a * y b)) • hel c k (vert p q (hel a p A) (hel b q B)) =
      ∑ c, z c • hel c k (vert p q (∑ a, x a • hel a p A) (∑ b, y b • hel b q B)) := by
  simp only [Fintype.sum_bool, vert_add_left, vert_add_right, vert_smul_left, vert_smul_right,
    hel_add, hel_smul]
  module

/-! ### Summability of the triad series -/

private lemma summable_sq_of_MZ (hf : MZ 2 f) : Summable fun k => ‖f k‖ ^ 2 := by
  have h : InH 0 f := hf.inH.mono (by norm_num)
  refine Summable.congr h fun k => ?_
  by_cases hk : k = 0
  · subst hk
    simp [sobWeight, hf.mean]
  · simp [sobWeight, hk]

private lemma summable_absk_sq_of_MZ (hf : MZ 2 f) :
    Summable fun k => (absk k * ‖f k‖) ^ 2 := by
  have h : InH 1 f := hf.inH.mono (by norm_num)
  refine Summable.congr h fun k => ?_
  by_cases hk : k = 0
  · subst hk
    simp [sobWeight, hf.mean]
  · simp only [sobWeight, hk, ite_false, mul_pow]
    norm_num

private lemma summable_left (hf : MZ 2 f) (hg : MZ 2 g) (k : Mode) :
    Summable fun p => ‖f p‖ * (absk (k - p) * ‖g (k - p)‖) :=
  (convR_le_of_l2 (a := fun p => ‖f p‖) (b := fun q => absk q * ‖g q‖) (fun _ => norm_nonneg _)
    (fun q => mul_nonneg (absk_nonneg q) (norm_nonneg _)) (summable_sq_of_MZ hf)
    (summable_absk_sq_of_MZ hg) k).1

private lemma summable_right (hf : MZ 2 f) (hg : MZ 2 g) (k : Mode) :
    Summable fun p => (absk p * ‖f p‖) * ‖g (k - p)‖ :=
  (convR_le_of_l2 (a := fun p => absk p * ‖f p‖) (b := fun q => ‖g q‖)
    (fun q => mul_nonneg (absk_nonneg q) (norm_nonneg _)) (fun _ => norm_nonneg _)
    (summable_absk_sq_of_MZ hf) (summable_sq_of_MZ hg) k).1

/-- The physical triad series converges. -/
private lemma summable_vert (hf : MZ 2 f) (hg : MZ 2 g) (k : Mode) :
    Summable fun p => vert p (k - p) (f p) (g (k - p)) := by
  refine Summable.of_norm_bounded ((summable_left hf hg k).add (summable_right hf hg k)) ?_
  intro p
  refine (norm_vert_le₁ p (k - p) (f p) (g (k - p))).trans ?_
  have h1 : 0 ≤ absk (k - p) * (‖f p‖ * ‖g (k - p)‖) :=
    mul_nonneg (absk_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have h2 : 0 ≤ absk p * (‖f p‖ * ‖g (k - p)‖) :=
    mul_nonneg (absk_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  nlinarith [h1, h2]

/-- The advective series converges. -/
private lemma summable_advect (hf : MZ 2 f) (hg : MZ 2 g) (k : Mode) :
    Summable fun p => (Complex.I * dotM (f p) (k - p)) • g (k - p) := by
  refine Summable.of_norm_bounded (summable_left hf hg k) fun p => ?_
  rw [norm_smul, norm_mul, Complex.norm_I, one_mul]
  calc ‖dotM (f p) (k - p)‖ * ‖g (k - p)‖
      ≤ (‖f p‖ * absk (k - p)) * ‖g (k - p)‖ :=
        mul_le_mul_of_nonneg_right (norm_dotM_le _ _) (norm_nonneg _)
    _ = ‖f p‖ * (absk (k - p) * ‖g (k - p)‖) := by ring

/-- The symmetric form on the diagonal is the original convection. -/
theorem Bsym_self (hu : MZ 2 u) : Bsym u u = convec u := by
  funext k
  have hA : HasSum (fun p => (Complex.I * dotM (u p) (k - p)) • u (k - p)) (advect u u k) :=
    (summable_advect hu hu k).hasSum
  have hB : HasSum (fun p => (Complex.I * dotM (u (k - p)) p) • u p) (advect u u k) := by
    have e : (fun p => (Complex.I * dotM (u (k - p)) p) • u p) =
        (fun p => (Complex.I * dotM (u p) (k - p)) • u (k - p)) ∘ Equiv.subLeft k := by
      funext p
      simp only [Function.comp, Equiv.subLeft_apply, sub_sub_cancel]
    rw [e]
    exact (Equiv.subLeft k).hasSum_iff.mpr hA
  have hs := ((lerayL k).hasSum (hA.add hB)).const_smul (1 / 2 : ℂ)
  have e : Bsym u u k = ∑' p, (1 / 2 : ℂ) • lerayL k ((Complex.I * dotM (u p) (k - p)) • u (k - p) +
      (Complex.I * dotM (u (k - p)) p) • u p) := by
    refine tsum_congr fun p => ?_
    simp only [vert, add_sub_cancel]
    rfl
  rw [e, hs.tsum_eq]
  change (1 / 2 : ℂ) • leray k (advect u u k + advect u u k) = leray k (advect u u k)
  rw [leray_add, ← two_smul ℂ, smul_smul]
  norm_num

private lemma leray_of_adm {s : ℝ} (hf : Adm s f) (k : Mode) : leray k (f k) = f k := by
  by_cases hk : k = 0
  · subst hk
    simp [leray, hf.mean]
  · exact leray_of_perp hk (hf.sol k)

/-- For solenoidal inputs, the helical sum with multiplier one is `Bsym`. -/
theorem Qm_one (hf : Adm 2 f) (hg : Adm 2 g) : Qm (fun _ _ _ _ _ => 1) f g = Bsym f g := by
  funext k
  refine tsum_congr fun p => ?_
  have h := sum_hel_vert (fun _ => 1) (fun _ => 1) (fun _ => 1) k p (k - p) (f p) (g (k - p))
  simp only [mul_one, one_smul, hel_sum] at h ⊢
  rw [h, leray_of_adm hf, leray_of_adm hg, leray_vert]

/-- The phased form is the conjugated convection. -/
theorem Qphase_eq (τ : ℝ) (hf : Adm 2 f) (hg : Adm 2 g) :
    Qphase τ f g = rotF (-τ) (Bsym (rotF τ f) (rotF τ g)) := by
  funext k
  have hs := summable_vert (hf.rotF τ).mz (hg.rotF τ).mz k
  change Qm (phaseM τ) f g k = rot (-τ) k (Bsym (rotF τ f) (rotF τ g) k)
  rw [Bsym, show rot (-τ) k _ = rotL (-τ) k _ from rfl, (rotL (-τ) k).map_tsum hs]
  refine tsum_congr fun p => ?_
  refine Eq.trans ?_ (sum_hel_vert (fun c => Complex.exp (Complex.I * ((-τ) * lam c k : ℝ)))
    (fun a => Complex.exp (Complex.I * (τ * lam a p : ℝ)))
    (fun b => Complex.exp (Complex.I * (τ * lam b (k - p) : ℝ))) k p (k - p) (f p) (g (k - p)))
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  congr 1
  simp only [phaseM, Phi, add_sub_cancel, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Bilinearity / symmetry of `Qm`. -/
theorem Qm_comm_of_symm {m : Mult} (hm : ∀ a b c p q, m a b c p q = m b a c q p)
    (_hf : MZ 2 f) (_hg : MZ 2 g) : Qm m f g = Qm m g f := by
  funext k
  refine ((Equiv.subLeft k).tsum_eq _).symm.trans (tsum_congr fun p => ?_)
  simp only [Equiv.subLeft_apply, sub_sub_cancel]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun c _ => ?_
  rw [hm a b c, vert_comm]

private lemma Phi_symm (a b c : Sgn) (p q : Mode) : Phi a b c p q = Phi b a c q p := by
  simp only [Phi, add_comm q p]
  ring

lemma phaseM_symm (τ : ℝ) (a b c : Sgn) (p q : Mode) : phaseM τ a b c p q = phaseM τ b a c q p := by
  simp only [phaseM, Phi_symm a b c p q]
lemma resM_symm (a b c : Sgn) (p q : Mode) : resM a b c p q = resM b a c q p := by
  simp only [resM, Phi_symm a b c p q]

/-! ### The derivative of the filter along a curve -/

private lemma oddSym_add (k : Mode) (a b : V3) : oddSym k (a + b) = oddSym k a + oddSym k b := by
  simp only [oddSym, smul_add, cross_add_right, leray_add]

private lemma oddSym_smul (k : Mode) (c : ℂ) (a : V3) : oddSym k (c • a) = c • oddSym k a := by
  simp only [oddSym, smul_comm _ c a, cross_smul_right, leray_smul]

/-- The filter expands into two phases. -/
private lemma rot_bool (τ : ℝ) (k : Mode) (v : V3) : rot τ k v =
    Complex.exp (Complex.I * (τ * lam true k : ℝ)) • hel true k v +
      Complex.exp (Complex.I * (τ * lam false k : ℝ)) • hel false k v := by
  rw [rot, Fintype.sum_bool]

/-- The filter acts on a helical component by its phase. -/
private lemma rot_hel (τ : ℝ) (a : Sgn) (k : Mode) (v : V3) :
    rot τ k (hel a k v) = Complex.exp (Complex.I * (τ * lam a k : ℝ)) • hel a k v := by
  rw [rot_bool]
  cases a
  · rw [hel_idem, hel_orth (by simp), smul_zero, zero_add]
  · rw [hel_idem, hel_orth (by simp), smul_zero, add_zero]

/-- On transverse vectors the filter commutes with the odd symbol. -/
private lemma rot_oddSym (τ : ℝ) (k : Mode) {w : V3} (hw : dotM w k = 0) :
    rot τ k (oddSym k w) = oddSym k (rot τ k w) := by
  by_cases hk : k = 0
  · subst hk
    simp [rot, hel_zero_mode, oddSym, leray]
  have hw' : hel true k w + hel false k w = w := by
    rw [← Fintype.sum_bool (fun a => hel a k w), hel_sum, leray_of_perp hk hw]
  have e1 : oddSym k w = (Complex.I * (lam true k : ℝ)) • hel true k w +
      (Complex.I * (lam false k : ℝ)) • hel false k w := by
    conv_lhs => rw [← hw', oddSym_add, oddSym_hel, oddSym_hel]
  rw [e1, rot_bool τ k w, rot_add, rot_smul, rot_smul, rot_hel, rot_hel, oddSym_add, oddSym_smul,
    oddSym_smul, oddSym_hel, oddSym_hel]
  module

/-- The product rule for `s ↦ R(ρ s) w(s)`. -/
private lemma hasDerivWithinAt_rot_comp (ρ : ℝ) (k : Mode) {w : ℝ → V3} {w' : V3} {S : Set ℝ}
    {t : ℝ} (hw : HasDerivWithinAt w w' S t) :
    HasDerivWithinAt (fun s => rot (ρ * s) k (w s))
      ((ρ : ℂ) • oddSym k (rot (ρ * t) k (w t)) + rot (ρ * t) k w') S t := by
  have key : ∀ a : Sgn, HasDerivWithinAt
      (fun s : ℝ => Complex.exp (Complex.I * ((ρ * s) * lam a k : ℝ)) • hel a k (w s))
      (Complex.exp (Complex.I * ((ρ * t) * lam a k : ℝ)) • hel a k w' +
        (Complex.exp (Complex.I * ((ρ * t) * lam a k : ℝ)) * (Complex.I * (ρ * lam a k : ℝ))) •
          hel a k (w t)) S t := by
    intro a
    have h1 : HasDerivAt (fun s : ℝ => Complex.I * (((ρ * s) * lam a k : ℝ) : ℂ))
        (Complex.I * (ρ * lam a k : ℝ)) t := by
      have h0 := (((hasDerivAt_id t).const_mul ρ).mul_const (lam a k)).ofReal_comp
      simpa using h0.const_mul Complex.I
    have h2 : HasDerivWithinAt (fun s => hel a k (w s)) (hel a k w') S t :=
      ((helL a k).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t hw
    exact h1.cexp.hasDerivWithinAt.smul h2
  have e : (fun s => rot (ρ * s) k (w s)) = fun s : ℝ =>
      Complex.exp (Complex.I * ((ρ * s) * lam true k : ℝ)) • hel true k (w s) +
        Complex.exp (Complex.I * ((ρ * s) * lam false k : ℝ)) • hel false k (w s) := by
    funext s
    rw [rot_bool]
  rw [e]
  refine ((key true).fun_add (key false)).congr_deriv ?_
  rw [rot_bool (ρ * t) k (w t), rot_bool (ρ * t) k w', oddSym_add, oddSym_smul, oddSym_smul,
    oddSym_hel, oddSym_hel]
  push_cast
  module

private lemma sol_sub {x y : Field} (hx : IsSolenoidal x) (hy : IsSolenoidal y) :
    IsSolenoidal (x - y) := by
  intro k
  have h : dotM ((x - y) k) k = dotM (x k) k - dotM (y k) k := by
    simp [dotM, sub_mul, Finset.sum_sub_distrib]
  rw [h, hx k, hy k, sub_zero]

/-- Continuity in `H²` survives a continuously moving filter. -/
private lemma tendsto_rotF_comp {w : ℝ → Field} {c : ℝ → ℝ} (hc : Continuous c)
    (hadm : ∀ t, 0 ≤ t → Adm 2 (w t)) {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    (hw : Tendsto (fun t => hnorm 2 (w t - w t₀)) (𝓝[Ici 0] t₀) (𝓝 0)) :
    Tendsto (fun t => hnorm 2 (rotF (c t) (w t) - rotF (c t₀) (w t₀))) (𝓝[Ici 0] t₀) (𝓝 0) := by
  have h0 := hadm t₀ ht₀
  have h1 : Tendsto (fun t => hnorm 2 (rotF (c t) (w t₀) - rotF (c t₀) (w t₀))) (𝓝[Ici 0] t₀)
      (𝓝 0) :=
    ((tendsto_hnorm_rotF h0.inH h0.sol (c t₀)).comp (hc.tendsto t₀)).mono_left nhdsWithin_le_nhds
  have h2 := hw.add h1
  rw [add_zero] at h2
  refine squeeze_zero' (.of_forall fun t => hnorm_nonneg _ _) ?_ h2
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ha := hadm t ht
  have e : rotF (c t) (w t) - rotF (c t₀) (w t₀) = rotF (c t) (w t - w t₀) +
      (rotF (c t) (w t₀) - rotF (c t₀) (w t₀)) := by
    rw [rotF_sub]
    abel
  rw [e]
  have h3 : InH 2 (rotF (c t) (w t - w t₀)) := by
    rw [rotF_sub]
    exact (ha.rotF _).inH.sub (h0.rotF _).inH
  refine (hnorm_add_le h3 ((h0.rotF _).inH.sub (h0.rotF _).inH)).trans
    (add_le_add (le_of_eq ?_) le_rfl)
  exact hnorm_rotF _ (sol_sub ha.sol h0.sol)

/-- Unfiltering: a global filtered solution gives a normalized original strong solution. -/
theorem IsHeatSol.unfilter {r : ℝ} {y : ℝ → Field} (hg : Adm 2 g)
    (hy : IsHeatSol (filtN r 0) (filtG r 0 g) ⊤ y) :
    IsStrongSolution 1 r g (y 0) (fun t => rotF (r * t) (y t)) := by
  have hadm : ∀ t, 0 ≤ t → Adm 2 (y t) := fun t ht => hy.adm t ht ENNReal.ofReal_lt_top
  refine ⟨?_, fun t ht => (hadm t ht).rotF _, fun t₀ ht₀ => ?_, fun k t ht => ?_⟩
  · funext k
    simp only [mul_zero]
    change rot 0 k (y 0 k) = y 0 k
    rw [rot_zero_time, leray_of_adm (hadm 0 le_rfl)]
  · exact tendsto_rotF_comp (c := fun t => r * t) (by fun_prop) hadm ht₀
      (hy.cont t₀ ht₀ ENNReal.ofReal_lt_top)
  · have ha := hadm t ht
    have h := hasDerivWithinAt_rot_comp r k (hy.mode k t ht ENNReal.ofReal_lt_top)
    simp only [filtN, filtG, add_zero] at h
    refine h.congr_deriv ?_
    have hQ : Qphase (r * t) (y t) (y t) = rotF (-(r * t)) (convec (rotF (r * t) (y t))) := by
      rw [Qphase_eq _ ha ha, Bsym_self (ha.rotF _).mz]
    have hC : rot (r * t) k (rotF (-(r * t)) (convec (rotF (r * t) (y t))) k) =
        convec (rotF (r * t) (y t)) k := by
      change rot (r * t) k (rot (-(r * t)) k _) = _
      rw [rot_rot, add_neg_cancel, rot_zero_time, convec, leray_idem]
    have hG : rot (r * t) k (rotF (-(r * t)) g k) = g k := by
      change rot (r * t) k (rot (-(r * t)) k _) = _
      rw [rot_rot, add_neg_cancel, rot_zero_time, leray_of_adm hg]
    rw [hQ, rot_add, rot_sub, rot_smul, hC, hG]
    change _ = _ • rot (r * t) k (y t k) + _ • oddSym k (rot (r * t) k (y t k)) - _ + _
    simp only [one_mul]
    module

/-- Filtering: a normalized original strong solution gives a global filtered solution. -/
theorem IsStrongSolution.filter {r : ℝ} {v₀ : Field} {v : ℝ → Field} (_hg : Adm 2 g)
    (hv : IsStrongSolution 1 r g v₀ v) :
    IsHeatSol (filtN r 0) (filtG r 0 g) ⊤ (fun t => rotF (-(r * t)) (v t)) := by
  refine ⟨fun t ht _ => (hv.adm t ht).rotF _, fun t₀ ht₀ _ => ?_, fun k t ht _ => ?_⟩
  · exact tendsto_rotF_comp (c := fun t => -(r * t)) (by fun_prop) hv.adm ht₀ (hv.cont t₀ ht₀)
  · have ha := hv.adm t ht
    have h := hasDerivWithinAt_rot_comp (-r) k (hv.mode k t ht)
    simp only [neg_mul] at h
    simp only [filtN, filtG, add_zero]
    refine h.congr_deriv ?_
    have hu := rotF_rotF_neg (-(r * t)) ha.sol ha.mean
    rw [neg_neg] at hu
    have hQ : Qphase (r * t) (rotF (-(r * t)) (v t)) (rotF (-(r * t)) (v t)) =
        rotF (-(r * t)) (convec (v t)) := by
      rw [Qphase_eq _ (ha.rotF _) (ha.rotF _), hu, Bsym_self ha.mz]
    rw [hQ, rot_add, rot_sub, rot_add, rot_smul, rot_smul, rot_oddSym _ _ (ha.sol k)]
    change _ + (_ + _ - rot (-(r * t)) k (convec (v t) k) + _) =
      _ • rot (-(r * t)) k (v t k) - rot (-(r * t)) k (convec (v t) k) + rot (-(r * t)) k (g k)
    simp only [one_mul]
    push_cast
    module

/-! ### Parabolic scaling -/

private lemma Adm.real_smul {s : ℝ} (c : ℝ) (hu : Adm s u) : Adm s ((c : ℂ) • u) := by
  refine ⟨hu.inH.smul c, fun k => ?_, fun k => ?_, ?_⟩
  · simp only [Pi.smul_apply, hu.real k]
    ext i
    simp [conjV]
  · change dotM ((c : ℂ) • u k) k = 0
    rw [dotM_smul, hu.sol k, mul_zero]
  · simp [hu.mean]

/-- The convection is quadratic. -/
private lemma convec_smul (c : ℂ) (w : Field) (k : Mode) :
    convec (c • w) k = c ^ 2 • convec w k := by
  have h : ∀ p, (Complex.I * dotM ((c • w) p) (k - p)) • (c • w) (k - p) =
      c ^ 2 • ((Complex.I * dotM (w p) (k - p)) • w (k - p)) := by
    intro p
    simp only [Pi.smul_apply, dotM_smul]
    module
  simp only [convec, advect, h]
  rw [tsum_const_smul'', leray_smul]

/-- One direction of the parabolic scaling, with a free dilation parameter. -/
private lemma scale_aux {ν α c : ℝ} (hc : 0 < c) {f u₀ : Field} {u : ℝ → Field}
    (h : IsStrongSolution ν α f u₀ u) :
    IsStrongSolution (c * ν) (c * α) ((c : ℂ) ^ 2 • f) ((c : ℂ) • u₀)
      (fun τ => (c : ℂ) • u (c * τ)) := by
  have hmaps : MapsTo (fun τ : ℝ => c * τ) (Ici 0) (Ici 0) := fun τ hτ => mul_nonneg hc.le hτ
  refine ⟨by simp [h.init], fun t ht => (h.adm _ (mul_nonneg hc.le ht)).real_smul c,
    fun t₀ ht₀ => ?_, fun k t ht => ?_⟩
  · have hφ : Tendsto (fun τ : ℝ => c * τ) (𝓝[Ici 0] t₀) (𝓝[Ici 0] (c * t₀)) :=
      (continuous_const.mul continuous_id).continuousWithinAt.tendsto_nhdsWithin hmaps
    have h1 := ((h.cont (c * t₀) (mul_nonneg hc.le ht₀)).comp hφ).const_mul ‖(c : ℂ)‖
    rw [mul_zero] at h1
    refine h1.congr fun t => ?_
    simp only [Function.comp, ← smul_sub, hnorm_smul]
  · have h1 := h.mode k (c * t) (mul_nonneg hc.le ht)
    have h2 : HasDerivWithinAt (fun τ : ℝ => c * τ) c (Ici 0) t := by
      simpa using ((hasDerivAt_id t).const_mul c).hasDerivWithinAt
    refine ((h1.scomp t h2 hmaps).const_smul (c : ℂ)).congr_deriv ?_
    rw [convec_smul]
    simp only [Pi.smul_apply, oddSym_smul, ← Complex.coe_smul]
    push_cast
    module

/-- Parabolic scaling between the physical and the normalized equation. -/
theorem isStrongSolution_scale {ν α : ℝ} (hν : 0 < ν) {f u₀ : Field} {u : ℝ → Field} :
    IsStrongSolution ν α f u₀ u ↔
      IsStrongSolution 1 (α / ν) (((ν ^ 2)⁻¹ : ℂ) • f) ((ν⁻¹ : ℂ) • u₀)
        (fun τ => (ν⁻¹ : ℂ) • u (τ / ν)) := by
  have hν0 : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  constructor
  · intro h
    have h' := scale_aux (c := ν⁻¹) (inv_pos.mpr hν) h
    rw [inv_mul_cancel₀ hν.ne', inv_mul_eq_div] at h'
    have e : (fun τ : ℝ => ((ν⁻¹ : ℝ) : ℂ) • u (ν⁻¹ * τ)) =
        fun τ => (ν⁻¹ : ℂ) • u (τ / ν) := by
      funext τ
      rw [inv_mul_eq_div]
      push_cast
      rfl
    rw [e] at h'
    push_cast at h'
    rwa [inv_pow] at h'
  · intro h
    have h' := scale_aux (c := ν) hν h
    have e : (fun τ : ℝ => (ν : ℂ) • (ν⁻¹ : ℂ) • u (ν * τ / ν)) = u := by
      funext τ
      rw [mul_div_cancel_left₀ _ hν.ne', smul_smul, mul_inv_cancel₀ hν0, one_smul]
    rw [mul_one, mul_div_cancel₀ _ hν.ne', smul_smul, smul_smul, mul_inv_cancel₀ hν0,
      mul_inv_cancel₀ (pow_ne_zero 2 hν0), one_smul, one_smul] at h'
    rwa [e] at h'

end OVNS
