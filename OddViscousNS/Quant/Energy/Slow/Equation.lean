import OddViscousNS.Quant.Energy.Slow.KinH1
import OddViscousNS.Quant.Energy.Slow.Tools
import OddViscousNS.Quant.Regimes.Continuation
import OddViscousNS.RefSector

/-!
# E7-F, the slow equation: the corrected slow field and its heat laws

Route `OddViscousNS_data/reports/t12_slow_fourier_route.md` (E7-F) for the slow-cap interface
`SlowCapsInterface` (`Interfaces.lean`).  Along the actual solution `x = y − ψ = S + F`
(`actual`, `Kinetic/Actual.lean`) the slow part solves
`S' = −AS − Π_S Q_{rt}(y,y) + Π_S g` (`slow_mode`), and
`Π_S Q_{rt}(y,y) = B(S,S) + Π_S Q_{rt}(F,F) + Π_S H_ψ` (`PiS_Qphase_split`, `PiS_Qphase_slow`:
on slow triads the phase vanishes, so `Π_S Q_τ(S,S) = B(S,S)`; slow–fast triads have a fast
output).  The fast–fast slow-output term `Π_S Q_{rt}(F,F)` has no `1/q` of its own: it is removed
by the **normal-form corrector** `R_S = N(F,F)` (`slowCorr`; `kinN` is the kinetic primitive of
`Kinetic/Defs.lean`, whose frozen-amplitude derivative is exactly `Π_S Q_{rt}(F,F)`,
`tripT_kinDM_eq`).  The corrected slow field `y_S = S + R_S` (`corrSlow`, TeX
eq. quant-corrected-slow) then solves the heat equation
  `y_S' = −A y_S + corrForce`,  `corrForce = corrRes − B(y_S, y_S)`,
  `corrRes = A R_S + slowRes`,  `slowRes = Π_S g − Π_S H_ψ + 2N(F',F) + B(y_S,y_S) − B(S,S)`,
where every term of `corrRes` other than the genuine slow force `Π_S g` carries a factor `1/q`
(`hnorm_slowCorr_le`, `hnorm_corrRes_le`, `corrRes_budget`): these are the slow-correction roles
18–21 of the TeX, paid by the threshold `qS` of `Main.lean`.

## Contents
* `HeatPair.map`, `HeatPair.PiH`, `HeatPair.PiV`: a mode-wise contraction (the sector
  projections) maps a `HeatPair` to a `HeatPair`.
* `hnorm_kinN_le_of_one_le`: `‖N(f,g)‖_σ ≤ (2^σ/q)(𝒜(f)‖g‖_σ + ‖f‖_σ 𝒜(g))` (`σ ≥ 1`), from the
  fixed-slow-output Cauchy bound (N3) and `product_estimate`.
* `PiS_Qphase_slow`, `PiS_Qphase_split`: the slow projection of the phased convection.
* `slowCorr`, `corrSlow`, `slowRes`, `corrRes`, `corrForce`, `slowCorrRHS`;
  `hasDerivWithinAt_slowCorr` (the mode derivative of the corrector, `ModeDeriv.lean`),
  `corrSlow_mode` (the heat-form mode equation).
* Bounds: `hnorm_slowCorr_le` (`‖R_S‖₂ ≤ 8c₄ b_F²/q`), `hnorm_corrRes_le` (the pointwise `H⁰`
  residual, `≤ φ + resPoly/q`), `hnorm_one_corrRes_le` (the pointwise `H¹` residual at a time with
  `F ∈ H³`, by `KinH1.lean`).
* `heatPair_corrSlow`, `heatPair_corrH`, `heatPair_corrV` (the heat pairs at `σ ∈ {0,1,2}`):
  `corrForce ∈ L²_t H¹` by the fast `H²` dissipation (`lintegral_corrForce_lt_top`).
* `intervalIntegrable_corrRes_sq`, `corrRes_budget` (the `L²_t H¹` residual budget of the `H²`
  barriers, `≤ 4φ² + 4` once `budgetPoly ≤ q`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS

/-! ### Mode-wise contractions of heat pairs -/

/-- Keeping the first two components, as a continuous linear map. -/
def horizL : V3 →L[ℂ] V3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 ![v 0, v 1, 0]
      map_add' := fun u v => by
        ext i
        fin_cases i <;> simp
      map_smul' := fun c v => by
        ext i
        fin_cases i <;> simp }

/-- Keeping the third component, as a continuous linear map. -/
def vertL : V3 →L[ℂ] V3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 ![0, 0, v 2]
      map_add' := fun u v => by
        ext i
        fin_cases i <;> simp
      map_smul' := fun c v => by
        ext i
        fin_cases i <;> simp }

lemma norm_horizL_le (v : V3) : ‖horizL v‖ ≤ ‖v‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  simp only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp only [horizL, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  nlinarith [sq_nonneg ‖v 2‖]

lemma norm_vertL_le (v : V3) : ‖vertL v‖ ≤ ‖v‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  simp only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp only [vertL, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]
  nlinarith [sq_nonneg ‖v 0‖, sq_nonneg ‖v 1‖]

lemma PiH_eq_horizL (u : Field) (k : Mode) :
    PiH u k = (if k 2 = 0 then horizL else 0) (u k) := by
  by_cases h : k 2 = 0 <;> simp [PiH, h, horizL]

lemma PiV_eq_vertL (u : Field) (k : Mode) :
    PiV u k = (if k 2 = 0 then vertL else 0) (u k) := by
  by_cases h : k 2 = 0 <;> simp [PiV, h, vertL]

/-- A family of mode-wise contractions `p k` maps a `HeatPair` to a `HeatPair`. -/
theorem HeatPair.map {σ a b : ℝ} {c F : ℝ → Field} (h : HeatPair σ a b c F)
    (p : Mode → V3 →L[ℂ] V3) (hp : ∀ k v, ‖p k v‖ ≤ ‖v‖) :
    HeatPair σ a b (fun t k => p k (c t k)) (fun t k => p k (F t k)) := by
  have hterm : ∀ (s : ℝ) (u : Field) (k : Mode),
      sobWeight s k * ‖p k (u k)‖ ^ 2 ≤ sobWeight s k * ‖u k‖ ^ 2 := fun s u k =>
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hp k _) 2) (sobWeight_nonneg s k)
  refine ⟨fun t ht => ?_, fun k t ht => ?_, fun k => ?_, ?_⟩
  · exact Summable.of_nonneg_of_le
      (fun k => mul_nonneg (sobWeight_nonneg σ k) (sq_nonneg _)) (hterm σ (c t)) (h.inH t ht)
  · have hd : HasDerivWithinAt (fun s => p k (c s k))
        (p k ((-(absSq k : ℝ) : ℂ) • c t k + F t k)) (Icc a b) t :=
      ((p k).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t (h.mode k t ht)
    rw [map_add, map_smul] at hd
    exact hd
  · exact (p k).continuous.comp_continuousOn (h.force_cont k)
  · refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Icc fun t _ => ?_) h.force_l2
    exact tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal (hterm _ (F t) k)

/-- The horizontal slow part of a heat pair is a heat pair. -/
theorem HeatPair.PiH {σ a b : ℝ} {c F : ℝ → Field} (h : HeatPair σ a b c F) :
    HeatPair σ a b (fun t => PiH (c t)) (fun t => PiH (F t)) := by
  have := h.map (fun k => if k 2 = 0 then horizL else 0) fun k v => by
    by_cases hk : k 2 = 0
    · simpa [hk] using norm_horizL_le v
    · simp [hk]
  simpa only [← PiH_eq_horizL] using this

/-- The vertical slow part of a heat pair is a heat pair. -/
theorem HeatPair.PiV {σ a b : ℝ} {c F : ℝ → Field} (h : HeatPair σ a b c F) :
    HeatPair σ a b (fun t => PiV (c t)) (fun t => PiV (F t)) := by
  have := h.map (fun k => if k 2 = 0 then vertL else 0) fun k v => by
    by_cases hk : k 2 = 0
    · simpa [hk] using norm_vertL_le v
    · simp [hk]
  simpa only [← PiV_eq_vertL] using this

/-! ### `H^σ` bounds of the kinetic primitive -/

/-- `‖N(f,g)‖_σ ≤ (2^σ/q)(𝒜(f)‖g‖_σ + ‖f‖_σ 𝒜(g))` for `σ ≥ 1` (the pointwise bound (N3)
`‖N(f,g)_k‖ ≤ (2/q)∑_p ‖f_p‖‖g_{k−p}‖` integrated by `product_estimate`). -/
theorem hnorm_kinN_le_of_one_le {r τ : ℝ} (hr : r ≠ 0) {σ : ℝ} (hσ : 1 ≤ σ) {f g : Field}
    (hf : MZ σ f) (hg : MZ σ g) (hf1 : Summable fun k => ‖f k‖)
    (hg1 : Summable fun k => ‖g k‖) :
    InH σ (kinN r τ f g) ∧
      hnorm σ (kinN r τ f g) ≤ 2 ^ σ / |r| * (wiener f * hnorm σ g + hnorm σ f * wiener g) := by
  have hr' : 0 < |r| := abs_pos.mpr hr
  obtain ⟨hs, hb⟩ := product_estimate hσ hf hg hf1 hg1
  set W : Mode → ℝ := fun k => absk k ^ (2 * σ) * (∑' p, ‖f p‖ * ‖g (k - p)‖) ^ 2 with hW
  have hW0 : ∀ k, 0 ≤ W k := fun k =>
    mul_nonneg (Real.rpow_nonneg (absk_nonneg k) _) (sq_nonneg _)
  have hf2 := summable_sq_of_summable hf1
  have hg2 := summable_sq_of_summable hg1
  have key : ∀ k, sobWeight σ k * ‖kinN r τ f g k‖ ^ 2 ≤ (2 / |r|) ^ 2 * W k := fun k => by
    by_cases hk : k = 0
    · have h0 : sobWeight σ k = 0 := by simp [sobWeight, hk]
      rw [h0, zero_mul]
      exact mul_nonneg (by positivity) (hW0 k)
    have hsw : sobWeight σ k = absk k ^ (2 * σ) := by simp [sobWeight, hk]
    have h1 := norm_kinN_le (τ := τ) hr hf2 hg2 k
    have h2 : ‖kinN r τ f g k‖ ^ 2 ≤ (2 / |r| * ∑' p, ‖f p‖ * ‖g (k - p)‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [hsw, hW]
    calc absk k ^ (2 * σ) * ‖kinN r τ f g k‖ ^ 2
        ≤ absk k ^ (2 * σ) * (2 / |r| * ∑' p, ‖f p‖ * ‖g (k - p)‖) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (absk_nonneg k) _)
      _ = (2 / |r|) ^ 2 * (absk k ^ (2 * σ) * (∑' p, ‖f p‖ * ‖g (k - p)‖) ^ 2) := by ring
  have hs' : Summable fun k => (2 / |r|) ^ 2 * W k := hs.mul_left _
  have hI : InH σ (kinN r τ f g) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_nonneg σ k) (sq_nonneg _)) key hs'
  refine ⟨hI, ?_⟩
  have h2σ : (2 : ℝ) ^ σ = 2 * 2 ^ (σ - 1) := by
    rw [mul_comm, ← Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    ring
  calc hnorm σ (kinN r τ f g) ≤ Real.sqrt (∑' k, (2 / |r|) ^ 2 * W k) :=
        Real.sqrt_le_sqrt (hI.tsum_le_tsum key hs')
    _ = 2 / |r| * Real.sqrt (∑' k, W k) := by
        rw [tsum_mul_left, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    _ ≤ 2 / |r| * (2 ^ (σ - 1) * (wiener f * hnorm σ g + hnorm σ f * wiener g)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by rw [h2σ]; ring

/-! ### The slow projection of the phased convection -/

lemma PiS_add' (u v : Field) : PiS (u + v) = PiS u + PiS v := by
  funext k
  by_cases h : k 2 = 0 <;> simp [PiS, h]

lemma PiS_PiS_eq (u : Field) : PiS (PiS u) = PiS u := by
  funext k
  by_cases h : k 2 = 0 <;> simp [PiS, h]

lemma PiF_PiF_eq (u : Field) : PiF (PiF u) = PiF u := by
  funext k
  by_cases h : k 2 = 0 <;> simp [PiF, h]

lemma PiH_PiS_eq (u : Field) : PiH (PiS u) = PiH u := by
  funext k
  by_cases h : k 2 = 0 <;> simp [PiH, PiS, h]

lemma PiV_PiS_eq (u : Field) : PiV (PiS u) = PiV u := by
  funext k
  by_cases h : k 2 = 0 <;> simp [PiV, PiS, h]

lemma PiH_add' (u v : Field) : PiH (u + v) = PiH u + PiH v := by
  funext k
  rw [Pi.add_apply, PiH_eq_horizL, PiH_eq_horizL, PiH_eq_horizL, Pi.add_apply, map_add]

lemma PiH_sub' (u v : Field) : PiH (u - v) = PiH u - PiH v := by
  funext k
  rw [Pi.sub_apply, PiH_eq_horizL, PiH_eq_horizL, PiH_eq_horizL, Pi.sub_apply, map_sub]

lemma PiV_add' (u v : Field) : PiV (u + v) = PiV u + PiV v := by
  funext k
  rw [Pi.add_apply, PiV_eq_vertL, PiV_eq_vertL, PiV_eq_vertL, Pi.add_apply, map_add]

lemma PiV_sub' (u v : Field) : PiV (u - v) = PiV u - PiV v := by
  funext k
  rw [Pi.sub_apply, PiV_eq_vertL, PiV_eq_vertL, PiV_eq_vertL, Pi.sub_apply, map_sub]

/-- The sector projections contract the `H^s` norms. -/
lemma hnorm_PiH_le' {s : ℝ} {f : Field} (hf : InH s f) : hnorm s (PiH f) ≤ hnorm s f := by
  have h1 := hnorm_sq_split_slow hf
  have h2 := hnorm_PiS_le hf
  have h3 := hnorm_nonneg s (PiS f)
  have h4 := hnorm_nonneg s f
  have h5 : hnorm s (PiH f) ^ 2 ≤ hnorm s f ^ 2 := by nlinarith [sq_nonneg (hnorm s (PiV f))]
  exact (pow_le_pow_iff_left₀ (hnorm_nonneg _ _) h4 two_ne_zero).1 h5

lemma hnorm_PiV_le' {s : ℝ} {f : Field} (hf : InH s f) : hnorm s (PiV f) ≤ hnorm s f := by
  have h1 := hnorm_sq_split_slow hf
  have h2 := hnorm_PiS_le hf
  have h3 := hnorm_nonneg s (PiS f)
  have h4 := hnorm_nonneg s f
  have h5 : hnorm s (PiV f) ^ 2 ≤ hnorm s f ^ 2 := by nlinarith [sq_nonneg (hnorm s (PiH f))]
  exact (pow_le_pow_iff_left₀ (hnorm_nonneg _ _) h4 two_ne_zero).1 h5

/-- On slow triads the phase vanishes: `Π_S Q_τ(S,S) = B(S,S)` for a slow field `S`
(the phased analogue of `PiS_Qres`). -/
theorem PiS_Qphase_slow (τ : ℝ) {S : Field} (hS : Adm 2 S) (hS' : PiS S = S) :
    PiS (Qphase τ S S) = Bsym S S := by
  funext k
  by_cases hk : k 2 = 0
  · rw [PiS_apply_slow _ hk, ← congrFun (Qm_one hS hS) k, Qphase, Qm, Qm]
    refine tsum_congr fun p => ?_
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => ?_
    by_cases hp : p 2 = 0
    · have hq : (k - p) 2 = 0 := by simp [hk, hp]
      have hpq : p + (k - p) = k := by abel
      have hΦ : Phi a b c p (k - p) = 0 := by
        simp [Phi, lam_slow hp, lam_slow hq, hpq, lam_slow hk]
      simp [phaseM, hΦ]
    · simp [slow_zero hS' hp, hel_zero_right, vert_zero_left]
  · rw [PiS_apply_fast _ hk, Bsym, ← tsum_zero (α := V3) (β := Mode)]
    refine tsum_congr fun p => ?_
    by_cases hp : p 2 = 0
    · have hq : (k - p) 2 ≠ 0 := by simpa [hp] using hk
      rw [slow_zero hS' hq, vert_zero_right]
    · rw [slow_zero hS' hp, vert_zero_left]

/-- `Π_S Q_τ(x,x) = B(S,S) + Π_S Q_τ(F,F)` for `x = S + F` (`Π_S Q_τ(S,F) = 0`, slow–fast
triads have a fast output). -/
theorem PiS_Qphase_split (τ : ℝ) {x : Field} (hx : Adm 2 x) :
    PiS (Qphase τ x x) = Bsym (PiS x) (PiS x) + PiS (Qphase τ (PiF x) (PiF x)) := by
  set S := PiS x with hSdef
  set F := PiF x with hFdef
  have hS : Adm 2 S := hx.PiS
  have hF : Adm 2 F := hx.PiF
  have hS' : PiS S = S := PiS_PiS_eq x
  have hF' : PiF F = F := PiF_PiF_eq x
  have hM := majorized_Qphase τ
  have hx' : x = S + F := (PiS_add_PiF x).symm
  have hsum : MZ 2 (S + F) := by rw [← hx']; exact hx.mz
  have hcomm : Qphase τ F S = Qphase τ S F := Qm_comm_of_symm (phaseM_symm τ) hF.mz hS.mz
  have hsplit : Qphase τ x x = Qphase τ S S + Qphase τ S F + Qphase τ S F + Qphase τ F F := by
    conv_lhs => rw [hx']
    rw [hM.add_left 0 _ _ _ hS.mz hF.mz hsum, hM.add_right 0 _ _ _ hS.mz hS.mz hF.mz,
      hM.add_right 0 _ _ _ hF.mz hS.mz hF.mz, hcomm]
    abel
  have hSF : PiS (Qphase τ S F) = 0 := by
    funext k
    by_cases hk : k 2 = 0
    · rw [PiS_apply_slow _ hk, Qphase_slow_fast τ hS' hF' hk]; rfl
    · rw [PiS_apply_fast _ hk]; rfl
  rw [hsplit, PiS_add', PiS_add', PiS_add', hSF, PiS_Qphase_slow τ hS hS']
  simp

namespace Quant

/-! ### The Fourier-side slow exponents -/

/-- The slow exponents of route E7-F: `a_S ≲ μ²`, `b_S ≲ μ³`, `∫ b_S² ≲ μ⁴`, `W_S ≲ μ^{5/2}`. -/
def slowExpF : SlowExp := ⟨2, 3, 4, 5 / 2⟩

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-! ### The corrected slow field -/

/-- The normal-form corrector `R_S = N(F,F)` of the slow equation (TeX: the corrector of
eq. quant-corrected-slow), with the kinetic primitive at the phase `τ = rt`. -/
def slowCorr (r : ℝ) (g : Field) (y : ℝ → Field) (t : ℝ) : Field :=
  kinN r (r * t) (PiF (actual r g y t)) (PiF (actual r g y t))

/-- The corrected slow field `y_S = S + R_S`. -/
def corrSlow (r : ℝ) (g : Field) (y : ℝ → Field) (t : ℝ) : Field :=
  PiS (actual r g y t) + slowCorr r g y t

/-- The residual slow force
`Π_S g − Π_S H_ψ + 2N(F',F) + (B(y_S,y_S) − B(S,S))`: the genuine force `Π_S g` plus the
`O(1/q)` corrections (force filter, corrector derivative, corrector in the nonlinearity). -/
def slowRes (r : ℝ) (g : Field) (y : ℝ → Field) (t : ℝ) : Field :=
  PiS g - PiS (Hpsi r g y t) +
    (2 : ℂ) • kinN r (r * t) (fastRHS r g y t) (PiF (actual r g y t)) +
    (Bsym (corrSlow r g y t) (corrSlow r g y t) -
      Bsym (PiS (actual r g y t)) (PiS (actual r g y t)))

/-- The heat-form residual `A R_S + slowRes` (everything in the force of `y_S` other than the
closed slow convection `−B(y_S,y_S)`). -/
def corrRes (r : ℝ) (g : Field) (y : ℝ → Field) (t : ℝ) : Field := fun k =>
  (absSq k : ℂ) • slowCorr r g y t k + slowRes r g y t k

/-- The heat-form force of `y_S`: `y_S' = −A y_S + corrForce`,
`corrForce = corrRes − B(y_S,y_S)`. -/
def corrForce (r : ℝ) (g : Field) (y : ℝ → Field) (t : ℝ) : Field :=
  corrRes r g y t - Bsym (corrSlow r g y t) (corrSlow r g y t)

/-- The derivative of the corrector: `R_S' = Π_S Q_{rt}(F,F) + 2N(F',F)` (frozen-amplitude
derivative `tripT_kinDM_eq`, then both input slots, `kinN_comm`). -/
def slowCorrRHS (r : ℝ) (g : Field) (y : ℝ → Field) (t : ℝ) : Field := fun k =>
  PiS (Qphase (r * t) (PiF (actual r g y t)) (PiF (actual r g y t))) k +
    (2 : ℂ) • kinN r (r * t) (fastRHS r g y t) (PiF (actual r g y t)) k

lemma PiS_slowCorr (r : ℝ) (g : Field) (y : ℝ → Field) (t : ℝ) :
    PiS (slowCorr r g y t) = slowCorr r g y t := PiS_kinN _ _

lemma PiS_corrSlow (r : ℝ) (g : Field) (y : ℝ → Field) (t : ℝ) :
    PiS (corrSlow r g y t) = corrSlow r g y t := by
  unfold corrSlow
  rw [PiS_add', PiS_PiS_eq, PiS_slowCorr]

/-- The corrector is admissible in `H²` along the solution. -/
theorem slowCorr_adm (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {t : ℝ} (ht : 0 ≤ t)
    (htT : ENNReal.ofReal t < Ty) : Adm 2 (slowCorr r g y t) := by
  have hF : Adm 2 (PiF (actual r g y t)) := (actual_adm h ht htT).PiF
  have hF1 : Summable fun k => ‖PiF (actual r g y t) k‖ := summable_wiener hF.inH
  have hF2 : Summable fun k => ‖PiF (actual r g y t) k‖ ^ 2 := summable_sq_of_summable hF1
  have h0 := kinN_adm (τ := r * t) hr hF hF
  exact ⟨(hnorm_kinN_le_of_one_le hr (by norm_num : (1 : ℝ) ≤ 2) hF.mz hF.mz hF1 hF1).1, h0.real,
    h0.sol, h0.mean⟩

/-- `‖R_S‖₂ ≤ (8/q) 𝒜(F) b_F ≤ 8c₄ b_F²/q`. -/
theorem hnorm_slowCorr_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {t : ℝ} (ht : 0 ≤ t)
    (htT : ENNReal.ofReal t < Ty) :
    hnorm 2 (slowCorr r g y t) ≤ 8 / |r| * (wiener (PiF (actual r g y t)) * fastNorm 2 r g y t) ∧
      hnorm 2 (slowCorr r g y t) ≤ 8 * c4 / |r| * fastNorm 2 r g y t ^ 2 := by
  have hF : Adm 2 (PiF (actual r g y t)) := (actual_adm h ht htT).PiF
  have hF1 : Summable fun k => ‖PiF (actual r g y t) k‖ := summable_wiener hF.inH
  have h1 := (hnorm_kinN_le_of_one_le (τ := r * t) hr (by norm_num : (1 : ℝ) ≤ 2) hF.mz hF.mz hF1
    hF1).2
  have h2 : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
  rw [h2] at h1
  have hW := wiener_le hF.mz
  have hr' : 0 < |r| := abs_pos.mpr hr
  have hb := hnorm_nonneg 2 (PiF (actual r g y t))
  have hc := c4_pos
  refine ⟨?_, ?_⟩
  · unfold slowCorr fastNorm
    refine h1.trans (le_of_eq ?_)
    ring
  · unfold slowCorr fastNorm
    refine h1.trans ?_
    have : wiener (PiF (actual r g y t)) * hnorm 2 (PiF (actual r g y t)) ≤
        c4 * hnorm 2 (PiF (actual r g y t)) ^ 2 := by nlinarith
    calc 4 / |r| * (wiener (PiF (actual r g y t)) * hnorm 2 (PiF (actual r g y t)) +
          hnorm 2 (PiF (actual r g y t)) * wiener (PiF (actual r g y t)))
        = 8 / |r| * (wiener (PiF (actual r g y t)) * hnorm 2 (PiF (actual r g y t))) := by ring
      _ ≤ 8 / |r| * (c4 * hnorm 2 (PiF (actual r g y t)) ^ 2) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring

/-- The corrected slow field is admissible in `H²` and slow. -/
theorem corrSlow_adm (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {t : ℝ} (ht : 0 ≤ t)
    (htT : ENNReal.ofReal t < Ty) : Adm 2 (corrSlow r g y t) := by
  have h1 := (actual_adm h ht htT).PiS
  have h2 := slowCorr_adm h hr ht htT
  refine ⟨h1.inH.add h2.inH, fun k => ?_, fun k => ?_, ?_⟩
  · simp only [corrSlow, Pi.add_apply, h1.real k, h2.real k]
    ext i; simp [conjV]
  · simp only [corrSlow, Pi.add_apply, dotM_add, h1.sol k, h2.sol k, add_zero]
  · simp [corrSlow, h1.mean, h2.mean]

/-- `‖y_S − S‖_σ = ‖R_S‖_σ ≤ ‖R_S‖₂` for `σ ≤ 2`: the slow norms of `S` and `y_S` differ by at
most `‖R_S‖₂`. -/
theorem slowNorm_le_corr (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {t : ℝ} (ht : 0 ≤ t)
    (htT : ENNReal.ofReal t < Ty) {σ : ℝ} (hσ : σ ≤ 2) :
    slowNorm σ r g y t ≤ hnorm σ (corrSlow r g y t) + hnorm 2 (slowCorr r g y t) ∧
      hnorm σ (corrSlow r g y t) ≤ slowNorm σ r g y t + hnorm 2 (slowCorr r g y t) := by
  have h1 := (actual_adm h ht htT).PiS.inH.mono hσ
  have h2 := (slowCorr_adm h hr ht htT).inH
  have h2' := h2.mono hσ
  have hR : hnorm σ (slowCorr r g y t) ≤ hnorm 2 (slowCorr r g y t) := hnorm_mono hσ h2
  have e : PiS (actual r g y t) = corrSlow r g y t - slowCorr r g y t := by
    simp [corrSlow]
  constructor
  · unfold slowNorm
    rw [e]
    exact (hnorm_sub_le (h1.add h2') h2').trans (add_le_add le_rfl hR)
  · unfold slowNorm
    exact (hnorm_add_le h1 h2').trans (add_le_add le_rfl hR)

/-- The same for the horizontal and vertical sectors (projections contract). -/
theorem horizNorm_le_corr (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {t : ℝ} (ht : 0 ≤ t)
    (htT : ENNReal.ofReal t < Ty) {σ : ℝ} (hσ : σ ≤ 2) :
    horizNorm σ r g y t ≤ hnorm σ (PiH (corrSlow r g y t)) + hnorm 2 (slowCorr r g y t) ∧
      hnorm σ (PiH (corrSlow r g y t)) ≤ horizNorm σ r g y t + hnorm 2 (slowCorr r g y t) := by
  have h1 := (actual_adm h ht htT).inH.mono hσ
  have h2 := (slowCorr_adm h hr ht htT).inH
  have h2' := h2.mono hσ
  have hR : hnorm σ (PiH (slowCorr r g y t)) ≤ hnorm 2 (slowCorr r g y t) :=
    (hnorm_mono hσ h2.PiH).trans (hnorm_PiH_le' h2)
  have e2 : PiH (corrSlow r g y t) = PiH (actual r g y t) + PiH (slowCorr r g y t) := by
    rw [corrSlow, PiH_add', PiH_PiS_eq]
  have e1 : PiH (actual r g y t) = PiH (corrSlow r g y t) - PiH (slowCorr r g y t) := by
    rw [e2]; abel
  have hz : InH σ (PiH (corrSlow r g y t)) := by
    rw [e2]; exact h1.PiH.add h2'.PiH
  constructor
  · unfold horizNorm
    have := hnorm_sub_le hz h2'.PiH
    rw [← e1] at this
    exact this.trans (add_le_add le_rfl hR)
  · unfold horizNorm
    have := hnorm_add_le h1.PiH h2'.PiH
    rw [← e2] at this
    exact this.trans (add_le_add le_rfl hR)

/-! ### The mode equation of the corrected slow field -/

/-- **The mode derivative of the corrector** `R_S = N(F,F)` along the actual solution:
`(R_S)_k' = Π_S Q_{rt}(F,F)_k + 2N(F',F)_k` (`slowCorrRHS`).  Differentiation of the `p`-sum
term by term (`hasDerivWithinAt_triV`), the frozen-amplitude slot summing to the phased convection
on the slow output (`tsum_triV_kinDM`: the resonant slow-output triads carry a vanishing vertex),
the two input slots to `N(F',F)` (`kinN_comm`); the passage to the limit by the integrated form
(`integral_tsum_deriv'` with the uniform control `triD_summable_bound` on compacts) and the
continuity of the right-hand side (`continuousOn_kinN_fastRHS_mode`): this is
`hasDerivWithinAt_kinN_fast`, `ModeDeriv.lean`. -/
theorem hasDerivWithinAt_slowCorr (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < Ty) (k : Mode) {t : ℝ} (ht : t ∈ Icc 0 b) :
    HasDerivWithinAt (fun u => slowCorr r g y u k) (slowCorrRHS r g y t k) (Icc 0 b) t :=
  hasDerivWithinAt_kinN_fast h hr hb hbT k ht

/-- The slow projection of `Q_{rt}(y,y)` along the solution:
`Π_S Q(y,y) = B(S,S) + Π_S Q(F,F) + Π_S H_ψ`. -/
theorem PiS_Qphase_actual (h : ActualSol μ φ r g y Ty) {t : ℝ} (ht : 0 ≤ t)
    (htT : ENNReal.ofReal t < Ty) :
    PiS (Qphase (r * t) (y t) (y t)) =
      Bsym (PiS (actual r g y t)) (PiS (actual r g y t)) +
        PiS (Qphase (r * t) (PiF (actual r g y t)) (PiF (actual r g y t))) +
        PiS (Hpsi r g y t) := by
  have hx := actual_adm h ht htT
  have e : Qphase (r * t) (y t) (y t) =
      Qphase (r * t) (actual r g y t) (actual r g y t) + Hpsi r g y t := by
    simp [Hpsi]
  rw [e, PiS_add', PiS_Qphase_split _ hx]

/-- **The heat-form mode equation of `y_S`**: `(y_S)_k' = −|k|² (y_S)_k + corrForce_k`. -/
theorem corrSlow_mode (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < Ty) (k : Mode) {t : ℝ} (ht : t ∈ Icc 0 b) :
    HasDerivWithinAt (fun u => corrSlow r g y u k)
      ((-(absSq k : ℝ) : ℂ) • corrSlow r g y t k + corrForce r g y t k) (Icc 0 b) t := by
  have htT := lt_lifespan ht.2 hbT
  have h1 := (slow_mode h k ht.1 htT).mono (fun v (hv : v ∈ Icc 0 b) => show v ∈ Ici 0 from hv.1)
  have h2 := hasDerivWithinAt_slowCorr h hr hb hbT k ht
  refine (h1.add h2).congr_deriv ?_
  have hsplit := congrFun (PiS_Qphase_actual h ht.1 htT) k
  simp only [Pi.add_apply] at hsplit
  simp only [slowRHS, slowCorrRHS, corrForce, corrRes, slowRes, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply]
  rw [hsplit]
  simp only [corrSlow, Pi.add_apply]
  generalize PiS (actual r g y t) k = S
  generalize slowCorr r g y t k = R
  generalize Bsym (PiS (actual r g y t)) (PiS (actual r g y t)) k = BS
  generalize Bsym (PiS (actual r g y t) + slowCorr r g y t)
    (PiS (actual r g y t) + slowCorr r g y t) k = Bz
  generalize PiS (Qphase (r * t) (PiF (actual r g y t)) (PiF (actual r g y t))) k = QF
  generalize PiS (Hpsi r g y t) k = Hk
  generalize PiS g k = gk
  generalize kinN r (r * t) (fastRHS r g y t) (PiF (actual r g y t)) k = N
  module

/-! ### The residual bounds (roles 18–21) -/

/-- The polynomial of the pointwise `H⁰` residual bound `‖corrRes‖₀ ≤ φ + resPoly/q`
(`hnorm_corrRes_le`): `A R_S` (`8c₄ Y²`), the force filter `Π_S H_ψ`
(`4φ(c₄(A+P) + W + c₄Y) + 8c₄φ²`), the corrector derivative `2N(F',F)`
(`4c₄Y(Y + 2(A+P+2φ)(W+c₄Y+2c₄φ))`), and the corrector in the nonlinearity
(`16c₄Y²(c₄A + W + c₄)`); caps enter through their nonnegative parts `cp`. -/
def resPoly (φ : ℝ) (caps : Caps) : ℝ :=
  let P := cp caps.PF
  let Y := cp caps.yF
  let A := cp caps.AS
  let W := cp caps.WS
  8 * c4 * Y ^ 2 + 4 * φ * (c4 * (A + P) + W + c4 * Y) + 8 * c4 * φ ^ 2 +
    4 * c4 * Y * (Y + 2 * (A + P + 2 * φ) * (W + c4 * Y + 2 * c4 * φ)) +
    16 * c4 * Y ^ 2 * (c4 * A + W + c4)

lemma resPoly_nonneg {φ : ℝ} (hφ : 0 ≤ φ) (caps : Caps) : 0 ≤ resPoly φ caps := by
  have := cp_nonneg caps.PF
  have := cp_nonneg caps.yF
  have := cp_nonneg caps.AS
  have := cp_nonneg caps.WS
  have := c4_pos
  unfold resPoly
  positivity

/-- `‖A f‖₀ = ‖f‖₂`. -/
lemma hnorm_zero_absSq_smul (f : Field) :
    hnorm 0 (fun k => (absSq k : ℂ) • f k) = hnorm 2 f := by
  unfold hnorm
  refine congrArg Real.sqrt (tsum_congr fun k => ?_)
  show sobWeight 0 k * ‖(absSq k : ℂ) • f k‖ ^ 2 = sobWeight 2 k * ‖f k‖ ^ 2
  by_cases hk : k = 0
  · simp [sobWeight, hk]
  · have h0 : sobWeight 0 k = 1 := by simp [sobWeight, hk]
    rw [h0, one_mul, norm_smul, mul_pow, sobWeight_two, Complex.norm_real,
      Real.norm_of_nonneg (absSq_nonneg k)]

/-- The constant multiplier `1` is bounded and real. -/
lemma one_mult_bdd : Mult.Bdd (fun _ _ _ _ _ => (1 : ℂ)) := fun _ _ _ _ _ => by simp

lemma one_mult_real : Mult.Real (fun _ _ _ _ _ => (1 : ℂ)) := fun _ _ _ _ _ => by simp

/-- `B` is the `Majorized` family with multiplier `1`. -/
lemma majorized_one : Majorized (fun _ : ℝ => Qm (fun _ _ _ _ _ => (1 : ℂ))) :=
  majorized_Qm (fun _ => fun _ _ _ _ _ => 1) (fun _ => one_mult_bdd) (fun _ => one_mult_real)
    fun _ _ _ _ _ => continuous_const

/-- Bilinearity of the slow convection around `S`:
`B(S+R, S+R) − B(S,S) = Q¹(S,R) + Q¹(R,S) + Q¹(R,R)`. -/
lemma Bsym_add_sub {S R : Field} (hS : Adm 2 S) (hR : Adm 2 R) (hz : Adm 2 (S + R)) :
    Bsym (S + R) (S + R) - Bsym S S =
      Qm (fun _ _ _ _ _ => (1 : ℂ)) S R + Qm (fun _ _ _ _ _ => (1 : ℂ)) R S +
        Qm (fun _ _ _ _ _ => (1 : ℂ)) R R := by
  have hM := majorized_one
  rw [← Qm_one hz hz, ← Qm_one hS hS]
  have e1 := hM.add_left 0 S R (S + R) hS.mz hR.mz hz.mz
  have e2 := hM.add_right 0 S S R hS.mz hS.mz hR.mz
  have e3 := hM.add_right 0 R S R hR.mz hS.mz hR.mz
  rw [e1, e2, e3]
  abel

/-- The force filter splits: `H_ψ = Q(x,ψ) + Q(ψ,x) + Q(ψ,ψ)` (`y = x + ψ`). -/
lemma Hpsi_eq (h : ActualSol μ φ r g y Ty) {u : ℝ} (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty) :
    Hpsi r g y u =
      Qphase (r * u) (actual r g y u) (psi r 0 g u) +
        Qphase (r * u) (psi r 0 g u) (actual r g y u) +
        Qphase (r * u) (psi r 0 g u) (psi r 0 g u) := by
  have hx := (actual_mz h hu huT)
  have hψ := (psi_adm (r := r) (t₀ := 0) h.force_adm u hu).mz
  have hy := (h.sol.adm u hu huT).mz
  have e : y u = actual r g y u + psi r 0 g u := by simp [actual]
  have hM := majorized_Qphase (r * u)
  have hy' : MZ 2 (actual r g y u + psi r 0 g u) := by rw [← e]; exact hy
  have e1 := hM.add_left 0 (actual r g y u) (psi r 0 g u) (actual r g y u + psi r 0 g u) hx hψ hy'
  have e2 := hM.add_right 0 (actual r g y u) (actual r g y u) (psi r 0 g u) hx hx hψ
  have e3 := hM.add_right 0 (psi r 0 g u) (actual r g y u) (psi r 0 g u) hψ hx hψ
  unfold Hpsi
  rw [e, e1, e2, e3]
  abel

/-- `‖x‖₁ ≤ a_S + a_F`. -/
lemma hnorm_one_actual_le (h : ActualSol μ φ r g y Ty) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) :
    hnorm 1 (actual r g y u) ≤ slowNorm 1 r g y u + fastNorm 1 r g y u := by
  have hx := (actual_adm h hu huT).inH.mono (by norm_num : (1 : ℝ) ≤ 2)
  have hsplit := hnorm_sq_split hx
  have h1 := hnorm_nonneg 1 (PiS (actual r g y u))
  have h2 := hnorm_nonneg 1 (PiF (actual r g y u))
  unfold slowNorm fastNorm
  refine (pow_le_pow_iff_left₀ (hnorm_nonneg _ _) (by positivity) two_ne_zero).1 ?_
  nlinarith

/-- `𝒜(x) ≤ W_S + c₄ b_F`. -/
lemma wiener_actual_le (h : ActualSol μ φ r g y Ty) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) :
    wiener (actual r g y u) ≤ slowWiener r g y u + c4 * fastNorm 2 r g y u := by
  have hx := actual_adm h hu huT
  have e : actual r g y u = PiS (actual r g y u) + PiF (actual r g y u) :=
    (PiS_add_PiF _).symm
  have h1 := wiener_add_le (summable_wiener hx.PiS.inH) (summable_wiener hx.PiF.inH)
  have h2 := wiener_le hx.PiF.mz
  unfold slowWiener fastNorm
  calc wiener (actual r g y u) = wiener (PiS (actual r g y u) + PiF (actual r g y u)) := by
        rw [← e]
    _ ≤ _ := h1
    _ ≤ _ := by linarith

/-- **The pointwise `H⁰` residual bound** on a prefix where the caps hold and the corrector is
small, `‖R_S‖₂ ≤ 1`: `‖corrRes u‖₀ ≤ φ + resPoly(φ, caps)/q` (`q = |r| ≥ 1`).  Terms:
`‖A R_S‖₀ = ‖R_S‖₂ ≤ 8c₄ b_F²/q` (`hnorm_slowCorr_le`); `‖Π_S g‖₀ ≤ φ`;
`‖H_ψ‖₀ ≤ 2(‖x‖₁𝒜(ψ) + 𝒜(x)‖ψ‖₁) + 2‖ψ‖₁𝒜(ψ)` (`hnorm_Qm_zero_le` on
`Q(x,ψ) + Q(ψ,x) + Q(ψ,ψ)`, `psi_bound`, `‖x‖₁ ≤ a_S + a_F`, `𝒜(x) ≤ W_S + c₄ b_F`);
`‖2N(F',F)‖₀ ≤ (4/q)𝒜(F)‖F'‖_{ℓ²}` (`hnorm_kinN_le`, `fastRHS_l2`, `‖Q(y,y)‖₀ ≤ 2‖y‖₁𝒜(y)`);
the nonlinear difference `‖B(y_S,y_S) − B(S,S)‖₀ ≤ 2(‖S‖₁𝒜(R) + 𝒜(S)‖R‖₁) + 2‖R‖₁𝒜(R)` with
`𝒜(R) ≤ c₄‖R‖₂`, `‖R‖₂ ≤ 1`. -/
theorem hnorm_corrRes_le (h : ActualSol μ φ r g y Ty) (hr : 1 ≤ |r|) {caps : Caps} {s t : ℝ}
    (hs : 0 ≤ s) (ht : ENNReal.ofReal t < Ty) (hP : OnPrefix caps r g y s t) {u : ℝ}
    (hu : u ∈ Icc s t) (hρ : hnorm 2 (slowCorr r g y u) ≤ 1) :
    hnorm 0 (corrRes r g y u) ≤ φ + resPoly φ caps / |r| := by
  have hr0 : r ≠ 0 := fun h0 => by rw [h0, abs_zero] at hr; linarith
  have hrpos : 0 < |r| := by linarith
  have hu0 : 0 ≤ u := hs.trans hu.1
  have huT := lt_lifespan hu.2 ht
  have hc4 := c4_pos
  have hφ : 0 ≤ φ := (hnorm_nonneg 2 g).trans h.force_le
  -- admissibility
  have hx := actual_adm h hu0 huT
  have hy := h.sol.adm u hu0 huT
  have hψ := psi_adm (r := r) (t₀ := 0) h.force_adm u hu0
  have hR := slowCorr_adm h hr0 hu0 huT
  have hz := corrSlow_adm h hr0 hu0 huT
  have hS := hx.PiS
  have hF := hx.PiF
  have hg0 : InH 0 g := h.force_adm.inH.mono (by norm_num)
  -- the caps at `u`
  obtain ⟨haF, hbF, haS, hbS, hWS⟩ := hP.1 u hu
  set P := cp caps.PF with hPdef
  set Y := cp caps.yF with hYdef
  set A := cp caps.AS with hAdef
  set W := cp caps.WS with hWdef
  have hP0 := cp_nonneg caps.PF
  have hY0 := cp_nonneg caps.yF
  have hA0 := cp_nonneg caps.AS
  have hW0 := cp_nonneg caps.WS
  have haF' : fastNorm 1 r g y u ≤ P := haF.trans (le_cp _)
  have hbF' : fastNorm 2 r g y u ≤ Y := hbF.trans (le_cp _)
  have haS' : slowNorm 1 r g y u ≤ A := haS.trans (le_cp _)
  have hWS' : slowWiener r g y u ≤ W := hWS.trans (le_cp _)
  have hbF0 := hnorm_nonneg 2 (PiF (actual r g y u))
  -- sizes of `x`, `ψ`, `y`, `F`, `R`
  have hx1 : hnorm 1 (actual r g y u) ≤ A + P := (hnorm_one_actual_le h hu0 huT).trans (by linarith)
  have hxW : wiener (actual r g y u) ≤ W + c4 * Y := by
    have := wiener_actual_le h hu0 huT
    have := mul_le_mul_of_nonneg_left hbF' hc4.le
    linarith
  have hg1 : hnorm 1 g ≤ φ := (hnorm_mono (by norm_num) h.force_adm.inH).trans h.force_le
  obtain ⟨-, hψ2⟩ := psi_bound (r := r) (t₀ := 0) hr0 h.force_adm u hu0
  have hψ2' : hnorm 2 (psi r 0 g u) ≤ 2 * φ / |r| := by
    refine hψ2.trans ?_
    rw [div_le_div_iff_of_pos_right hrpos]
    linarith
  have hψ1 : hnorm 1 (psi r 0 g u) ≤ 2 * φ / |r| :=
    (hnorm_mono (by norm_num) hψ.inH).trans hψ2'
  have hψW : wiener (psi r 0 g u) ≤ c4 * (2 * φ / |r|) :=
    (wiener_le hψ.mz).trans (mul_le_mul_of_nonneg_left hψ2' hc4.le)
  have hinv : 1 / |r| ≤ 1 := by rw [div_le_one hrpos]; exact hr
  have hψ1' : hnorm 1 (psi r 0 g u) ≤ 2 * φ := by
    have : 2 * φ / |r| ≤ 2 * φ := by
      rw [div_le_iff₀ hrpos]; nlinarith
    linarith
  have hψW' : wiener (psi r 0 g u) ≤ 2 * c4 * φ := by
    have : c4 * (2 * φ / |r|) ≤ 2 * c4 * φ := by
      rw [mul_div_assoc', div_le_iff₀ hrpos]
      have := mul_le_mul_of_nonneg_left hr (by positivity : (0 : ℝ) ≤ 2 * c4 * φ)
      linarith
    linarith
  have hy1 : hnorm 1 (y u) ≤ A + P + 2 * φ := by
    have e : y u = actual r g y u + psi r 0 g u := by simp [actual]
    rw [e]
    have := hnorm_add_le (hx.inH.mono (by norm_num : (1 : ℝ) ≤ 2))
      (hψ.inH.mono (by norm_num : (1 : ℝ) ≤ 2))
    linarith
  have hyW : wiener (y u) ≤ W + c4 * Y + 2 * c4 * φ := by
    have e : y u = actual r g y u + psi r 0 g u := by simp [actual]
    rw [e]
    have := wiener_add_le (summable_wiener hx.inH) (summable_wiener hψ.inH)
    linarith
  have hFW : wiener (PiF (actual r g y u)) ≤ c4 * Y :=
    (wiener_le hF.mz).trans (mul_le_mul_of_nonneg_left hbF' hc4.le)
  have hR2 : hnorm 2 (slowCorr r g y u) ≤ 8 * c4 * Y ^ 2 / |r| := by
    refine (hnorm_slowCorr_le h hr0 hu0 huT).2.trans ?_
    have hsq : fastNorm 2 r g y u ^ 2 ≤ Y ^ 2 := pow_le_pow_left₀ hbF0 hbF' 2
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (by nlinarith) hrpos.le
  have hR1 : hnorm 1 (slowCorr r g y u) ≤ hnorm 2 (slowCorr r g y u) :=
    hnorm_mono (by norm_num) hR.inH
  have hRW : wiener (slowCorr r g y u) ≤ c4 * hnorm 2 (slowCorr r g y u) := wiener_le hR.mz
  have hR0 := hnorm_nonneg 2 (slowCorr r g y u)
  -- (1) `‖A R_S‖₀`
  have hAR : hnorm 0 (fun k => (absSq k : ℂ) • slowCorr r g y u k) ≤ 8 * c4 * Y ^ 2 / |r| := by
    rw [hnorm_zero_absSq_smul]; exact hR2
  -- (2) the genuine force
  have hgS : hnorm 0 (PiS g) ≤ φ :=
    (hnorm_PiS_le hg0).trans ((hnorm_mono (by norm_num) h.force_adm.inH).trans h.force_le)
  -- (3) the force filter
  have hQ1 : InH 0 (Qphase (r * u) (actual r g y u) (psi r 0 g u)) ∧
      hnorm 0 (Qphase (r * u) (actual r g y u) (psi r 0 g u)) ≤
        hnorm 1 (actual r g y u) * wiener (psi r 0 g u) +
          wiener (actual r g y u) * hnorm 1 (psi r 0 g u) :=
    hnorm_Qm_zero_le (phaseM_bdd (r * u)) hx.mz hψ.mz
  have hQ2 : InH 0 (Qphase (r * u) (psi r 0 g u) (actual r g y u)) ∧
      hnorm 0 (Qphase (r * u) (psi r 0 g u) (actual r g y u)) ≤
        hnorm 1 (psi r 0 g u) * wiener (actual r g y u) +
          wiener (psi r 0 g u) * hnorm 1 (actual r g y u) :=
    hnorm_Qm_zero_le (phaseM_bdd (r * u)) hψ.mz hx.mz
  have hQ3 : InH 0 (Qphase (r * u) (psi r 0 g u) (psi r 0 g u)) ∧
      hnorm 0 (Qphase (r * u) (psi r 0 g u) (psi r 0 g u)) ≤
        hnorm 1 (psi r 0 g u) * wiener (psi r 0 g u) +
          wiener (psi r 0 g u) * hnorm 1 (psi r 0 g u) :=
    hnorm_Qm_zero_le (phaseM_bdd (r * u)) hψ.mz hψ.mz
  have hHpsi : hnorm 0 (PiS (Hpsi r g y u)) ≤
      (4 * φ * (c4 * (A + P) + W + c4 * Y) + 8 * c4 * φ ^ 2) / |r| := by
    have hHe := Hpsi_eq h hu0 huT
    have hH0 : InH 0 (Hpsi r g y u) := by
      rw [hHe]; exact (hQ1.1.add hQ2.1).add hQ3.1
    refine (hnorm_PiS_le hH0).trans ?_
    rw [hHe]
    have h1 := hnorm_add_le (hQ1.1.add hQ2.1) hQ3.1
    have h2 := hnorm_add_le hQ1.1 hQ2.1
    have hx1' := hnorm_nonneg 1 (actual r g y u)
    have hxW' := wiener_nonneg (actual r g y u)
    have hψ1n := hnorm_nonneg 1 (psi r 0 g u)
    have hψWn := wiener_nonneg (psi r 0 g u)
    -- the three products
    have p1 : hnorm 1 (actual r g y u) * wiener (psi r 0 g u) ≤ (A + P) * (c4 * (2 * φ / |r|)) :=
      mul_le_mul hx1 hψW hψWn (by positivity)
    have p2 : wiener (actual r g y u) * hnorm 1 (psi r 0 g u) ≤ (W + c4 * Y) * (2 * φ / |r|) :=
      mul_le_mul hxW hψ1 hψ1n (by positivity)
    have p3 : hnorm 1 (psi r 0 g u) * wiener (psi r 0 g u) ≤ (2 * φ / |r|) * (c4 * (2 * φ / |r|)) :=
      mul_le_mul hψ1 hψW hψWn (by positivity)
    have hsum : 2 * ((A + P) * (c4 * (2 * φ / |r|))) + 2 * ((W + c4 * Y) * (2 * φ / |r|)) +
        2 * ((2 * φ / |r|) * (c4 * (2 * φ / |r|))) ≤
        (4 * φ * (c4 * (A + P) + W + c4 * Y) + 8 * c4 * φ ^ 2) / |r| := by
      have e : 2 * ((A + P) * (c4 * (2 * φ / |r|))) + 2 * ((W + c4 * Y) * (2 * φ / |r|)) +
          2 * ((2 * φ / |r|) * (c4 * (2 * φ / |r|))) =
          (4 * φ * (c4 * (A + P) + W + c4 * Y)) / |r| + 8 * c4 * φ ^ 2 / |r| * (1 / |r|) := by
        field_simp
        ring
      rw [e, add_div]
      have : 8 * c4 * φ ^ 2 / |r| * (1 / |r|) ≤ 8 * c4 * φ ^ 2 / |r| * 1 :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      linarith
    linarith [hQ1.2, hQ2.2, hQ3.2]
  -- (4) the corrector derivative
  have hN : hnorm 0 ((2 : ℂ) • kinN r (r * u) (fastRHS r g y u) (PiF (actual r g y u))) ≤
      4 * c4 * Y * (Y + 2 * (A + P + 2 * φ) * (W + c4 * Y + 2 * c4 * φ)) / |r| := by
    rw [hnorm_smul, kinN_comm]
    have hk := hnorm_kinN_le (τ := r * u) hr0 (summable_wiener hF.inH) (fastRHS_l2 h hu0 huT).1
    have hF' := (fastRHS_l2 h hu0 huT).2
    have hQy : hnorm 0 (Qphase (r * u) (y u) (y u)) ≤
        hnorm 1 (y u) * wiener (y u) + wiener (y u) * hnorm 1 (y u) :=
      (hnorm_Qm_zero_le (phaseM_bdd (r * u)) hy.mz hy.mz).2
    have hQy' : hnorm 0 (Qphase (r * u) (y u) (y u)) ≤
        2 * ((A + P + 2 * φ) * (W + c4 * Y + 2 * c4 * φ)) := by
      have := mul_le_mul hy1 hyW (wiener_nonneg _) (by positivity)
      have := mul_le_mul hyW hy1 (hnorm_nonneg _ _) (by positivity)
      linarith
    have hbF'' : hnorm 2 (PiF (actual r g y u)) ≤ Y := hbF'
    have hF'le : Real.sqrt (∑' k, ‖fastRHS r g y u k‖ ^ 2) ≤
        Y + 2 * ((A + P + 2 * φ) * (W + c4 * Y + 2 * c4 * φ)) := by linarith
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2]
    have hprod : wiener (PiF (actual r g y u)) * Real.sqrt (∑' k, ‖fastRHS r g y u k‖ ^ 2) ≤
        c4 * Y * (Y + 2 * ((A + P + 2 * φ) * (W + c4 * Y + 2 * c4 * φ))) :=
      mul_le_mul hFW hF'le (Real.sqrt_nonneg _) (by positivity)
    calc 2 * hnorm 0 (kinN r (r * u) (PiF (actual r g y u)) (fastRHS r g y u))
        ≤ 2 * (2 / |r| * (wiener (PiF (actual r g y u)) *
            Real.sqrt (∑' k, ‖fastRHS r g y u k‖ ^ 2))) := by linarith [hk.2]
      _ ≤ 2 * (2 / |r| * (c4 * Y * (Y + 2 * ((A + P + 2 * φ) * (W + c4 * Y + 2 * c4 * φ))))) :=
          by gcongr
      _ = 4 * c4 * Y * (Y + 2 * (A + P + 2 * φ) * (W + c4 * Y + 2 * c4 * φ)) / |r| := by
          field_simp
          ring
  -- (5) the nonlinear difference
  have hBd : hnorm 0 (Bsym (corrSlow r g y u) (corrSlow r g y u) -
      Bsym (PiS (actual r g y u)) (PiS (actual r g y u))) ≤
      16 * c4 * Y ^ 2 * (c4 * A + W + c4) / |r| := by
    have hz' : Adm 2 (PiS (actual r g y u) + slowCorr r g y u) := hz
    rw [show corrSlow r g y u = PiS (actual r g y u) + slowCorr r g y u from rfl,
      Bsym_add_sub hS hR hz']
    have q1 := hnorm_Qm_zero_le one_mult_bdd hS.mz hR.mz
    have q2 := hnorm_Qm_zero_le one_mult_bdd hR.mz hS.mz
    have q3 := hnorm_Qm_zero_le one_mult_bdd hR.mz hR.mz
    have h1 := hnorm_add_le (q1.1.add q2.1) q3.1
    have h2 := hnorm_add_le q1.1 q2.1
    have hS1 : hnorm 1 (PiS (actual r g y u)) ≤ A := haS'
    have hSW : wiener (PiS (actual r g y u)) ≤ W := hWS'
    have hRWn := wiener_nonneg (slowCorr r g y u)
    have hR1n := hnorm_nonneg 1 (slowCorr r g y u)
    set ρ := hnorm 2 (slowCorr r g y u) with hρdef
    have p1 : hnorm 1 (PiS (actual r g y u)) * wiener (slowCorr r g y u) ≤ A * (c4 * ρ) :=
      mul_le_mul hS1 hRW hRWn hA0
    have p2 : wiener (PiS (actual r g y u)) * hnorm 1 (slowCorr r g y u) ≤ W * ρ :=
      mul_le_mul hSW hR1 hR1n hW0
    have p3 : hnorm 1 (slowCorr r g y u) * wiener (slowCorr r g y u) ≤ ρ * (c4 * ρ) :=
      mul_le_mul hR1 hRW hRWn hR0
    have hρ2 : ρ * (c4 * ρ) ≤ c4 * ρ := by
      have h' := mul_le_mul_of_nonneg_left hρ (mul_nonneg hc4.le hR0)
      linarith only [h']
    have hsum : 2 * (A * (c4 * ρ)) + 2 * (W * ρ) + 2 * (c4 * ρ) ≤
        16 * c4 * Y ^ 2 * (c4 * A + W + c4) / |r| := by
      have e : 2 * (A * (c4 * ρ)) + 2 * (W * ρ) + 2 * (c4 * ρ) = 2 * (c4 * A + W + c4) * ρ := by
        ring
      rw [e]
      have := mul_le_mul_of_nonneg_left hR2 (by positivity : (0 : ℝ) ≤ 2 * (c4 * A + W + c4))
      refine this.trans (le_of_eq ?_)
      field_simp
      ring
    linarith only [h1, h2, q1.2, q2.2, q3.2, p1, p2, p3, hρ2, hsum]
  -- assembly
  have e : corrRes r g y u = (fun k => (absSq k : ℂ) • slowCorr r g y u k) + slowRes r g y u := by
    funext k; rfl
  have hAR0 : InH 0 (fun k => (absSq k : ℂ) • slowCorr r g y u k) := by
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_nonneg 0 k) (sq_nonneg _))
      (fun k => ?_) hR.inH
    by_cases hk : k = 0
    · simp [hk, sobWeight]
    · have h0 : sobWeight 0 k = 1 := by simp [sobWeight, hk]
      rw [h0, one_mul, norm_smul, mul_pow, sobWeight_two, Complex.norm_real,
        Real.norm_of_nonneg (absSq_nonneg k)]
  have hgS0 : InH 0 (PiS g) := hg0.PiS
  have hH0 : InH 0 (PiS (Hpsi r g y u)) := by
    rw [Hpsi_eq h hu0 huT]; exact ((hQ1.1.add hQ2.1).add hQ3.1).PiS
  have hN0 : InH 0 ((2 : ℂ) • kinN r (r * u) (fastRHS r g y u) (PiF (actual r g y u))) := by
    rw [kinN_comm]
    exact ((hnorm_kinN_le hr0 (summable_wiener hF.inH) (fastRHS_l2 h hu0 huT).1).1).smul _
  have hBz0 : InH 0 (Bsym (corrSlow r g y u) (corrSlow r g y u)) := by
    rw [← Qm_one hz hz]; exact (hnorm_Qm_zero_le one_mult_bdd hz.mz hz.mz).1
  have hBS0 : InH 0 (Bsym (PiS (actual r g y u)) (PiS (actual r g y u))) := by
    rw [← Qm_one hS hS]; exact (hnorm_Qm_zero_le one_mult_bdd hS.mz hS.mz).1
  have hres0 : InH 0 (slowRes r g y u) := ((hgS0.sub hH0).add hN0).add (hBz0.sub hBS0)
  have t1 := hnorm_add_le hAR0 hres0
  unfold slowRes at t1
  have t2 := hnorm_add_le ((hgS0.sub hH0).add hN0) (hBz0.sub hBS0)
  have t3 := hnorm_add_le (hgS0.sub hH0) hN0
  have t4 := hnorm_sub_le hgS0 hH0
  have hresPoly : resPoly φ caps / |r| = 8 * c4 * Y ^ 2 / |r| +
      (4 * φ * (c4 * (A + P) + W + c4 * Y) + 8 * c4 * φ ^ 2) / |r| +
      4 * c4 * Y * (Y + 2 * (A + P + 2 * φ) * (W + c4 * Y + 2 * c4 * φ)) / |r| +
      16 * c4 * Y ^ 2 * (c4 * A + W + c4) / |r| := by
    simp only [resPoly]
    field_simp
    ring
  rw [e, hresPoly]
  unfold slowRes
  linarith only [t1, t2, t3, t4, hAR, hgS, hHpsi, hN, hBd]

/-! ### The residual in `H¹` -/

/-- `‖x‖₂ ≤ b_S + b_F`. -/
lemma hnorm_two_actual_le (h : ActualSol μ φ r g y Ty) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) :
    hnorm 2 (actual r g y u) ≤ slowNorm 2 r g y u + fastNorm 2 r g y u := by
  have hsplit := hnorm_sq_split (actual_adm h hu huT).inH
  have h1 := hnorm_nonneg 2 (PiS (actual r g y u))
  have h2 := hnorm_nonneg 2 (PiF (actual r g y u))
  unfold slowNorm fastNorm
  refine (pow_le_pow_iff_left₀ (hnorm_nonneg _ _) (by positivity) two_ne_zero).1 ?_
  nlinarith

/-- `‖A R_S‖₁ = ‖R_S‖₃ ≤ (16 c₄ ‖F‖₂/q) ‖F‖₃` at a time with `F ∈ H³`. -/
lemma hnorm_one_A_slowCorr_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hF3 : InH 3 (PiF (actual r g y u))) :
    InH 1 (fun k => (absSq k : ℂ) • slowCorr r g y u k) ∧
      hnorm 1 (fun k => (absSq k : ℂ) • slowCorr r g y u k) ≤
        16 * c4 * fastNorm 2 r g y u / |r| * fastNorm 3 r g y u := by
  have hF := (actual_adm h hu huT).PiF
  have hmz : MZ 3 (PiF (actual r g y u)) := ⟨hF3, hF.mean⟩
  have hF1 := summable_wiener hF.inH
  obtain ⟨hI, hle⟩ := hnorm_kinN_le_of_one_le (τ := r * u) hr (by norm_num : (1 : ℝ) ≤ 3) hmz hmz
    hF1 hF1
  obtain ⟨hI', he⟩ := hnorm_one_absSq_smul hI
  have hr' : 0 < |r| := abs_pos.mpr hr
  have e8 : (2 : ℝ) ^ (3 : ℝ) = 8 := by norm_num
  rw [e8] at hle
  refine ⟨hI', ?_⟩
  have he' : hnorm 1 (fun k => (absSq k : ℂ) • slowCorr r g y u k) =
      hnorm 3 (kinN r (r * u) (PiF (actual r g y u)) (PiF (actual r g y u))) := he
  rw [he']
  refine hle.trans ?_
  have hw := wiener_le hF.mz
  have n3 := hnorm_nonneg 3 (PiF (actual r g y u))
  have e : 16 * c4 * fastNorm 2 r g y u / |r| * fastNorm 3 r g y u =
      8 / |r| * (2 * (c4 * hnorm 2 (PiF (actual r g y u)) * hnorm 3 (PiF (actual r g y u)))) := by
    unfold fastNorm
    ring
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have := mul_le_mul_of_nonneg_right hw n3
  linarith

/-- **The pointwise `H¹` bound of the residual**, at a time with `F ∈ H³`:
`‖corrRes‖₁ ≤ ‖g‖₁ + (c₄‖F‖₂/q)(24‖F‖₃ + 52𝒜(y)‖y‖₂) + 8‖ψ‖₂(𝒜(x) + c₄‖x‖₂ + c₄‖ψ‖₂) +
8‖R_S‖₂(𝒜(S) + c₄‖S‖₂ + c₄‖R_S‖₂)`. -/
theorem hnorm_one_corrRes_le (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) (hF3 : InH 3 (PiF (actual r g y u))) :
    InH 1 (corrRes r g y u) ∧
      hnorm 1 (corrRes r g y u) ≤ hnorm 1 g +
        c4 * fastNorm 2 r g y u / |r| *
          (24 * fastNorm 3 r g y u + 52 * (wiener (y u) * hnorm 2 (y u))) +
        8 * hnorm 2 (psi r 0 g u) * (wiener (actual r g y u) + c4 * hnorm 2 (actual r g y u) +
          c4 * hnorm 2 (psi r 0 g u)) +
        8 * hnorm 2 (slowCorr r g y u) * (slowWiener r g y u + c4 * slowNorm 2 r g y u +
          c4 * hnorm 2 (slowCorr r g y u)) := by
  have hx := actual_adm h hu huT
  have hψ := psi_adm (r := r) (t₀ := 0) h.force_adm u hu
  have hR := slowCorr_adm h hr hu huT
  have hz : Adm 2 (PiS (actual r g y u) + slowCorr r g y u) := corrSlow_adm h hr hu huT
  have hS := hx.PiS
  have hg1 : InH 1 g := h.force_adm.inH.mono (by norm_num)
  -- (1) `A R_S`
  obtain ⟨i1, b1⟩ := hnorm_one_A_slowCorr_le h hr hu huT hF3
  -- (2) the genuine force
  have i2 : InH 1 (PiS g) := hg1.PiS
  have b2 := hnorm_PiS_le hg1
  -- (3) the force filter
  obtain ⟨i3, b3⟩ := hnorm_Qm_three_bound (phaseM_bdd (r * u)) hx.mz hψ.mz
  have e3 : Hpsi r g y u = Qm (phaseM (r * u)) (actual r g y u) (psi r 0 g u) +
      Qm (phaseM (r * u)) (psi r 0 g u) (actual r g y u) +
      Qm (phaseM (r * u)) (psi r 0 g u) (psi r 0 g u) := Hpsi_eq h hu huT
  rw [← e3] at i3 b3
  have b3' := hnorm_PiS_le i3
  -- (4) the corrector derivative
  obtain ⟨i4, b4⟩ := hnorm_one_kinN_fastRHS_le h hr (r * u) hu huT hF3
  have i4' := i4.smul (2 : ℂ)
  have b4' : hnorm 1 ((2 : ℂ) • kinN r (r * u) (fastRHS r g y u) (PiF (actual r g y u))) ≤
      2 * (c4 * fastNorm 2 r g y u / |r| *
        (4 * fastNorm 3 r g y u + 26 * (wiener (y u) * hnorm 2 (y u)))) := by
    rw [hnorm_smul]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2]
    exact mul_le_mul_of_nonneg_left b4 (by norm_num)
  -- (5) the nonlinear difference
  obtain ⟨i5, b5⟩ := hnorm_Qm_three_bound one_mult_bdd hS.mz hR.mz
  have e5 : Bsym (corrSlow r g y u) (corrSlow r g y u) -
      Bsym (PiS (actual r g y u)) (PiS (actual r g y u)) =
      Qm (fun _ _ _ _ _ => (1 : ℂ)) (PiS (actual r g y u)) (slowCorr r g y u) +
        Qm (fun _ _ _ _ _ => (1 : ℂ)) (slowCorr r g y u) (PiS (actual r g y u)) +
        Qm (fun _ _ _ _ _ => (1 : ℂ)) (slowCorr r g y u) (slowCorr r g y u) :=
    Bsym_add_sub hS hR hz
  rw [← e5] at i5 b5
  -- assembly
  have e : corrRes r g y u = (fun k => (absSq k : ℂ) • slowCorr r g y u k) + slowRes r g y u := by
    funext k; rfl
  have hres : InH 1 (slowRes r g y u) := ((i2.sub i3.PiS).add i4').add i5
  have t1 := hnorm_add_le i1 hres
  unfold slowRes at t1
  have t2 := hnorm_add_le ((i2.sub i3.PiS).add i4') i5
  have t3 := hnorm_add_le (i2.sub i3.PiS) i4'
  have t4 := hnorm_sub_le i2 i3.PiS
  refine ⟨by rw [e]; exact i1.add hres, ?_⟩
  have ealg : c4 * fastNorm 2 r g y u / |r| *
      (24 * fastNorm 3 r g y u + 52 * (wiener (y u) * hnorm 2 (y u))) =
      16 * c4 * fastNorm 2 r g y u / |r| * fastNorm 3 r g y u +
        2 * (c4 * fastNorm 2 r g y u / |r| *
          (4 * fastNorm 3 r g y u + 26 * (wiener (y u) * hnorm 2 (y u)))) := by
    ring
  rw [ealg, e]
  unfold slowRes
  simp only [slowWiener, slowNorm] at *
  linarith only [t1, t2, t3, t4, b1, b2, b3, b3', b4', b5]

/-- The affine bound of the residual on `[0, b]`. -/
theorem exists_corrRes_bound (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {b : ℝ}
    (hbT : ENNReal.ofReal b < Ty) :
    ∃ a c M : ℝ, 0 ≤ M ∧ ∀ u ∈ Icc 0 b, hnorm 2 (corrSlow r g y u) ≤ M ∧
      (InH 3 (PiF (actual r g y u)) →
        InH 1 (corrRes r g y u) ∧ hnorm 1 (corrRes r g y u) ≤ a + c * fastNorm 3 r g y u) := by
  obtain ⟨M, hM0, hM⟩ := exists_actual_bound' h hr hbT
  have hrp := abs_pos.mpr hr
  have hc := c4_pos
  have hΨ0 : 0 ≤ 2 * hnorm 1 g / |r| := by have := hnorm_nonneg 1 g; positivity
  set Ψ := 2 * hnorm 1 g / |r| with hΨ
  have hρ0 : 0 ≤ 8 * c4 / |r| * M ^ 2 := by positivity
  set ρ := 8 * c4 / |r| * M ^ 2 with hρ
  refine ⟨hnorm 1 g + c4 * M / |r| * (52 * (c4 * M * M)) + 8 * Ψ * (c4 * M + c4 * M + c4 * Ψ) +
    8 * ρ * (c4 * M + c4 * M + c4 * ρ), c4 * M / |r| * 24, M + ρ, by positivity, fun u hu => ?_⟩
  have huT := lt_lifespan hu.2 hbT
  have hx := actual_adm h hu.1 huT
  obtain ⟨hMx, hMF, hMS, hMy⟩ := hM u hu
  have hR : hnorm 2 (slowCorr r g y u) ≤ ρ := by
    refine (hnorm_slowCorr_le h hr hu.1 huT).2.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact pow_le_pow_left₀ (hnorm_nonneg _ _) hMF 2
  refine ⟨?_, fun hF3 => ?_⟩
  · exact (hnorm_add_le hx.PiS.inH (slowCorr_adm h hr hu.1 huT).inH).trans (add_le_add hMS hR)
  obtain ⟨hI, hle⟩ := hnorm_one_corrRes_le h hr hu.1 huT hF3
  refine ⟨hI, hle.trans ?_⟩
  have hψ : hnorm 2 (psi r 0 g u) ≤ Ψ := (psi_bound (t₀ := 0) hr h.force_adm u hu.1).2
  have hy := h.sol.adm u hu.1 huT
  have hwy : wiener (y u) ≤ c4 * M := (wiener_le hy.mz).trans (by gcongr)
  have hwx : wiener (actual r g y u) ≤ c4 * M := (wiener_le hx.mz).trans (by gcongr)
  have hwS : wiener (PiS (actual r g y u)) ≤ c4 * M := (wiener_le hx.PiS.mz).trans (by gcongr)
  have n1 := hnorm_nonneg 2 (PiF (actual r g y u))
  have n2 := hnorm_nonneg 3 (PiF (actual r g y u))
  have n3 := wiener_nonneg (y u)
  have n4 := hnorm_nonneg 2 (y u)
  have n5 := hnorm_nonneg 2 (psi r 0 g u)
  have n6 := hnorm_nonneg 2 (slowCorr r g y u)
  have n7 := wiener_nonneg (actual r g y u)
  have n8 := wiener_nonneg (PiS (actual r g y u))
  have n9 := hnorm_nonneg 2 (actual r g y u)
  have n10 := hnorm_nonneg 2 (PiS (actual r g y u))
  calc _ ≤ hnorm 1 g + c4 * M / |r| * (24 * fastNorm 3 r g y u + 52 * (c4 * M * M)) +
        8 * Ψ * (c4 * M + c4 * M + c4 * Ψ) + 8 * ρ * (c4 * M + c4 * M + c4 * ρ) := by
        unfold fastNorm slowWiener slowNorm
        gcongr
    _ = _ := by ring

/-- The affine bound of the force on `[0, b]`. -/
theorem exists_corrForce_bound (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {b : ℝ}
    (hbT : ENNReal.ofReal b < Ty) :
    ∃ a c : ℝ, ∀ u ∈ Icc 0 b, InH 3 (PiF (actual r g y u)) →
      InH 1 (corrForce r g y u) ∧ hnorm 1 (corrForce r g y u) ≤ a + c * fastNorm 3 r g y u := by
  obtain ⟨a, c, M, hM0, hbd⟩ := exists_corrRes_bound h hr hbT
  have hc := c4_pos
  refine ⟨a + 8 * c4 * M ^ 2, c, fun u hu hF3 => ?_⟩
  have huT := lt_lifespan hu.2 hbT
  obtain ⟨hzM, hres⟩ := hbd u hu
  obtain ⟨hI, hle⟩ := hres hF3
  have hz := corrSlow_adm h hr hu.1 huT
  obtain ⟨iB, bB⟩ := hnorm_Qm_one_bound one_mult_bdd hz.mz hz.mz
  rw [Qm_one hz hz] at iB bB
  refine ⟨hI.sub iB, ?_⟩
  have t := hnorm_sub_le hI iB
  have hw := wiener_le hz.mz
  have n1 := hnorm_nonneg 2 (corrSlow r g y u)
  have n2 := wiener_nonneg (corrSlow r g y u)
  have h1 : wiener (corrSlow r g y u) * hnorm 2 (corrSlow r g y u) ≤ c4 * M ^ 2 := by
    calc _ ≤ c4 * hnorm 2 (corrSlow r g y u) * hnorm 2 (corrSlow r g y u) :=
          mul_le_mul_of_nonneg_right hw n1
      _ = c4 * hnorm 2 (corrSlow r g y u) ^ 2 := by ring
      _ ≤ c4 * M ^ 2 := by gcongr
  have e : hnorm 2 (corrSlow r g y u) * wiener (corrSlow r g y u) =
      wiener (corrSlow r g y u) * hnorm 2 (corrSlow r g y u) := mul_comm _ _
  rw [e] at bB
  unfold corrForce
  linarith

/-- `u ↦ (R_S)_k` is continuous on `[0, b]`. -/
lemma continuousOn_slowCorr_mode (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < Ty) (k : Mode) :
    ContinuousOn (fun u => slowCorr r g y u k) (Icc 0 b) := fun _ ht =>
  (hasDerivWithinAt_slowCorr h hr hb hbT k ht).continuousWithinAt

/-- `u ↦ B(S,S)_k` is continuous on `[0, b]`. -/
lemma continuousOn_Bsym_slow_mode (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {b : ℝ}
    (hbT : ENNReal.ofReal b < Ty) (k : Mode) :
    ContinuousOn (fun u => Bsym (PiS (actual r g y u)) (PiS (actual r g y u)) k) (Icc 0 b) := by
  obtain ⟨M, -, hM⟩ := exists_actual_bound' h hr hbT
  have hS : ∀ u ∈ Icc 0 b, Adm 2 (PiS (actual r g y u)) := fun u hu =>
    (actual_adm h hu.1 (lt_lifespan hu.2 hbT)).PiS
  have := continuousOn_majorized_mode majorized_one (f := fun u => PiS (actual r g y u))
    (g := fun u => PiS (actual r g y u)) (fun u hu => (hS u hu).mz) (fun u hu => (hS u hu).mz)
    (fun u₀ hu₀ => slow_cont h hbT hu₀) (fun u₀ hu₀ => slow_cont h hbT hu₀)
    (fun u hu => ⟨(hM u hu).2.2.1, (hM u hu).2.2.1⟩) k
  exact this.congr fun u hu => (congrFun (Qm_one (hS u hu) (hS u hu)) k).symm

/-- `u ↦ (Π_S H_ψ)_k` is continuous on `[0, b]`. -/
lemma continuousOn_PiS_Hpsi_mode (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < Ty) (k : Mode) :
    ContinuousOn (fun u => PiS (Hpsi r g y u) k) (Icc 0 b) := by
  by_cases hk : k 2 = 0
  · simp only [PiS_apply_slow _ hk]
    exact continuousOn_Hpsi_mode h hr hb hbT k
  · simp only [PiS_apply_fast _ hk]
    exact continuousOn_const

/-- The force modes are continuous on `[0, b]`: in `corrForce` the convection of `y_S` cancels,
`corrForce = A R_S + Π_S g − Π_S H_ψ + 2N(F',F) − B(S,S)`. -/
theorem continuousOn_corrForce_mode (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < Ty) (k : Mode) :
    ContinuousOn (fun u => corrForce r g y u k) (Icc 0 b) := by
  have h1 := (continuousOn_slowCorr_mode h hr hb hbT k).const_smul (absSq k : ℂ)
  have h2 := continuousOn_PiS_Hpsi_mode h hr hb hbT k
  have h3 := (continuousOn_kinN_fastRHS_mode h hr hbT k).const_smul (2 : ℂ)
  have h4 := continuousOn_Bsym_slow_mode h hr hbT k
  refine (((h1.sub h2).add h3).sub h4).add (continuousOn_const (c := PiS g k)) |>.congr
    fun u _ => ?_
  simp only [corrForce, corrRes, slowRes, Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
  abel

/-- The residual modes are measurable: `corrRes = corrForce + B(y_S,y_S)`, and a mode of
`B(y_S,y_S)` is an a.e. limit of continuous finite sums. -/
theorem aestronglyMeasurable_corrRes_mode (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {b : ℝ}
    (hb : 0 ≤ b) (hbT : ENNReal.ofReal b < Ty) (k : Mode) :
    AEStronglyMeasurable (fun u => corrRes r g y u k) (volume.restrict (Icc 0 b)) := by
  have hzc : ∀ j, ContinuousOn (fun u => corrSlow r g y u j) (Icc 0 b) := fun j =>
    (continuousOn_slow_mode h hbT j).add (continuousOn_slowCorr_mode h hr hb hbT j)
  have hB : AEStronglyMeasurable (fun u => Bsym (corrSlow r g y u) (corrSlow r g y u) k)
      (volume.restrict (Icc 0 b)) := by
    refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset Mode))
      (f := fun S u => ∑ p ∈ S, vert p (k - p) (corrSlow r g y u p) (corrSlow r g y u (k - p)))
      (fun S => ?_) ?_
    · exact (continuousOn_finsetSum S fun p _ =>
        continuousOn_vert (hzc p) (hzc (k - p))).aestronglyMeasurable measurableSet_Icc
    · rw [ae_restrict_iff' measurableSet_Icc]
      refine .of_forall fun u hu => ?_
      have hz := corrSlow_adm h hr hu.1 (lt_lifespan hu.2 hbT)
      exact (summable_vert hz.mz hz.mz k).hasSum
  have hF := (continuousOn_corrForce_mode h hr hb hbT k).aestronglyMeasurable
    (μ := volume) measurableSet_Icc
  refine (hF.add hB).congr (.of_forall fun u => ?_)
  simp [corrForce]

/-- `‖corrForce‖₁² ∈ L¹` on `[0, b]`. -/
theorem lintegral_corrForce_lt_top (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < Ty) : ∫⁻ t in Icc 0 b, hsE 1 (corrForce r g y t) < ∞ := by
  obtain ⟨a, c, hbd⟩ := exists_corrForce_bound h hr hbT
  exact lintegral_hsE_one_lt_top h hb hbT hbd

/-- **The corrected slow field is a heat pair** at `σ ∈ {0, 1, 2}` with force `corrForce`
(TeX eq. quant-corrected-slow).  Modes: `corrSlow_mode`; regularity `y_S ∈ H²` (`corrSlow_adm`);
continuity of the force modes (`continuousOn_corrForce_mode`, along the `H²`-continuous path `S`
and the `ℓ²`-continuous `F'`); `L²_t H^{σ−1}` of the force: the `H¹` bound for `σ = 2`, by the
fast `H²` dissipation `∫ c_F² < ∞` (`lintegral_corrForce_lt_top`), and monotonicity for
`σ ≤ 1`. -/
theorem heatPair_corrSlow (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {σ b : ℝ}
    (hσ : σ = 0 ∨ σ = 1 ∨ σ = 2) (hb : 0 ≤ b) (hbT : ENNReal.ofReal b < Ty) :
    HeatPair σ 0 b (corrSlow r g y) (corrForce r g y) := by
  have hσ2 : σ ≤ 2 := by rcases hσ with rfl | rfl | rfl <;> norm_num
  refine ⟨fun t ht => (corrSlow_adm h hr ht.1 (lt_lifespan ht.2 hbT)).inH.mono hσ2,
    fun k t ht => corrSlow_mode h hr hb hbT k ht,
    fun k => continuousOn_corrForce_mode h hr hb hbT k, ?_⟩
  exact (lintegral_mono fun t => hsE_le_of_le (by linarith) _).trans_lt
    (lintegral_corrForce_lt_top h hr hb hbT)

/-- The horizontal part `h = Π_H y_S` is a heat pair with force `Π_H corrForce`. -/
theorem heatPair_corrH (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {σ b : ℝ}
    (hσ : σ = 0 ∨ σ = 1 ∨ σ = 2) (hb : 0 ≤ b) (hbT : ENNReal.ofReal b < Ty) :
    HeatPair σ 0 b (fun t => PiH (corrSlow r g y t)) (fun t => PiH (corrForce r g y t)) :=
  (heatPair_corrSlow h hr hσ hb hbT).PiH

/-- The vertical part `ζ = Π_V y_S` is a heat pair with force `Π_V corrForce`. -/
theorem heatPair_corrV (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {σ b : ℝ}
    (hσ : σ = 0 ∨ σ = 1 ∨ σ = 2) (hb : 0 ≤ b) (hbT : ENNReal.ofReal b < Ty) :
    HeatPair σ 0 b (fun t => PiV (corrSlow r g y t)) (fun t => PiV (corrForce r g y t)) :=
  (heatPair_corrSlow h hr hσ hb hbT).PiV

/-- The polynomial of the `L²_t H¹` residual budget (`corrRes_budget`), with the numerical constant
`2¹¹(1 + c₄)²` of the proof.  The monomials the proof pays are `Y²`, `YΓ` (`A R_S` and `N(F',F)`
against the fast `H³` dissipation `∫ c_F² ≤ Y² + 128 Z²`, `Z = (W+c₄Y+2c₄φ)(B+Y+2φ)`, of the fast
`H²` law; here `Γ = Y + (W+Y+φ)(B+Y+φ)`), and the pointwise `H¹` pieces `φ(W + Y + B + φ)`
(force filter), `Y²(W + B + 1)` (corrector in the nonlinearity).  The monomials `(AY + WP)Γ`, `Y³`
and `φ(A+P+W+Y+φ)Γ` of the route plan are slack: `hnorm_one_kinN_fastRHS_le` treats
`N(Π_F Q(y,y), F)` as a whole, with both derivatives on one factor. -/
def budgetPoly (φ : ℝ) (caps : Caps) : ℝ :=
  let P := cp caps.PF
  let Y := cp caps.yF
  let A := cp caps.AS
  let B := cp caps.BS
  let W := cp caps.WS
  let Γ := Y + (W + Y + φ) * (B + Y + φ)
  2 ^ 11 * (1 + c4) ^ 2 * (1 + Y ^ 2 + Y * Γ + (A * Y + W * P) * Γ + Y ^ 3 +
    φ * (A + P + W + Y + φ) * Γ + φ * (W + Y + B + φ) + Y ^ 2 * (W + B + 1))

lemma one_le_budgetPoly {φ : ℝ} (hφ : 0 ≤ φ) (caps : Caps) : 1 ≤ budgetPoly φ caps := by
  have := cp_nonneg caps.PF
  have := cp_nonneg caps.yF
  have := cp_nonneg caps.AS
  have := cp_nonneg caps.BS
  have := cp_nonneg caps.WS
  have hc := c4_pos
  simp only [budgetPoly]
  set Y := cp caps.yF
  set Γ := Y + (cp caps.WS + Y + φ) * (cp caps.BS + Y + φ) with hΓ
  have hΓ0 : 0 ≤ Γ := by positivity
  have hrest : 0 ≤ Y ^ 2 + Y * Γ + (cp caps.AS * Y + cp caps.WS * cp caps.PF) * Γ + Y ^ 3 +
      φ * (cp caps.AS + cp caps.PF + cp caps.WS + Y + φ) * Γ +
      φ * (cp caps.WS + Y + cp caps.BS + φ) + Y ^ 2 * (cp caps.WS + cp caps.BS + 1) := by
    positivity
  have h1 : (1 : ℝ) ≤ (1 + c4) ^ 2 := one_le_pow₀ (by linarith)
  calc (1 : ℝ) ≤ 2 ^ 11 * (1 + c4) ^ 2 * 1 := by nlinarith
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith

/-- The cap of `𝒜(y)‖y‖₂`: `Z = (W + c₄Y + 2c₄φ)(B + Y + 2φ)`. -/
private def zCap (φ : ℝ) (caps : Caps) : ℝ :=
  (cp caps.WS + c4 * cp caps.yF + 2 * c4 * φ) * (cp caps.BS + cp caps.yF + 2 * φ)

/-- The constant part of the `1/q` terms of the `H¹` residual. -/
private def budA (φ : ℝ) (caps : Caps) : ℝ :=
  52 * c4 * cp caps.yF * zCap φ caps +
    16 * φ * (cp caps.WS + 2 * c4 * cp caps.yF + c4 * cp caps.BS + 2 * c4 * φ) +
    64 * c4 * cp caps.yF ^ 2 * (cp caps.WS + c4 * cp caps.BS + c4)

/-- The coefficient of `‖F‖₃` in the `1/q` terms of the `H¹` residual. -/
private def budB (caps : Caps) : ℝ := 24 * c4 * cp caps.yF

/-- All the coefficients of the budget are dominated monomial by monomial. -/
private lemma budget_arith_aux {c Y B W φ : ℝ} (hc : 0 ≤ c) (hY : 0 ≤ Y) (hB : 0 ≤ B) (hW : 0 ≤ W)
    (hφ : 0 ≤ φ) :
    488 * c * Y * ((W + c * Y + 2 * c * φ) * (B + Y + 2 * φ)) +
        32 * φ * (W + 2 * c * Y + c * B + 2 * c * φ) + 128 * c * Y ^ 2 * (W + c * B + c) +
        24 * c * Y ^ 2 ≤
      2 ^ 11 * (1 + c) ^ 2 * (Y ^ 2 + Y * ((W + Y + φ) * (B + Y + φ)) + φ * (W + Y + B + φ) +
        Y ^ 2 * (W + B + 1)) := by
  rw [← sub_nonneg]
  ring_nf
  positivity

/-- `budgetPoly` pays the budget: `2a + b(Y + 16 Z) ≤ q`, `8c₄Y² ≤ q`. -/
private lemma budget_le {φ : ℝ} (hφ : 0 ≤ φ) (caps : Caps) :
    2 * budA φ caps + budB caps * (cp caps.yF + 16 * zCap φ caps) ≤ budgetPoly φ caps ∧
      8 * c4 * cp caps.yF ^ 2 ≤ budgetPoly φ caps := by
  have hP := cp_nonneg caps.PF
  have hY := cp_nonneg caps.yF
  have hA := cp_nonneg caps.AS
  have hB := cp_nonneg caps.BS
  have hW := cp_nonneg caps.WS
  have hc := c4_pos
  have haux := budget_arith_aux hc.le hY hB hW hφ
  simp only [budA, budB, zCap, budgetPoly]
  set P := cp caps.PF
  set Y := cp caps.yF
  set A := cp caps.AS
  set B := cp caps.BS
  set W := cp caps.WS
  have hslack : 0 ≤ 2 ^ 11 * (1 + c4) ^ 2 * (1 + Y ^ 2 +
      (A * Y + W * P) * (Y + (W + Y + φ) * (B + Y + φ)) + Y ^ 3 +
      φ * (A + P + W + Y + φ) * (Y + (W + Y + φ) * (B + Y + φ))) := by positivity
  constructor
  · linarith only [haux, hslack]
  · have h8 : 8 * c4 * Y ^ 2 ≤ 2 ^ 11 * (1 + c4) ^ 2 * Y ^ 2 := by
      have : 8 * c4 ≤ 2 ^ 11 * (1 + c4) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    have hrest : 0 ≤ 2 ^ 11 * (1 + c4) ^ 2 * (1 + Y * (Y + (W + Y + φ) * (B + Y + φ)) +
        (A * Y + W * P) * (Y + (W + Y + φ) * (B + Y + φ)) + Y ^ 3 +
        φ * (A + P + W + Y + φ) * (Y + (W + Y + φ) * (B + Y + φ)) + φ * (W + Y + B + φ) +
        Y ^ 2 * (W + B + 1)) := by positivity
    linarith only [h8, hrest]

/-- The sizes along the solution under the caps (`q ≥ 1`). -/
private lemma prefix_sizes (h : ActualSol μ φ r g y Ty) (hq : 1 ≤ |r|) {caps : Caps} {s t : ℝ}
    (hs : 0 ≤ s) (ht : ENNReal.ofReal t < Ty) (hP : OnPrefix caps r g y s t) {u : ℝ}
    (hu : u ∈ Icc s t) :
    hnorm 2 (psi r 0 g u) ≤ 2 * φ / |r| ∧
      wiener (actual r g y u) ≤ cp caps.WS + c4 * cp caps.yF ∧
      hnorm 2 (actual r g y u) ≤ cp caps.BS + cp caps.yF ∧
      wiener (y u) ≤ cp caps.WS + c4 * cp caps.yF + 2 * c4 * φ ∧
      hnorm 2 (y u) ≤ cp caps.BS + cp caps.yF + 2 * φ ∧
      hnorm 2 (slowCorr r g y u) ≤ 8 * c4 * cp caps.yF ^ 2 / |r| := by
  have hr0 : r ≠ 0 := fun h0 => by rw [h0, abs_zero] at hq; linarith
  have hrpos : 0 < |r| := by linarith
  have hu0 : 0 ≤ u := hs.trans hu.1
  have huT := lt_lifespan hu.2 ht
  have hc4 := c4_pos
  have hφ : 0 ≤ φ := (hnorm_nonneg 2 g).trans h.force_le
  have hx := actual_adm h hu0 huT
  have hψ := psi_adm (r := r) (t₀ := 0) h.force_adm u hu0
  obtain ⟨-, hbF, -, hbS, hWS⟩ := hP.1 u hu
  have hY : fastNorm 2 r g y u ≤ cp caps.yF := hbF.trans (le_cp _)
  have hB : slowNorm 2 r g y u ≤ cp caps.BS := hbS.trans (le_cp _)
  have hW : slowWiener r g y u ≤ cp caps.WS := hWS.trans (le_cp _)
  have hg1 : hnorm 1 g ≤ φ := (hnorm_mono (by norm_num) h.force_adm.inH).trans h.force_le
  have hψ2 : hnorm 2 (psi r 0 g u) ≤ 2 * φ / |r| := by
    refine (psi_bound (t₀ := 0) hr0 h.force_adm u hu0).2.trans ?_
    rw [div_le_div_iff_of_pos_right hrpos]
    linarith
  have hψ2' : hnorm 2 (psi r 0 g u) ≤ 2 * φ := hψ2.trans (div_le_self (by positivity) hq)
  have hwx : wiener (actual r g y u) ≤ cp caps.WS + c4 * cp caps.yF :=
    (wiener_actual_le h hu0 huT).trans
      (add_le_add hW (mul_le_mul_of_nonneg_left hY hc4.le))
  have hnx : hnorm 2 (actual r g y u) ≤ cp caps.BS + cp caps.yF :=
    (hnorm_two_actual_le h hu0 huT).trans (add_le_add hB hY)
  have e : y u = actual r g y u + psi r 0 g u := by simp [actual]
  refine ⟨hψ2, hwx, hnx, ?_, ?_, ?_⟩
  · rw [e]
    have h1 := wiener_add_le (summable_wiener hx.inH) (summable_wiener hψ.inH)
    have h2 := (wiener_le hψ.mz).trans (mul_le_mul_of_nonneg_left hψ2' hc4.le)
    linarith
  · rw [e]
    have := hnorm_add_le hx.inH hψ.inH
    linarith
  · refine (hnorm_slowCorr_le h hr0 hu0 huT).2.trans ?_
    have hsq : fastNorm 2 r g y u ^ 2 ≤ cp caps.yF ^ 2 :=
      pow_le_pow_left₀ (hnorm_nonneg _ _) hY 2
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (by nlinarith) hrpos.le

/-- `‖Q(y,y)‖₁ ≤ 8𝒜(y)‖y‖₂ ≤ 8 Z` on a prefix. -/
private lemma wiener_mul_y_le_zCap (h : ActualSol μ φ r g y Ty) (hq : 1 ≤ |r|) {caps : Caps}
    {s t : ℝ} (hs : 0 ≤ s) (ht : ENNReal.ofReal t < Ty) (hP : OnPrefix caps r g y s t) {u : ℝ}
    (hu : u ∈ Icc s t) : wiener (y u) * hnorm 2 (y u) ≤ zCap φ caps := by
  obtain ⟨-, -, -, h1, h2, -⟩ := prefix_sizes h hq hs ht hP hu
  have hφ : 0 ≤ φ := (hnorm_nonneg 2 g).trans h.force_le
  have := cp_nonneg caps.WS
  have := cp_nonneg caps.yF
  have := c4_pos
  exact mul_le_mul h1 h2 (hnorm_nonneg _ _) (by positivity)

/-- **The budget form of the pointwise `H¹` bound**:
`‖corrRes‖₁ ≤ φ + (a + b‖F‖₃)/q` on a prefix, with `a = budA`, `b = budB`, once `q ≥ 1` and
`‖R_S‖₂ ≤ 1` (`8c₄Y² ≤ q`). -/
private lemma hnorm_one_corrRes_caps (h : ActualSol μ φ r g y Ty) (hq : 1 ≤ |r|) {caps : Caps}
    {s t : ℝ} (hs : 0 ≤ s) (ht : ENNReal.ofReal t < Ty) (hP : OnPrefix caps r g y s t)
    (hρ : 8 * c4 * cp caps.yF ^ 2 ≤ |r|) {u : ℝ} (hu : u ∈ Icc s t)
    (hF3 : InH 3 (PiF (actual r g y u))) :
    hnorm 1 (corrRes r g y u) ≤
      φ + (budA φ caps + budB caps * fastNorm 3 r g y u) / |r| := by
  have hr0 : r ≠ 0 := fun h0 => by rw [h0, abs_zero] at hq; linarith
  have hrpos : 0 < |r| := by linarith
  have hu0 : 0 ≤ u := hs.trans hu.1
  have huT := lt_lifespan hu.2 ht
  have hc4 := c4_pos
  have hφ : 0 ≤ φ := (hnorm_nonneg 2 g).trans h.force_le
  obtain ⟨hψ2, hwx, hnx, -, -, hR⟩ := prefix_sizes h hq hs ht hP hu
  have hZ := wiener_mul_y_le_zCap h hq hs ht hP hu
  obtain ⟨-, hbF, -, hbS, hWS⟩ := hP.1 u hu
  have hY : fastNorm 2 r g y u ≤ cp caps.yF := hbF.trans (le_cp _)
  have hB : slowNorm 2 r g y u ≤ cp caps.BS := hbS.trans (le_cp _)
  have hW : slowWiener r g y u ≤ cp caps.WS := hWS.trans (le_cp _)
  have hg1 : hnorm 1 g ≤ φ := (hnorm_mono (by norm_num) h.force_adm.inH).trans h.force_le
  have hψ2' : hnorm 2 (psi r 0 g u) ≤ 2 * φ := hψ2.trans (div_le_self (by positivity) hq)
  have hR1 : hnorm 2 (slowCorr r g y u) ≤ 1 := by
    refine hR.trans ?_
    rw [div_le_one hrpos]
    exact hρ
  have hY0 := cp_nonneg caps.yF
  have hB0 := cp_nonneg caps.BS
  have hW0 := cp_nonneg caps.WS
  have n1 : 0 ≤ fastNorm 2 r g y u := hnorm_nonneg _ _
  have n2 : 0 ≤ fastNorm 3 r g y u := hnorm_nonneg _ _
  have n3 := mul_nonneg (wiener_nonneg (y u)) (hnorm_nonneg 2 (y u))
  have n5 := hnorm_nonneg 2 (psi r 0 g u)
  have n6 := hnorm_nonneg 2 (slowCorr r g y u)
  have n7 := wiener_nonneg (actual r g y u)
  have n8 : 0 ≤ slowWiener r g y u := wiener_nonneg _
  have n9 := hnorm_nonneg 2 (actual r g y u)
  have n10 : 0 ≤ slowNorm 2 r g y u := hnorm_nonneg _ _
  refine (hnorm_one_corrRes_le h hr0 hu0 huT hF3).2.trans ?_
  have hmain : hnorm 1 g + c4 * fastNorm 2 r g y u / |r| *
      (24 * fastNorm 3 r g y u + 52 * (wiener (y u) * hnorm 2 (y u))) +
      8 * hnorm 2 (psi r 0 g u) * (wiener (actual r g y u) + c4 * hnorm 2 (actual r g y u) +
        c4 * hnorm 2 (psi r 0 g u)) +
      8 * hnorm 2 (slowCorr r g y u) * (slowWiener r g y u + c4 * slowNorm 2 r g y u +
        c4 * hnorm 2 (slowCorr r g y u)) ≤
      φ + c4 * cp caps.yF / |r| * (24 * fastNorm 3 r g y u + 52 * zCap φ caps) +
      8 * (2 * φ / |r|) * (cp caps.WS + c4 * cp caps.yF + c4 * (cp caps.BS + cp caps.yF) +
        c4 * (2 * φ)) +
      8 * (8 * c4 * cp caps.yF ^ 2 / |r|) * (cp caps.WS + c4 * cp caps.BS + c4 * 1) := by
    gcongr
  refine hmain.trans (le_of_eq ?_)
  simp only [budA, budB]
  ring

/-- The arithmetic of the budget. -/
private lemma budget_arith {a b Y Z q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (hK : 2 * a + b * (Y + 16 * Z) ≤ |q|) : 2 * a ^ 2 + b ^ 2 * (Y ^ 2 + 128 * Z ^ 2) ≤ q ^ 2 := by
  have hK0 : 0 ≤ 2 * a + b * (Y + 16 * Z) := by positivity
  have h2 := pow_le_pow_left₀ hK0 hK 2
  rw [sq_abs] at h2
  have e : (2 * a + b * (Y + 16 * Z)) ^ 2 = (2 * a ^ 2 + b ^ 2 * (Y ^ 2 + 128 * Z ^ 2)) +
      (2 * a ^ 2 + 128 * b ^ 2 * Z ^ 2 + 4 * a * b * Y + 64 * a * b * Z +
        32 * b ^ 2 * Y * Z) := by ring
  have hn : 0 ≤ 2 * a ^ 2 + 128 * b ^ 2 * Z ^ 2 + 4 * a * b * Y + 64 * a * b * Z +
      32 * b ^ 2 * Y * Z := by positivity
  linarith

/-- The `H¹` residual is square-integrable on every piece of the lifespan: its modes are measurable
(`aestronglyMeasurable_corrRes_mode`) and, at almost every time, `‖corrRes‖₁` is bounded by an
affine function of `‖F‖₃` (`exists_corrRes_bound`), square-integrable by the fast `H²` law. -/
theorem intervalIntegrable_corrRes_sq (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) :
    IntervalIntegrable (fun u => hnorm 1 (corrRes r g y u) ^ 2) volume s t := by
  have ht0 : 0 ≤ t := hs.trans hst
  obtain ⟨a, c, M, -, hbd⟩ := exists_corrRes_bound h hr ht
  have hI := integrableOn_hnorm_sq' (s := 1) (u := corrRes r g y) (S := Icc 0 t)
    (fun k => aestronglyMeasurable_corrRes_mode h hr ht0 ht k)
    (lintegral_hsE_one_lt_top h ht0 ht fun u hu hF3 => (hbd u hu).2 hF3)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hst]
  exact hI.mono_set fun u hu => ⟨hs.trans hu.1.le, hu.2⟩

/-- **The `L²_t H¹` residual budget** of the `H²` barriers on a piece of length `≤ 2`:
`∫_s^t ‖corrRes‖₁² ≤ 4φ² + 4` once the slow-correction roles are paid, `budgetPoly ≤ q`
(`‖Π_S g‖₁ ≤ φ` gives `2φ²(t−s) ≤ 4φ²`; the `1/q` terms contribute `≤ 4`: the fast `H³`
dissipation of the piece is bounded by the fast `H²` law, `∫ c_F² ≤ y² + 2 sup ‖Q(y,y)‖₁²`
(`fast_dissipation_le`), and the corrector derivative by `hnorm_one_kinN_fastRHS_le`, with both
derivatives on one factor). -/
theorem corrRes_budget (h : ActualSol μ φ r g y Ty) {caps : Caps} {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) (hlen : t - s ≤ 2)
    (hthr : budgetPoly φ caps ≤ |r|) (hP : OnPrefix caps r g y s t) :
    (∫ u in s..t, hnorm 1 (corrRes r g y u) ^ 2) ≤ 4 * φ ^ 2 + 4 := by
  have hφ : 0 ≤ φ := (hnorm_nonneg 2 g).trans h.force_le
  have hq : 1 ≤ |r| := (one_le_budgetPoly hφ caps).trans hthr
  have hr0 : r ≠ 0 := fun h0 => by rw [h0, abs_zero] at hq; linarith
  obtain ⟨hK, hρ⟩ := budget_le hφ caps
  have hY0 := cp_nonneg caps.yF
  have hB0 := cp_nonneg caps.BS
  have hW0 := cp_nonneg caps.WS
  have hc4 := c4_pos
  have hZ0 : 0 ≤ zCap φ caps := by unfold zCap; positivity
  have ha0 : 0 ≤ budA φ caps := by unfold budA; positivity
  have hb0 : 0 ≤ budB caps := by unfold budB; positivity
  have hK2 := budget_arith ha0 hb0 hY0 hZ0 (hK.trans hthr)
  set a := budA φ caps
  set b := budB caps
  set Y := cp caps.yF
  set Z := zCap φ caps
  have hr2 : 0 < r ^ 2 := by positivity
  -- the fast dissipation on the piece
  have hJ : ∫ u in s..t, fastNorm 3 r g y u ^ 2 ≤ Y ^ 2 + 128 * Z ^ 2 := by
    have hD : ∀ u ∈ Icc s t, hnorm 1 (Qphase (r * u) (y u) (y u)) ≤ 8 * Z := fun u hu => by
      have hy := (h.sol.adm u (hs.trans hu.1) (lt_lifespan hu.2 ht)).mz
      have h1 := (hnorm_Qm_one_bound (phaseM_bdd (r * u)) hy hy).2
      have h2 := wiener_mul_y_le_zCap h hq hs ht hP hu
      have e : hnorm 2 (y u) * wiener (y u) = wiener (y u) * hnorm 2 (y u) := mul_comm _ _
      have h3 : hnorm 1 (Qphase (r * u) (y u) (y u)) ≤
          4 * (wiener (y u) * hnorm 2 (y u) + hnorm 2 (y u) * wiener (y u)) := h1
      rw [e] at h3
      linarith
    have hF : fastNorm 2 r g y s ≤ Y := (hP.1 s ⟨le_rfl, hst⟩).2.1.trans (le_cp _)
    have hF2 : fastNorm 2 r g y s ^ 2 ≤ Y ^ 2 := pow_le_pow_left₀ (hnorm_nonneg _ _) hF 2
    have hd := fast_dissipation_le h hs hst ht hD
    have hts : 0 ≤ t - s := sub_nonneg.2 hst
    nlinarith [sq_nonneg Z, mul_le_mul_of_nonneg_left hlen (sq_nonneg (8 * Z))]
  -- the bound at almost every time
  have hae : ∀ᵐ u ∂(volume.restrict (Icc s t)), hnorm 1 (corrRes r g y u) ^ 2 ≤
      2 * φ ^ 2 + 4 * a ^ 2 / r ^ 2 + 4 * b ^ 2 / r ^ 2 * fastNorm 3 r g y u ^ 2 := by
    filter_upwards [ae_fast_three h hs hst ht, ae_restrict_mem measurableSet_Icc] with u hF3 hu
    have hb := hnorm_one_corrRes_caps h hq hs ht hP (hρ.trans hthr) hu hF3
    have hc := hnorm_nonneg 3 (PiF (actual r g y u))
    have h1 : hnorm 1 (corrRes r g y u) ^ 2 ≤
        (φ + (a + b * fastNorm 3 r g y u) / |r|) ^ 2 :=
      pow_le_pow_left₀ (hnorm_nonneg _ _) hb 2
    have e : (a + b * fastNorm 3 r g y u) ^ 2 / r ^ 2 =
        ((a + b * fastNorm 3 r g y u) / |r|) ^ 2 := by
      rw [div_pow, sq_abs]
    have h2 : (a + b * fastNorm 3 r g y u) ^ 2 ≤
        2 * a ^ 2 + 2 * (b ^ 2 * fastNorm 3 r g y u ^ 2) := by
      nlinarith [sq_nonneg (a - b * fastNorm 3 r g y u)]
    have h3 : (φ + (a + b * fastNorm 3 r g y u) / |r|) ^ 2 ≤
        2 * φ ^ 2 + 2 * ((a + b * fastNorm 3 r g y u) ^ 2 / r ^ 2) := by
      rw [e]
      nlinarith [sq_nonneg (φ - (a + b * fastNorm 3 r g y u) / |r|)]
    have h4 : (a + b * fastNorm 3 r g y u) ^ 2 / r ^ 2 ≤
        (2 * a ^ 2 + 2 * (b ^ 2 * fastNorm 3 r g y u ^ 2)) / r ^ 2 :=
      div_le_div_of_nonneg_right h2 hr2.le
    have e2 : 2 * ((2 * a ^ 2 + 2 * (b ^ 2 * fastNorm 3 r g y u ^ 2)) / r ^ 2) =
        4 * a ^ 2 / r ^ 2 + 4 * b ^ 2 / r ^ 2 * fastNorm 3 r g y u ^ 2 := by ring
    linarith
  -- integration
  have hI1 := intervalIntegrable_corrRes_sq h hr0 hs hst ht
  have hI3 := (intervalIntegrable_fast_three h hs hst ht).const_mul (4 * b ^ 2 / r ^ 2)
  have hI2 := (intervalIntegrable_const
    (c := 2 * φ ^ 2 + 4 * a ^ 2 / r ^ 2) (μ := volume) (a := s) (b := t)).add hI3
  have hmono := intervalIntegral.integral_mono_ae_restrict hst hI1 hI2 hae
  have hval : ∫ u in s..t, (2 * φ ^ 2 + 4 * a ^ 2 / r ^ 2 +
      4 * b ^ 2 / r ^ 2 * fastNorm 3 r g y u ^ 2) = (t - s) * (2 * φ ^ 2 + 4 * a ^ 2 / r ^ 2) +
      4 * b ^ 2 / r ^ 2 * ∫ u in s..t, fastNorm 3 r g y u ^ 2 := by
    rw [intervalIntegral.integral_add intervalIntegrable_const hI3,
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul]
  rw [hval] at hmono
  have h5 : (2 * a ^ 2 + b ^ 2 * (Y ^ 2 + 128 * Z ^ 2)) / r ^ 2 ≤ 1 := by
    rw [div_le_one hr2]
    exact hK2
  have h6 : 4 * b ^ 2 / r ^ 2 * ∫ u in s..t, fastNorm 3 r g y u ^ 2 ≤
      4 * b ^ 2 / r ^ 2 * (Y ^ 2 + 128 * Z ^ 2) :=
    mul_le_mul_of_nonneg_left hJ (by positivity)
  have h7 : (t - s) * (2 * φ ^ 2 + 4 * a ^ 2 / r ^ 2) ≤ 2 * (2 * φ ^ 2 + 4 * a ^ 2 / r ^ 2) :=
    mul_le_mul_of_nonneg_right hlen (by positivity)
  have e3 : 2 * (2 * φ ^ 2 + 4 * a ^ 2 / r ^ 2) + 4 * b ^ 2 / r ^ 2 * (Y ^ 2 + 128 * Z ^ 2) =
      4 * φ ^ 2 + 4 * ((2 * a ^ 2 + b ^ 2 * (Y ^ 2 + 128 * Z ^ 2)) / r ^ 2) := by ring
  linarith

end Quant

end OVNS

end
