import OddViscousNS.Quant.Energy.Kinetic.Bounds

/-!
# E4.4 for the kinetic functional: the identities along the actual solution

`kinCorr_identity`: the kinetic correction `Re⟨N(F,F), S⟩` is absolutely continuous along the
actual solution with derivative `kinCorrRHS = ⟨S, Π_S Q_{rt}(F,F)⟩ + 2⟨S, N(F',F)⟩ +
⟨S', N(F,F)⟩` (TeX: "differentiate all input and output slots, use the slow-output resonant
null, and retain the two mixed orders"), from the general multilinear correction lemma
`trilinear_integral_identity` (`Derivative.lean`) with the paths `F, S` of `Actual.lean`.
`W0_identity`: the TeX derivative of `W₀`,
`W₀(t) − W₀(s) = ∫ₛᵗ (−2a_F² − 2⟨F, H_ψ⟩ − 2⟨S', N(F,F)⟩ − 4⟨S, N(F',F)⟩)`, in which the exchange
term `2⟨S, Q(F,F)⟩` of the kinetic law (`fast_energy_identity`, `pair_fast_Qphase`) has cancelled
against the frozen-amplitude derivative of `N(F,F)`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS

variable {r : ℝ}

namespace Quant

variable {μ φ : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-- The kinetic correction as a triad sum: `Re⟨N(F,F), S⟩ = Re ∑_{(p,q)} tripT (kinM r (rt)) F F S`
along the actual solution. -/
theorem kinCorr_eq_tsum (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {t : ℝ} (ht : 0 ≤ t)
    (htT : ENNReal.ofReal t < Ty) :
    kinCorr r g y t = (∑' x : Mode × Mode, tripT (kinM r (r * t)) (PiF (actual r g y t))
      (PiF (actual r g y t)) (PiS (actual r g y t)) x.1 x.2).re := by
  have hx := actual_adm h ht htT
  have hF : Adm 2 (PiF (actual r g y t)) := hx.PiF
  have hS : Adm 2 (PiS (actual r g y t)) := hx.PiS
  have hF2 : Summable fun k => ‖PiF (actual r g y t) k‖ ^ 2 :=
    summable_norm_sq_of_inH (hF.inH.mono (by norm_num))
  have hF1 : Summable fun k => ‖PiF (actual r g y t) k‖ := summable_wiener hF.inH
  have hS2 : Summable fun k => ‖PiS (actual r g y t) k‖ ^ 2 :=
    summable_norm_sq_of_inH (hS.inH.mono (by norm_num))
  exact pair_kinN_eq_re_tsum hr (r * t) hS.real hF2 hF2
    (summable_tripT_kinM hr (r * t) hF1 hF2 hS2)

/-- The integrand of the derivative of the kinetic correction (TeX: "differentiate all input and
output slots"): `⟨S, Π_S Q_{rt}(F,F)⟩ + 2⟨S, N(F',F)⟩ + ⟨S', N(F,F)⟩`, with `F' = fastRHS`,
`S' = slowRHS` (the slow-output resonant null has already removed `Q_res`, `tripT_kinDM_eq`). -/
def kinCorrRHS (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  pair 0 (PiS (actual r g y u))
      (Qphase (r * u) (PiF (actual r g y u)) (PiF (actual r g y u))) +
    2 * pair 0 (PiS (actual r g y u))
      (kinN r (r * u) (fastRHS r g y u) (PiF (actual r g y u))) +
    pair 0 (slowRHS r g y u)
      (kinN r (r * u) (PiF (actual r g y u)) (PiF (actual r g y u)))

/-- The real part of the derivative family along the actual solution is `kinCorrRHS`: the
`e^{iτΦ}` slot is `⟨S, Q_{rt}(F,F)⟩` (`tripT_kinDM_eq`, `pair_Qphase_eq_re_tsum`), the two mixed
slots are `⟨S, N(F',F)⟩` each (`kinN_comm`), and the output slot is `⟨S', N(F,F)⟩`. -/
lemma tripDPath_re_eq (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) :
    (∑' x : Mode × Mode, tripDPath (fun v => kinM r (r * v)) (fun v => kinDM (r * v))
      (fun v => PiF (actual r g y v)) (fastRHS r g y) (fun v => PiF (actual r g y v))
      (fastRHS r g y) (fun v => PiS (actual r g y v)) (slowRHS r g y) u x).re =
      kinCorrRHS r g y u := by
  have hx := actual_adm h hu huT
  have hF : Adm 2 (PiF (actual r g y u)) := hx.PiF
  have hS : Adm 2 (PiS (actual r g y u)) := hx.PiS
  have hXF : PiF (PiF (actual r g y u)) = PiF (actual r g y u) := by
    funext k; by_cases hk : k 2 = 0 <;> simp [PiF, hk]
  have hZS : PiS (PiS (actual r g y u)) = PiS (actual r g y u) := by
    funext k; by_cases hk : k 2 = 0 <;> simp [PiS, hk]
  have hF1 : Summable fun k => ‖PiF (actual r g y u) k‖ := summable_wiener hF.inH
  have hF2 : Summable fun k => ‖PiF (actual r g y u) k‖ ^ 2 :=
    summable_norm_sq_of_inH (hF.inH.mono (by norm_num))
  have hS2 : Summable fun k => ‖PiS (actual r g y u) k‖ ^ 2 :=
    summable_norm_sq_of_inH (hS.inH.mono (by norm_num))
  have hF'2 := (fastRHS_l2 h hu huT).1
  have hS'2 := (slowRHS_l2 h hu huT).1
  -- the four summabilities (unweighted)
  have unw : ∀ {M : Mult} {A B Cf : Field},
      Summable (fun x : Mode × Mode => (sobWeight 0 (x.1 + x.2) : ℂ) * tripT M A B Cf x.1 x.2) →
      Summable (fun x : Mode × Mode => tripT M A B Cf x.1 x.2) := fun {M A B Cf} hs =>
    (summable_congr fun x => weight_zero_mul (tripT_zero_of_add_eq_zero M A B Cf)).mp hs
  have w1 := summable_tripT (phaseM_bdd (r * u)) (σ := 0) (by norm_num) hF.mz hF.mz hS.mz
  have w2 := summable_tripT_kinM' hr (r * u) hF'2 hF1 hS2
  have w3 := summable_tripT_kinM hr (r * u) hF1 hF'2 hS2
  have w4 := summable_tripT_kinM hr (r * u) hF1 hF2 hS'2
  have t1 : Summable fun x : Mode × Mode =>
      tripT (kinDM (r * u)) (PiF (actual r g y u)) (PiF (actual r g y u)) (PiS (actual r g y u))
        x.1 x.2 := by
    refine (unw w1).congr fun x => ?_
    exact (tripT_kinDM_eq (r * u) hXF hZS x.1 x.2).symm
  have t2 := unw w2
  have t3 := unw w3
  have t4 := unw w4
  have e : (∑' x : Mode × Mode, tripDPath (fun v => kinM r (r * v)) (fun v => kinDM (r * v))
      (fun v => PiF (actual r g y v)) (fastRHS r g y) (fun v => PiF (actual r g y v))
      (fastRHS r g y) (fun v => PiS (actual r g y v)) (slowRHS r g y) u x) =
      (∑' x : Mode × Mode, tripT (kinDM (r * u)) (PiF (actual r g y u)) (PiF (actual r g y u))
        (PiS (actual r g y u)) x.1 x.2) +
      (∑' x : Mode × Mode, tripT (kinM r (r * u)) (fastRHS r g y u) (PiF (actual r g y u))
        (PiS (actual r g y u)) x.1 x.2) +
      (∑' x : Mode × Mode, tripT (kinM r (r * u)) (PiF (actual r g y u)) (fastRHS r g y u)
        (PiS (actual r g y u)) x.1 x.2) +
      (∑' x : Mode × Mode, tripT (kinM r (r * u)) (PiF (actual r g y u)) (PiF (actual r g y u))
        (slowRHS r g y u) x.1 x.2) := by
    rw [← t1.tsum_add t2, ← (t1.add t2).tsum_add t3, ← ((t1.add t2).add t3).tsum_add t4]
    exact tsum_congr fun x => by simp only [tripDPath, tripD]
  rw [e, Complex.add_re, Complex.add_re, Complex.add_re]
  have r1 : (∑' x : Mode × Mode, tripT (kinDM (r * u)) (PiF (actual r g y u))
      (PiF (actual r g y u)) (PiS (actual r g y u)) x.1 x.2).re =
      pair 0 (PiS (actual r g y u))
        (Qphase (r * u) (PiF (actual r g y u)) (PiF (actual r g y u))) := by
    have e1 : (∑' x : Mode × Mode, tripT (kinDM (r * u)) (PiF (actual r g y u))
        (PiF (actual r g y u)) (PiS (actual r g y u)) x.1 x.2) =
        ∑' x : Mode × Mode, tripT (phaseM (r * u)) (PiF (actual r g y u))
          (PiF (actual r g y u)) (PiS (actual r g y u)) x.1 x.2 :=
      tsum_congr fun x => tripT_kinDM_eq (r * u) hXF hZS x.1 x.2
    rw [e1]
    exact (pair_Qphase_eq_re_tsum (r * u) hS.real hF.mz hF.mz hS.mz).symm
  have r2 : (∑' x : Mode × Mode, tripT (kinM r (r * u)) (fastRHS r g y u) (PiF (actual r g y u))
      (PiS (actual r g y u)) x.1 x.2).re =
      pair 0 (PiS (actual r g y u)) (kinN r (r * u) (fastRHS r g y u) (PiF (actual r g y u))) :=
    (pair_kinN_eq_re_tsum hr (r * u) hS.real hF'2 hF2 w2).symm
  have r3 : (∑' x : Mode × Mode, tripT (kinM r (r * u)) (PiF (actual r g y u)) (fastRHS r g y u)
      (PiS (actual r g y u)) x.1 x.2).re =
      pair 0 (PiS (actual r g y u)) (kinN r (r * u) (fastRHS r g y u) (PiF (actual r g y u))) := by
    rw [← kinN_comm]
    exact (pair_kinN_eq_re_tsum hr (r * u) hS.real hF2 hF'2 w3).symm
  have r4 : (∑' x : Mode × Mode, tripT (kinM r (r * u)) (PiF (actual r g y u))
      (PiF (actual r g y u)) (slowRHS r g y u) x.1 x.2).re =
      pair 0 (slowRHS r g y u) (kinN r (r * u) (PiF (actual r g y u)) (PiF (actual r g y u))) :=
    (pair_kinN_eq_re_tsum hr (r * u) (slowRHS_real h hu huT) hF2 hF2 w4).symm
  rw [r1, r2, r3, r4]
  unfold kinCorrRHS
  ring

/-- **E4.4 for the kinetic functional** (spec risk R5; survey §2.1 (c)): along the actual
solution the kinetic correction `Re⟨N(F,F),S⟩` is absolutely continuous with derivative
`kinCorrRHS`.

Proof plan (all ingredients are in this file): write `kinCorr = Re ∑_{(p,q)} tripT (kinM r (rt))
F F S` (`kinCorr_eq_tsum`); apply `trilinear_integral_identity` on `[s,t]` with the paths
`X = Y = F`, `Z = S`, `X' = Y' = fastRHS`, `Z' = slowRHS` (`fast_mode`, `slow_mode`,
`continuousOn_fastRHS_mode`, `continuousOn_slowRHS_mode`) and the multiplier family
`m u = kinM r (r u)`, `m' u = kinDM r (r u)` (`hasDerivAt_kinM`, `continuous_kinDM`); the
summability at the endpoints is `summable_tripT_kinM`; the uniform control `hB` on
`∑ ‖tripD‖` is the sum of four `ℓ¹ℓ²ℓ²` bounds (`norm_tripT_le` for the `kinDM` slot through
`tripT_kinDM_eq`, `norm_tripT_kinM_le` for the other three; `summable_tri_first/second/third`),
with the sup bounds `‖F‖₂, ‖S‖₂ ≤ ‖y‖₂ + ‖ψ‖₂` (`IsHeatSol.exists_bound`, `psi_bound`),
`‖F'‖_{ℓ²} ≤ ‖F‖₂ + ‖Q(y,y)‖₀`, `‖S'‖_{ℓ²} ≤ ‖S‖₂ + ‖Q(y,y)‖₀ + ‖g‖₀` (`exists_Qphase_bound`)
and `𝒜(F) ≤ c₄‖F‖₂` (`wiener_le`).  Finally take real parts (`Complex.reCLM`,
`ContinuousLinearMap.intervalIntegral_comp_comm`, with `intervalIntegrable_tsum_of_bound`) and
identify the four real sums by `pair_Qphase_eq_re_tsum` (after `tripT_kinDM_eq`) and
`pair_kinN_eq_re_tsum` (`kinN_comm` merges the two mixed orders; `slowRHS` is real since `S`,
`Q(y,y)` and `g` are). -/
theorem kinCorr_identity (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) :
    IntervalIntegrable (kinCorrRHS r g y) volume s t ∧
      kinCorr r g y t - kinCorr r g y s = ∫ u in s..t, kinCorrRHS r g y u := by
  have ht0 : 0 ≤ t := hs.trans hst
  have hr' : 0 < |r| := abs_pos.mpr hr
  have hmem : ∀ u ∈ Icc s t, 0 ≤ u ∧ ENNReal.ofReal u < Ty := fun u hu =>
    ⟨hs.trans hu.1, lt_lifespan hu.2 ht⟩
  -- the paths and the multiplier family
  set X : ℝ → Field := fun u => PiF (actual r g y u) with hXdef
  set Z : ℝ → Field := fun u => PiS (actual r g y u) with hZdef
  set m : ℝ → Mult := fun u => kinM r (r * u) with hmdef
  set m' : ℝ → Mult := fun u => kinDM (r * u) with hm'def
  -- pointwise facts
  have hXF : ∀ u, PiF (X u) = X u := fun u => by
    funext k; by_cases hk : k 2 = 0 <;> simp [hXdef, PiF, hk]
  have hZS : ∀ u, PiS (Z u) = Z u := fun u => by
    funext k; by_cases hk : k 2 = 0 <;> simp [hZdef, PiS, hk]
  have hadm : ∀ u ∈ Icc s t, Adm 2 (X u) ∧ Adm 2 (Z u) := fun u hu =>
    ⟨(actual_adm h (hmem u hu).1 (hmem u hu).2).PiF, (actual_adm h (hmem u hu).1 (hmem u hu).2).PiS⟩
  have hX1 : ∀ u ∈ Icc s t, Summable fun k => ‖X u k‖ := fun u hu =>
    summable_wiener (hadm u hu).1.inH
  have hX2 : ∀ u ∈ Icc s t, Summable fun k => ‖X u k‖ ^ 2 := fun u hu =>
    summable_norm_sq_of_inH ((hadm u hu).1.inH.mono (by norm_num))
  have hXg : ∀ u ∈ Icc s t, Summable fun k => (absk k * ‖X u k‖) ^ 2 := fun u hu =>
    summable_grad_sq (hadm u hu).1.mz
  have hZ1 : ∀ u ∈ Icc s t, Summable fun k => ‖Z u k‖ := fun u hu =>
    summable_wiener (hadm u hu).2.inH
  have hZ2 : ∀ u ∈ Icc s t, Summable fun k => ‖Z u k‖ ^ 2 := fun u hu =>
    summable_norm_sq_of_inH ((hadm u hu).2.inH.mono (by norm_num))
  have hX'2 : ∀ u ∈ Icc s t, Summable fun k => ‖fastRHS r g y u k‖ ^ 2 := fun u hu =>
    (fastRHS_l2 h (hmem u hu).1 (hmem u hu).2).1
  have hZ'2 : ∀ u ∈ Icc s t, Summable fun k => ‖slowRHS r g y u k‖ ^ 2 := fun u hu =>
    (slowRHS_l2 h (hmem u hu).1 (hmem u hu).2).1
  -- derivatives and continuity of the paths on `[s, t]`
  have hXd : ∀ k, ∀ u ∈ Icc s t,
      HasDerivWithinAt (fun v => X v k) (fastRHS r g y u k) (Icc s t) u := fun k u hu =>
    (fast_mode h k (hmem u hu).1 (hmem u hu).2).mono fun v hv => show v ∈ Ici 0 from hs.trans hv.1
  have hZd : ∀ k, ∀ u ∈ Icc s t,
      HasDerivWithinAt (fun v => Z v k) (slowRHS r g y u k) (Icc s t) u := fun k u hu =>
    (slow_mode h k (hmem u hu).1 (hmem u hu).2).mono fun v hv => show v ∈ Ici 0 from hs.trans hv.1
  have hX'c : ∀ k, ContinuousOn (fun u => fastRHS r g y u k) (Icc s t) := fun k =>
    (continuousOn_fastRHS_mode h ht0 ht k).mono (Icc_subset_Icc_left hs)
  have hZ'c : ∀ k, ContinuousOn (fun u => slowRHS r g y u k) (Icc s t) := fun k =>
    (continuousOn_slowRHS_mode h ht0 ht k).mono (Icc_subset_Icc_left hs)
  have hmd : ∀ a' b' c p q, ∀ u ∈ Icc s t,
      HasDerivWithinAt (fun v => m v a' b' c p q) (m' u a' b' c p q) (Icc s t) u :=
    fun a' b' c p q u _ => (hasDerivAt_kinM hr a' b' c p q u).hasDerivWithinAt
  have hm'c : ∀ a' b' c p q, ContinuousOn (fun u => m' u a' b' c p q) (Icc s t) :=
    fun a' b' c p q => (continuous_kinDM a' b' c p q).continuousOn
  -- summability at the endpoints
  have hsum : ∀ u ∈ Icc s t, Summable (tripPath m X X Z u) := fun u hu => by
    have := (summable_congr fun x =>
      weight_zero_mul (tripT_zero_of_add_eq_zero (m u) (X u) (X u) (Z u))).mp
      (summable_tripT_kinM hr (r * u) (hX1 u hu) (hX2 u hu) (hZ2 u hu))
    exact this
  -- the uniform bound
  obtain ⟨Mx, hMx0, hMx⟩ := exists_actual_bound h hr ht
  obtain ⟨D, hD0, hD⟩ := exists_Qphase_bound h ht
  have hg2 := hnorm_nonneg 2 g
  set C := 16 * (c4 * Mx * (Mx * Mx)) + 2 / |r| * (2 * (c4 * Mx * ((Mx + D) * Mx)) +
    c4 * Mx * (Mx * (Mx + D + hnorm 2 g))) with hCdef
  have hB : ∀ u ∈ Icc s t,
      Summable (fun x =>
        ‖tripDPath m m' X (fastRHS r g y) X (fastRHS r g y) Z (slowRHS r g y) u x‖) ∧
      ∑' x, ‖tripDPath m m' X (fastRHS r g y) X (fastRHS r g y) Z (slowRHS r g y) u x‖ ≤ C := by
    intro u hu
    have hu0 := (hmem u hu).1
    have huT := (hmem u hu).2
    have hu' : u ∈ Icc 0 t := ⟨hu0, hu.2⟩
    obtain ⟨hsum', hle⟩ := tripD_summable_bound hr (r * u) (hXF u) (hZS u) (hX1 u hu) (hX2 u hu)
      (hXg u hu) (hX'2 u hu) (hZ1 u hu) (hZ2 u hu) (hZ'2 u hu)
    refine ⟨hsum', hle.trans ?_⟩
    have hx2 : hnorm 2 (actual r g y u) ≤ Mx := hMx u hu'
    have hF2 : hnorm 2 (X u) ≤ Mx := (hnorm_PiF_le (actual_adm h hu0 huT).inH).trans hx2
    have hS2 : hnorm 2 (Z u) ≤ Mx := (hnorm_PiS_le (actual_adm h hu0 huT).inH).trans hx2
    have e1 : ∑' k, ‖Z u k‖ = wiener (Z u) := rfl
    have e2 : ∑' k, ‖X u k‖ = wiener (X u) := rfl
    have hWS : ∑' k, ‖Z u k‖ ≤ c4 * Mx := by
      rw [e1]; exact (wiener_le (hadm u hu).2.mz).trans (mul_le_mul_of_nonneg_left hS2 c4_pos.le)
    have hWF : ∑' k, ‖X u k‖ ≤ c4 * Mx := by
      rw [e2]; exact (wiener_le (hadm u hu).1.mz).trans (mul_le_mul_of_nonneg_left hF2 c4_pos.le)
    have hG1 : Real.sqrt (∑' k, (absk k * ‖X u k‖) ^ 2) ≤ Mx := by
      rw [sqrt_tsum_grad_sq]
      exact (hnorm_mono (by norm_num) (hadm u hu).1.inH).trans hF2
    have hN0 : Real.sqrt (∑' k, ‖X u k‖ ^ 2) ≤ Mx := by
      rw [← hnorm_zero_eq (hadm u hu).1.mean]
      exact (hnorm_mono (by norm_num) (hadm u hu).1.inH).trans hF2
    have hNS : Real.sqrt (∑' k, ‖Z u k‖ ^ 2) ≤ Mx := by
      rw [← hnorm_zero_eq (hadm u hu).2.mean]
      exact (hnorm_mono (by norm_num) (hadm u hu).2.inH).trans hS2
    have hN' : Real.sqrt (∑' k, ‖fastRHS r g y u k‖ ^ 2) ≤ Mx + D :=
      (fastRHS_l2 h hu0 huT).2.trans (add_le_add hF2 (hD u hu').2)
    have hNS' : Real.sqrt (∑' k, ‖slowRHS r g y u k‖ ^ 2) ≤ Mx + D + hnorm 2 g :=
      (slowRHS_l2 h hu0 huT).2.trans (add_le_add (add_le_add hS2 (hD u hu').2) le_rfl)
    have n1 : 0 ≤ ∑' k, ‖Z u k‖ := tsum_nonneg fun _ => norm_nonneg _
    have n2 : 0 ≤ ∑' k, ‖X u k‖ := tsum_nonneg fun _ => norm_nonneg _
    have n3 := Real.sqrt_nonneg (∑' k, (absk k * ‖X u k‖) ^ 2)
    have n4 := Real.sqrt_nonneg (∑' k, ‖X u k‖ ^ 2)
    have n5 := Real.sqrt_nonneg (∑' k, ‖Z u k‖ ^ 2)
    have n6 := Real.sqrt_nonneg (∑' k, ‖fastRHS r g y u k‖ ^ 2)
    have n7 := Real.sqrt_nonneg (∑' k, ‖slowRHS r g y u k‖ ^ 2)
    have hcM : 0 ≤ c4 * Mx := mul_nonneg c4_pos.le hMx0
    have hMD : 0 ≤ Mx + D := add_nonneg hMx0 hD0
    have hMDg : 0 ≤ Mx + D + hnorm 2 g := add_nonneg hMD hg2
    rw [hCdef]
    gcongr
  -- the complex identity
  have key := trilinear_integral_identity (m := m) (m' := m') (X := X) (X' := fastRHS r g y)
    (Y := X) (Y' := fastRHS r g y) (Z := Z) (Z' := slowRHS r g y) hst hmd hm'c hXd hX'c hXd hX'c
    hZd hZ'c (hsum s ⟨le_rfl, hst⟩) (hsum t ⟨hst, le_rfl⟩) hB
  -- continuity of the derivative family and integrability
  have hmc : ∀ a' b' c p q, ContinuousOn (fun u => m u a' b' c p q) (Icc s t) :=
    fun a' b' c p q u hu => (hmd a' b' c p q u hu).continuousWithinAt
  have hXc : ∀ k, ContinuousOn (fun u => X u k) (Icc s t) := fun k u hu =>
    (hXd k u hu).continuousWithinAt
  have hZc : ∀ k, ContinuousOn (fun u => Z u k) (Icc s t) := fun k u hu =>
    (hZd k u hu).continuousWithinAt
  have hc : ∀ x : Mode × Mode, ContinuousOn
      (fun u => tripDPath m m' X (fastRHS r g y) X (fastRHS r g y) Z (slowRHS r g y) u x)
      (Icc s t) := fun x =>
    continuousOn_tripDPath x (fun a' b' c => hmc a' b' c _ _) (fun a' b' c => hm'c a' b' c _ _)
      (hXc _) (hX'c _) (hXc _) (hX'c _) (hZc _) (hZ'c _)
  have hG := intervalIntegrable_tsum_of_bound hst hc hB
  -- real parts: the left side
  have hL : (∑' x, tripPath m X X Z t x).re - (∑' x, tripPath m X X Z s x).re =
      kinCorr r g y t - kinCorr r g y s := by
    rw [kinCorr_eq_tsum h hr ht0 ht, kinCorr_eq_tsum h hr hs (lt_lifespan hst ht)]
    rfl
  -- real parts: the integrand
  have hre : ∀ u ∈ Icc s t,
      (∑' x, tripDPath m m' X (fastRHS r g y) X (fastRHS r g y) Z (slowRHS r g y) u x).re =
        kinCorrRHS r g y u := fun u hu =>
    tripDPath_re_eq h hr (hmem u hu).1 (hmem u hu).2
  -- integrability of the real part
  have hGre : IntervalIntegrable (fun u =>
      (∑' x, tripDPath m m' X (fastRHS r g y) X (fastRHS r g y) Z (slowRHS r g y) u x).re)
      volume s t := by
    refine hG.mono_fun ?_ ?_
    · exact Complex.continuous_re.comp_aestronglyMeasurable
        ((intervalIntegrable_iff.1 hG).aestronglyMeasurable)
    · exact Filter.Eventually.of_forall fun u => by
        simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm _
  have hI : IntervalIntegrable (kinCorrRHS r g y) volume s t := by
    refine hGre.congr fun u hu => hre u ?_
    rw [uIoc_of_le hst] at hu
    exact Ioc_subset_Icc_self hu
  refine ⟨hI, ?_⟩
  have hR := congrArg Complex.re key
  rw [Complex.sub_re, hL] at hR
  rw [hR, ← Complex.reCLM_apply, ← Complex.reCLM.intervalIntegral_comp_comm hG]
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le hst] at hu
  simp only [Complex.reCLM_apply]
  exact hre u hu

/-- The integrand of the derivative of `W₀` (TeX: "`W₀' = −2a_F² − 2⟨F,H_ψ⟩ − 2⟨S',N(F,F)⟩ −
4⟨S,N(F',F)⟩`", the exchange term `2⟨S,Q(F,F)⟩` having cancelled against the frozen-amplitude
derivative of `N(F,F)`). -/
def W0RHS (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  -2 * fastNorm 1 r g y u ^ 2 - 2 * pair 0 (PiF (actual r g y u)) (Hpsi r g y u) -
    2 * pair 0 (slowRHS r g y u) (kinN r (r * u) (PiF (actual r g y u)) (PiF (actual r g y u))) -
    4 * pair 0 (PiS (actual r g y u)) (kinN r (r * u) (fastRHS r g y u) (PiF (actual r g y u)))

/-- The pointwise algebra of the derivative of `W₀`: the kinetic law's pairing
`⟨F, −Π_F Q(y,y)⟩` equals `⟨S, Q(F,F)⟩ − ⟨F, H_ψ⟩` (`pair_fast_Qphase`). -/
lemma pair_fast_force_eq (h : ActualSol μ φ r g y Ty) {u : ℝ} (hu : 0 ≤ u)
    (huT : ENNReal.ofReal u < Ty) :
    pair 0 (PiF (actual r g y u)) (-PiF (Qphase (r * u) (y u) (y u))) =
      pair 0 (PiS (actual r g y u))
        (Qphase (r * u) (PiF (actual r g y u)) (PiF (actual r g y u))) -
      pair 0 (PiF (actual r g y u)) (Hpsi r g y u) := by
  have hx := actual_adm h hu huT
  have hy := h.sol.adm u hu huT
  have hF' : PiF (PiF (actual r g y u)) = PiF (actual r g y u) := by
    funext k; by_cases hk : k 2 = 0 <;> simp [PiF, hk]
  have hQx : InH (0 - 1) (Qphase (r * u) (actual r g y u) (actual r g y u)) :=
    ((hnorm_Qm_zero_le (phaseM_bdd _) hx.mz hx.mz).1).mono (by norm_num)
  have hQy : InH 0 (Qphase (r * u) (y u) (y u)) :=
    (hnorm_Qm_zero_le (phaseM_bdd _) hy.mz hy.mz).1
  have hH : InH (0 - 1) (Hpsi r g y u) :=
    (hQy.sub (hnorm_Qm_zero_le (phaseM_bdd _) hx.mz hx.mz).1).mono (by norm_num)
  have hF1 : InH (0 + 1) (PiF (actual r g y u)) := hx.PiF.inH.mono (by norm_num)
  have e : Qphase (r * u) (y u) (y u) =
      Qphase (r * u) (actual r g y u) (actual r g y u) + Hpsi r g y u := by
    simp [Hpsi]
  rw [pair_neg_right, pair_PiF_right 0 hF', e, pair_add hF1 hQx hH, pair_fast_Qphase _ hx]
  ring

/-- **The TeX derivative of `W₀`** (eq. quant-kinetic, before the floors are paid):
`W₀(t) − W₀(s) = ∫ₛᵗ (−2a_F² − 2⟨F,H_ψ⟩ − 2⟨S',N(F,F)⟩ − 4⟨S,N(F',F)⟩)`, from the kinetic law
`fast_energy_identity`, the exchange identity `pair_fast_Qphase` and `kinCorr_identity`. -/
theorem W0_identity (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty) :
    W0 r g y t - W0 r g y s = ∫ u in s..t, W0RHS r g y u := by
  obtain ⟨hI1, hI2⟩ := intervalIntegrable_fast h hs hst ht
  have hE := fast_energy_identity h hs hst ht
  obtain ⟨hI3, hK⟩ := kinCorr_identity h hr hs hst ht
  have e : W0 r g y t - W0 r g y s =
      ∫ u in s..t, (-2 * fastNorm 1 r g y u ^ 2 +
        2 * pair 0 (PiF (actual r g y u)) (-PiF (Qphase (r * u) (y u) (y u))) -
        2 * kinCorrRHS r g y u) := by
    rw [intervalIntegral.integral_sub ((hI1.const_mul _).add (hI2.const_mul _)) (hI3.const_mul _),
      intervalIntegral.integral_add (hI1.const_mul _) (hI2.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    unfold W0
    linarith
  rw [e]
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le hst] at hu
  have hu0 : 0 ≤ u := hs.trans hu.1
  have huT := lt_lifespan hu.2 ht
  simp only [W0RHS, kinCorrRHS]
  rw [pair_fast_force_eq h hu0 huT]
  ring

end Quant

end OVNS

end
