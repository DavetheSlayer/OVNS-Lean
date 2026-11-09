import OddViscousNS.Closed.Certificate
import OddViscousNS.Closed.XYode
import OddViscousNS.Closed.CubicCont
import OddViscousNS.Closed.Barrier
import OddViscousNS.Closed.Transfer
import OddViscousNS.Closed.Cubic

/-!
# Invariance of the barrier region and the unforced metric bounds

Let `y` be a heat solution of the unforced filtered system `y' = −Ay − Q_{rt}(y,y)` on `[0,T)`
with `‖y 0‖₂ ≤ s = 97/40` (the normalized field `v = u/ν`; `w = v/s` is the scaled field).
Then `Y(y t) ≤ s²` for all `t < T` and `∫_a^b Z(y) ≤ 100000 s²`.
Proof (§6 of the reconstruction): with `X_w = X(y)/s²`, `Y_w = Y(y)/s²`, `(X_w(0), Y_w(0))` lies in
`R = {Y ≤ S̃(X)}` (`X_w(0) ≤ 1`, `3Y_w(0) ≤ 2X_w(0) + 1`, `datum_le_Stilde`); at a contact with the
piece `L_i` the laws `X' = −2J₁`, `Y' = −2Z − 2s·cubic(w)` and `edge_heat` give
`(Y_w − L_i(X_w))' < 0` (`neg_after_of_integral`, continuity from `XYode` and `CubicCont`), and
at a contact with the plateau `cubic_le_kappa` gives `Z − s|cubic| ≥ Z/200000`; so `Y_w ≤ S̃(X_w)`
(`barrier_of_local`), hence `Y_w ≤ 1`.  The interior heat `Z − s|cubic| ≥ 10⁻⁵ Z` on all of `R`
(ray argument `Stilde_ray` + `edge_heat`, or the plateau) and `integral_bound_of_le` give
`∫ Z_w ≤ 100000`.
-/

open scoped ENNReal
open MeasureTheory Set

namespace OVNS

/-! ### Field-level facts: rotation invariance, scaling, heat inequalities -/

private lemma norm_rotF_eq' (τ : ℝ) {w : Field} (hw : Adm 2 w) (k : Mode) :
    ‖rotF τ w k‖ = ‖w k‖ := by
  by_cases hk : k = 0
  · subst hk
    simp [rotF, rot, hel, hw.mean]
  · rw [show rotF τ w k = rot τ k (w k) from rfl, norm_rot, leray_of_perp hk (hw.sol k)]

private lemma Xr_rotF (τ : ℝ) {w : Field} (hw : Adm 2 w) : Xr (rotF τ w) = Xr w := by
  unfold Xr
  simp_rw [norm_rotF_eq' τ hw]

private lemma Yr_rotF (τ : ℝ) {w : Field} (hw : Adm 2 w) : Yr (rotF τ w) = Yr w := by
  unfold Yr
  simp_rw [norm_rotF_eq' τ hw]

private lemma Zr_rotF (τ : ℝ) {w : Field} (hw : Adm 2 w) : Zr (rotF τ w) = Zr w := by
  unfold Zr
  simp_rw [norm_rotF_eq' τ hw]

private lemma J1r_rotF (τ : ℝ) {w : Field} (hw : Adm 2 w) : J1r (rotF τ w) = J1r w := by
  unfold J1r
  simp_rw [norm_rotF_eq' τ hw]

private lemma norm_smul_sq' (c : ℝ) (w : Field) (k : Mode) :
    ‖((c : ℂ) • w) k‖ ^ 2 = c ^ 2 * ‖w k‖ ^ 2 := by
  rw [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

private lemma Xr_smul (c : ℝ) (w : Field) : Xr ((c : ℂ) • w) = c ^ 2 * Xr w := by
  unfold Xr
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  split_ifs
  · simp
  · rw [norm_smul_sq']

private lemma Yr_smul (c : ℝ) (w : Field) : Yr ((c : ℂ) • w) = c ^ 2 * Yr w := by
  unfold Yr
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [norm_smul_sq']
  ring

private lemma Zr_smul (c : ℝ) (w : Field) : Zr ((c : ℂ) • w) = c ^ 2 * Zr w := by
  unfold Zr
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [norm_smul_sq']
  ring

private lemma J1r_smul (c : ℝ) (w : Field) : J1r ((c : ℂ) • w) = c ^ 2 * J1r w := by
  unfold J1r
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [norm_smul_sq']
  ring

private lemma convec_smul' (c : ℂ) (w : Field) (k : Mode) :
    convec (c • w) k = c ^ 2 • convec w k := by
  have h : ∀ p, (Complex.I * dotM ((c • w) p) (k - p)) • (c • w) (k - p) =
      c ^ 2 • ((Complex.I * dotM (w p) (k - p)) • w (k - p)) := by
    intro p
    simp only [Pi.smul_apply, dotM_smul]
    module
  simp only [convec, advect, h]
  rw [tsum_const_smul'', leray_smul]

private lemma cubic_smul (c : ℝ) (w : Field) : cubic ((c : ℂ) • w) = c ^ 3 * cubic w := by
  unfold cubic
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [convec_smul', Pi.smul_apply, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    ← mul_assoc, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  ring

private lemma Yr_zero : Yr 0 = 0 := by
  simp [Yr]

private lemma hm_nonneg'' (k : Mode) : 0 ≤ hm k := weightLE2_Y.nonneg k

private lemma Zr_nonneg' (u : Field) : 0 ≤ Zr u :=
  tsum_nonneg fun k => mul_nonneg (mul_nonneg (absSq_nonneg k) (hm_nonneg'' k)) (sq_nonneg _)

private lemma J1r_nonneg' (u : Field) : 0 ≤ J1r u :=
  tsum_nonneg fun k => mul_nonneg (absSq_nonneg k) (sq_nonneg _)

/-- The edge certificate for a scaled field `c • u`, expressed in terms of `u`. -/
private lemma heat_scaled (hRB : RowBound fun _ => M₀) {i : ℕ} (hi : i < 41) {u : Field}
    (hu : Adm 2 u) (hne : u ≠ 0) {c : ℝ} (hc : 0 < c)
    (hX : c ^ 2 * Xr u ∈ Icc (kX (i + 1) : ℝ) (kX i))
    (hY : c ^ 2 * Yr u = piece i (c ^ 2 * Xr u)) :
    1 / 100000 * Zr u ≤ Zr u - (slope i : ℝ) * J1r u - 97 / 40 * c * |cubic u| := by
  have hne' : ((c : ℂ) • u) ≠ 0 := by
    intro h
    exact hne ((smul_eq_zero.mp h).resolve_left (by exact_mod_cast hc.ne'))
  have h := edge_heat hRB hi (adm_smul_real c hu) hne' (by rwa [Xr_smul])
    (by rw [Yr_smul, Xr_smul]; exact hY)
  rw [Zr_smul, J1r_smul, cubic_smul, abs_mul, abs_pow, abs_of_pos hc] at h
  have hc2 : 0 < c ^ 2 := by positivity
  refine le_of_mul_le_mul_left ?_ hc2
  linear_combination h

private lemma Yc_real : ((Yc : ℚ) : ℝ) = (1 - 1 / 100000) / ((97 / 40) * κ₀) ^ 2 := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) Yc_eq
  push_cast at h
  rw [h, κ₀]

private lemma Yc_pos' : (0 : ℝ) < (Yc : ℝ) := by exact_mod_cast Yc_pos

/-- On the plateau `Y ≤ s² Y_c` the cubic is dominated by `(1 − 1/200000) Z`. -/
private lemma plateau_heat (hRB : RowBound fun _ => M₀) {u : Field} (hu : Adm 2 u)
    (hY : Yr u ≤ (97 / 40) ^ 2 * (Yc : ℝ)) : |cubic u| ≤ (1 - 1 / 200000) * Zr u := by
  have hk := cubic_le_kappa hRB hu
  have hY0 : 0 ≤ Yr u := le_trans (Xr_nonneg hu) (Xr_le_Yr hu)
  have hκ : 0 < κ₀ := by norm_num [κ₀]
  have hsq : (κ₀ * Real.sqrt (Yr u)) ^ 2 ≤ (1 - 1 / 200000) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hY0]
    have h1 : κ₀ ^ 2 * Yr u ≤ κ₀ ^ 2 * ((97 / 40) ^ 2 * (Yc : ℝ)) :=
      mul_le_mul_of_nonneg_left hY (by positivity)
    rw [Yc_real] at h1
    have h2 : κ₀ ^ 2 * ((97 / 40) ^ 2 * ((1 - 1 / 100000) / ((97 / 40) * κ₀) ^ 2)) =
        1 - 1 / 100000 := by
      field_simp
    linarith
  have hle : κ₀ * Real.sqrt (Yr u) ≤ 1 - 1 / 200000 := by
    have h0 : 0 ≤ κ₀ * Real.sqrt (Yr u) := by positivity
    nlinarith
  calc |cubic u| ≤ κ₀ * Real.sqrt (Yr u) * Zr u := hk
    _ ≤ (1 - 1 / 200000) * Zr u := mul_le_mul_of_nonneg_right hle (Zr_nonneg' u)

/-- A contact with the barrier is either with the plateau or with some piece. -/
private lemma contact_cases (x : ℝ) : Stilde x = Yc ∨ ∃ i < 41, Stilde x = piece i x := by
  rcases max_choice (Yc : ℝ) ((Finset.range 41).sup' ⟨0, by simp⟩ fun i => piece i x) with h | h
  · exact Or.inl h
  · obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup'
      (⟨0, by simp⟩ : (Finset.range 41).Nonempty) (fun i => piece i x)
    exact Or.inr ⟨i, Finset.mem_range.mp hi, h.trans he⟩

/-- The interior heat on the barrier region: `Z − |cubic| ≥ Z/200000`. -/
private lemma region_heat (hRB : RowBound fun _ => M₀) {u : Field} (hu : Adm 2 u)
    (hX1 : Xr u / (97 / 40) ^ 2 ≤ 1)
    (hYS : Yr u / (97 / 40) ^ 2 ≤ Stilde (Xr u / (97 / 40) ^ 2)) :
    1 / 200000 * Zr u ≤ Zr u - |cubic u| := by
  by_cases hP : Yr u ≤ (97 / 40) ^ 2 * (Yc : ℝ)
  · have := plateau_heat hRB hu hP
    linarith
  push Not at hP
  have hYc := Yc_pos'
  have hne : u ≠ 0 := by
    rintro rfl
    rw [Yr_zero] at hP
    nlinarith
  obtain ⟨x, hx⟩ : ∃ x, x = Xr u / (97 / 40) ^ 2 := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = Yr u / (97 / 40) ^ 2 := ⟨_, rfl⟩
  rw [← hx] at hX1 hYS
  rw [← hv] at hYS
  have hyv : (Yc : ℝ) < v := by rw [hv, lt_div_iff₀ (by norm_num)]; linarith
  have hxy : x ≤ v := by
    rw [hx, hv]; exact div_le_div_of_nonneg_right (Xr_le_Yr hu) (by norm_num)
  have hx0 : 0 < x := by
    by_contra h
    push Not at h
    have hXc : (0 : ℝ) < Xc := by exact_mod_cast Xc_pos
    have := Stilde_eq_Yc (x := x) (by linarith)
    linarith
  have hcont : ContinuousOn (fun l => Stilde (l * x) - l * v) (Icc 1 (1 / x)) :=
    ((Stilde_continuous.comp (continuous_id.mul continuous_const)).sub
      (continuous_id.mul continuous_const)).continuousOn
  have h1x : 1 ≤ 1 / x := by rw [le_div_iff₀ hx0]; linarith
  have hmem : (0 : ℝ) ∈ Icc ((fun l => Stilde (l * x) - l * v) (1 / x))
      ((fun l => Stilde (l * x) - l * v) 1) := by
    constructor
    · simp only
      rw [one_div_mul_cancel hx0.ne']
      have h1 := Stilde_le_one (x := 1) le_rfl
      have h2 : 1 ≤ 1 / x * v := by rw [one_div_mul_eq_div, le_div_iff₀ hx0]; linarith
      linarith
    · simp only [one_mul]
      linarith
  obtain ⟨l, hl, hl0⟩ := intermediate_value_Icc' h1x hcont hmem
  simp only at hl0
  have hl1 : 1 ≤ l := hl.1
  have hlx : l * x ≤ 1 := by
    calc l * x ≤ 1 / x * x := mul_le_mul_of_nonneg_right hl.2 hx0.le
      _ = 1 := one_div_mul_cancel hx0.ne'
  have hcontact : l * v = Stilde (l * x) := by linarith
  rcases contact_cases (l * x) with hS | ⟨i, hi, hpi⟩
  · nlinarith
  have hedge := edge_of_contact hi hlx hpi.symm
  have hc : 0 < Real.sqrt l / (97 / 40) := by
    have : 0 < Real.sqrt l := Real.sqrt_pos.mpr (by linarith)
    positivity
  have hc2 : (Real.sqrt l / (97 / 40)) ^ 2 = l / (97 / 40) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by linarith)]
  have eX : (Real.sqrt l / (97 / 40)) ^ 2 * Xr u = l * x := by rw [hc2, hx]; ring
  have eY : (Real.sqrt l / (97 / 40)) ^ 2 * Yr u = l * v := by rw [hc2, hv]; ring
  have key := heat_scaled hRB hi hu hne hc (by rw [eX]; exact hedge)
    (by rw [eX, eY, hcontact, hpi])
  have e1 : 97 / 40 * (Real.sqrt l / (97 / 40)) = Real.sqrt l := by ring
  rw [e1] at key
  have hsl : 1 ≤ Real.sqrt l := Real.one_le_sqrt.mpr hl1
  have hC : |cubic u| ≤ Real.sqrt l * |cubic u| := le_mul_of_one_le_left (abs_nonneg _) hsl
  have hmJ : 0 ≤ (slope i : ℝ) * J1r u :=
    mul_nonneg (by exact_mod_cast (slope_pos i hi).le) (J1r_nonneg' u)
  have hZ := Zr_nonneg' u
  linarith

/-! ### Time-level facts along the unforced filtered solution -/

section Time

variable {r : ℝ} {T : ℝ≥0∞} {y : ℝ → Field}

private lemma goodForce_zero' : GoodForce (fun _ => (0 : Field)) 0 := by
  refine ⟨fun _ => ⟨?_, ?_, ?_, ?_⟩, fun _ => by simp [hnorm_zero], fun _ => ?_⟩
  · simp [InH]
  · intro k; simp [conjV]; rfl
  · intro k; simp [dotM]
  · rfl
  · simp [hnorm_zero]

private lemma heatPair_y' (hy : IsHeatSol (filtN r 0) (fun _ => 0) T y) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < T) :
    HeatPair 2 0 b y (fun t => 0 - filtN r 0 t (y t) (y t)) :=
  hy.heatPair (majorized_filtN r 0) goodForce_zero' hb hbT

private lemma lt_T {t b : ℝ} (htb : t ≤ b) (hbT : ENNReal.ofReal b < T) :
    ENNReal.ofReal t < T :=
  lt_of_le_of_lt (ENNReal.ofReal_le_ofReal htb) hbT

private lemma adm_y (hy : IsHeatSol (filtN r 0) (fun _ => 0) T y) {t b : ℝ} (ht : t ∈ Icc 0 b)
    (hbT : ENNReal.ofReal b < T) : Adm 2 (y t) :=
  hy.adm t ht.1 (lt_T ht.2 hbT)

private noncomputable def ωZ : Mode → ℝ := fun k => absSq k * hmet (nsq k)

private noncomputable def ωJ : Mode → ℝ := fun k => absSq k

private lemma sobWeight_two' {k : Mode} (hk : k ≠ 0) : sobWeight 2 k = absSq k ^ 2 := by
  have h0 : 0 ≤ absSq k := absSq_nonneg k
  simp only [sobWeight, hk, ↓reduceIte]
  rw [absk, show (2 : ℝ) * 2 = (4 : ℕ) by norm_num, Real.rpow_natCast,
    show 4 = 2 * 2 by rfl, pow_mul, Real.sq_sqrt h0]

private lemma weightLE2_Z : WeightLE2 ωZ := by
  refine ⟨fun k => mul_nonneg (absSq_nonneg k) (weightLE2_Y.nonneg k), by simp [ωZ, absSq],
    fun k => ?_⟩
  by_cases hk : k = 0
  · subst hk; simp [ωZ, absSq, sobWeight]
  · rw [sobWeight_two' hk, sq]
    exact mul_le_mul_of_nonneg_left (by rw [← nsq_cast]; exact hmet_upper _) (absSq_nonneg k)

private lemma weightLE2_J : WeightLE2 ωJ := by
  refine ⟨absSq_nonneg, by simp [ωJ, absSq], fun k => ?_⟩
  by_cases hk : k = 0
  · subst hk; simp [ωJ, absSq, sobWeight]
  · rw [sobWeight_two' hk]
    simp only [ωJ]
    nlinarith [one_le_absSq hk]

private lemma cont_X (hy : IsHeatSol (filtN r 0) (fun _ => 0) T y) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < T) : ContinuousOn (fun t => Xr (y t)) (Icc 0 b) :=
  (continuousOn_X hy hb hbT).congr fun t _ => (wE_X (y t)).symm

private lemma cont_Y (hy : IsHeatSol (filtN r 0) (fun _ => 0) T y) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < T) : ContinuousOn (fun t => Yr (y t)) (Icc 0 b) :=
  continuousOn_Y hy hb hbT

private lemma cont_Z (hy : IsHeatSol (filtN r 0) (fun _ => 0) T y) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < T) : ContinuousOn (fun t => Zr (y t)) (Icc 0 b) :=
  (heatPair_y' hy hb hbT).continuousOn_wE weightLE2_Z hb

private lemma cont_J (hy : IsHeatSol (filtN r 0) (fun _ => 0) T y) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < T) : ContinuousOn (fun t => J1r (y t)) (Icc 0 b) :=
  (heatPair_y' hy hb hbT).continuousOn_wE weightLE2_J hb

private lemma cont_C (hy : IsHeatSol (filtN r 0) (fun _ => 0) T y) {b : ℝ}
    (hbT : ENNReal.ofReal b < T) :
    ContinuousOn (fun t => cubic (rotF (r * t) (y t))) (Icc 0 b) :=
  continuousOn_cubic_rotF (fun _ ht => adm_y hy ht hbT) fun t₀ ht₀ =>
    (hy.cont t₀ ht₀.1 (lt_T ht₀.2 hbT)).mono_left (nhdsWithin_mono _ Icc_subset_Ici_self)

private lemma ii {f : ℝ → ℝ} {b : ℝ} (hf : ContinuousOn f (Icc 0 b)) {a t : ℝ} (ha : 0 ≤ a)
    (hat : a ≤ t) (htb : t ≤ b) : IntervalIntegrable f volume a t := by
  refine (hf.mono ?_).intervalIntegrable
  rw [uIcc_of_le hat]
  exact Icc_subset_Icc ha htb

private lemma wDiss_X_eq (u : Field) : wDiss ωX u = J1r u := by
  unfold wDiss J1r
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0 <;> simp [ωX, hk, absSq]

private lemma law_X (hy : IsHeatSol (filtN r 0) (fun _ => 0) T y) {a t : ℝ} (ha : 0 ≤ a)
    (hat : a ≤ t) (ht : ENNReal.ofReal t < T) :
    Xr (y t) + 2 * ∫ u in a..t, J1r (y u) = Xr (y a) := by
  have h := X_law hy ha hat ht
  simp only [wDiss_X_eq, wE_X] at h
  exact h

private lemma law_Y (hy : IsHeatSol (filtN r 0) (fun _ => 0) T y) {a t : ℝ} (ha : 0 ≤ a)
    (hat : a ≤ t) (ht : ENNReal.ofReal t < T) :
    Yr (y t) + 2 * ∫ u in a..t, Zr (y u) =
      Yr (y a) - 2 * ∫ u in a..t, cubic (rotF (r * u) (y u)) := by
  have h := Y_law hy ha hat ht
  simp only [wDiss_Y] at h
  exact h

private lemma integral_g (hy : IsHeatSol (filtN r 0) (fun _ => 0) T y) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < T) {a t : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) (htb : t ≤ b) (m : ℝ) :
    ∫ u in a..t, (-2 * (Zr (y u) + cubic (rotF (r * u) (y u))) + 2 * m * J1r (y u)) /
      (97 / 40) ^ 2 =
      ((Yr (y t) - Yr (y a)) - m * (Xr (y t) - Xr (y a))) / (97 / 40) ^ 2 := by
  have hZ := ii (cont_Z hy hb hbT) ha hat htb
  have hC := ii (cont_C (r := r) hy hbT) ha hat htb
  have hJ := ii (cont_J hy hb hbT) ha hat htb
  have lX := law_X hy ha hat (lt_T htb hbT)
  have lY := law_Y hy ha hat (lt_T htb hbT)
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_add (f := fun u => -2 * (Zr (y u) + cubic (rotF (r * u) (y u))))
      (g := fun u => 2 * m * J1r (y u)) ((hZ.add hC).const_mul _) (hJ.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hZ hC]
  congr 1
  linear_combination -lY + m * lX

/-- Local negativity after a contact, from the heat at the contact. -/
private lemma local_neg (hy : IsHeatSol (filtN r 0) (fun _ => 0) T y) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < T) {τ₀ : ℝ} (hτ₀ : τ₀ ∈ Ico 0 b) (m : ℝ) {φ : ℝ → ℝ}
    (hpos : 0 < Zr (y τ₀) + cubic (rotF (r * τ₀) (y τ₀)) - m * J1r (y τ₀))
    (hφ : ∀ τ ∈ Ico τ₀ b,
      φ τ ≤ ((Yr (y τ) - Yr (y τ₀)) - m * (Xr (y τ) - Xr (y τ₀))) / (97 / 40) ^ 2) :
    ∃ δ > 0, ∀ τ ∈ Ioo τ₀ (τ₀ + δ), τ < b → φ τ < 0 := by
  have hg : ContinuousOn (fun u =>
      (-2 * (Zr (y u) + cubic (rotF (r * u) (y u))) + 2 * m * J1r (y u)) / (97 / 40) ^ 2)
      (Icc 0 b) :=
    ((continuousOn_const.mul ((cont_Z hy hb hbT).add (cont_C hy hbT))).add
      (continuousOn_const.mul (cont_J hy hb hbT))).div_const _
  refine neg_after_of_integral hτ₀ (hg.mono Ico_subset_Icc_self) ?_ ?_
  · show (-2 * (Zr (y τ₀) + cubic (rotF (r * τ₀) (y τ₀))) + 2 * m * J1r (y τ₀)) /
      (97 / 40) ^ 2 < 0
    apply div_neg_of_neg_of_pos _ (by norm_num)
    linarith
  · intro τ hτ
    rw [integral_g hy hb hbT hτ₀.1 hτ.1 hτ.2.le]
    exact hφ τ hτ

/-- The datum lies in the barrier region. -/
private lemma init_region {w : Field} (hw : Adm 2 w) (h0 : hnorm 2 w ≤ 97 / 40) :
    Xr w / (97 / 40) ^ 2 ≤ 1 ∧ Yr w / (97 / 40) ^ 2 ≤ Stilde (Xr w / (97 / 40) ^ 2) := by
  have hn : hnorm 2 w ^ 2 ≤ (97 / 40) ^ 2 := pow_le_pow_left₀ (hnorm_nonneg _ _) h0 2
  have h1 := Xr_le_hnorm_sq hw
  have h2 := three_Yr_le hw
  have h3 := Xr_nonneg hw
  have hX1 : Xr w / (97 / 40) ^ 2 ≤ 1 := by rw [div_le_one (by norm_num)]; linarith
  refine ⟨hX1, ?_⟩
  have hd := datum_le_Stilde (div_nonneg h3 (by norm_num)) hX1
  have : Yr w / (97 / 40) ^ 2 ≤ (2 * (Xr w / (97 / 40) ^ 2) + 1) / 3 := by
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
    field_simp
    nlinarith
  linarith

private lemma X_le_init (hy : IsHeatSol (filtN r 0) (fun _ => 0) T y) {t : ℝ} (ht : 0 ≤ t)
    (htT : ENNReal.ofReal t < T) : Xr (y t) ≤ Xr (y 0) := by
  have h := law_X hy le_rfl ht htT
  have : 0 ≤ ∫ u in (0 : ℝ)..t, J1r (y u) :=
    intervalIntegral.integral_nonneg ht fun u _ => J1r_nonneg' _
  linarith

private lemma Ymet_eq {w : Field} (hw : Adm 2 w) : Ymet w = ENNReal.ofReal (Yr w) := by
  unfold Ymet Yr
  rw [ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (hm_nonneg'' k) (sq_nonneg _))
    (summable_Y hw)]
  rfl

private lemma Zmet_eq {w : Field} (hw : Adm 2 w) : Zmet w = ENNReal.ofReal (Zr w) := by
  unfold Zmet Zr
  rw [ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (mul_nonneg (absSq_nonneg k)
    (hm_nonneg'' k)) (sq_nonneg _)) (summable_Z hw)]
  refine tsum_congr fun k => ?_
  rw [nsq_cast]
  rfl

/-- The barrier region is invariant on `[0, b)`. -/
private lemma barrier_inv (hRB : RowBound fun _ => M₀)
    (hy : IsHeatSol (filtN r 0) (fun _ => 0) T y) (h0 : hnorm 2 (y 0) ≤ 97 / 40) {b : ℝ}
    (hb : 0 ≤ b) (hbT : ENNReal.ofReal b < T) :
    ∀ τ ∈ Ico 0 b, Yr (y τ) / (97 / 40) ^ 2 - Stilde (Xr (y τ) / (97 / 40) ^ 2) ≤ 0 := by
  have hA0 : Adm 2 (y 0) := adm_y hy ⟨le_rfl, hb⟩ hbT
  obtain ⟨hX0, hY0⟩ := init_region hA0 h0
  have hφc : ContinuousOn (fun τ => Yr (y τ) / (97 / 40) ^ 2 - Stilde (Xr (y τ) / (97 / 40) ^ 2))
      (Ico 0 b) :=
    (((cont_Y hy hb hbT).div_const _).sub (Stilde_continuous.comp_continuousOn
      ((cont_X hy hb hbT).div_const _))).mono Ico_subset_Icc_self
  refine barrier_of_local hφc (by linarith) ?_
  intro τ₀ hτ₀ hz
  beta_reduce at hz
  have hz' : Yr (y τ₀) / (97 / 40) ^ 2 = Stilde (Xr (y τ₀) / (97 / 40) ^ 2) := by linarith
  have hmem : τ₀ ∈ Icc 0 b := Ico_subset_Icc_self hτ₀
  have hA := adm_y hy hmem hbT
  have hAv : Adm 2 (rotF (r * τ₀) (y τ₀)) := hA.rotF _
  have hX1 : Xr (y τ₀) / (97 / 40) ^ 2 ≤ 1 :=
    le_trans (div_le_div_of_nonneg_right (X_le_init hy hτ₀.1 (lt_T hmem.2 hbT))
      (by norm_num)) hX0
  have hYc := Yc_pos'
  have hYpos : 0 < Yr (y τ₀) := by
    have := Yc_le_Stilde (Xr (y τ₀) / (97 / 40) ^ 2)
    have h' : 0 < Yr (y τ₀) / (97 / 40) ^ 2 := by linarith
    exact (div_pos_iff_of_pos_right (by norm_num)).mp h'
  have hne : rotF (r * τ₀) (y τ₀) ≠ 0 := by
    intro h
    have := Yr_rotF (r * τ₀) hA
    rw [h, Yr_zero] at this
    linarith
  have hZpos : 0 < Zr (y τ₀) := by
    have := Zr_pos_of_ne hAv hne
    rwa [Zr_rotF _ hA] at this
  have hCabs := neg_abs_le (cubic (rotF (r * τ₀) (y τ₀)))
  rcases contact_cases (Xr (y τ₀) / (97 / 40) ^ 2) with hP | ⟨i, hi, hpi⟩
  · have e : Yr (y τ₀) / (97 / 40) ^ 2 = Yc := hz'.trans hP
    have hYle : Yr (rotF (r * τ₀) (y τ₀)) ≤ (97 / 40) ^ 2 * (Yc : ℝ) := by
      rw [Yr_rotF _ hA, ← e]
      field_simp
      rfl
    have hheat := plateau_heat hRB hAv hYle
    rw [Zr_rotF _ hA] at hheat
    refine local_neg hy hb hbT hτ₀ 0 (by linarith) fun τ _ => ?_
    have := Yc_le_Stilde (Xr (y τ) / (97 / 40) ^ 2)
    have h3 : ((Yr (y τ) - Yr (y τ₀)) - 0 * (Xr (y τ) - Xr (y τ₀))) / (97 / 40) ^ 2 =
        Yr (y τ) / (97 / 40) ^ 2 - Yr (y τ₀) / (97 / 40) ^ 2 := by ring
    rw [h3]
    linarith
  · have hedge := edge_of_contact hi hX1 hpi.symm
    have eX : (40 / 97 : ℝ) ^ 2 * Xr (y τ₀) = Xr (y τ₀) / (97 / 40) ^ 2 := by ring
    have eY : (40 / 97 : ℝ) ^ 2 * Yr (y τ₀) = Yr (y τ₀) / (97 / 40) ^ 2 := by ring
    have key := heat_scaled hRB hi hAv hne (by norm_num : (0 : ℝ) < 40 / 97)
      (by rw [Xr_rotF _ hA, eX]; exact hedge)
      (by rw [Xr_rotF _ hA, Yr_rotF _ hA, eX, eY]; exact hz'.trans hpi)
    rw [Zr_rotF _ hA, J1r_rotF _ hA] at key
    refine local_neg hy hb hbT hτ₀ (slope i) (by linarith) fun τ _ => ?_
    have h1 := piece_le_Stilde hi (Xr (y τ) / (97 / 40) ^ 2)
    have h2 : piece i (Xr (y τ) / (97 / 40) ^ 2) - piece i (Xr (y τ₀) / (97 / 40) ^ 2) =
        slope i * (Xr (y τ) / (97 / 40) ^ 2 - Xr (y τ₀) / (97 / 40) ^ 2) := by
      unfold piece; ring
    have h3 : ((Yr (y τ) - Yr (y τ₀)) - slope i * (Xr (y τ) - Xr (y τ₀))) / (97 / 40) ^ 2 =
        Yr (y τ) / (97 / 40) ^ 2 - Yr (y τ₀) / (97 / 40) ^ 2 -
          slope i * (Xr (y τ) / (97 / 40) ^ 2 - Xr (y τ₀) / (97 / 40) ^ 2) := by ring
    rw [h3]
    linarith [hz'.trans hpi]

/-- Pointwise membership in the barrier region. -/
private lemma region_pt (hRB : RowBound fun _ => M₀)
    (hy : IsHeatSol (filtN r 0) (fun _ => 0) T y) (h0 : hnorm 2 (y 0) ≤ 97 / 40) {t : ℝ}
    (ht : 0 ≤ t) (htT : ENNReal.ofReal t < T) :
    Xr (y t) / (97 / 40) ^ 2 ≤ 1 ∧
      Yr (y t) / (97 / 40) ^ 2 ≤ Stilde (Xr (y t) / (97 / 40) ^ 2) := by
  obtain ⟨b, hb0, htb, hbT⟩ := ENNReal.lt_iff_exists_real_btwn.mp htT
  have htb' : t < b := (ENNReal.ofReal_lt_ofReal_iff'.mp htb).1
  have hA0 : Adm 2 (y 0) := hy.adm 0 le_rfl (lt_T ht htT)
  refine ⟨le_trans (div_le_div_of_nonneg_right (X_le_init hy ht htT) (by norm_num))
    (init_region hA0 h0).1, ?_⟩
  have := barrier_inv hRB hy h0 hb0 hbT t ⟨ht, htb'⟩
  linarith

end Time

theorem unforced_metric_bounds (hRB : RowBound fun _ => M₀) {r : ℝ} {T : ℝ≥0∞} {y : ℝ → Field}
    (hy : IsHeatSol (filtN r 0) (fun _ => 0) T y) (h0 : hnorm 2 (y 0) ≤ 97 / 40) :
    (∀ t, 0 ≤ t → ENNReal.ofReal t < T → Ymet (y t) ≤ ENNReal.ofReal ((97 / 40) ^ 2)) ∧
    ∀ a b : ℝ, 0 ≤ a → a ≤ b → ENNReal.ofReal b < T →
      ∫⁻ τ in Icc a b, Zmet (y τ) ≤ ENNReal.ofReal (100000 * (97 / 40) ^ 2) := by
  have hS2 : (0 : ℝ) < (97 / 40) ^ 2 := by norm_num
  have hY1 : ∀ t, 0 ≤ t → ENNReal.ofReal t < T → Yr (y t) ≤ (97 / 40) ^ 2 := by
    intro t ht htT
    obtain ⟨hX1, hYS⟩ := region_pt hRB hy h0 ht htT
    have := Stilde_le_one hX1
    have h' : Yr (y t) / (97 / 40) ^ 2 ≤ 1 := by linarith
    rwa [div_le_one hS2] at h'
  refine ⟨fun t ht htT => ?_, fun a b ha hab hbT => ?_⟩
  · rw [Ymet_eq (hy.adm t ht htT)]
    exact ENNReal.ofReal_le_ofReal (hY1 t ht htT)
  have hb : 0 ≤ b := ha.trans hab
  have hZc := cont_Z hy hb hbT
  have hCc := cont_C (r := r) hy hbT
  have hheat : ∀ u ∈ Icc 0 b,
      1 / 100000 / 2 * Zr (y u) ≤ Zr (y u) + cubic (rotF (r * u) (y u)) := by
    intro u hu
    have hA := adm_y hy hu hbT
    obtain ⟨hX1, hYS⟩ := region_pt hRB hy h0 hu.1 (lt_T hu.2 hbT)
    have h := region_heat hRB (hA.rotF (r * u)) (by rwa [Xr_rotF _ hA])
      (by rwa [Xr_rotF _ hA, Yr_rotF _ hA])
    rw [Zr_rotF _ hA] at h
    have := neg_abs_le (cubic (rotF (r * u) (y u)))
    linarith
  have hlaw : ∀ t ∈ Icc 0 b, Yr (y t) =
      Yr (y 0) - 2 * ∫ u in (0 : ℝ)..t, (Zr (y u) + cubic (rotF (r * u) (y u))) := by
    intro t ht
    have l := law_Y hy le_rfl ht.1 (lt_T ht.2 hbT)
    rw [intervalIntegral.integral_add (ii hZc le_rfl ht.1 ht.2) (ii hCc le_rfl ht.1 ht.2)]
    linarith
  have hIB := integral_bound_of_le (T := b) (c := 1 / 100000) (Y := fun t => Yr (y t))
    (Z := fun t => Zr (y t)) (C := fun t => cubic (rotF (r * t) (y t))) (by norm_num)
    ((ii hZc le_rfl hb le_rfl).add (ii hCc le_rfl hb le_rfl)) (ii hZc le_rfl hb le_rfl)
    hlaw hheat b ⟨hb, le_rfl⟩
  beta_reduce at hIB
  have hY0 := hY1 0 le_rfl (lt_T hb hbT)
  have hAb := adm_y hy ⟨hb, le_rfl⟩ hbT
  have hYb : 0 ≤ Yr (y b) := le_trans (Xr_nonneg hAb) (Xr_le_Yr hAb)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (ii hZc le_rfl ha hab)
    (ii hZc ha hab le_rfl)
  have h0a : 0 ≤ ∫ u in (0 : ℝ)..a, Zr (y u) :=
    intervalIntegral.integral_nonneg ha fun u _ => Zr_nonneg' _
  have hab' : ∫ u in a..b, Zr (y u) ≤ 100000 * (97 / 40) ^ 2 := by linarith
  have hEq : ∫⁻ τ in Icc a b, Zmet (y τ) = ∫⁻ τ in Icc a b, ENNReal.ofReal (Zr (y τ)) :=
    setLIntegral_congr_fun measurableSet_Icc fun τ hτ =>
      Zmet_eq (adm_y hy ⟨ha.trans hτ.1, hτ.2⟩ hbT)
  have hint : IntegrableOn (fun τ => Zr (y τ)) (Icc a b) :=
    (hZc.mono (Icc_subset_Icc ha le_rfl)).integrableOn_compact isCompact_Icc
  rw [hEq, ← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun τ => Zr_nonneg' _), integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab]
  exact ENNReal.ofReal_le_ofReal hab'

end OVNS
