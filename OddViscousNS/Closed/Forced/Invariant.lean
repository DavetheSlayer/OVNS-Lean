import OddViscousNS.Closed.Forced.Check.Sound
import OddViscousNS.Closed.Forced.Barrier
import OddViscousNS.Closed.Forced.Kinetic
import OddViscousNS.Closed.Cubic

/-!
# Metric bounds along forced heat solutions from a kernel-checked row certificate

A row certificate `(k, f₀, J, cells, t)` that passes `chainOk`, the cell checks, the terminal check
and the window check (`RowOK`) gives, for every forced filtered heat solution `y` with
`‖y 0‖₂ ≤ s`, `‖g‖₂ ≤ f₀ s` (`k = s κ₀`, `f₀ ≤ 1`) and under `RowBound (fun _ => M₀)`:
`Y(y t) ≤ s² Y*` for all `t < T` and `∫_a^b Z(y) ≤ s² J` on every window `b − a ≤ 1`
(`row_metric_bounds`, the metric hypothesis of `heat_global_of_metric`).

Route: `graph_invariant` applied to `X = Xr (y ·)/s²`, `Y = Yr (y ·)/s²` on `[0, b)` for each
`b < T`; the active-constraint hypotheses come from the laws (`X_law_f`, `Y_law_f`) through
`neg_after_of_integral` with the pointwise face inequalities (`SFace.sound`, `KFace.sound`,
`Term.sound`, the cubic bounded by `cubic_le_kappa` on the rotated field); `X ≤ s²` from
`kinetic_cap`; the window from `Term.heat` and the force bound `|⟨R g, h v⟩| ≤ ‖g‖₂ √X ≤ f₀ s²`.
-/

open scoped ENNReal
open MeasureTheory Set

namespace OVNS

namespace Forced

open Chk

/-- The slope sequence of a cell list (`0` beyond the list). -/
noncomputable def slopes (cells : List Cell) : ℕ → ℝ :=
  fun l => ((cells[l]?).map fun C => (C.m : ℝ)).getD 0


private lemma slopes_cons_zero (C : Cell) (rest : List Cell) : slopes (C :: rest) 0 = C.m := by
  simp [slopes]

private lemma slopes_cons_succ (C : Cell) (rest : List Cell) (i : ℕ) :
    slopes (C :: rest) (i + 1) = slopes rest i := by
  simp [slopes]

private lemma slopes_of_lt {cells : List Cell} {l : ℕ} (hl : l < cells.length) :
    slopes cells l = (cells[l]'hl).m := by
  simp [slopes, List.getElem?_eq_getElem hl]

private lemma slopes_nonneg {k f0 : ℚ} {cells : List Cell} (h : cells.all (Cell.ok k f0) = true)
    (l : ℕ) : 0 ≤ slopes cells l := by
  unfold slopes
  cases hc : cells[l]? with
  | none => simp
  | some C =>
    have hok := List.all_eq_true.mp h C (List.mem_of_getElem? hc)
    cases C with
    | slope F =>
      simp only [Cell.ok, SFace.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hm0⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hok
      simp only [Option.map_some, Option.getD_some, Cell.m]
      exact_mod_cast hm0
    | kin F => simp [Cell.m]

/-- The chain with general starting accumulators. -/
private lemma chain_gen {t : Term} : ∀ (cells : List Cell) (B E : ℚ),
    chainOk B E cells t = true →
    (∀ l (hl : l < cells.length), ((cells[l]'hl).B : ℝ) = B + (l : ℝ) / 1000 ∧
      ((cells[l]'hl).E : ℝ) = E - ∑ i ∈ Finset.range l, slopes cells i / 1000) ∧
    (t.Y : ℝ) = B + (cells.length : ℝ) / 1000 ∧
    (t.E : ℝ) = E - ∑ i ∈ Finset.range cells.length, slopes cells i / 1000
  | [], B, E, h => by
    simp only [chainOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hY, hE⟩, -⟩ := h
    refine ⟨fun l hl => absurd hl (Nat.not_lt_zero _), ?_, ?_⟩ <;> simp [hY, hE]
  | C :: rest, B, E, h => by
    simp only [chainOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hB, hE⟩, -⟩, hr⟩ := h
    obtain ⟨ih1, ih2, ih3⟩ := chain_gen rest _ _ hr
    refine ⟨fun l hl => ?_, ?_, ?_⟩
    · cases l with
      | zero => simp [hB, hE]
      | succ l =>
        obtain ⟨h1, h2⟩ := ih1 l (by simpa using hl)
        simp only [List.getElem_cons_succ]
        rw [h1, h2, Finset.sum_range_succ', slopes_cons_zero]
        simp only [slopes_cons_succ]
        push_cast
        constructor <;> ring
    · rw [ih2, List.length_cons]; push_cast; ring
    · rw [ih3, List.length_cons, Finset.sum_range_succ', slopes_cons_zero]
      simp only [slopes_cons_succ]
      push_cast; ring

/-- A fully checked row certificate. -/
structure RowOK (k f0 : ℚ) (J : ℕ) (cells : List Cell) (t : Term) : Prop where
  chain : chainOk 1 1 cells t = true
  cells_ok : cells.all (Cell.ok k f0) = true
  term_ok : t.ok k f0 = true
  window : windowOk f0 J t = true

/-- The chain fixes the knots and levels: cell `l` is `(B_l, E_l)` with `B_l = 1 + l/1000`,
`E_l = 1 − ∑_{i<l} m_i/1000`, and the terminal is `(B_N, E_N)`, `N = cells.length`. -/
theorem chainOk_spec {cells : List Cell} {t : Term} (h : chainOk 1 1 cells t = true) :
    (∀ l (hl : l < cells.length),
      ((cells[l]'hl).B : ℝ) = knotB l ∧ ((cells[l]'hl).E : ℝ) = levelE (slopes cells) l) ∧
    (t.Y : ℝ) = knotB cells.length ∧ (t.E : ℝ) = levelE (slopes cells) cells.length := by
  obtain ⟨h1, h2, h3⟩ := chain_gen cells 1 1 h
  refine ⟨fun l hl => ?_, ?_, ?_⟩
  · obtain ⟨a, b⟩ := h1 l hl
    rw [a, b]; simp [knotB, levelE]
  · rw [h2]; simp [knotB]
  · rw [h3]; simp [levelE]



/-- The `Y`-part of `graph_invariant`, also covering the empty chain `N = 0`. -/
private lemma inv_Y {b : ℝ} {X Y : ℝ → ℝ} {m : ℕ → ℝ} {N : ℕ} (hm : ∀ l, 0 ≤ m l)
    (hX : ContinuousOn X (Ico 0 b)) (hY : ContinuousOn Y (Ico 0 b))
    (hX0 : X 0 ≤ 1) (hY0 : Y 0 ≤ 1) (hXle : ∀ τ ∈ Ico 0 b, X τ ≤ 1)
    (hterm : ∀ τ₀ ∈ Ico 0 b, Y τ₀ = knotB N → X τ₀ ≤ levelE m N →
      ∃ δ > 0, ∀ τ ∈ Ioo τ₀ (τ₀ + δ), τ < b → Y τ ≤ knotB N)
    (hface : ∀ l < N, ∀ τ₀ ∈ Ico 0 b, Y τ₀ ∈ Icc (knotB l) (knotB (l + 1)) →
      X τ₀ = piece m l (Y τ₀) →
      ∃ δ > 0, ∀ τ ∈ Ioo τ₀ (τ₀ + δ), τ < b → X τ + m l * Y τ ≤ X τ₀ + m l * Y τ₀) :
    ∀ τ ∈ Ico 0 b, Y τ ≤ knotB N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · intro τ hτ
    have := barrier_of_local' (φ := fun τ => Y τ - knotB 0) (hY.sub continuousOn_const)
      (by simp only [knotB, CharP.cast_eq_zero, zero_div, add_zero]; linarith) (fun τ₀ hτ₀ hz => by
        obtain ⟨δ, hδ, h⟩ := hterm τ₀ hτ₀ (by linarith)
          (by simp only [levelE, Finset.range_zero, Finset.sum_empty, sub_zero]; exact hXle τ₀ hτ₀)
        exact ⟨δ, hδ, fun τ hτ hτb => by linarith [h τ hτ hτb]⟩) τ hτ
    linarith
  · intro τ hτ
    have hB : (1 : ℝ) ≤ knotB N := by unfold knotB; have : (0 : ℝ) ≤ N := N.cast_nonneg; linarith
    exact (graph_invariant hm hN hX hY (by rw [graphFun_eq_one m N hY0]; exact hX0)
      (hY0.trans hB) hXle hterm hface τ hτ).1

section Analytic

variable {r : ℝ} {T : ℝ≥0∞} {y : ℝ → Field} {g : Field}

private lemma ltT {t b : ℝ} (htb : t ≤ b) (hbT : ENNReal.ofReal b < T) :
    ENNReal.ofReal t < T :=
  lt_of_le_of_lt (ENNReal.ofReal_le_ofReal htb) hbT

private lemma wDissX (u : Field) : wDiss ωX u = J1r u := by
  unfold wDiss J1r
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0 <;> simp [ωX, hk, absSq]

private lemma wEX (u : Field) : wE ωX u = Xr u := wE_X u

private lemma wEY (u : Field) : wE ωY u = Yr u := rfl

private lemma wDissY (u : Field) : wDiss ωY u = Zr u := wDiss_Y u

private lemma Zr_nn (u : Field) : 0 ≤ Zr u :=
  tsum_nonneg fun k => mul_nonneg (mul_nonneg (absSq_nonneg k) (weightLE2_Y.nonneg k))
    (sq_nonneg _)

private lemma Ymet_eq' {w : Field} (hw : Adm 2 w) : Ymet w = ENNReal.ofReal (Yr w) := by
  unfold Ymet Yr
  rw [ENNReal.ofReal_tsum_of_nonneg
    (fun k => mul_nonneg (show 0 ≤ hm k from weightLE2_Y.nonneg k) (sq_nonneg _))
    (summable_Y hw)]
  rfl

private lemma Zmet_eq' {w : Field} (hw : Adm 2 w) : Zmet w = ENNReal.ofReal (Zr w) := by
  unfold Zmet Zr
  rw [ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (mul_nonneg (absSq_nonneg k)
    (show 0 ≤ hm k from weightLE2_Y.nonneg k)) (sq_nonneg _)) (summable_Z hw)]
  refine tsum_congr fun k => ?_
  rw [nsq_cast]
  rfl

private lemma iiF {f : ℝ → ℝ} {b : ℝ} (hf : ContinuousOn f (Icc 0 b)) {a t : ℝ} (ha : 0 ≤ a)
    (hat : a ≤ t) (htb : t ≤ b) : IntervalIntegrable f volume a t := by
  refine (hf.mono ?_).intervalIntegrable
  rw [uIcc_of_le hat]
  exact Icc_subset_Icc ha htb

/-- The integrand of `α X + μ Y` along the forced flow. -/
private noncomputable def Gint (r : ℝ) (y : ℝ → Field) (g : Field) (α μ : ℝ) (u : ℝ) : ℝ :=
  -2 * α * J1r (y u) + 2 * α * wPair ωX (y u) (filtG r 0 g u) + -2 * μ * Zr (y u) +
    -2 * μ * cubic (rotF (r * u) (y u)) + 2 * μ * wPair ωY (y u) (filtG r 0 g u)

private lemma Gint_cont (hg : Adm 2 g) (hy : IsHeatSol (filtN r 0) (filtG r 0 g) T y) {b : ℝ}
    (hb : 0 ≤ b) (hbT : ENNReal.ofReal b < T) (α μ : ℝ) :
    ContinuousOn (Gint r y g α μ) (Icc 0 b) := by
  unfold Gint
  exact ((((continuousOn_const.mul (continuousOn_J1_f hg hy hb hbT)).add
    (continuousOn_const.mul (continuousOn_pairX_f hg hy hb hbT))).add
    (continuousOn_const.mul (continuousOn_Z_f hg hy hb hbT))).add
    (continuousOn_const.mul (continuousOn_cubic_f hg hy hb hbT))).add
    (continuousOn_const.mul (continuousOn_pairY_f hg hy hb hbT))

private lemma Gint_integral (hg : Adm 2 g) (hy : IsHeatSol (filtN r 0) (filtG r 0 g) T y)
    {b : ℝ} (hb : 0 ≤ b) (hbT : ENNReal.ofReal b < T) {a t : ℝ} (ha : 0 ≤ a) (hat : a ≤ t)
    (htb : t ≤ b) (α μ : ℝ) :
    ∫ u in a..t, Gint r y g α μ u =
      (α * Xr (y t) + μ * Yr (y t)) - (α * Xr (y a) + μ * Yr (y a)) := by
  have iJ := iiF (continuousOn_J1_f hg hy hb hbT) ha hat htb
  have iPX := iiF (continuousOn_pairX_f hg hy hb hbT) ha hat htb
  have iZ := iiF (continuousOn_Z_f hg hy hb hbT) ha hat htb
  have iC := iiF (continuousOn_cubic_f hg hy hb hbT) ha hat htb
  have iPY := iiF (continuousOn_pairY_f hg hy hb hbT) ha hat htb
  have lX := X_law_f hg hy ha hat (ltT htb hbT)
  have lY := Y_law_f hg hy ha hat (ltT htb hbT)
  simp only [wDissX, wEX, wEY, wDissY] at lX lY
  unfold Gint
  rw [intervalIntegral.integral_add ((((iJ.const_mul _).add (iPX.const_mul _)).add
      (iZ.const_mul _)).add (iC.const_mul _)) (iPY.const_mul _),
    intervalIntegral.integral_add (((iJ.const_mul _).add (iPX.const_mul _)).add
      (iZ.const_mul _)) (iC.const_mul _),
    intervalIntegral.integral_add ((iJ.const_mul _).add (iPX.const_mul _)) (iZ.const_mul _),
    intervalIntegral.integral_add (iJ.const_mul _) (iPX.const_mul _)]
  simp only [intervalIntegral.integral_const_mul]
  linear_combination (-α) * lX + (-μ) * lY

/-- Strict decrease of `α X + μ Y` right after a point where its integrand is negative. -/
private lemma local_dec (hg : Adm 2 g) (hy : IsHeatSol (filtN r 0) (filtG r 0 g) T y) {b : ℝ}
    (hb : 0 ≤ b) (hbT : ENNReal.ofReal b < T) {τ₀ : ℝ} (hτ₀ : τ₀ ∈ Ico 0 b) (α μ : ℝ)
    (hneg : Gint r y g α μ τ₀ < 0) :
    ∃ δ > 0, ∀ τ ∈ Ioo τ₀ (τ₀ + δ), τ < b →
      α * Xr (y τ) + μ * Yr (y τ) < α * Xr (y τ₀) + μ * Yr (y τ₀) := by
  obtain ⟨δ, hδ, h⟩ := neg_after_of_integral
    (φ := fun τ => (α * Xr (y τ) + μ * Yr (y τ)) - (α * Xr (y τ₀) + μ * Yr (y τ₀))) hτ₀
    ((Gint_cont hg hy hb hbT α μ).mono Ico_subset_Icc_self) hneg
    (fun τ hτ => (Gint_integral hg hy hb hbT hτ₀.1 hτ.1 hτ.2.le α μ).ge)
  exact ⟨δ, hδ, fun τ hτ hτb => sub_neg.mp (h τ hτ hτb)⟩

private lemma Gint_eq (α μ τ₀ : ℝ) :
    Gint r y g α μ τ₀ = 2 * (α * (-J1r (y τ₀) + wPair ωX (y τ₀) (rotF (-(r * (τ₀ + 0))) g)) +
      μ * (-(Zr (y τ₀) + cubic (rotF (r * τ₀) (y τ₀))) +
        wPair ωY (y τ₀) (rotF (-(r * (τ₀ + 0))) g))) := by
  unfold Gint filtG
  ring


/-- The kinetic cap in the normalized form `X ≤ s²`. -/
private lemma X_cap {f0 s : ℚ} (hs : 0 < s) (hf0 : f0 ≤ 1) (hg : Adm 2 g)
    (hgn : hnorm 2 g ≤ f0 * s) (hy : IsHeatSol (filtN r 0) (filtG r 0 g) T y)
    (h0 : hnorm 2 (y 0) ≤ s) {τ : ℝ} (hτ : 0 ≤ τ) (hτT : ENNReal.ofReal τ < T) :
    Xr (y τ) ≤ (s : ℝ) ^ 2 := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hf0R : (f0 : ℝ) ≤ 1 := by exact_mod_cast hf0
  have hA0 : Adm 2 (y 0) := hy.adm 0 le_rfl (ltT hτ hτT)
  have hfs : (f0 : ℝ) * s ≤ s := by nlinarith
  refine (kinetic_cap hg hy hτ hτT).trans (max_le ?_ ?_)
  · exact (Xr_le_hnorm_sq hA0).trans (pow_le_pow_left₀ (hnorm_nonneg _ _) h0 2)
  · exact pow_le_pow_left₀ (hnorm_nonneg _ _) (hgn.trans hfs) 2

/-- The cubic of the rotated field is bounded by `κ₀ √Y Z` of the field itself. -/
private lemma cubic_rot_le (hRB : RowBound fun _ => M₀) {v : Field} (hv : Adm 2 v) (θ : ℝ) :
    |cubic (rotF θ v)| ≤ κ₀ * Real.sqrt (Yr v) * Zr v := by
  have hC := cubic_le_kappa hRB (hv.rotF θ)
  rwa [Yr_rotF _ hv, Zr_rotF _ hv] at hC

/-- The invariance of `Y ≤ s² Y*` on `[0, b)`. -/
private lemma Y_inv {k f0 s : ℚ} {J : ℕ} {cells : List Cell} {t : Term} (hs : 0 < s)
    (hk : (k : ℝ) = s * κ₀) (hf0 : f0 ≤ 1) (hR : RowOK k f0 J cells t)
    (hRB : RowBound fun _ => M₀) (hg : Adm 2 g)
    (hgn : hnorm 2 g ≤ f0 * s) (hy : IsHeatSol (filtN r 0) (filtG r 0 g) T y)
    (h0 : hnorm 2 (y 0) ≤ s) {b : ℝ} (hb : 0 ≤ b) (hbT : ENNReal.ofReal b < T) :
    ∀ τ ∈ Ico 0 b, Yr (y τ) / (s : ℝ) ^ 2 ≤ knotB cells.length := by
  have hSpos : (0 : ℝ) < (s : ℝ) ^ 2 := by positivity
  obtain ⟨hcell, htY, htE⟩ := chainOk_spec hR.chain
  have hadm : ∀ τ ∈ Icc 0 b, Adm 2 (y τ) := fun τ hτ => hy.adm τ hτ.1 (ltT hτ.2 hbT)
  have hA0 := hadm 0 ⟨le_rfl, hb⟩
  have hn0 : hnorm 2 (y 0) ^ 2 ≤ (s : ℝ) ^ 2 := pow_le_pow_left₀ (hnorm_nonneg _ _) h0 2
  refine inv_Y (X := fun τ => Xr (y τ) / (s : ℝ) ^ 2) (Y := fun τ => Yr (y τ) / (s : ℝ) ^ 2)
    (m := slopes cells) (slopes_nonneg hR.cells_ok)
    ((((continuousOn_X_f hg hy hb hbT).congr fun u _ => (wEX (y u)).symm).div_const _).mono
      Ico_subset_Icc_self)
    ((((continuousOn_Y_f hg hy hb hbT).congr fun u _ => (wEY (y u)).symm).div_const _).mono
      Ico_subset_Icc_self) ?_ ?_ ?_ ?_ ?_
  · rw [div_le_one hSpos]; exact (Xr_le_hnorm_sq hA0).trans hn0
  · rw [div_le_one hSpos]; exact (Yr_le_hnorm_sq hA0).trans hn0
  · intro τ hτ
    rw [div_le_one hSpos]
    exact X_cap hs hf0 hg hgn hy h0 hτ.1 (ltT hτ.2.le hbT)
  · intro τ₀ hτ₀ hYe hXe
    have hA := hadm τ₀ (Ico_subset_Icc_self hτ₀)
    have hYv : Yr (y τ₀) = (s : ℝ) ^ 2 * t.Y := by
      rw [htY, ← hYe]; field_simp
    have hXv : Xr (y τ₀) ≤ (s : ℝ) ^ 2 * t.E := by
      rw [htE]; rw [div_le_iff₀ hSpos] at hXe; linarith
    have hsd := Term.sound hs hk hR.term_ok hA hg hgn (-(r * (τ₀ + 0)))
      (cubic_rot_le hRB hA (r * τ₀)) hYv hXv
    obtain ⟨δ, hδ, h⟩ := local_dec hg hy hb hbT hτ₀ 0 1 (by rw [Gint_eq]; linarith)
    refine ⟨δ, hδ, fun τ hτ hτb => ?_⟩
    have h' := h τ hτ hτb
    show Yr (y τ) / (s : ℝ) ^ 2 ≤ knotB cells.length
    rw [div_le_iff₀ hSpos]
    rw [htY] at hYv
    linarith
  · intro l hl τ₀ hτ₀ hYc hXc
    have hA := hadm τ₀ (Ico_subset_Icc_self hτ₀)
    obtain ⟨hBl, hEl⟩ := hcell l hl
    have hml := slopes_of_lt hl
    have hok : Cell.ok k f0 (cells[l]'hl) = true :=
      List.all_eq_true.mp hR.cells_ok _ (List.getElem_mem hl)
    have eX : Xr (y τ₀) = (s : ℝ) ^ 2 * (Xr (y τ₀) / (s : ℝ) ^ 2) := by field_simp
    have eY : Yr (y τ₀) = (s : ℝ) ^ 2 * (Yr (y τ₀) / (s : ℝ) ^ 2) := by field_simp
    have hYr : Yr (y τ₀) ∈ Icc ((s : ℝ) ^ 2 * (cells[l]'hl).B)
        ((s : ℝ) ^ 2 * ((cells[l]'hl).B + 1 / 1000)) := by
      rw [knotB_succ, ← hBl] at hYc
      rw [eY]
      exact ⟨mul_le_mul_of_nonneg_left hYc.1 hSpos.le, mul_le_mul_of_nonneg_left hYc.2 hSpos.le⟩
    have hXr : Xr (y τ₀) = (s : ℝ) ^ 2 * (cells[l]'hl).E -
        (cells[l]'hl).m * (Yr (y τ₀) - (s : ℝ) ^ 2 * (cells[l]'hl).B) := by
      have hX' : Xr (y τ₀) / (s : ℝ) ^ 2 = (cells[l]'hl).E -
          (cells[l]'hl).m * (Yr (y τ₀) / (s : ℝ) ^ 2 - (cells[l]'hl).B) := by
        rw [hEl, hBl, ← hml]; exact hXc
      rw [eX, eY, hX']
      ring
    have hgoal : ∀ μ : ℝ, slopes cells l = μ → Gint r y g 1 μ τ₀ < 0 →
        ∃ δ > 0, ∀ τ ∈ Ioo τ₀ (τ₀ + δ), τ < b →
          Xr (y τ) / (s : ℝ) ^ 2 + slopes cells l * (Yr (y τ) / (s : ℝ) ^ 2) ≤
            Xr (y τ₀) / (s : ℝ) ^ 2 + slopes cells l * (Yr (y τ₀) / (s : ℝ) ^ 2) := by
      intro μ hμ hneg
      obtain ⟨δ, hδ, h⟩ := local_dec hg hy hb hbT hτ₀ 1 μ hneg
      refine ⟨δ, hδ, fun τ hτ hτb => ?_⟩
      have h' := h τ hτ hτb
      rw [hμ, show ∀ x z : ℝ, x / (s : ℝ) ^ 2 + μ * (z / (s : ℝ) ^ 2) =
        (1 * x + μ * z) / (s : ℝ) ^ 2 from fun x z => by ring,
        show ∀ x z : ℝ, x / (s : ℝ) ^ 2 + μ * (z / (s : ℝ) ^ 2) =
        (1 * x + μ * z) / (s : ℝ) ^ 2 from fun x z => by ring]
      exact div_le_div_of_nonneg_right h'.le hSpos.le
    rcases hc : cells[l]'hl with F | F
    · rw [hc] at hok hYr hXr hml
      simp only [Cell.ok, Cell.B, Cell.E, Cell.m] at hok hYr hXr hml
      have hsd := SFace.sound hs hk hok hA hg hgn (-(r * (τ₀ + 0)))
        (cubic_rot_le hRB hA (r * τ₀)) hYr hXr
      exact hgoal F.m hml (by rw [Gint_eq]; linarith)
    · rw [hc] at hok hYr hXr hml
      simp only [Cell.m, Rat.cast_zero] at hml
      simp only [Cell.ok, Cell.B, Cell.E, Cell.m, Rat.cast_zero, zero_mul, sub_zero] at hok hYr hXr
      have hsd := KFace.sound hs hok hA hg hgn (-(r * (τ₀ + 0))) hYr.1 hXr
      exact hgoal 0 hml (by rw [Gint_eq]; linarith)


/-- The window bound `∫_a^b Z ≤ s² J` from the terminal heat and the force bound. -/
private lemma window_bound {k f0 s : ℚ} {J : ℕ} {cells : List Cell} {t : Term} (hs : 0 < s)
    (hk : (k : ℝ) = s * κ₀) (hf0 : f0 ≤ 1) (hR : RowOK k f0 J cells t)
    (hRB : RowBound fun _ => M₀) (hg : Adm 2 g)
    (hgn : hnorm 2 g ≤ f0 * s) (hy : IsHeatSol (filtN r 0) (filtG r 0 g) T y)
    (h0 : hnorm 2 (y 0) ≤ s)
    (hYb : ∀ τ, 0 ≤ τ → ENNReal.ofReal τ < T → Yr (y τ) ≤ (s : ℝ) ^ 2 * t.Y)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hba : b ≤ a + 1) (hbT : ENNReal.ofReal b < T) :
    ∫ u in a..b, Zr (y u) ≤ (s : ℝ) ^ 2 * J := by
  have hb : 0 ≤ b := ha.trans hab
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hSpos : (0 : ℝ) < (s : ℝ) ^ 2 := by positivity
  have hw := hR.window
  simp only [windowOk, Bool.and_eq_true, decide_eq_true_eq] at hw
  obtain ⟨hH, hJ⟩ := hw
  have hHR : (0 : ℝ) < t.H := by exact_mod_cast hH
  have hJR : ((t.Y : ℝ) / 2 + f0) / t.H ≤ J := by
    have h2 := (Rat.cast_le (K := ℝ)).2 hJ; push_cast at h2; exact h2
  have iZ := iiF (continuousOn_Z_f hg hy hb hbT) ha hab le_rfl
  have iC := iiF (continuousOn_cubic_f hg hy hb hbT) ha hab le_rfl
  have iP := iiF (continuousOn_pairY_f hg hy hb hbT) ha hab le_rfl
  have lY := Y_law_f hg hy ha hab hbT
  simp only [wEY, wDissY] at lY
  have hf0s : (0 : ℝ) ≤ f0 * s := (hnorm_nonneg _ _).trans hgn
  have hpt1 : ∀ u ∈ Icc a b,
      (t.H : ℝ) * Zr (y u) ≤ Zr (y u) + cubic (rotF (r * u) (y u)) := by
    intro u hu
    have hu0 : 0 ≤ u := ha.trans hu.1
    have huT := ltT hu.2 hbT
    have hA := hy.adm u hu0 huT
    exact Term.heat hs hk hR.term_ok hA (cubic_rot_le hRB hA (r * u)) (hYb u hu0 huT)
  have hpt2 : ∀ u ∈ Icc a b, wPair ωY (y u) (filtG r 0 g u) ≤ f0 * s * s := by
    intro u hu
    have hu0 : 0 ≤ u := ha.trans hu.1
    have huT := ltT hu.2 hbT
    have hA := hy.adm u hu0 huT
    have hP := force_pair_Y_le (-(r * (u + 0))) hg hA
    have hsq : Real.sqrt (Xr (y u)) ≤ s :=
      (Real.sqrt_le_sqrt (X_cap hs hf0 hg hgn hy h0 hu0 huT)).trans_eq (Real.sqrt_sq hsR.le)
    calc wPair ωY (y u) (filtG r 0 g u) ≤ |wPair ωY (y u) (rotF (-(r * (u + 0))) g)| :=
          le_abs_self _
      _ ≤ hnorm 2 g * Real.sqrt (Xr (y u)) := hP
      _ ≤ f0 * s * s := mul_le_mul hgn hsq (Real.sqrt_nonneg _) hf0s
  have I1 : (t.H : ℝ) * ∫ u in a..b, Zr (y u) ≤
      (∫ u in a..b, Zr (y u)) + ∫ u in a..b, cubic (rotF (r * u) (y u)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add iZ iC]
    exact intervalIntegral.integral_mono_on hab (iZ.const_mul _) (iZ.add iC) hpt1
  have I2 : ∫ u in a..b, wPair ωY (y u) (filtG r 0 g u) ≤ (b - a) * (f0 * s * s) := by
    have := intervalIntegral.integral_mono_on hab iP intervalIntegrable_const hpt2
    rwa [intervalIntegral.integral_const, smul_eq_mul] at this
  have I3 : (b - a) * (f0 * s * s) ≤ f0 * s * s :=
    mul_le_of_le_one_left (mul_nonneg hf0s hsR.le) (by linarith)
  have hYa := hYb a ha (ltT hab hbT)
  have hAb := hy.adm b hb hbT
  have hYb0 : 0 ≤ Yr (y b) := (Xr_nonneg hAb).trans (Xr_le_Yr hAb)
  have hfin : (t.H : ℝ) * ∫ u in a..b, Zr (y u) ≤ (s : ℝ) ^ 2 * ((t.Y / 2 + f0)) := by
    nlinarith
  calc ∫ u in a..b, Zr (y u) ≤ (s : ℝ) ^ 2 * ((t.Y / 2 + f0)) / t.H := by
        rw [le_div_iff₀ hHR]; linarith
    _ = (s : ℝ) ^ 2 * (((t.Y : ℝ) / 2 + f0) / t.H) := by ring
    _ ≤ (s : ℝ) ^ 2 * J := mul_le_mul_of_nonneg_left hJR hSpos.le

end Analytic

theorem row_metric_bounds {k f0 s : ℚ} {J : ℕ} {cells : List Cell} {t : Term} (hs : 0 < s)
    (hk : (k : ℝ) = s * κ₀) (hf0 : f0 ≤ 1) (hR : RowOK k f0 J cells t)
    (hRB : RowBound fun _ => M₀) {r : ℝ} {T : ℝ≥0∞} {y : ℝ → Field} {g : Field} (hg : Adm 2 g)
    (hgn : hnorm 2 g ≤ f0 * s) (hy : IsHeatSol (filtN r 0) (filtG r 0 g) T y)
    (h0 : hnorm 2 (y 0) ≤ s) :
    (∀ τ, 0 ≤ τ → ENNReal.ofReal τ < T → Ymet (y τ) ≤ ENNReal.ofReal ((s : ℝ) ^ 2 * t.Y)) ∧
    ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ a + 1 → ENNReal.ofReal b < T →
      ∫⁻ τ in Icc a b, Zmet (y τ) ≤ ENNReal.ofReal ((s : ℝ) ^ 2 * J) := by
  have hSpos : (0 : ℝ) < (s : ℝ) ^ 2 := by positivity
  obtain ⟨-, htY, -⟩ := chainOk_spec hR.chain
  have hYb : ∀ τ, 0 ≤ τ → ENNReal.ofReal τ < T → Yr (y τ) ≤ (s : ℝ) ^ 2 * t.Y := by
    intro τ hτ hτT
    obtain ⟨b, hb0, hτb, hbT⟩ := ENNReal.lt_iff_exists_real_btwn.mp hτT
    have hτb' : τ < b := (ENNReal.ofReal_lt_ofReal_iff'.mp hτb).1
    have h := Y_inv hs hk hf0 hR hRB hg hgn hy h0 hb0 hbT τ ⟨hτ, hτb'⟩
    rw [div_le_iff₀ hSpos, ← htY] at h
    linarith
  refine ⟨fun τ hτ hτT => ?_, fun a b ha hab hba hbT => ?_⟩
  · rw [Ymet_eq' (hy.adm τ hτ hτT)]
    exact ENNReal.ofReal_le_ofReal (hYb τ hτ hτT)
  have hb : 0 ≤ b := ha.trans hab
  have hab' := window_bound hs hk hf0 hR hRB hg hgn hy h0 hYb ha hab hba hbT
  have hZc := continuousOn_Z_f hg hy hb hbT
  have hEq : ∫⁻ τ in Icc a b, Zmet (y τ) = ∫⁻ τ in Icc a b, ENNReal.ofReal (Zr (y τ)) :=
    setLIntegral_congr_fun measurableSet_Icc fun τ hτ =>
      Zmet_eq' (hy.adm τ (ha.trans hτ.1) (ltT hτ.2 hbT))
  have hint : IntegrableOn (fun τ => Zr (y τ)) (Icc a b) :=
    (hZc.mono (Icc_subset_Icc ha le_rfl)).integrableOn_compact isCompact_Icc
  rw [hEq, ← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun τ => Zr_nn _), integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab]
  exact ENNReal.ofReal_le_ofReal hab'

end Forced

end OVNS
