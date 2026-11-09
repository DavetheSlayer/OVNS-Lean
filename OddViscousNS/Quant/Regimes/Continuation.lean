import OddViscousNS.Quant.Regimes.Algebra
import OddViscousNS.LocalMaximal
import OddViscousNS.LocalUniq

/-!
# Regimes layer, node 4: causal continuation (R3)

Spec §1.2 (`[R3]`), §2.2 R3; Source 3 §10–11; TeX "virtual fast barrier and causal
continuation".  The bootstrap runs on a *maximal* filtered solution (`OVNS.exists_maximal`:
`∃ T y, 0 < T ∧ IsHeatSol N G T y ∧ y 0 = y₀ ∧ (T ≠ ⊤ → ∀ C, ¬ ∀ t, 0 ≤ t → ofReal t < T →
hnorm 2 (y t) ≤ C)`), in pieces of length in `[Tp − 1, Tp]`; overlaps are glued by
`OVNS.heatSol_unique` (`IsHeatSol N G T y → IsHeatSol N G T y' → y 0 = y' 0 → ∀ t, 0 ≤ t →
ofReal t < T → y t = y' t`).

Proved here (pure real analysis / logic):
* `first_exit`: the first-exit lemma *with history*: a continuous deficit `φ` on `[0, T)` with
  `φ 0 < 0`, which is strictly negative at every `τ₀` such that `φ ≤ 0` on `[0, τ₀]`, stays
  negative.  (The library's `OVNS.barrier_of_local'` picks the *last* zero and its local
  hypothesis sees only `φ τ₀ = 0`; the bootstrap's strict improvement needs the whole history
  `[0, τ₀]`, hence this variant, proved along the same lines.)
* `pieces_induction`: the induction over pieces (the generalization of Induction.lean's
  `all_windows` to variable piece lengths `≥ L ≥ 1`): if from every good time `τ` in the
  lifespan the solution reaches a good time `τ' ≥ τ + L` in the lifespan with the bounds on
  `[τ, τ']`, then the lifespan is `⊤` and the bounds hold for all times.
Also proved (locked statements): `norms_continuous` (time-continuity of `a_F, b_F, a_S, b_S,
W_S` along a heat solution: `IsHeatSol.cont`, `H²`-continuity of `psi` by dominated convergence,
`hnorm_PiF_le`/`hnorm_PiS_le`, `wiener_le`) and `piece_first_exit` (`first_exit` applied to the
seven cap deficits, using `StrictImprovement`).
and the amended `piece_step` (one lookahead piece: first exit `onPrefix_closed` + blow-up
alternative (private `lifespan_gt`) + kinetic good point from `KinFun`, Chebyshev over the last
unit).  Amendments: per-cap improved caps `ci` (`Caps.Below`) instead of one factor `θ`, the
post-clip fast `H²` level `Y₀` in `GoodPoint`/`StrictImprovement`, and the kinetic level
`W₀ ≤ W_max` chained through `piece_step`.
-/

open scoped ENNReal Topology
open MeasureTheory Set Filter

noncomputable section

namespace OVNS.Quant

/-! ### The abstract bootstrap data -/

/-- The pointwise caps at one time (the five original caps, then the slow sub-caps of D4). -/
def PointCaps (caps : Caps) (r : ℝ) (g : Field) (y : ℝ → Field) (τ : ℝ) : Prop :=
  fastNorm 1 r g y τ ≤ caps.PF ∧ fastNorm 2 r g y τ ≤ caps.yF ∧ slowNorm 1 r g y τ ≤ caps.AS ∧
    slowNorm 2 r g y τ ≤ caps.BS ∧ slowWiener r g y τ ≤ caps.WS ∧
    slowNorm 0 r g y τ ≤ caps.ES ∧ horizNorm 1 r g y τ ≤ caps.AH ∧ horizNorm 2 r g y τ ≤ caps.BH

/-- The improved caps `ci` lie strictly below `caps` componentwise, with nonnegative improved
square-integral budgets (amendment: one improvement factor per cap, so that the `H²` cap can
use the barrier's own contraction). -/
def Caps.Below (ci c : Caps) : Prop :=
  ci.PF < c.PF ∧ ci.yF < c.yF ∧ ci.AS < c.AS ∧ ci.BS < c.BS ∧ ci.WS < c.WS ∧
    ci.JF < c.JF ∧ ci.JS < c.JS ∧ 0 ≤ ci.JF ∧ 0 ≤ ci.JS ∧ ci.ES < c.ES ∧ ci.AH < c.AH ∧
    ci.BH < c.BH

/-- A good restart point (Source 3 §10, "first simultaneous kinetic good point"): `τ ≥ 0`, the
fast `H¹` trace is at most `M_f`, the start levels `c0` hold (the post-clip fast `H²` level and
the slow start levels, amendments) and the pointwise improved caps `ci` hold at `τ`. -/
structure GoodPoint (Mf : ℝ) (c0 ci : Caps) (r : ℝ) (g : Field) (y : ℝ → Field) (τ : ℝ) :
    Prop where
  /-- `0 ≤ τ`. -/
  nonneg : 0 ≤ τ
  /-- The incoming fast `H¹` trace. -/
  fastH1 : fastNorm 1 r g y τ ≤ Mf
  /-- The start levels at `τ`. -/
  start : PointCaps c0 r g y τ
  /-- The pointwise improved caps at `τ`. -/
  pointCaps : PointCaps ci r g y τ

/-- **The bootstrap input** (spec §1.2, Source 3 §2/§10; amended): on every piece `[s, t]` of
length `≤ Tp` inside the lifespan, starting at a good point, on which the caps hold and the
threshold is paid, the caps improve to `ci` on `[s, t]`, and after the first unit the start
levels `c0` hold again.  This is what E6 (`scalar_peak_on_piece`,
`scalar_dissipation_on_piece`), E10 (`barrier_cap`) and E7 (`SlowCapsInterface`) deliver once
the caps are chosen (R1). -/
def StrictImprovement (Mf Tp μ φ : ℝ) (q : Caps → ℝ) (caps ci c0 : Caps) : Prop :=
  ∀ (r : ℝ) (g : Field) (y : ℝ → Field) (Ty : ℝ≥0∞), ActualSol μ φ r g y Ty →
    ∀ s t : ℝ, GoodPoint Mf c0 ci r g y s → PieceHyp Tp q r g y Ty caps s t →
      OnPrefix ci r g y s t ∧ ∀ v ∈ Icc (s + 1) t, PointCaps c0 r g y v

/-- The caps on a prefix give the pointwise caps at each of its times. -/
theorem pointCaps_of_onPrefix {c : Caps} {r : ℝ} {g : Field} {y : ℝ → Field} {s t u : ℝ}
    (h : OnPrefix c r g y s t) (hu : u ∈ Icc s t) : PointCaps c r g y u := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := h.1 u hu
  obtain ⟨b1, b2, b3⟩ := h.2.2.2 u hu
  exact ⟨a1, a2, a3, a4, a5, b1, b2, b3⟩

/-- Point caps at `s` give the caps on the degenerate prefix `[s, s]`. -/
theorem onPrefix_point {c : Caps} {r : ℝ} {g : Field} {y : ℝ → Field} {s : ℝ}
    (h : PointCaps c r g y s) (hJF : 0 ≤ c.JF) (hJS : 0 ≤ c.JS) : OnPrefix c r g y s s := by
  obtain ⟨a1, a2, a3, a4, a5, b1, b2, b3⟩ := h
  refine ⟨fun u hu ↦ ?_, by rw [intervalIntegral.integral_same]; exact hJF,
    by rw [intervalIntegral.integral_same]; exact hJS, fun u hu ↦ ?_⟩
  · rw [show u = s from le_antisymm hu.2 hu.1]
    exact ⟨a1, a2, a3, a4, a5⟩
  · rw [show u = s from le_antisymm hu.2 hu.1]
    exact ⟨b1, b2, b3⟩

/-! ### The first-exit lemma with history -/

/-- **First exit with history.** A continuous `φ` on `[0, T)` with `φ 0 < 0` such that
`φ τ₀ < 0` whenever `φ ≤ 0` on `[0, τ₀]` stays strictly negative on `[0, T)`. -/
theorem first_exit {T : ℝ} {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Ico 0 T)) (h0 : φ 0 < 0)
    (himp : ∀ τ₀ ∈ Ico 0 T, (∀ τ ∈ Icc 0 τ₀, φ τ ≤ 0) → φ τ₀ < 0) :
    ∀ τ ∈ Ico 0 T, φ τ < 0 := by
  intro τ₁ hτ₁
  by_contra hpos
  push Not at hpos
  set S : Set ℝ := Icc 0 τ₁ ∩ φ ⁻¹' Ici 0 with hS
  have hsub : Icc 0 τ₁ ⊆ Ico 0 T := fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hτ₁.2⟩
  have hcl : IsClosed S := (hφ.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hne : S.Nonempty := ⟨τ₁, ⟨hτ₁.1, le_rfl⟩, hpos⟩
  have hbdd : BddBelow S := ⟨0, fun x hx => hx.1.1⟩
  have hmem : sInf S ∈ S := hcl.csInf_mem hne hbdd
  set τ₀ := sInf S with hτ₀
  have hτ₀ge : 0 ≤ φ τ₀ := hmem.2
  have hτ₀mem : τ₀ ∈ Ico 0 T := hsub hmem.1
  have hgt : 0 < τ₀ := by
    rcases lt_or_eq_of_le hmem.1.1 with h | h
    · exact h
    · exfalso
      rw [← h] at hτ₀ge
      linarith
  have hneg : ∀ u ∈ Ico 0 τ₀, φ u < 0 := by
    intro u hu
    by_contra hu'
    push Not at hu'
    have : τ₀ ≤ u := csInf_le hbdd ⟨⟨hu.1, hu.2.le.trans hmem.1.2⟩, hu'⟩
    linarith [hu.2]
  -- by continuity, `φ τ₀ ≤ 0`, hence `φ τ₀ = 0`
  have hle : φ τ₀ ≤ 0 := by
    by_contra hpos'
    push Not at hpos'
    obtain ⟨δ, hδ, hball⟩ :=
      Metric.continuousWithinAt_iff.mp (hφ τ₀ hτ₀mem) (φ τ₀) hpos'
    set x := max (τ₀ - δ / 2) (τ₀ / 2) with hx
    have hx0 : 0 ≤ x := le_trans (by linarith) (le_max_right _ _)
    have hxlt : x < τ₀ := max_lt (by linarith) (by linarith)
    have hxmem : x ∈ Ico 0 T := ⟨hx0, lt_trans hxlt hτ₀mem.2⟩
    have hd : dist x τ₀ < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [le_max_left (τ₀ - δ / 2) (τ₀ / 2)]
    have := hball hxmem hd
    rw [Real.dist_eq, abs_lt] at this
    linarith [hneg x ⟨hx0, hxlt⟩, this.1]
  have hall : ∀ τ ∈ Icc 0 τ₀, φ τ ≤ 0 := by
    intro τ hτ
    rcases lt_or_eq_of_le hτ.2 with h | h
    · exact (hneg τ ⟨hτ.1, h⟩).le
    · rw [h]
      exact hle
  linarith [himp τ₀ hτ₀mem hall]

/-! ### The induction over pieces -/

/-- **Induction over pieces** (generalizes Induction.lean's `all_windows`).  If from every good
time `τ` inside the lifespan `Ty` the solution reaches a good time `τ' ≥ τ + L` inside the
lifespan with the bounds on `[τ, τ']`, and `0` is good, then `Ty = ⊤` and the bounds hold at all
times `t ≥ 0`. -/
theorem pieces_induction {Ty : ℝ≥0∞} {Good Bnd : ℝ → Prop} {L : ℝ} (hL : 1 ≤ L)
    (hstep : ∀ τ : ℝ, 0 ≤ τ → ENNReal.ofReal τ < Ty → Good τ →
      ∃ τ' : ℝ, τ + L ≤ τ' ∧ ENNReal.ofReal τ' < Ty ∧ Good τ' ∧ ∀ u ∈ Icc τ τ', Bnd u)
    (h0 : 0 < Ty) (hG0 : Good 0) : Ty = ⊤ ∧ ∀ t : ℝ, 0 ≤ t → Bnd t := by
  classical
  -- the type of good times inside the lifespan
  let G := {τ : ℝ // 0 ≤ τ ∧ ENNReal.ofReal τ < Ty ∧ Good τ}
  have hnext : ∀ τ : G, ∃ τ' : G, τ.1 + L ≤ τ'.1 ∧ ∀ u ∈ Icc τ.1 τ'.1, Bnd u := by
    rintro ⟨τ, hτ0, hτT, hτG⟩
    obtain ⟨τ', h1, h2, h3, h4⟩ := hstep τ hτ0 hτT hτG
    exact ⟨⟨τ', by linarith, h2, h3⟩, h1, h4⟩
  choose next hnext using hnext
  let g0 : G := ⟨0, le_rfl, by simpa using h0, hG0⟩
  let seq : ℕ → G := fun n => next^[n] g0
  have hseq_succ : ∀ n, seq (n + 1) = next (seq n) := fun n =>
    Function.iterate_succ_apply' next n g0
  have hseq0 : (seq 0).1 = 0 := rfl
  have hgrow : ∀ n : ℕ, (n : ℝ) * L ≤ (seq n).1 := by
    intro n
    induction n with
    | zero => simp [hseq0]
    | succ n ih =>
      have := (hnext (seq n)).1
      rw [hseq_succ]
      push_cast
      linarith
  have hTop : Ty = ⊤ := by
    by_contra hne
    obtain ⟨n, hn⟩ := exists_nat_gt (Ty.toReal / L)
    have hlt : ENNReal.ofReal (seq n).1 < Ty := (seq n).2.2.1
    have h1 : (seq n).1 < Ty.toReal := (ENNReal.ofReal_lt_iff_lt_toReal (seq n).2.1 hne).1 hlt
    have h2 : Ty.toReal < n * L := by rwa [div_lt_iff₀ (by linarith)] at hn
    linarith [hgrow n]
  refine ⟨hTop, fun t ht => ?_⟩
  have hex : ∃ n : ℕ, t ≤ (seq (n + 1)).1 := by
    obtain ⟨n, hn⟩ := exists_nat_gt (t / L)
    refine ⟨n, ?_⟩
    have h1 : t < n * L := by rwa [div_lt_iff₀ (by linarith)] at hn
    have h2 := hgrow (n + 1)
    push_cast at h2
    nlinarith
  let n := Nat.find hex
  have hn : t ≤ (seq (n + 1)).1 := Nat.find_spec hex
  have hlow : (seq n).1 ≤ t := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h, hseq0]
      exact ht
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
      have hmin := Nat.find_min hex (show k < n by omega)
      push Not at hmin
      rw [hk]
      exact hmin.le
  have hn' : t ≤ (next (seq n)).1 := by
    rw [← hseq_succ]
    exact hn
  exact (hnext (seq n)).2 t ⟨hlow, hn'⟩

/-! ### Solution properties and the piece step (locked) -/

/-! ### Time-continuity helpers -/

/-- The helical coefficient of the corrector is at most `2` in size at nonnegative times. -/
private lemma norm_coef_le (x y z L t : ℝ) (hL : 1 ≤ L) (ht : 0 ≤ t) :
    ‖(Complex.exp (-(Complex.I * (x : ℂ))) -
        Complex.exp (-((L * t : ℝ) : ℂ)) * Complex.exp (-(Complex.I * (y : ℂ)))) /
      ((L : ℂ) - Complex.I * (z : ℂ))‖ ≤ 2 := by
  rw [norm_div]
  have hden : 1 ≤ ‖(L : ℂ) - Complex.I * (z : ℂ)‖ := by
    refine hL.trans (le_trans (le_of_eq ?_) (Complex.re_le_norm _))
    simp
  have he1 : ‖Complex.exp (-(Complex.I * (x : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have he2 : ‖Complex.exp (-(Complex.I * (y : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have he3 : ‖Complex.exp (-((L * t : ℝ) : ℂ))‖ ≤ 1 := by
    rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hnum : ‖Complex.exp (-(Complex.I * (x : ℂ))) -
      Complex.exp (-((L * t : ℝ) : ℂ)) * Complex.exp (-(Complex.I * (y : ℂ)))‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, he1, he2]
    linarith
  rw [div_le_iff₀ (by linarith)]
  nlinarith [norm_nonneg (Complex.exp (-(Complex.I * (x : ℂ))) -
      Complex.exp (-((L * t : ℝ) : ℂ)) * Complex.exp (-(Complex.I * (y : ℂ))))]

/-- Mode-wise size of the corrector at nonnegative times: `‖ψ(t)_k‖ ≤ 4 ‖g_k‖`. -/
private lemma norm_psi_le (r : ℝ) (g : Field) {t : ℝ} (ht : 0 ≤ t) (k : Mode) :
    ‖psi r 0 g t k‖ ≤ 4 * ‖g k‖ := by
  unfold psi
  split_ifs with hk
  · rw [norm_zero]
    positivity
  · have hk0 : k ≠ 0 := by
      rintro rfl
      exact hk rfl
    have h1 : (1 : ℝ) ≤ absSq k := one_le_absSq hk0
    refine (norm_sum_le _ _).trans ?_
    rw [Fintype.sum_bool]
    have hterm : ∀ a : Sgn, ‖((Complex.exp (-(Complex.I * (r * (t + 0) * lam a k : ℝ))) -
        Complex.exp (-(absSq k * t : ℝ)) * Complex.exp (-(Complex.I * (r * 0 * lam a k : ℝ)))) /
          ((absSq k : ℂ) - Complex.I * (r * lam a k : ℝ))) • hel a k (g k)‖ ≤ 2 * ‖g k‖ := by
      intro a
      rw [norm_smul]
      exact mul_le_mul (norm_coef_le _ _ _ _ _ h1 ht) (norm_hel_le a k (g k)) (norm_nonneg _)
        (by norm_num)
    linarith [hterm true, hterm false]

/-- Dominated convergence for the `H²` distance. -/
private lemma tendsto_hnorm_sub {F : ℝ → Field} {l : Filter ℝ} {t₀ : ℝ} {B : Mode → ℝ}
    (hB : Summable B) (hdom : ∀ᶠ t in l, ∀ k, sobWeight 2 k * ‖F t k - F t₀ k‖ ^ 2 ≤ B k)
    (hpt : ∀ k, Tendsto (fun t ↦ F t k) l (𝓝 (F t₀ k))) :
    Tendsto (fun t ↦ hnorm 2 (F t - F t₀)) l (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := l) (f := fun t k ↦ sobWeight 2 k *
      ‖F t k - F t₀ k‖ ^ 2) (g := fun _ ↦ (0 : ℝ)) hB (fun k ↦ ?_) ?_
  · have h2 := (Real.continuous_sqrt.tendsto _).comp h
    simpa [hnorm, Function.comp_def] using h2
  · have : Tendsto (fun t ↦ F t k - F t₀ k) l (𝓝 0) := by
      simpa using (hpt k).sub_const (F t₀ k)
    have h3 := ((this.norm).pow 2).const_mul (sobWeight 2 k)
    simpa using h3
  · filter_upwards [hdom] with t ht k
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sobWeight_nonneg 2 k) (sq_nonneg _))]
    exact ht k

/-- The corrector is continuous in `H²` on `[0, ∞)`. -/
private lemma psi_cont {r : ℝ} {g : Field} (hg : Adm 2 g) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    Tendsto (fun t ↦ hnorm 2 (psi r 0 g t - psi r 0 g t₀)) (𝓝[Ici 0] t₀) (𝓝 0) := by
  refine tendsto_hnorm_sub (B := fun k ↦ 64 * (sobWeight 2 k * ‖g k‖ ^ 2))
    (hg.inH.mul_left 64) ?_ fun k ↦
      ((psi_mode (r := r) (t₀ := 0) hg k t₀).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with t ht k
  have h1 := norm_psi_le r g (mem_Ici.mp ht) k
  have h2 := norm_psi_le r g ht₀ k
  have h3 : ‖psi r 0 g t k - psi r 0 g t₀ k‖ ≤ 8 * ‖g k‖ :=
    (norm_sub_le _ _).trans (by linarith)
  have h4 : ‖psi r 0 g t k - psi r 0 g t₀ k‖ ^ 2 ≤ 64 * ‖g k‖ ^ 2 := by
    nlinarith [norm_nonneg (psi r 0 g t k - psi r 0 g t₀ k)]
  nlinarith [sobWeight_nonneg 2 k]

/-- `Π_F` commutes with subtraction. -/
private lemma PiF_sub (u v : Field) : PiF u - PiF v = PiF (u - v) := by
  funext k
  simp only [PiF, Pi.sub_apply]
  split_ifs <;> simp

/-- `Π_S` commutes with subtraction. -/
private lemma PiS_sub (u v : Field) : PiS u - PiS v = PiS (u - v) := by
  funext k
  simp only [PiS, Pi.sub_apply]
  split_ifs <;> simp

/-- A `1`-Lipschitz projection gives `|‖Pu‖_j − ‖Pv‖_j| ≤ ‖u − v‖₂` for `j ≤ 2`. -/
private lemma lip_proj {P : Field → Field} (hsub : ∀ u v, P u - P v = P (u - v))
    (hin : ∀ (s : ℝ) (u : Field), InH s u → InH s (P u))
    (hle : ∀ (s : ℝ) (u : Field), InH s u → hnorm s (P u) ≤ hnorm s u) {j : ℝ} (hj : j ≤ 2)
    {u v : Field} (hu : InH 2 u) (hv : InH 2 v) :
    |hnorm j (P u) - hnorm j (P v)| ≤ hnorm 2 (u - v) := by
  have huv : InH 2 (u - v) := hu.sub hv
  have hd : hnorm j (P (u - v)) ≤ hnorm 2 (u - v) :=
    (hle j _ (huv.mono hj)).trans (hnorm_mono hj huv)
  have hd' : hnorm j (P (v - u)) ≤ hnorm 2 (u - v) := by
    rw [hnorm_sub_comm]
    exact (hle j _ ((hv.sub hu).mono hj)).trans (hnorm_mono hj (hv.sub hu))
  have hPu := hin j u (hu.mono hj)
  have hPv := hin j v (hv.mono hj)
  rw [abs_sub_le_iff]
  constructor
  · have := hnorm_add_le (hPu.sub hPv) hPv
    rw [sub_add_cancel, hsub] at this
    linarith
  · have := hnorm_add_le (hPv.sub hPu) hPu
    rw [sub_add_cancel, hsub] at this
    linarith

private lemma PiH_sub (u v : Field) : PiH u - PiH v = PiH (u - v) := by
  funext k
  by_cases h : k 2 = 0
  · simp only [PiH, h, ite_true, Pi.sub_apply]
    ext i
    fin_cases i <;> simp
  · simp [PiH, h]

/-- `‖Π_H f‖_s ≤ ‖f‖_s`. -/
private lemma hnorm_PiH_le' {s : ℝ} {f : Field} (hf : InH s f) : hnorm s (PiH f) ≤ hnorm s f := by
  have h := hnorm_sq_split_slow hf
  have h1 : hnorm s (PiH f) ≤ hnorm s (PiS f) :=
    (pow_le_pow_iff_left₀ (hnorm_nonneg _ _) (hnorm_nonneg _ _) (by norm_num : (2 : ℕ) ≠ 0)).1
      (by nlinarith [sq_nonneg (hnorm s (PiV f))])
  exact h1.trans (hnorm_PiS_le hf)

/-- The Wiener norm is subadditive on `H²`. -/
private lemma wiener_add_le {a b : Field} (ha : InH 2 a) (hb : InH 2 b) :
    wiener (a + b) ≤ wiener a + wiener b := by
  unfold wiener
  rw [← (summable_wiener ha).tsum_add (summable_wiener hb)]
  exact (summable_wiener (ha.add hb)).tsum_le_tsum (fun k ↦ norm_add_le _ _)
    ((summable_wiener ha).add (summable_wiener hb))

/-- Lipschitz bound for the slow Wiener norm. -/
private lemma lip_wiener {u v : Field} (hu : MZ 2 u) (hv : MZ 2 v) :
    |wiener (PiS u) - wiener (PiS v)| ≤ c4 * hnorm 2 (u - v) := by
  have hmz : ∀ a b : Field, MZ 2 a → MZ 2 b → MZ 2 (PiS (a - b)) := fun a b ha hb ↦
    ⟨(ha.inH.sub hb.inH).PiS, by simp [PiS, ha.mean, hb.mean]⟩
  have hc := c4_pos
  have h1 := wiener_le (hmz u v hu hv)
  have h2 := wiener_le (hmz v u hv hu)
  have h3 := hnorm_PiS_le (hu.inH.sub hv.inH)
  have h4 := hnorm_PiS_le (hv.inH.sub hu.inH)
  rw [hnorm_sub_comm (f := v)] at h4
  rw [abs_sub_le_iff]
  constructor
  · have := wiener_add_le (hu.inH.PiS.sub hv.inH.PiS) hv.inH.PiS
    rw [sub_add_cancel, PiS_sub] at this
    nlinarith
  · have := wiener_add_le (hv.inH.PiS.sub hu.inH.PiS) hu.inH.PiS
    rw [sub_add_cancel, PiS_sub] at this
    nlinarith

/-- A function controlled by a distance tending to `0` is continuous. -/
private lemma cwa_of_le {N d : ℝ → ℝ} {S : Set ℝ} {t₀ C : ℝ}
    (hd : Tendsto d (𝓝[S] t₀) (𝓝 0)) (hle : ∀ t ∈ S, |N t - N t₀| ≤ C * d t) :
    ContinuousWithinAt N S t₀ := by
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
    (by simpa using hd.const_mul C)
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact hle t ht

/-- The actual field is `MZ 2` inside the lifespan. -/
theorem actual_mz {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}
    (hsol : ActualSol μ φ r g y Ty) {t : ℝ} (ht : 0 ≤ t) (htT : ENNReal.ofReal t < Ty) :
    MZ 2 (actual r g y t) := by
  have h1 := hsol.sol.adm t ht htT
  have h2 := psi_adm (r := r) (t₀ := 0) hsol.force_adm t ht
  exact ⟨h1.inH.sub h2.inH, by simp [actual, h1.mean, h2.mean]⟩

/-- The actual field is continuous in `H²` on `[0, b]` inside the lifespan. -/
private lemma actual_cont {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}
    (hsol : ActualSol μ φ r g y Ty) {b : ℝ} (hbT : ENNReal.ofReal b < Ty) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc 0 b) :
    Tendsto (fun t ↦ hnorm 2 (actual r g y t - actual r g y t₀)) (𝓝[Icc 0 b] t₀) (𝓝 0) := by
  have hlife : ∀ t ∈ Icc (0 : ℝ) b, ENNReal.ofReal t < Ty := fun t ht ↦
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ht.2) hbT
  have hsub : Icc (0 : ℝ) b ⊆ Ici 0 := fun t ht ↦ ht.1
  have hy := (hsol.sol.cont t₀ ht₀.1 (hlife t₀ ht₀)).mono_left (nhdsWithin_mono _ hsub)
  have hp := (psi_cont (r := r) hsol.force_adm t₀ ht₀.1).mono_left (nhdsWithin_mono _ hsub)
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ hnorm_nonneg _ _) ?_
    (by simpa using hy.add hp)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have e : actual r g y t - actual r g y t₀ =
      (y t - y t₀) - (psi r 0 g t - psi r 0 g t₀) := by
    simp only [actual]
    abel
  rw [e]
  exact hnorm_sub_le (((hsol.sol.adm t ht.1 (hlife t ht)).inH).sub
      (hsol.sol.adm t₀ ht₀.1 (hlife t₀ ht₀)).inH)
    ((psi_adm hsol.force_adm t ht.1).inH.sub (psi_adm hsol.force_adm t₀ ht₀.1).inH)

/-- **Time-continuity of the cap functions** along a filtered heat solution (locked): on every
compact `[0, b]` inside the lifespan, `a_F, b_F, a_S, b_S, W_S` are continuous.  Proof: `y` is
`H²`-continuous (`IsHeatSol.cont`), `psi r 0 g` is `H²`-continuous in time (its modes are
explicit exponentials, `psi_mode`), `hnorm_PiF_le`/`hnorm_PiS_le` make the projections
`1`-Lipschitz, and `wiener_le` bounds the Wiener norm by `c₄ ‖·‖₂`. -/
theorem norms_continuous {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}
    (hsol : ActualSol μ φ r g y Ty) {b : ℝ} (_hb : 0 ≤ b) (hbT : ENNReal.ofReal b < Ty) :
    ContinuousOn (fastNorm 1 r g y) (Icc 0 b) ∧ ContinuousOn (fastNorm 2 r g y) (Icc 0 b) ∧
      ContinuousOn (slowNorm 1 r g y) (Icc 0 b) ∧ ContinuousOn (slowNorm 2 r g y) (Icc 0 b) ∧
      ContinuousOn (slowWiener r g y) (Icc 0 b) ∧ ContinuousOn (slowNorm 0 r g y) (Icc 0 b) ∧
      ContinuousOn (horizNorm 1 r g y) (Icc 0 b) ∧ ContinuousOn (horizNorm 2 r g y) (Icc 0 b) := by
  have hlife : ∀ t ∈ Icc (0 : ℝ) b, ENNReal.ofReal t < Ty := fun t ht ↦
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ht.2) hbT
  have hmz : ∀ t ∈ Icc (0 : ℝ) b, MZ 2 (actual r g y t) := fun t ht ↦
    actual_mz hsol ht.1 (hlife t ht)
  have hF : ∀ j : ℝ, j ≤ 2 → ContinuousOn (fastNorm j r g y) (Icc 0 b) := by
    intro j hj t₀ ht₀
    refine cwa_of_le (C := 1) (actual_cont hsol hbT ht₀) fun t ht ↦ ?_
    rw [one_mul]
    exact lip_proj PiF_sub (fun _ _ h ↦ h.PiF) (fun _ _ h ↦ hnorm_PiF_le h) hj
      (hmz t ht).inH (hmz t₀ ht₀).inH
  have hS : ∀ j : ℝ, j ≤ 2 → ContinuousOn (slowNorm j r g y) (Icc 0 b) := by
    intro j hj t₀ ht₀
    refine cwa_of_le (C := 1) (actual_cont hsol hbT ht₀) fun t ht ↦ ?_
    rw [one_mul]
    exact lip_proj PiS_sub (fun _ _ h ↦ h.PiS) (fun _ _ h ↦ hnorm_PiS_le h) hj
      (hmz t ht).inH (hmz t₀ ht₀).inH
  have hW : ContinuousOn (slowWiener r g y) (Icc 0 b) := fun t₀ ht₀ ↦
    cwa_of_le (actual_cont hsol hbT ht₀) fun t ht ↦ lip_wiener (hmz t ht) (hmz t₀ ht₀)
  have hH : ∀ j : ℝ, j ≤ 2 → ContinuousOn (horizNorm j r g y) (Icc 0 b) := by
    intro j hj t₀ ht₀
    refine cwa_of_le (C := 1) (actual_cont hsol hbT ht₀) fun t ht ↦ ?_
    rw [one_mul]
    exact lip_proj PiH_sub (fun _ _ h ↦ h.PiH) (fun _ _ h ↦ hnorm_PiH_le' h) hj
      (hmz t ht).inH (hmz t₀ ht₀).inH
  exact ⟨hF 1 (by norm_num), hF 2 le_rfl, hS 1 (by norm_num), hS 2 le_rfl, hW,
    hS 0 (by norm_num), hH 1 (by norm_num), hH 2 le_rfl⟩

/-! ### `H³` regularity of the actual fast part at almost every time -/

/-- The helical coefficient of the corrector is at most `2/L` in size at nonnegative times. -/
private lemma norm_coef_le_div (x y z L t : ℝ) (hL : 1 ≤ L) (ht : 0 ≤ t) :
    ‖(Complex.exp (-(Complex.I * (x : ℂ))) -
        Complex.exp (-((L * t : ℝ) : ℂ)) * Complex.exp (-(Complex.I * (y : ℂ)))) /
      ((L : ℂ) - Complex.I * (z : ℂ))‖ ≤ 2 / L := by
  rw [norm_div]
  have hden : L ≤ ‖(L : ℂ) - Complex.I * (z : ℂ)‖ := by
    refine le_trans (le_of_eq ?_) (Complex.re_le_norm _)
    simp
  have he1 : ‖Complex.exp (-(Complex.I * (x : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have he2 : ‖Complex.exp (-(Complex.I * (y : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have he3 : ‖Complex.exp (-((L * t : ℝ) : ℂ))‖ ≤ 1 := by
    rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hnum : ‖Complex.exp (-(Complex.I * (x : ℂ))) -
      Complex.exp (-((L * t : ℝ) : ℂ)) * Complex.exp (-(Complex.I * (y : ℂ)))‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, he1, he2]
    linarith
  exact div_le_div₀ (by norm_num) hnum (by linarith) hden

/-- Mode-wise smoothing of the corrector: `‖ψ(t)_k‖ ≤ 4 ‖g_k‖ / |k|²`. -/
private lemma norm_psi_le_div (r : ℝ) (g : Field) {t : ℝ} (ht : 0 ≤ t) {k : Mode}
    (hk0 : k ≠ 0) : ‖psi r 0 g t k‖ ≤ 4 * ‖g k‖ / absSq k := by
  have h1 : (1 : ℝ) ≤ absSq k := one_le_absSq hk0
  unfold psi
  split_ifs with hk
  · rw [norm_zero]
    positivity
  · refine (norm_sum_le _ _).trans ?_
    rw [Fintype.sum_bool]
    have hterm : ∀ a : Sgn, ‖((Complex.exp (-(Complex.I * (r * (t + 0) * lam a k : ℝ))) -
        Complex.exp (-(absSq k * t : ℝ)) * Complex.exp (-(Complex.I * (r * 0 * lam a k : ℝ)))) /
          ((absSq k : ℂ) - Complex.I * (r * lam a k : ℝ))) • hel a k (g k)‖ ≤
          2 / absSq k * ‖g k‖ := by
      intro a
      rw [norm_smul]
      exact mul_le_mul (norm_coef_le_div _ _ _ _ _ h1 ht) (norm_hel_le a k (g k))
        (norm_nonneg _) (by positivity)
    have e : 4 * ‖g k‖ / absSq k = 2 / absSq k * ‖g k‖ + 2 / absSq k * ‖g k‖ := by ring
    rw [e]
    linarith [hterm true, hterm false]

/-- `sobWeight 3 = |k|⁶` and `sobWeight 2 = |k|⁴` away from `0`. -/
private lemma sobWeight_nat {n : ℕ} {k : Mode} (hk : k ≠ 0) :
    sobWeight (n : ℝ) k = absSq k ^ n := by
  simp only [sobWeight, hk, ite_false]
  rw [← absk_sq, ← pow_mul, ← Real.rpow_natCast]
  push_cast
  ring_nf

/-- The corrector is in `H³` at nonnegative times (parabolic smoothing of the explicit modes). -/
theorem inH3_psi {r : ℝ} {g : Field} (hg : Adm 2 g) {t : ℝ} (ht : 0 ≤ t) :
    InH 3 (psi r 0 g t) := by
  refine Summable.of_nonneg_of_le (fun k ↦ mul_nonneg (sobWeight_nonneg 3 k) (sq_nonneg _))
    (fun k ↦ ?_) (hg.inH.mul_left 16)
  by_cases hk : k = 0
  · simp [sobWeight, hk]
  have h1 : (1 : ℝ) ≤ absSq k := one_le_absSq hk
  have h3 : sobWeight 3 k = absSq k ^ 3 := by exact_mod_cast sobWeight_nat (n := 3) hk
  have h2 : sobWeight 2 k = absSq k ^ 2 := by exact_mod_cast sobWeight_nat (n := 2) hk
  rw [h3, h2]
  have hp := norm_psi_le_div r g ht hk
  have hp2 : ‖psi r 0 g t k‖ ^ 2 ≤ (4 * ‖g k‖ / absSq k) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hp 2
  have hA : 0 < absSq k := by linarith
  calc absSq k ^ 3 * ‖psi r 0 g t k‖ ^ 2 ≤ absSq k ^ 3 * (4 * ‖g k‖ / absSq k) ^ 2 :=
        mul_le_mul_of_nonneg_left hp2 (by positivity)
    _ = 16 * (absSq k * ‖g k‖ ^ 2) := by field_simp; ring
    _ ≤ 16 * (absSq k ^ 2 * ‖g k‖ ^ 2) := by
        gcongr
        nlinarith

/-- At almost every time of `[0, b]` inside the lifespan, the actual fast part is in `H³`
(`IsHeatSol.heatPair`, `HeatPair.ae_inH`, `inH3_psi`). -/
theorem ae_inH3_fast {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}
    (hsol : ActualSol μ φ r g y Ty) {b : ℝ} (hb : 0 ≤ b) (hbT : ENNReal.ofReal b < Ty) :
    ∀ᵐ u ∂(volume.restrict (Icc 0 b)), InH 3 (PiF (actual r g y u)) := by
  have hp := (hsol.sol.heatPair (majorized_filtN r 0) (goodForce_filtG r 0 hsol.force_adm) hb
    hbT).ae_inH hb
  filter_upwards [hp, ae_restrict_mem measurableSet_Icc] with u hu hmem
  have e : (2 : ℝ) + 1 = 3 := by norm_num
  rw [e] at hu
  exact (hu.sub (inH3_psi hsol.force_adm hmem.1)).PiF

/-! ### First-exit helpers -/

/-- The ten cap deficits at time `s + τ`, combined by `max`. -/
def deficit (caps : Caps) (r : ℝ) (g : Field) (y : ℝ → Field) (s τ : ℝ) : ℝ :=
  max (fastNorm 1 r g y (s + τ) - caps.PF) (max (fastNorm 2 r g y (s + τ) - caps.yF)
    (max (slowNorm 1 r g y (s + τ) - caps.AS) (max (slowNorm 2 r g y (s + τ) - caps.BS)
      (max (slowWiener r g y (s + τ) - caps.WS)
      (max (slowNorm 0 r g y (s + τ) - caps.ES) (max (horizNorm 1 r g y (s + τ) - caps.AH)
      (max (horizNorm 2 r g y (s + τ) - caps.BH)
        (max ((∫ u in s..s + τ, fastNorm 2 r g y u ^ 2) - caps.JF)
          ((∫ u in s..s + τ, slowNorm 2 r g y u ^ 2) - caps.JS)))))))))

/-- A shifted continuous function minus a constant is continuous. -/
private lemma shift_cont {N : ℝ → ℝ} {s c : ℝ} (hs : 0 ≤ s)
    (hN : ContinuousOn N (Icc 0 (s + c))) (C : ℝ) :
    ContinuousOn (fun τ ↦ N (s + τ) - C) (Icc 0 c) :=
  (hN.comp (continuous_id'.const_add s).continuousOn fun τ hτ ↦
    ⟨by linarith [hτ.1], by linarith [hτ.2]⟩).sub
    continuousOn_const

/-- A shifted primitive of a continuous square minus a constant is continuous. -/
private lemma shift_int_cont {N : ℝ → ℝ} {s c : ℝ} (hs : 0 ≤ s) (hc : 0 ≤ c)
    (hN : ContinuousOn N (Icc 0 (s + c))) (C : ℝ) :
    ContinuousOn (fun τ ↦ (∫ u in s..s + τ, N u ^ 2) - C) (Icc 0 c) := by
  have hN' : ContinuousOn (fun u ↦ N u ^ 2) (uIcc s (s + c)) := by
    rw [uIcc_of_le (by linarith)]
    exact (hN.mono (Icc_subset_Icc hs le_rfl)).pow 2
  have hP := intervalIntegral.continuousOn_primitive_interval (μ := volume)
    (hN'.integrableOn_compact isCompact_uIcc)
  rw [uIcc_of_le (by linarith)] at hP
  exact (hP.comp (continuous_id'.const_add s).continuousOn fun τ hτ ↦
    ⟨by linarith [hτ.1], by linarith [hτ.2]⟩).sub
    continuousOn_const

/-- The deficit is continuous on `[0, c]` when `[s, s + c]` lies in the lifespan. -/
lemma deficit_cont {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}
    (hsol : ActualSol μ φ r g y Ty) (caps : Caps) {s c : ℝ} (hs : 0 ≤ s) (hc : 0 ≤ c)
    (hT : ENNReal.ofReal (s + c) < Ty) : ContinuousOn (deficit caps r g y s) (Icc 0 c) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := norms_continuous hsol (b := s + c) (by linarith) hT
  unfold deficit
  exact ContinuousOn.sup (shift_cont hs h1 _) <| ContinuousOn.sup (shift_cont hs h2 _) <|
    ContinuousOn.sup (shift_cont hs h3 _) <| ContinuousOn.sup (shift_cont hs h4 _) <|
      ContinuousOn.sup (shift_cont hs h5 _) <| ContinuousOn.sup (shift_cont hs h6 _) <|
      ContinuousOn.sup (shift_cont hs h7 _) <| ContinuousOn.sup (shift_cont hs h8 _) <|
        ContinuousOn.sup (shift_int_cont hs hc h2 _) (shift_int_cont hs hc h4 _)

/-- A function continuous on every `[0, c]`, `0 ≤ c < T`, is continuous on `[0, T)`. -/
private lemma continuousOn_Ico_of_Icc {f : ℝ → ℝ} {T : ℝ}
    (h : ∀ c, 0 ≤ c → c < T → ContinuousOn f (Icc 0 c)) : ContinuousOn f (Ico 0 T) := by
  intro x hx
  have hxc : x ∈ Icc 0 ((x + T) / 2) := ⟨hx.1, by linarith [hx.2]⟩
  refine ((h _ (by linarith [hx.1, hx.2]) (by linarith [hx.2])) x hxc).mono_of_mem_nhdsWithin ?_
  have : Iio ((x + T) / 2) ∈ 𝓝 x := Iio_mem_nhds (by linarith [hx.2])
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds this] with u hu1 hu2
  exact ⟨hu1.1, le_of_lt hu2⟩

/-- A nonpositive deficit on `[0, τ₀]` gives the caps on `[s, s + τ₀]`. -/
lemma onPrefix_of_deficit {caps : Caps} {r : ℝ} {g : Field} {y : ℝ → Field} {s τ₀ : ℝ}
    (hτ₀ : 0 ≤ τ₀) (h : ∀ τ ∈ Icc 0 τ₀, deficit caps r g y s τ ≤ 0) :
    OnPrefix caps r g y s (s + τ₀) := by
  have hτ := h τ₀ ⟨hτ₀, le_rfl⟩
  simp only [deficit, max_le_iff, sub_nonpos] at hτ
  obtain ⟨-, -, -, -, -, -, -, -, hJF, hJS⟩ := hτ
  have hpt : ∀ u ∈ Icc s (s + τ₀), PointCaps caps r g y u := by
    intro u hu
    have hu' := h (u - s) ⟨by linarith [hu.1], by linarith [hu.2]⟩
    simp only [deficit, max_le_iff, sub_nonpos, add_sub_cancel] at hu'
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, -, -⟩ := hu'
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩
  refine ⟨fun u hu ↦ ?_, hJF, hJS, fun u hu ↦ ?_⟩
  · obtain ⟨a1, a2, a3, a4, a5, -⟩ := hpt u hu
    exact ⟨a1, a2, a3, a4, a5⟩
  · obtain ⟨-, -, -, -, -, a6, a7, a8⟩ := hpt u hu
    exact ⟨a6, a7, a8⟩

/-- The improved caps on `[s, s + τ₀]` make the deficit at `τ₀` strictly negative. -/
lemma deficit_neg_of_below {caps ci : Caps} (hlt : ci.Below caps)
    {r : ℝ} {g : Field} {y : ℝ → Field} {s τ₀ : ℝ} (hτ₀ : 0 ≤ τ₀)
    (h : OnPrefix ci r g y s (s + τ₀)) : deficit caps r g y s τ₀ < 0 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ :=
    pointCaps_of_onPrefix h (u := s + τ₀) ⟨by linarith, le_rfl⟩
  obtain ⟨-, hJF, hJS, -⟩ := h
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, -, -, p8, p9, p10⟩ := hlt
  simp only [deficit, max_lt_iff, sub_neg]
  exact ⟨a1.trans_lt p1, a2.trans_lt p2, a3.trans_lt p3, a4.trans_lt p4, a5.trans_lt p5,
    a6.trans_lt p8, a7.trans_lt p9, a8.trans_lt p10, hJF.trans_lt p6, hJS.trans_lt p7⟩

/-- The deficit is strictly negative at a good point. -/
lemma deficit_zero {Mf : ℝ} {caps ci c0 : Caps} (hlt : ci.Below caps)
    {r : ℝ} {g : Field} {y : ℝ → Field} {s : ℝ}
    (hgood : GoodPoint Mf c0 ci r g y s) : deficit caps r g y s 0 < 0 := by
  have h : OnPrefix ci r g y s (s + 0) := by
    rw [add_zero]
    exact onPrefix_point hgood.pointCaps hlt.2.2.2.2.2.2.2.1 hlt.2.2.2.2.2.2.2.2.1
  exact deficit_neg_of_below hlt le_rfl h

/-- **Closed first exit**: the caps hold on the whole piece `[s, s + T']` when it lies strictly
inside the lifespan. -/
theorem onPrefix_closed {Mf Tp μ φ : ℝ} {q : Caps → ℝ} {caps ci c0 : Caps}
    (hlt : ci.Below caps) (himp : StrictImprovement Mf Tp μ φ q caps ci c0)
    {r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} (hsol : ActualSol μ φ r g y Ty)
    (hthr : q caps ≤ |r|) {s T' : ℝ} (hgood : GoodPoint Mf c0 ci r g y s) (hT'0 : 0 ≤ T')
    (hT' : T' ≤ Tp) (hlife : ENNReal.ofReal (s + T') < Ty) : OnPrefix caps r g y s (s + T') := by
  have hs := hgood.nonneg
  have hcont := deficit_cont hsol caps hs hT'0 hlife
  have himp' : ∀ τ₀ ∈ Ico 0 T', (∀ τ ∈ Icc 0 τ₀, deficit caps r g y s τ ≤ 0) →
      deficit caps r g y s τ₀ < 0 := by
    intro τ₀ hτ₀ hle
    have hpre := onPrefix_of_deficit hτ₀.1 hle
    have hpiece : PieceHyp Tp q r g y Ty caps s (s + τ₀) :=
      ⟨⟨hs, by linarith [hτ₀.1],
        lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by linarith [hτ₀.2])) hlife, hthr, hpre⟩,
        by linarith [hτ₀.2]⟩
    exact deficit_neg_of_below hlt hτ₀.1 (himp r g y Ty hsol s (s + τ₀) hgood hpiece).1
  have hneg := first_exit (hcont.mono Ico_subset_Icc_self) (deficit_zero hlt hgood) himp'
  refine onPrefix_of_deficit hT'0 fun τ hτ ↦ ?_
  rcases lt_or_eq_of_le hτ.2 with h | h
  · exact (hneg τ ⟨hτ.1, h⟩).le
  · rw [h]
    rcases lt_or_eq_of_le hT'0 with h0 | h0
    · have hmem : Icc 0 T' ∈ 𝓝[<] T' :=
        mem_of_superset (Ico_mem_nhdsLT h0) Ico_subset_Icc_self
      have ht := (hcont T' ⟨hT'0, le_rfl⟩).mono_of_mem_nhdsWithin hmem
      exact le_of_tendsto ht
        (by filter_upwards [Ico_mem_nhdsLT h0] with u hu using (hneg u hu).le)
    · rw [← h0]
      exact (deficit_zero hlt hgood).le

/-! ### Blow-up helpers -/

/-- The corrector is bounded in `H²` by `4 ‖g‖₂` at nonnegative times. -/
private lemma hnorm_psi_le {r : ℝ} {g : Field} (hg : Adm 2 g) {t : ℝ} (ht : 0 ≤ t) :
    hnorm 2 (psi r 0 g t) ≤ 4 * hnorm 2 g := by
  unfold hnorm
  rw [show (4 : ℝ) = √16 by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
    ← Real.sqrt_mul (by norm_num)]
  refine Real.sqrt_le_sqrt ?_
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun k ↦ ?_) (psi_adm (r := r) (t₀ := 0) hg t ht).inH
    (hg.inH.mul_left 16)
  have h1 := norm_psi_le r g ht k
  have h2 : ‖psi r 0 g t k‖ ^ 2 ≤ 16 * ‖g k‖ ^ 2 := by
    nlinarith [norm_nonneg (psi r 0 g t k)]
  nlinarith [sobWeight_nonneg 2 k]

/-- `‖y‖₂ ≤ b_F + b_S + 4 ‖g‖₂` inside the lifespan. -/
theorem hnorm_y_le {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}
    (hsol : ActualSol μ φ r g y Ty) {t : ℝ} (ht : 0 ≤ t) (htT : ENNReal.ofReal t < Ty) :
    hnorm 2 (y t) ≤ fastNorm 2 r g y t + slowNorm 2 r g y t + 4 * hnorm 2 g := by
  have ha := (actual_mz hsol ht htT).inH
  have hp := (psi_adm (r := r) (t₀ := 0) hsol.force_adm t ht).inH
  have e : y t = (PiS (actual r g y t) + PiF (actual r g y t)) + psi r 0 g t := by
    rw [PiS_add_PiF]
    simp [actual]
  rw [e]
  have h1 := hnorm_add_le (ha.PiS.add ha.PiF) hp
  have h2 := hnorm_add_le ha.PiS ha.PiF
  have h3 := hnorm_psi_le (r := r) hsol.force_adm ht
  simp only [fastNorm, slowNorm]
  linarith

/-- `‖y‖₂` is bounded on `[0, s]` inside the lifespan. -/
lemma bdd_initial {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}
    (hsol : ActualSol μ φ r g y Ty) {s : ℝ} (hsT : ENNReal.ofReal s < Ty) :
    ∃ M : ℝ, ∀ t ∈ Icc 0 s, hnorm 2 (y t) ≤ M := by
  have hlife : ∀ t ∈ Icc (0 : ℝ) s, ENNReal.ofReal t < Ty := fun t ht ↦
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ht.2) hsT
  have hcont : ContinuousOn (fun t ↦ hnorm 2 (y t)) (Icc 0 s) := by
    intro t₀ ht₀
    have hy := (hsol.sol.cont t₀ ht₀.1 (hlife t₀ ht₀)).mono_left
      (nhdsWithin_mono _ fun t (ht : t ∈ Icc (0 : ℝ) s) ↦ ht.1)
    refine cwa_of_le (C := 1) hy fun t ht ↦ ?_
    rw [one_mul]
    exact lip_proj (P := id) (fun _ _ ↦ rfl) (fun _ _ h ↦ h) (fun _ _ _ ↦ le_rfl) le_rfl
      (hsol.sol.adm t ht.1 (hlife t ht)).inH (hsol.sol.adm t₀ ht₀.1 (hlife t₀ ht₀)).inH
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  exact ⟨M, fun t ht ↦ (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hM t ht)⟩

/-- **First exit on a piece** (locked; `first_exit` applied to the seven cap deficits).  From a
good point `s`, as long as the lookahead `[s, s + T']` (`T' ≤ Tp`) stays inside the lifespan,
the caps hold on every `[s, t]`, `t < s + T'`: the deficit
`max(a_F − P_F, b_F − y, a_S − A_S, b_S − B_S, W_S − WS, ∫_s b_F² − J_F, ∫_s b_S² − J_S)` is
continuous (`norms_continuous`, continuity of primitives), negative at `s` (`GoodPoint`,
`ci.Below caps`) and, whenever `≤ 0` on `[s, s+τ₀]`, strictly negative at `s+τ₀` by
`StrictImprovement`. -/
theorem piece_first_exit {Mf Tp μ φ : ℝ} {q : Caps → ℝ} {caps ci c0 : Caps}
    (hlt : ci.Below caps) (himp : StrictImprovement Mf Tp μ φ q caps ci c0)
    {r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} (hsol : ActualSol μ φ r g y Ty)
    (hthr : q caps ≤ |r|) {s T' : ℝ} (hgood : GoodPoint Mf c0 ci r g y s) (hT'0 : 0 < T')
    (hT' : T' ≤ Tp) (hlife : ENNReal.ofReal (s + T') ≤ Ty) :
    ∀ t : ℝ, s ≤ t → t < s + T' → OnPrefix caps r g y s t := by
  intro t hst htT
  have hs := hgood.nonneg
  have h := onPrefix_closed hlt himp hsol hthr hgood (T' := t - s) (by linarith)
    (by linarith) ?_
  · rwa [add_sub_cancel] at h
  · rw [add_sub_cancel]
    exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 htT) hlife

/-- **Blow-up alternative on a piece**: from a good point `s` inside the lifespan of a solution
with the blow-up alternative, the lifespan exceeds `s + T'` for every `0 < T' ≤ Tp`
(`piece_first_exit` bounds `‖y‖₂ ≤ y + B_S + 4 ‖g‖₂` on the existing part of the piece, and
`‖y‖₂` is bounded on `[0, s]` by continuity). -/
private lemma lifespan_gt {Mf Tp μ φ : ℝ} {q : Caps → ℝ} {caps ci c0 : Caps}
    (hlt : ci.Below caps) (himp : StrictImprovement Mf Tp μ φ q caps ci c0)
    {r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} (hsol : ActualSol μ φ r g y Ty)
    (hbl : Ty ≠ ⊤ → ∀ C : ℝ, ¬ ∀ t, 0 ≤ t → ENNReal.ofReal t < Ty → hnorm 2 (y t) ≤ C)
    (hthr : q caps ≤ |r|) {s T' : ℝ} (hgood : GoodPoint Mf c0 ci r g y s) (hT'0 : 0 < T')
    (hT' : T' ≤ Tp) (hs : ENNReal.ofReal s < Ty) : ENNReal.ofReal (s + T') < Ty := by
  have hs0 := hgood.nonneg
  by_contra hcon
  push Not at hcon
  have hTop : Ty ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hcon
  have hse : s < Ty.toReal := (ENNReal.ofReal_lt_iff_lt_toReal hs0 hTop).1 hs
  have hle : Ty.toReal ≤ s + T' := ENNReal.toReal_le_of_le_ofReal (by linarith) hcon
  have hcaps := piece_first_exit hlt himp hsol hthr hgood (T' := Ty.toReal - s)
    (by linarith) (by linarith) (by rw [add_sub_cancel, ENNReal.ofReal_toReal hTop])
  obtain ⟨M, hM⟩ := bdd_initial hsol hs
  refine hbl hTop (max M (caps.yF + caps.BS + 4 * hnorm 2 g)) fun t ht htT ↦ ?_
  rcases le_or_gt t s with h | h
  · exact (hM t ⟨ht, h⟩).trans (le_max_left _ _)
  · have htT' : t < Ty.toReal := (ENNReal.ofReal_lt_iff_lt_toReal ht hTop).1 htT
    have hc := ((hcaps t h.le (by linarith)).1 t ⟨h.le, le_rfl⟩)
    have hy := hnorm_y_le hsol ht htT
    exact hy.trans (le_trans (by linarith [hc.2.1, hc.2.2.2.1]) (le_max_right _ _))

/-- The kinetic clauses of `KineticInterface` for one solution with kinetic functional `W0`
(`KineticInterface μ φ q₀` is `∀ r g y Ty, ActualSol μ φ r g y Ty → ∃ W0, KinFun …`). -/
def KinFun (μ : ℝ) (q₀ : Caps → ℝ) (r : ℝ) (g : Field) (y : ℝ → Field) (Ty : ℝ≥0∞)
    (W0 : ℝ → ℝ) : Prop :=
  ∀ (caps : Caps) (s t : ℝ), PrefixHyp q₀ r g y Ty caps s t →
    (∀ u ∈ Icc s t, 3 / 4 * fastNorm 0 r g y u ^ 2 ≤ W0 u ∧
      W0 u ≤ 5 / 4 * fastNorm 0 r g y u ^ 2) ∧
    (s = 0 → W0 0 ≤ 5 / 4 * (μ + 1 / 4) ^ 2) ∧
    W0 t - W0 s + (∫ u in s..t, fastNorm 1 r g y u ^ 2) ≤ (t - s) / 8 ∧
    W0 t ≤ max (W0 s) (5 / 32)

/-- The caps restrict from `[s, t]` to `[s₁, t]` (continuous `b_F`, `b_S`). -/
theorem onPrefix_sub {caps : Caps} {r : ℝ} {g : Field} {y : ℝ → Field} {s t s₁ : ℝ}
    (h : OnPrefix caps r g y s t) (hs₁ : s ≤ s₁) (hs₁t : s₁ ≤ t)
    (hf : ContinuousOn (fastNorm 2 r g y) (Icc s t))
    (hS : ContinuousOn (slowNorm 2 r g y) (Icc s t)) : OnPrefix caps r g y s₁ t := by
  have hst : s ≤ t := hs₁.trans hs₁t
  refine ⟨fun u hu ↦ h.1 u ⟨hs₁.trans hu.1, hu.2⟩, ?_, ?_,
    fun u hu ↦ h.2.2.2 u ⟨hs₁.trans hu.1, hu.2⟩⟩
  · refine le_trans ?_ h.2.1
    exact intervalIntegral.integral_mono_interval hs₁ hs₁t le_rfl
      (Eventually.of_forall fun u ↦ sq_nonneg _) ((hf.pow 2).intervalIntegrable_of_Icc hst)
  · refine le_trans ?_ h.2.2.1
    exact intervalIntegral.integral_mono_interval hs₁ hs₁t le_rfl
      (Eventually.of_forall fun u ↦ sq_nonneg _) ((hS.pow 2).intervalIntegrable_of_Icc hst)

/-- **One piece of the lookahead bootstrap** (amended; Source 3 §10).  On a maximal solution with
the blow-up alternative (`exists_maximal`), from a good point `s` with kinetic level
`W₀(s) ≤ W_max`: the lifespan exceeds `s + Tp` (`lifespan_gt`), the caps hold on `[s, s + Tp]`
(`onPrefix_closed`), they improve there (`StrictImprovement`), the kinetic functional stays
`≤ W_max` (clause `W₀ t ≤ max (W₀ s) (5/32)`), and Chebyshev on `∫ a_F² ≤ 1/8 + W_max < M_f²`
over the last unit `[s + Tp − 1, s + Tp]` gives the next good point `s'`. -/
theorem piece_step {Mf Tp μ φ Wmax : ℝ} {q q₀ : Caps → ℝ} {caps ci c0 : Caps}
    (hlt : ci.Below caps) (hTp : 2 ≤ Tp) (himp : StrictImprovement Mf Tp μ φ q caps ci c0)
    {r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} (hsol : ActualSol μ φ r g y Ty)
    (hbl : Ty ≠ ⊤ → ∀ C : ℝ, ¬ ∀ t, 0 ≤ t → ENNReal.ofReal t < Ty → hnorm 2 (y t) ≤ C)
    (hthr : q caps ≤ |r|) (hthr₀ : q₀ caps ≤ |r|) {W0 : ℝ → ℝ}
    (hW0 : KinFun μ q₀ r g y Ty W0) (hMf : 0 ≤ Mf) (hWmax : 5 / 32 ≤ Wmax)
    (hMfW : 1 / 8 + Wmax < Mf ^ 2) {s : ℝ} (hgood : GoodPoint Mf c0 ci r g y s)
    (hW0s : W0 s ≤ Wmax) (hs : ENNReal.ofReal s < Ty) :
    ∃ s' : ℝ, s + (Tp - 1) ≤ s' ∧ s' ≤ s + Tp ∧ ENNReal.ofReal s' < Ty ∧
      GoodPoint Mf c0 ci r g y s' ∧ W0 s' ≤ Wmax ∧ OnPrefix caps r g y s s' := by
  have hs0 := hgood.nonneg
  set t := s + Tp with ht
  have hlife : ENNReal.ofReal t < Ty :=
    lifespan_gt hlt himp hsol hbl hthr hgood (by linarith) le_rfl hs
  have hlifeu : ∀ u, u ≤ t → ENNReal.ofReal u < Ty := fun u hu ↦
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hu) hlife
  have hon : ∀ u ∈ Icc s t, OnPrefix caps r g y s u := fun u hu ↦ by
    have h := onPrefix_closed hlt himp hsol hthr hgood (T' := u - s) (by linarith [hu.1])
      (by linarith [hu.2]) (by rw [add_sub_cancel]; exact hlifeu u hu.2)
    rwa [add_sub_cancel] at h
  have hW0u : ∀ u ∈ Icc s t, W0 u ≤ Wmax := fun u hu ↦
    ((hW0 caps s u ⟨hs0, hu.1, hlifeu u hu.2, hthr₀, hon u hu⟩).2.2.2).trans
      (max_le hW0s hWmax)
  have himpt := himp r g y Ty hsol s t hgood
    ⟨⟨hs0, by linarith, hlife, hthr, hon t ⟨by linarith, le_rfl⟩⟩, by linarith⟩
  obtain ⟨hc1, hc2, -, hc4, -⟩ := norms_continuous hsol (b := t) (by linarith) hlife
  have hsub : Icc s t ⊆ Icc 0 t := Icc_subset_Icc hs0 le_rfl
  have hrest : OnPrefix caps r g y (t - 1) t := onPrefix_sub (hon t ⟨by linarith, le_rfl⟩)
    (by linarith) (by linarith) (hc2.mono hsub) (hc4.mono hsub)
  obtain ⟨hk1, -, hk3, -⟩ := hW0 caps (t - 1) t ⟨by linarith, by linarith, hlife, hthr₀, hrest⟩
  have hWt : 0 ≤ W0 t := le_trans (by positivity) (hk1 t ⟨by linarith, le_rfl⟩).1
  have hWt1 := hW0u (t - 1) ⟨by linarith, by linarith⟩
  have hint : (∫ u in (t - 1)..t, fastNorm 1 r g y u ^ 2) < Mf ^ 2 := by
    have e : (t - (t - 1)) / 8 = 1 / 8 := by ring
    rw [e] at hk3
    linarith
  have hex : ∃ u ∈ Icc (t - 1) t, fastNorm 1 r g y u < Mf := by
    by_contra hno
    push Not at hno
    have hmono : (∫ _u in (t - 1)..t, Mf ^ 2) ≤ ∫ u in (t - 1)..t, fastNorm 1 r g y u ^ 2 :=
      intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
        (((hc1.mono (Icc_subset_Icc (by linarith) le_rfl)).pow 2).intervalIntegrable_of_Icc
          (by linarith))
        fun u hu ↦ pow_le_pow_left₀ hMf (hno u hu) 2
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    linarith
  obtain ⟨u, hu, hau⟩ := hex
  have hus : u ∈ Icc s t := ⟨by linarith [hu.1], hu.2⟩
  refine ⟨u, by linarith [hu.1], hu.2, hlifeu u hu.2, ⟨by linarith [hu.1], hau.le,
    himpt.2 u ⟨by linarith [hu.1], hu.2⟩, pointCaps_of_onPrefix himpt.1 hus⟩, hW0u u hus,
    hon u hus⟩

end OVNS.Quant

end
