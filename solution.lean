import Mathlib
import OddViscousNS

/-!
# Solution file: proofs of the theorems of `challenge.lean`

`challenge.lean` states Theorems 1.1, 1.2 and 1.3 of the OVNS manuscript over Mathlib alone, with
each proof replaced by `sorry`.  This file repeats its definitions and its five statements word for
word and replaces each `sorry` by a proof.  The proofs come from the `OddViscousNS` library, which
works with its own definitions (`OVNS.*`); the lemmas below translate between the two.

Check it with these two commands; the `#print axioms` lines at the end must list only `propext`,
`Classical.choice`, `Quot.sound`.

    lake build OddViscousNS
    lake env lean solution.lean
-/

open scoped ComplexConjugate ENNReal Topology InnerProductSpace Matrix
open MeasureTheory Set Filter

noncomputable section

namespace Challenge

/- Notation. These are macros: they introduce no new constants. -/

-- A vector field on `𝕋³ = (ℝ/2πℤ)³`, given by its Fourier coefficients `û_k ∈ ℂ³`, `k ∈ ℤ³`.
local notation "Field" => (Fin 3 → ℤ) → EuclideanSpace ℂ (Fin 3)

-- The wave vector `k ∈ ℤ³` as an element of `ℂ³`; in particular `‖κ k‖ = |k|`.
local notation:max "κ" k:max =>
  (WithLp.toLp 2 fun i => ((k : Fin 3 → ℤ) i : ℂ) : EuclideanSpace ℂ (Fin 3))

-- The Leray symbol `P_k`: the orthogonal projection of `ℂ³` onto `k^⊥`.
local notation:max "P" k:max => Submodule.starProjection (ℂ ∙ κ k)ᗮ

/-- `‖u‖_s² = ∑_{k ≠ 0} |k|^{2s} |û_k|² ∈ [0, ∞]`, the squared homogeneous `H^s` coefficient norm. -/
def hsE (s : ℝ) (u : Field) : ℝ≥0∞ :=
  ∑' k, if k = 0 then 0 else ENNReal.ofReal (‖κ k‖ ^ (2 * s) * ‖u k‖ ^ 2)

/-- Real, mean-zero, divergence-free fields in `H^s`. -/
structure Adm (s : ℝ) (u : Field) : Prop where
  finite : hsE s u < ∞
  real : ∀ k i, u (-k) i = conj (u k i)
  sol : ∀ k, ⟪κ k, u k⟫_ℂ = 0
  mean : u 0 = 0

/-- `t ↦ u t` is continuous on `[0,∞)` with values in `H^s`. -/
def ContH (s : ℝ) (u : ℝ → Field) : Prop :=
  ∀ t₀ ∈ Ici (0 : ℝ), Tendsto (fun t => hsE s (u t - u t₀)) (𝓝[Ici 0] t₀) (𝓝 0)

/-- `u ∈ L²_loc([0,∞); H^s)`. -/
def L2locH (s : ℝ) (u : ℝ → Field) : Prop :=
  ∀ T : ℝ, 0 ≤ T → ∫⁻ t in Icc 0 T, hsE s (u t) < ∞

/-- A global strong solution in `C([0,∞); H²_sol)` of
`∂ₜu + ℙ((u·∇)u) = νΔu + αLu + f`, `u(0) = u₀`, where `L = ℙ(e₃ × Δ)`: every Fourier coefficient
is differentiable on `[0,∞)` (one-sided at `0`) and satisfies its mode equation
`d/dt û_k = -ν|k|² û_k + α P_k(e₃ × (-|k|² û_k)) - P_k ∑_{p+q=k} (i q·û_p) û_q + f̂_k`. -/
structure IsStrongSolution (ν α : ℝ) (f u₀ : Field) (u : ℝ → Field) : Prop where
  init : u 0 = u₀
  adm : ∀ t, 0 ≤ t → Adm 2 (u t)
  cont : ContH 2 u
  mode : ∀ k t, 0 ≤ t → HasDerivWithinAt (fun s => u s k)
    ((-(ν * ‖κ k‖ ^ 2 : ℝ) : ℂ) • u t k
      + (α : ℂ) • P k (WithLp.toLp 2
          (![0, 0, 1] ⨯₃ WithLp.ofLp ((-((‖κ k‖ ^ 2 : ℝ) : ℂ)) • u t k)))
      - P k (∑' p, (Complex.I * ⟪κ (k - p), u t p⟫_ℂ) • u t (k - p))
      + f k) (Ici 0) t

/-- Smoothness at positive times, in the form equivalent to `u ∈ C^∞((0,∞) × 𝕋³)`:
each mode is smooth in time, and every time derivative lies in every `H^r`, locally uniformly
on `(0,∞)`. -/
def SmoothAtPositiveTimes (u : ℝ → Field) : Prop :=
  (∀ k, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => u t k) (Ioi 0)) ∧
  ∀ (j : ℕ) (r a b : ℝ), 0 < a → a ≤ b → ∃ C : ℝ, ∀ t ∈ Icc a b,
    hsE r (fun k => iteratedDerivWithin j (fun s => u s k) (Ioi 0) t) ≤ ENNReal.ofReal C

/-- The conclusion of Theorem 1.1 for the datum `u₀`, the steady force `f`, the coefficient `α`
and the bound `Bd`: a unique global strong solution in `C([0,∞);H²) ∩ L²_loc H³`, uniform
`H¹, H²` bounds `‖u(t)‖₁, ‖u(t)‖₂ ≤ ν·Bd`, sliding `H³` square integrals
`∫_t^{t+h} ‖u‖₃² ≤ ν⌈νh⌉·Bd`, and for `f = 0` persistence of every `H^s`, `s ≥ 2` (continuously,
with `u ∈ L²_loc H^{s+1}`), together with smoothness at positive times. -/
def GlobalConclusion (ν α : ℝ) (f u₀ : Field) (Bd : ℝ) : Prop :=
  ∃ u : ℝ → Field, IsStrongSolution ν α f u₀ u ∧
    (∀ u', IsStrongSolution ν α f u₀ u' → ∀ t, 0 ≤ t → u' t = u t) ∧ L2locH 3 u ∧
    (∀ t, 0 ≤ t → hsE 1 (u t) ≤ ENNReal.ofReal (ν * Bd) ^ 2 ∧
      hsE 2 (u t) ≤ ENNReal.ofReal (ν * Bd) ^ 2) ∧
    (∀ t h : ℝ, 0 ≤ t → 0 ≤ h →
      ∫⁻ s in Icc t (t + h), hsE 3 (u s) ≤ ENNReal.ofReal (ν * ⌈ν * h⌉ * Bd)) ∧
    (f = 0 → (∀ s, 2 ≤ s → hsE s u₀ < ∞ →
        (∀ t, 0 ≤ t → hsE s (u t) < ∞) ∧ ContH s u ∧ L2locH (s + 1) u) ∧
      SmoothAtPositiveTimes u)

/-- The metric `h(|k|²)` of Section "Weighted energy": `1000·h(j)` is tabulated for `1 ≤ j ≤ 32`
and `h(j) = 29j/100 + 117/500` for `j ≥ 33`; `h(0) = 0` is a convention (the zero mode never
enters). -/
def hm (k : Fin 3 → ℤ) : ℝ :=
  let j := ∑ i, (k i).natAbs ^ 2
  if j = 0 then 0
  else if j ≤ 32 then
    (([1000, 1569, 2042, 2462, 2847, 3205, 3543, 3864, 4171, 4467, 4752, 5029, 5297, 5559, 5814,
      6063, 6307, 6545, 6779, 7009, 7235, 7457, 7676, 7891, 8103, 8313, 8519, 8723, 8924, 9123,
      9319, 9514] : List ℕ).getD (j - 1) 0 : ℝ) / 1000
  else 29 * (j : ℝ) / 100 + 117 / 500

/-! ## Translation between these definitions and the library's (`OVNS.*`). -/

lemma kappa_eq (k : Fin 3 → ℤ) : κ k = OVNS.modeVec k := rfl

lemma kappa_zero : κ (0 : Fin 3 → ℤ) = 0 := by
  ext i; simp

lemma norm_kappa_sq (k : Fin 3 → ℤ) : ‖κ k‖ ^ 2 = OVNS.absSq k := by
  rw [EuclideanSpace.norm_sq_eq, OVNS.absSq]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [sq_abs]

lemma norm_kappa (k : Fin 3 → ℤ) : ‖κ k‖ = OVNS.absk k := by
  rw [OVNS.absk, ← norm_kappa_sq, Real.sqrt_sq (norm_nonneg _)]

lemma inner_kappa (k : Fin 3 → ℤ) (v : EuclideanSpace ℂ (Fin 3)) : ⟪κ k, v⟫_ℂ = OVNS.dotM v k := by
  rw [PiLp.inner_apply, OVNS.dotM]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [RCLike.inner_apply]

lemma leray_eq (k : Fin 3 → ℤ) (v : EuclideanSpace ℂ (Fin 3)) (hk : k ≠ 0) :
    P k v = OVNS.leray k v := by
  rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_singleton, OVNS.leray,
    ite_eq_right hk, inner_kappa, norm_kappa_sq, kappa_eq]
  rfl

lemma P_zero (v : EuclideanSpace ℂ (Fin 3)) : P (0 : Fin 3 → ℤ) v = v := by
  rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_singleton, kappa_zero,
    smul_zero, sub_zero]

lemma cross_eq (w : EuclideanSpace ℂ (Fin 3)) :
    WithLp.toLp 2 (![0, 0, 1] ⨯₃ WithLp.ofLp w) = OVNS.cross OVNS.e3 w := by
  rw [OVNS.cross, cross_apply]
  congr 1

lemma hsE_eq (s : ℝ) (u : Field) : hsE s u = OVNS.hsE s u := by
  unfold hsE OVNS.hsE
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0
  · subst hk; simp [OVNS.sobWeight]
  · rw [ite_eq_right hk, OVNS.sobWeight, ite_eq_right hk, norm_kappa]

lemma adm_iff (s : ℝ) (u : Field) : Adm s u ↔ OVNS.Adm s u := by
  constructor
  · rintro ⟨hfin, hreal, hsol, hmean⟩
    refine ⟨OVNS.inH_iff_hsE_lt_top.2 (by rw [← hsE_eq]; exact hfin), fun k => ?_, fun k => ?_, hmean⟩
    · ext i; simpa [OVNS.conjV] using hreal k i
    · rw [← inner_kappa]; exact hsol k
  · rintro ⟨hinH, hreal, hsol, hmean⟩
    refine ⟨by rw [hsE_eq]; exact OVNS.inH_iff_hsE_lt_top.1 hinH, fun k i => ?_, fun k => ?_, hmean⟩
    · have := congrArg (fun v : EuclideanSpace ℂ (Fin 3) => v i) (hreal k)
      simpa [OVNS.conjV] using this
    · rw [inner_kappa]; exact hsol k

lemma contH_iff {s : ℝ} {u : ℝ → Field} (hIn : ∀ t, 0 ≤ t → OVNS.InH s (u t)) :
    ContH s u ↔ OVNS.ContH s u := by
  have key : ∀ t₀, 0 ≤ t₀ → ∀ᶠ t in 𝓝[Ici 0] t₀,
      OVNS.hsE s (u t - u t₀) = ENNReal.ofReal (OVNS.hnorm s (u t - u t₀) ^ 2) := by
    intro t₀ ht₀
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact OVNS.hsE_eq_ofReal ((hIn t ht).sub (hIn t₀ ht₀))
  constructor
  · intro h t₀ ht₀
    have h1 := h t₀ ht₀
    simp only [hsE_eq] at h1
    have h2 : Tendsto (fun t => Real.sqrt (OVNS.hsE s (u t - u t₀)).toReal) (𝓝[Ici 0] t₀) (𝓝 0) := by
      have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1).sqrt
      simpa [Function.comp_def] using this
    refine h2.congr' ?_
    filter_upwards [key t₀ ht₀] with t ht
    rw [ht, ENNReal.toReal_ofReal (sq_nonneg _), Real.sqrt_sq (OVNS.hnorm_nonneg _ _)]
  · intro h t₀ ht₀
    have h1 := h t₀ ht₀
    have h2 : Tendsto (fun t => ENNReal.ofReal (OVNS.hnorm s (u t - u t₀) ^ 2))
        (𝓝[Ici 0] t₀) (𝓝 0) := by
      have := ENNReal.tendsto_ofReal (h1.pow 2)
      simpa using this
    simp only [hsE_eq]
    exact h2.congr' ((key t₀ ht₀).mono fun t ht => ht.symm)

lemma l2locH_iff (s : ℝ) (u : ℝ → Field) : L2locH s u ↔ OVNS.L2locH s u := by
  simp only [L2locH, OVNS.L2locH, hsE_eq]

lemma smooth_iff (u : ℝ → Field) : SmoothAtPositiveTimes u ↔ OVNS.SmoothAtPositiveTimes u := by
  simp only [SmoothAtPositiveTimes, OVNS.SmoothAtPositiveTimes, hsE_eq]

lemma rhs_eq (ν α : ℝ) (f v : Field) (hsol : OVNS.IsSolenoidal v) (k : Fin 3 → ℤ) :
    ((-(ν * ‖κ k‖ ^ 2 : ℝ) : ℂ) • v k
      + (α : ℂ) • P k (WithLp.toLp 2
          (![0, 0, 1] ⨯₃ WithLp.ofLp ((-((‖κ k‖ ^ 2 : ℝ) : ℂ)) • v k)))
      - P k (∑' p, (Complex.I * ⟪κ (k - p), v p⟫_ℂ) • v (k - p))
      + f k)
    = ((-(ν * OVNS.absSq k : ℝ) : ℂ) • v k + (α : ℂ) • OVNS.oddSym k (v k)
        - OVNS.convec v k + f k) := by
  by_cases hk : k = 0
  · subst hk
    have hd : ∀ p : Fin 3 → ℤ, OVNS.dotM (v p) (0 - p) = 0 := by
      intro p
      have h := hsol p
      simp only [OVNS.dotM] at h ⊢
      simp [mul_neg, Finset.sum_neg_distrib, h]
    have hsum : (∑' p : Fin 3 → ℤ, (Complex.I * ⟪κ ((0 : Fin 3 → ℤ) - p), v p⟫_ℂ) •
        v ((0 : Fin 3 → ℤ) - p)) = 0 := by
      simp only [inner_kappa, hd, mul_zero, zero_smul, tsum_zero]
    rw [hsum, P_zero, P_zero, kappa_zero]
    simp [OVNS.oddSym, OVNS.convec, OVNS.leray, OVNS.absSq]
  · rw [norm_kappa_sq, leray_eq _ _ hk, leray_eq _ _ hk, cross_eq, OVNS.oddSym, OVNS.convec,
      OVNS.advect]
    simp only [inner_kappa]

lemma isStrongSolution_iff (ν α : ℝ) (f u₀ : Field) (u : ℝ → Field) :
    IsStrongSolution ν α f u₀ u ↔ OVNS.IsStrongSolution ν α f u₀ u := by
  constructor
  · rintro ⟨hinit, hadm, hcont, hmode⟩
    have hadm' : ∀ t, 0 ≤ t → OVNS.Adm 2 (u t) := fun t ht => (adm_iff _ _).1 (hadm t ht)
    refine ⟨hinit, hadm', (contH_iff fun t ht => (hadm' t ht).inH).1 hcont, fun k t ht => ?_⟩
    have := hmode k t ht
    rwa [rhs_eq ν α f (u t) (hadm' t ht).sol k] at this
  · rintro ⟨hinit, hadm, hcont, hmode⟩
    have hadm' : ∀ t, 0 ≤ t → Adm 2 (u t) := fun t ht => (adm_iff _ _).2 (hadm t ht)
    refine ⟨hinit, hadm', (contH_iff fun t ht => (hadm t ht).inH).2 hcont, fun k t ht => ?_⟩
    rw [rhs_eq ν α f (u t) (hadm t ht).sol k]
    exact hmode k t ht

lemma hsE_le_iff {s : ℝ} {v : Field} (hv : OVNS.InH s v) {M : ℝ} (hM : 0 ≤ M) :
    hsE s v ≤ ENNReal.ofReal M ^ 2 ↔ OVNS.hnorm s v ≤ M := by
  rw [hsE_eq, OVNS.hsE_eq_ofReal hv, ← ENNReal.ofReal_pow hM,
    ENNReal.ofReal_le_ofReal_iff (by positivity), sq_le_sq₀ (OVNS.hnorm_nonneg _ _) hM]

/-! ## From the library's `GlobalConclusion'` to `GlobalConclusion`. -/

lemma globalConclusion_of_lib {ν α : ℝ} {f u₀ : Field} {Bd : ℝ}
    (h : OVNS.GlobalConclusion' ν α f u₀ Bd) : GlobalConclusion ν α f u₀ Bd := by
  obtain ⟨u, hu, huniq, hL2, hB, hW, hz⟩ := h
  have hadm : ∀ t, 0 ≤ t → OVNS.Adm 2 (u t) := hu.adm
  have hBd : 0 ≤ ν * Bd := (OVNS.hnorm_nonneg _ _).trans (hB 0 le_rfl).2
  refine ⟨u, (isStrongSolution_iff _ _ _ _ _).2 hu,
    fun u' hu' => huniq u' ((isStrongSolution_iff _ _ _ _ _).1 hu'),
    (l2locH_iff _ _).2 hL2, fun t ht => ?_, fun t h ht hh => ?_, fun hf0 => ?_⟩
  · obtain ⟨h1, h2⟩ := hB t ht
    exact ⟨(hsE_le_iff ((hadm t ht).inH.mono one_le_two) hBd).2 h1,
      (hsE_le_iff (hadm t ht).inH hBd).2 h2⟩
  · simpa only [hsE_eq] using hW t h ht hh
  · obtain ⟨hpers, hsm⟩ := hz hf0
    refine ⟨fun s hs hs0 => ?_, (smooth_iff u).2 hsm⟩
    have hIn0 : OVNS.InH s u₀ := OVNS.inH_iff_hsE_lt_top.2 (by rw [← hsE_eq]; exact hs0)
    obtain ⟨hIn, hC, hL⟩ := hpers s hs hIn0
    exact ⟨fun t ht => by rw [hsE_eq]; exact OVNS.inH_iff_hsE_lt_top.1 (hIn t ht),
      (contH_iff hIn).2 hC, (l2locH_iff _ _).2 hL⟩

/-! ## The metric of Theorem 1.3. -/

lemma nsq_cast (k : Fin 3 → ℤ) : ((OVNS.nsq k : ℕ) : ℝ) = ‖κ k‖ ^ 2 := by
  rw [norm_kappa_sq, OVNS.nsq, OVNS.absSq]
  push_cast
  simp [Nat.cast_natAbs, sq_abs]

lemma Ymet_scaled_eq (ν s : ℝ) (u : ℝ → Field) (τ : ℝ) :
    OVNS.Ymet (OVNS.scaled ν s u τ) =
      ∑' k, ENNReal.ofReal (hm k * ‖((1 / (ν * s) : ℝ) : ℂ) • u (τ / ν) k‖ ^ 2) := rfl

lemma Zmet_scaled_eq (ν s : ℝ) (u : ℝ → Field) (τ : ℝ) :
    OVNS.Zmet (OVNS.scaled ν s u τ) =
      ∑' k, ENNReal.ofReal (‖κ k‖ ^ 2 * hm k * ‖((1 / (ν * s) : ℝ) : ℂ) • u (τ / ν) k‖ ^ 2) := by
  unfold OVNS.Zmet
  exact tsum_congr fun k => by rw [nsq_cast]; rfl

/-- **Theorem 1.1 (Norm-uniform global regularity).** -/
theorem global_regularity :
    ∃ R Bd : ℝ → ℝ → ℝ, (∀ μ φ, 0 ≤ R μ φ) ∧
      ∀ (ν M F α : ℝ) (u₀ f : Field), 0 < ν → 0 ≤ M → 0 ≤ F →
        Adm 2 u₀ → Adm 2 f →
        hsE 2 u₀ ≤ ENNReal.ofReal M ^ 2 → hsE 2 f ≤ ENNReal.ofReal F ^ 2 →
        R (M / ν) (F / ν ^ 2) ≤ |α| / ν →
        ∃ u : ℝ → Field,
          IsStrongSolution ν α f u₀ u ∧
          (∀ u', IsStrongSolution ν α f u₀ u' → ∀ t, 0 ≤ t → u' t = u t) ∧
          L2locH 3 u ∧
          (∀ t, 0 ≤ t → hsE 1 (u t) ≤ ENNReal.ofReal (ν * Bd (M / ν) (F / ν ^ 2)) ^ 2 ∧
            hsE 2 (u t) ≤ ENNReal.ofReal (ν * Bd (M / ν) (F / ν ^ 2)) ^ 2) ∧
          (∀ t h : ℝ, 0 ≤ t → 0 ≤ h →
            ∫⁻ s in Icc t (t + h), hsE 3 (u s) ≤
              ENNReal.ofReal (ν * ⌈ν * h⌉ * Bd (M / ν) (F / ν ^ 2))) ∧
          (f = 0 → (∀ s, 2 ≤ s → hsE s u₀ < ∞ →
              (∀ t, 0 ≤ t → hsE s (u t) < ∞) ∧ ContH s u ∧ L2locH (s + 1) u) ∧
            SmoothAtPositiveTimes u) := by
  obtain ⟨R, Bd, hR, H⟩ := OVNS.global_regularity
  refine ⟨R, Bd, hR, fun ν M F α u₀ f hν hM hF hu₀ hf hu₀M hfF hRα => ?_⟩
  have hu₀' := (adm_iff _ _).1 hu₀
  have hf' := (adm_iff _ _).1 hf
  obtain ⟨u, hu, huniq, hL2, hB, hW, hz⟩ := H ν M F α u₀ f hν hM hF hu₀' hf'
    ((hsE_le_iff hu₀'.inH hM).1 hu₀M) ((hsE_le_iff hf'.inH hF).1 hfF) hRα
  have hadm : ∀ t, 0 ≤ t → OVNS.Adm 2 (u t) := hu.adm
  refine ⟨u, (isStrongSolution_iff _ _ _ _ _).2 hu,
    fun u' hu' => huniq u' ((isStrongSolution_iff _ _ _ _ _).1 hu'),
    (l2locH_iff _ _).2 hL2, fun t ht => ?_, fun t h ht hh => ?_, fun hf0 => ?_⟩
  · obtain ⟨h1, h2⟩ := hB t ht
    have hBd : 0 ≤ ν * Bd (M / ν) (F / ν ^ 2) := (OVNS.hnorm_nonneg _ _).trans h2
    exact ⟨(hsE_le_iff ((hadm t ht).inH.mono one_le_two) hBd).2 h1,
      (hsE_le_iff (hadm t ht).inH hBd).2 h2⟩
  · simpa only [hsE_eq] using hW t h ht hh
  · obtain ⟨hpers, hsm⟩ := hz hf0
    refine ⟨fun s hs hs0 => ?_, (smooth_iff u).2 hsm⟩
    have hIn0 : OVNS.InH s u₀ := OVNS.inH_iff_hsE_lt_top.2 (by rw [← hsE_eq]; exact hs0)
    obtain ⟨hIn, hC, hL⟩ := hpers s hs hIn0
    exact ⟨fun t ht => by rw [hsE_eq]; exact OVNS.inH_iff_hsE_lt_top.1 (hIn t ht),
      (contH_iff hIn).2 hC, (l2locH_iff _ _).2 hL⟩


/-- **Theorem 1.2, fixed-force bound** (eq:fixed-force-power). For each normalized force radius
`φ ≥ 0` and each `ε > 0` there is `C = C_{φ,ε} < ∞` such that `|α|/ν ≥ C (1 + M/ν)^{9876/719+ε}`
is a sufficient choice in Theorem 1.1 for all data `‖u₀‖₂ ≤ M` and forces `‖f‖₂ ≤ F` with
`F/ν² ≤ φ`. -/
theorem quantitative_fixed_force :
    ∀ φ ε : ℝ, 0 ≤ φ → 0 < ε → ∃ C : ℝ, ∃ Bd : ℝ → ℝ → ℝ,
      ∀ (ν M F α : ℝ) (u₀ f : Field), 0 < ν → 0 ≤ M → 0 ≤ F → Adm 2 u₀ → Adm 2 f →
        hsE 2 u₀ ≤ ENNReal.ofReal M ^ 2 → hsE 2 f ≤ ENNReal.ofReal F ^ 2 → F / ν ^ 2 ≤ φ →
        C * (1 + M / ν) ^ ((9876 : ℝ) / 719 + ε) ≤ |α| / ν →
        GlobalConclusion ν α f u₀ (Bd (M / ν) (F / ν ^ 2)) := by
  intro φ ε hφ hε
  obtain ⟨C, Bd, h⟩ := OVNS.quantitative_fixed_force φ ε hφ hε
  refine ⟨C, Bd, fun ν M F α u₀ f hν hM hF hu₀ hf hu₀M hfF hφ' hα => ?_⟩
  have hu₀' := (adm_iff _ _).1 hu₀
  have hf' := (adm_iff _ _).1 hf
  exact globalConclusion_of_lib (h ν M F α u₀ f hν hM hF hu₀' hf'
    ((hsE_le_iff hu₀'.inH hM).1 hu₀M) ((hsE_le_iff hf'.inH hF).1 hfF) hφ' hα)

/-- **Theorem 1.2, joint large-force bound** (eq:joint-force). With `X = e^e + M/ν`,
`R = X + F/ν²`, `U = X^{1719/719}`, there are absolute constants `C, C₀, R₀ > 0` such that, when
`R ≥ max(R₀, X²⁴)`, `|α|/ν ≥ C U R³ exp(C₀ log R / log log R)` is a sufficient choice in
Theorem 1.1. -/
theorem quantitative_joint_force :
    ∃ C C₀ R₀ : ℝ, 0 < C ∧ 0 < C₀ ∧ 0 < R₀ ∧ ∃ Bd : ℝ → ℝ → ℝ,
      ∀ (ν M F α : ℝ) (u₀ f : Field), 0 < ν → 0 ≤ M → 0 ≤ F → Adm 2 u₀ → Adm 2 f →
        hsE 2 u₀ ≤ ENNReal.ofReal M ^ 2 → hsE 2 f ≤ ENNReal.ofReal F ^ 2 →
        let X := Real.exp (Real.exp 1) + M / ν
        let R := X + F / ν ^ 2
        let U := X ^ ((1719 : ℝ) / 719)
        max R₀ (X ^ (24 : ℝ)) ≤ R →
        C * U * R ^ 3 * Real.exp (C₀ * Real.log R / Real.log (Real.log R)) ≤ |α| / ν →
        GlobalConclusion ν α f u₀ (Bd (M / ν) (F / ν ^ 2)) := by
  obtain ⟨C, C₀, R₀, hC, hC₀, hR₀, Bd, h⟩ := OVNS.quantitative_joint_force
  refine ⟨C, C₀, R₀, hC, hC₀, hR₀, Bd, fun ν M F α u₀ f hν hM hF hu₀ hf hu₀M hfF => ?_⟩
  intro X R U hR hα
  have hu₀' := (adm_iff _ _).1 hu₀
  have hf' := (adm_iff _ _).1 hf
  exact globalConclusion_of_lib (h ν M F α u₀ f hν hM hF hu₀' hf'
    ((hsE_le_iff hu₀'.inH hM).1 hu₀M) ((hsE_le_iff hf'.inH hF).1 hfF) hR hα)


/-- **Theorem 1.3, unforced branch.** For every fixed real `α` (including `0`, either sign) and
all real mean-zero divergence-free `H²` data with `‖u₀‖₂ ≤ M`, `0 ≤ M/ν ≤ 97/40`, the conclusion
of Theorem 1.1 holds with zero force and a bound `Bd` uniform in `α`; moreover, for every strong
solution `u`, the scaled solution `w(τ) = u(τ/ν)/(ν·97/40)` satisfies `Y(w(τ)) ≤ 1` for all
`τ ≥ 0` and `∫₀^∞ Z(w(τ)) dτ ≤ 100000`. -/
theorem closed_regions_unforced :
    ∃ Bd : ℝ, 0 ≤ Bd ∧
      ∀ (ν α M : ℝ) (u₀ : Field), 0 < ν → 0 ≤ M → Adm 2 u₀ → hsE 2 u₀ ≤ ENNReal.ofReal M ^ 2 →
        M / ν ≤ 97 / 40 →
        GlobalConclusion ν α 0 u₀ Bd ∧
        ∀ u : ℝ → Field, IsStrongSolution ν α 0 u₀ u →
          (∀ τ, 0 ≤ τ → ∑' k, ENNReal.ofReal
            (hm k * ‖((1 / (ν * (97 / 40)) : ℝ) : ℂ) • u (τ / ν) k‖ ^ 2) ≤ 1) ∧
          ∫⁻ τ in Ici 0, ∑' k, ENNReal.ofReal
            (‖κ k‖ ^ 2 * hm k * ‖((1 / (ν * (97 / 40)) : ℝ) : ℂ) • u (τ / ν) k‖ ^ 2) ≤ 100000 := by
  obtain ⟨Bd, hBd, H⟩ := OVNS.closed_regions_unforced
  refine ⟨Bd, hBd, fun ν α M u₀ hν hM hu₀ hu₀M hMν => ?_⟩
  have hu₀' := (adm_iff _ _).1 hu₀
  obtain ⟨hG, hYZ⟩ := H ν α M u₀ hν hM hu₀' ((hsE_le_iff hu₀'.inH hM).1 hu₀M) hMν
  refine ⟨globalConclusion_of_lib hG, fun u hu => ?_⟩
  obtain ⟨hY, hZ⟩ := hYZ u ((isStrongSolution_iff _ _ _ _ _).1 hu)
  simp only [Ymet_scaled_eq, Zmet_scaled_eq] at hY hZ
  exact ⟨hY, hZ⟩

/-- **Theorem 1.3, forced branch.** Each row `(208013·μ_max, 208013·φ_max, J)` of the table is a
closed rectangle `M/ν ≤ μ_max`, `F/ν² ≤ φ_max` on which, for every fixed real `α`, the conclusion
of Theorem 1.1 holds with a bound `Bd` uniform in `α` and in the row; moreover, with `s = μ_max`,
the scaled solution `w(τ) = u(τ/ν)/(νs)` of every strong solution satisfies `∫_a^b Z(w(τ)) dτ ≤ J`
on every interval `0 ≤ a ≤ b ≤ a + 1`. -/
theorem closed_regions_forced : ∃ Bd : ℝ, 0 ≤ Bd ∧
    ∀ r ∈ ([(419650, 419650, 850), (425500, 382950, 294), (434000, 347200, 468),
        (442000, 309400, 320), (458500, 229250, 808), (478500, 119625, 355),
        (489500, 48950, 124)] : List (ℕ × ℕ × ℕ)),
      ∀ (ν α M F : ℝ) (u₀ f : Field), 0 < ν → 0 ≤ M → 0 ≤ F →
        Adm 2 u₀ → Adm 2 f → hsE 2 u₀ ≤ ENNReal.ofReal M ^ 2 → hsE 2 f ≤ ENNReal.ofReal F ^ 2 →
        208013 * (M / ν) ≤ r.1 → 208013 * (F / ν ^ 2) ≤ r.2.1 →
        GlobalConclusion ν α f u₀ Bd ∧
        ∀ u : ℝ → Field, IsStrongSolution ν α f u₀ u →
          ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ a + 1 →
            ∫⁻ τ in Icc a b, ∑' k, ENNReal.ofReal (‖κ k‖ ^ 2 * hm k *
              ‖((1 / (ν * ((r.1 : ℝ) / 208013)) : ℝ) : ℂ) • u (τ / ν) k‖ ^ 2) ≤ r.2.2 := by
  obtain ⟨Bd, hBd, H⟩ := OVNS.closed_regions_forced
  refine ⟨Bd, hBd, fun r hr ν α M F u₀ f hν hM hF hu₀ hf hu₀M hfF hMr hFr => ?_⟩
  have hu₀' := (adm_iff _ _).1 hu₀
  have hf' := (adm_iff _ _).1 hf
  obtain ⟨hG, hZ⟩ := H r hr ν α M F u₀ f hν hM hF hu₀' hf' ((hsE_le_iff hu₀'.inH hM).1 hu₀M)
    ((hsE_le_iff hf'.inH hF).1 hfF) hMr hFr
  refine ⟨globalConclusion_of_lib hG, fun u hu a b ha hab hb1 => ?_⟩
  have := hZ u ((isStrongSolution_iff _ _ _ _ _).1 hu) a b ha hab hb1
  simpa only [Zmet_scaled_eq] using this


end Challenge

#print axioms Challenge.global_regularity
#print axioms Challenge.quantitative_fixed_force
#print axioms Challenge.quantitative_joint_force
#print axioms Challenge.closed_regions_unforced
#print axioms Challenge.closed_regions_forced
