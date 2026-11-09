import OddViscousNS.Quant.Regimes.Algebra
import OddViscousNS.Gronwall

/-!
# Regimes layer, node 2: the scalar lemma (E6, fast `H¹` peak and dissipation)

TeX Lemma quant-scalar ("Peak and dissipation from different scalar comparisons"), in the
integrated form delivered by `H1EnergyInterface` (spec §2.1).  Proved here (pure real analysis):
* `gronwall_fixed_start`: Gronwall–Bellman from a fixed start, for a *continuous* unknown `Φ`,
  derived from the library's all-starts `gronwall_simple` through the primitive
  `y t = A + ∫_a^t (κΦ + β)`.  The energy `E` of the interface is not known to be continuous, so
  the comparison runs on `Φ = a_F²` (continuous along a `CH²` path) and `E` enters only through
  the coercivity `ℓ₁ a_F² ≤ 2E`;
* `peak_bound_core`: the nonlinear bootstrap `Φ ≤ e (2/ℓ)(E s + c M^{1−p} I + S)` from
  `E v − E s ≤ ∫ (c Φ^{2−p} + β + m Φ)` on a prefix where `Φ ≤ M`, `∫ Φ ≤ I` (the kinetic
  integral), `∫ β ≤ S`, `(2/ℓ)∫ m ≤ 1` (the timed multiplier quota).  With `M = P_F²`,
  `I = I_a ≍ μ²`, `p = 1/β` this is `A² ≲ P_F^{2(1−p)} μ²`, i.e. `A ≍ μ^β` at the fixed point;
* `dissipation_root`: `(n−λ) J ≤ B + N̄ √J ⇒ J ≤ ((N̄ + √(N̄² + 4(n−λ)B))/(2(n−λ)))²`.
Also proved (formerly locked `sorry`s): `young_cubic` (Young for `C_s a^{3−σ} b^σ`, from
`Real.young_inequality_of_nonneg`), and the two interface-shaped statements
`scalar_peak_on_piece`, `scalar_dissipation_on_piece` (E6 on a piece: Young + the `N_f b_F` step
+ the two cores; they additionally need the time-continuity of `a_F, b_F`, a solution property
stated as hypotheses here and discharged in `Continuation.lean`).
-/

open scoped ENNReal
open MeasureTheory Set intervalIntegral

noncomputable section

namespace OVNS.Quant

/-! ### Gronwall–Bellman from a fixed start -/

/-- **Fixed-start Gronwall–Bellman.** If `Φ` is continuous on `[a, b]` and
`Φ t ≤ A + ∫_a^t (κ Φ + β)` for every `t ∈ [a, b]` (one fixed start `a`, `A ≥ 0`, `κ, β ≥ 0`
integrable), then `Φ t ≤ (A + ∫_a^b β) exp(∫_a^b κ)` on `[a, b]`.  Proof: the primitive
`y t = A + ∫_a^t (κ Φ + β)` is continuous, dominates `Φ`, and satisfies the all-starts
inequality `y t ≤ y s + ∫_s^t (κ y + β)`, so `gronwall_simple` applies to `y`. -/
theorem gronwall_fixed_start {Φ κ β : ℝ → ℝ} {a b A : ℝ} (hab : a ≤ b) (hA : 0 ≤ A)
    (hΦ : ContinuousOn Φ (Icc a b)) (hκ : IntervalIntegrable κ volume a b)
    (hκ0 : ∀ u, 0 ≤ κ u) (hβ : IntervalIntegrable β volume a b) (hβ0 : ∀ u, 0 ≤ β u)
    (h : ∀ t ∈ Icc a b, Φ t ≤ A + ∫ u in a..t, (κ u * Φ u + β u)) :
    ∀ t ∈ Icc a b, Φ t ≤ (A + ∫ u in a..b, β u) * Real.exp (∫ u in a..b, κ u) := by
  have hΦ' : ContinuousOn Φ (uIcc a b) := by rwa [uIcc_of_le hab]
  set f : ℝ → ℝ := fun u => κ u * Φ u + β u with hf
  have hfi : IntervalIntegrable f volume a b := (hκ.mul_continuousOn hΦ').add hβ
  set y : ℝ → ℝ := fun t => A + ∫ u in a..t, f u with hy
  have hyc : ContinuousOn y (Icc a b) := by
    have h1 : IntegrableOn f (uIcc a b) volume := by
      rw [uIcc_of_le hab]
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).1 hfi
    have := (continuousOn_const (c := A)).add
      (intervalIntegral.continuousOn_primitive_interval h1)
    rwa [uIcc_of_le hab] at this
  have hΦy : ∀ t ∈ Icc a b, Φ t ≤ y t := h
  have hsub' : ∀ c, a ≤ c → c ≤ b → uIcc a c ⊆ uIcc a b := fun c hc hc' => by
    rw [uIcc_of_le hc, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl hc'
  have hyi : ∀ s t, a ≤ s → s ≤ t → t ≤ b → y t ≤ y s + ∫ u in s..t, (κ u * y u + β u) := by
    intro s t hs hst ht
    have hsub : uIcc s t ⊆ uIcc a b := by
      rw [uIcc_of_le hst, uIcc_of_le hab]
      exact Icc_subset_Icc hs ht
    have e : y t - y s = ∫ u in s..t, f u := by
      simp only [hy]
      rw [add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left
        (hfi.mono_set (hsub' t (hs.trans hst) ht)) (hfi.mono_set (hsub' s hs (hst.trans ht)))]
    have hyc' : ContinuousOn y (uIcc s t) := by
      rw [uIcc_of_le hst]
      exact hyc.mono (Icc_subset_Icc hs ht)
    have hint : IntervalIntegrable (fun u => κ u * y u + β u) volume s t :=
      ((hκ.mono_set hsub).mul_continuousOn hyc').add (hβ.mono_set hsub)
    have hle : ∫ u in s..t, f u ≤ ∫ u in s..t, (κ u * y u + β u) := by
      refine intervalIntegral.integral_mono_on hst (hfi.mono_set hsub) hint fun u hu => ?_
      have hu' : u ∈ Icc a b := ⟨hs.trans hu.1, hu.2.trans ht⟩
      simp only [hf]
      have := mul_le_mul_of_nonneg_left (hΦy u hu') (hκ0 u)
      linarith
    linarith
  intro t ht
  have hG := gronwall_simple hab hyc hκ hκ0 hβ hβ0 hyi a t le_rfl ht.1 ht.2
  have hya : y a = A := by simp [hy]
  rw [hya] at hG
  have hβt : ∫ u in a..t, β u ≤ ∫ u in a..b, β u :=
    intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 (Filter.Eventually.of_forall hβ0) hβ
  have hκt : ∫ u in a..t, κ u ≤ ∫ u in a..b, κ u :=
    intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 (Filter.Eventually.of_forall hκ0) hκ
  have hnn : 0 ≤ A + ∫ u in a..t, β u :=
    add_nonneg hA (intervalIntegral.integral_nonneg ht.1 fun u _ => hβ0 u)
  calc Φ t ≤ y t := hΦy t ht
    _ ≤ (A + ∫ u in a..t, β u) * Real.exp (∫ u in a..t, κ u) := hG
    _ ≤ (A + ∫ u in a..b, β u) * Real.exp (∫ u in a..b, κ u) :=
        mul_le_mul (by linarith) (Real.exp_le_exp.2 hκt) (Real.exp_pos _).le (by linarith)

/-! ### The nonlinear peak bound (Lemma quant-scalar, peak) -/

/-- **E6 peak, core.** On `[s, t]` let `Φ ≥ 0` be continuous with `Φ ≤ M`, `∫_s^t Φ ≤ I`, and
let `E` satisfy the coercivity `ℓ Φ ≤ 2E` and the integrated energy inequality
`E v − E s ≤ ∫_s^v (c Φ^{2−p} + β + m Φ)` with `β, m ≥ 0`, `∫ β ≤ S`, `(2/ℓ)∫ m ≤ 1`.  Then
`Φ ≤ e (2/ℓ)(E s + c M^{1−p} I + S)` on `[s, t]`.  (Young's inequality has already been applied:
the cubic and the `N_f b_F` term are in `c Φ^{2−p}` and `β`; the dissipation is dropped.) -/
theorem peak_bound_core {Φ E β m : ℝ → ℝ} {s t ℓ M I S c p : ℝ} (hst : s ≤ t) (hℓ : 0 < ℓ)
    (hp1 : p ≤ 1) (hc : 0 ≤ c) (hM : 0 ≤ M) (hI : 0 ≤ I) (hS : 0 ≤ S)
    (hΦ : ContinuousOn Φ (Icc s t)) (hΦ0 : ∀ u, 0 ≤ Φ u)
    (hΦM : ∀ u ∈ Icc s t, Φ u ≤ M) (hΦI : (∫ u in s..t, Φ u) ≤ I)
    (hcoer : ∀ u ∈ Icc s t, ℓ * Φ u ≤ 2 * E u)
    (hβ : IntervalIntegrable β volume s t) (hβ0 : ∀ u, 0 ≤ β u)
    (hβS : (∫ u in s..t, β u) ≤ S)
    (hm : IntervalIntegrable m volume s t) (hm0 : ∀ u, 0 ≤ m u)
    (hmass : 2 / ℓ * (∫ u in s..t, m u) ≤ 1)
    (hE : ∀ v ∈ Icc s t, E v - E s ≤ ∫ u in s..v, (c * Φ u ^ (2 - p) + β u + m u * Φ u)) :
    ∀ v ∈ Icc s t, Φ v ≤ Real.exp 1 * (2 / ℓ) * (E s + c * M ^ (1 - p) * I + S) := by
  have hΦ' : ContinuousOn Φ (uIcc s t) := by rwa [uIcc_of_le hst]
  have hΦi : IntervalIntegrable Φ volume s t := hΦ'.intervalIntegrable
  have h2ℓ : 0 < 2 / ℓ := by positivity
  have hM1 : 0 ≤ M ^ (1 - p) := Real.rpow_nonneg hM _
  have hEs : 0 ≤ E s := by
    have := mul_nonneg hℓ.le (hΦ0 s)
    linarith [hcoer s ⟨le_rfl, hst⟩]
  have hA0 : 0 ≤ 2 / ℓ * E s := mul_nonneg h2ℓ.le hEs
  -- the comparison data for `gronwall_fixed_start`
  set κ : ℝ → ℝ := fun u => 2 / ℓ * m u with hκ
  set β' : ℝ → ℝ := fun u => 2 / ℓ * (c * M ^ (1 - p) * Φ u + β u) with hβ'
  have hκi : IntervalIntegrable κ volume s t := hm.const_mul _
  have hκ0 : ∀ u, 0 ≤ κ u := fun u => mul_nonneg h2ℓ.le (hm0 u)
  have hβ'i : IntervalIntegrable β' volume s t := ((hΦi.const_mul _).add hβ).const_mul _
  have hβ'0 : ∀ u, 0 ≤ β' u := fun u =>
    mul_nonneg h2ℓ.le (add_nonneg (mul_nonneg (mul_nonneg hc hM1) (hΦ0 u)) (hβ0 u))
  -- `Φ v ≤ (2/ℓ) E s + ∫_s^v (κ Φ + β')`
  have hmain : ∀ v ∈ Icc s t, Φ v ≤ 2 / ℓ * E s + ∫ u in s..v, (κ u * Φ u + β' u) := by
    intro v hv
    have hsub : uIcc s v ⊆ uIcc s t := by
      rw [uIcc_of_le hv.1, uIcc_of_le hst]
      exact Icc_subset_Icc le_rfl hv.2
    have hpow : IntervalIntegrable (fun u => Φ u ^ (2 - p)) volume s v :=
      ((hΦ'.mono hsub).rpow_const fun u _ => Or.inr (by linarith)).intervalIntegrable
    have hi1 : IntervalIntegrable (fun u => c * Φ u ^ (2 - p) + β u + m u * Φ u) volume s v :=
      ((hpow.const_mul c).add (hβ.mono_set hsub)).add
        ((hm.mono_set hsub).mul_continuousOn (hΦ'.mono hsub))
    have hi2 : IntervalIntegrable (fun u => c * M ^ (1 - p) * Φ u + β u + m u * Φ u)
        volume s v :=
      (((hΦi.mono_set hsub).const_mul _).add (hβ.mono_set hsub)).add
        ((hm.mono_set hsub).mul_continuousOn (hΦ'.mono hsub))
    have hpt : ∀ u ∈ Icc s v, c * Φ u ^ (2 - p) + β u + m u * Φ u ≤
        c * M ^ (1 - p) * Φ u + β u + m u * Φ u := by
      intro u hu
      have hu' : u ∈ Icc s t := ⟨hu.1, hu.2.trans hv.2⟩
      have h1 : Φ u ^ (2 - p) = Φ u ^ (1 - p) * Φ u := by
        rw [show (2 - p : ℝ) = (1 - p) + 1 by ring, Real.rpow_add' (hΦ0 u) (by linarith),
          Real.rpow_one]
      have h2 : Φ u ^ (1 - p) ≤ M ^ (1 - p) :=
        Real.rpow_le_rpow (hΦ0 u) (hΦM u hu') (by linarith)
      have h3 : c * Φ u ^ (2 - p) ≤ c * M ^ (1 - p) * Φ u := by
        rw [h1]
        calc c * (Φ u ^ (1 - p) * Φ u) ≤ c * (M ^ (1 - p) * Φ u) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (hΦ0 u)) hc
          _ = c * M ^ (1 - p) * Φ u := by ring
      linarith
    have hint_le := intervalIntegral.integral_mono_on hv.1 hi1 hi2 hpt
    have hEv := hE v hv
    have e : ∫ u in s..v, (κ u * Φ u + β' u) =
        2 / ℓ * ∫ u in s..v, (c * M ^ (1 - p) * Φ u + β u + m u * Φ u) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun u _ => ?_
      simp only [hκ, hβ']
      ring
    rw [e]
    have hΦv : Φ v ≤ 2 / ℓ * E v := by
      have := hcoer v hv
      rw [div_mul_eq_mul_div, le_div_iff₀ hℓ]
      linarith
    calc Φ v ≤ 2 / ℓ * E v := hΦv
      _ ≤ 2 / ℓ * (E s + ∫ u in s..v, (c * M ^ (1 - p) * Φ u + β u + m u * Φ u)) :=
          mul_le_mul_of_nonneg_left (by linarith) h2ℓ.le
      _ = _ := by ring
  intro v hv
  have hG := gronwall_fixed_start hst hA0 hΦ hκi hκ0 hβ'i hβ'0 hmain v hv
  have hβ'int : ∫ u in s..t, β' u ≤ 2 / ℓ * (c * M ^ (1 - p) * I + S) := by
    have e : ∫ u in s..t, β' u =
        2 / ℓ * (c * M ^ (1 - p) * (∫ u in s..t, Φ u) + ∫ u in s..t, β u) := by
      simp only [hβ']
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hΦi.const_mul _) hβ,
        intervalIntegral.integral_const_mul]
    rw [e]
    apply mul_le_mul_of_nonneg_left _ h2ℓ.le
    have := mul_le_mul_of_nonneg_left hΦI (mul_nonneg hc hM1)
    linarith
  have hκint : ∫ u in s..t, κ u ≤ 1 := by
    simp only [hκ]
    rw [intervalIntegral.integral_const_mul]
    exact hmass
  have hnn : 0 ≤ 2 / ℓ * E s + 2 / ℓ * (c * M ^ (1 - p) * I + S) :=
    add_nonneg hA0 (mul_nonneg h2ℓ.le (add_nonneg (mul_nonneg (mul_nonneg hc hM1) hI) hS))
  calc Φ v ≤ (2 / ℓ * E s + ∫ u in s..t, β' u) * Real.exp (∫ u in s..t, κ u) := hG
    _ ≤ (2 / ℓ * E s + 2 / ℓ * (c * M ^ (1 - p) * I + S)) * Real.exp 1 :=
        mul_le_mul (by linarith) (Real.exp_le_exp.2 hκint) (Real.exp_pos _).le hnn
    _ = Real.exp 1 * (2 / ℓ) * (E s + c * M ^ (1 - p) * I + S) := by ring

/-! ### The dissipation root (Lemma quant-scalar, dissipation) -/

/-- **E6 dissipation, core** (TeX `scalar_dissipation`): the positive root of
`n J ≤ B + N̄ √J`, i.e. `J ≤ ((N̄ + √(N̄² + 4nB))/(2n))²`. -/
theorem dissipation_root {n B N J : ℝ} (hn : 0 < n) (hB : 0 ≤ B) (hN : 0 ≤ N) (hJ : 0 ≤ J)
    (h : n * J ≤ B + N * Real.sqrt J) :
    J ≤ ((N + Real.sqrt (N ^ 2 + 4 * n * B)) / (2 * n)) ^ 2 := by
  set x := Real.sqrt J with hx
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hJx : J = x ^ 2 := (Real.sq_sqrt hJ).symm
  set D := Real.sqrt (N ^ 2 + 4 * n * B) with hD
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hD2 : D ^ 2 = N ^ 2 + 4 * n * B := Real.sq_sqrt (by positivity)
  have hND : N ≤ D := (Real.le_sqrt hN (by positivity)).2 (by nlinarith)
  have key : x ≤ (N + D) / (2 * n) := by
    by_contra hlt
    push Not at hlt
    rw [div_lt_iff₀ (by positivity)] at hlt
    have hpos : 0 < (x * (2 * n) - N - D) * (x * (2 * n) - N + D) :=
      mul_pos (by linarith) (by linarith)
    have h' : n * (n * J) ≤ n * (B + N * x) := mul_le_mul_of_nonneg_left h hn.le
    rw [hJx] at h'
    nlinarith
  calc J = x ^ 2 := hJx
    _ ≤ ((N + D) / (2 * n)) ^ 2 := pow_le_pow_left₀ hx0 key 2

/-! ### Young's inequality for the cubic (locked) -/

/-- **Young for the cubic** (TeX proof of Lemma quant-scalar): for `0 < σ < 1`, `λ > 0`,
`C_s ≥ 0` there is `c_y ≥ 0` with `C_s a^{3−σ} b^σ ≤ λ b² + c_y a^{4−2p}`, `p = 1/β`,
`4 − 2p = 2(3−σ)/(2−σ)` (exponents `2/σ`, `2/(2−σ)`; `c_y = (1−σ/2)[σ/(2λ)]^{σ/(2−σ)} C_s^{2−2p}`).
Grade S: `Real.young_inequality_of_nonneg`. -/
theorem young_cubic {σ Cs lam : ℝ} (hσ : 0 < σ ∧ σ < 1) (hCs : 0 ≤ Cs) (hlam : 0 < lam) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      Cs * a ^ (3 - σ) * b ^ σ ≤ lam * b ^ 2 + c * a ^ (4 - 2 / betaOf σ) := by
  obtain ⟨hσ0, hσ1⟩ := hσ
  set k : ℝ := Real.sqrt (2 * lam / σ) with hk
  have hk0 : 0 < k := Real.sqrt_pos.2 (by positivity)
  have hk2 : k ^ 2 = 2 * lam / σ := Real.sq_sqrt (by positivity)
  have hkσ : 0 < k ^ σ := Real.rpow_pos_of_pos hk0 _
  set q : ℝ := 2 / (2 - σ) with hq
  have hpq : (2 / σ).HolderConjugate q := by
    rw [Real.holderConjugate_iff]
    refine ⟨by rw [lt_div_iff₀ hσ0]; linarith, ?_⟩
    rw [hq, inv_div, inv_div]
    field_simp
    ring
  refine ⟨(2 - σ) / 2 * (Cs / k ^ σ) ^ q, ?_, ?_⟩
  · have : 0 ≤ (Cs / k ^ σ) ^ q := Real.rpow_nonneg (div_nonneg hCs hkσ.le) _
    have : 0 ≤ (2 - σ) / 2 := by linarith
    positivity
  intro a b ha hb
  have hx := Real.young_inequality_of_nonneg (Real.rpow_nonneg (mul_nonneg hk0.le hb) σ)
    (mul_nonneg (div_nonneg hCs hkσ.le) (Real.rpow_nonneg ha (3 - σ))) hpq
  have e1 : (k * b) ^ σ * (Cs / k ^ σ * a ^ (3 - σ)) = Cs * a ^ (3 - σ) * b ^ σ := by
    rw [Real.mul_rpow hk0.le hb]
    field_simp
  have e2 : ((k * b) ^ σ) ^ (2 / σ) / (2 / σ) = lam * b ^ 2 := by
    rw [← Real.rpow_mul (mul_nonneg hk0.le hb), show σ * (2 / σ) = (2 : ℝ) by field_simp,
      Real.rpow_two, mul_pow, hk2]
    field_simp
  have e3 : (Cs / k ^ σ * a ^ (3 - σ)) ^ q / q =
      (2 - σ) / 2 * (Cs / k ^ σ) ^ q * a ^ (4 - 2 / betaOf σ) := by
    rw [Real.mul_rpow (div_nonneg hCs hkσ.le) (Real.rpow_nonneg ha _), ← Real.rpow_mul ha]
    have : (3 - σ) * q = 4 - 2 / betaOf σ := by
      simp only [hq, betaOf]
      have : (1 - σ) ≠ 0 := by linarith
      have : (2 - σ) ≠ 0 := by linarith
      field_simp
      ring
    rw [this, hq]
    field_simp
  rw [e1, e2, e3] at hx
  exact hx

/-! ### Private helpers for E6 on a piece -/

private lemma integral_le_of_le' {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) (hg0 : ∀ u ∈ Icc a b, 0 ≤ g u)
    (hfg : ∀ u ∈ Icc a b, f u ≤ g u) : ∫ u in a..b, f u ≤ ∫ u in a..b, g u := by
  by_cases hf : IntervalIntegrable f volume a b
  · exact intervalIntegral.integral_mono_on hab hf hg hfg
  · rw [intervalIntegral.integral_undef hf]
    exact intervalIntegral.integral_nonneg hab hg0

lemma one_lt_betaOf {σ : ℝ} (hσ : 0 < σ ∧ σ < 1) : 1 < betaOf σ := by
  unfold betaOf
  rw [lt_div_iff₀ (by linarith)]
  linarith

lemma energy_step {a b E Nf ff m : ℝ → ℝ} {s t u₁ u₂ σ Cs cy lam ε : ℝ}
    (hσ : 0 < σ ∧ σ < 1) (hε : 0 < ε) (hlam : 0 ≤ lam) (hcy0 : 0 ≤ cy)
    (h1 : s ≤ u₁) (h12 : u₁ ≤ u₂) (h2 : u₂ ≤ t)
    (ha : ContinuousOn a (Icc s t)) (hb : ContinuousOn b (Icc s t)) (ha0 : ∀ u, 0 ≤ a u)
    (hb0 : ∀ u, 0 ≤ b u)
    (hcy : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      Cs * a ^ (3 - σ) * b ^ σ ≤ lam * b ^ 2 + cy * a ^ (4 - 2 / betaOf σ))
    (hfm : ∀ u ∈ Icc s t, 0 ≤ ff u ∧ 0 ≤ m u)
    (hNi : IntervalIntegrable (fun u => Nf u ^ 2) volume s t)
    (hfi : IntervalIntegrable ff volume s t) (hmi : IntervalIntegrable m volume s t)
    (hint : E u₂ - E u₁ + 3 / 4 * (∫ u in u₁..u₂, b u ^ 2) ≤
      ∫ u in u₁..u₂, (Cs * a u ^ (3 - σ) * b u ^ σ + Nf u * b u + ff u + m u * a u ^ 2)) :
    E u₂ - E u₁ + 3 / 4 * (∫ u in u₁..u₂, b u ^ 2) ≤ (lam + ε) * (∫ u in u₁..u₂, b u ^ 2) +
      ∫ u in u₁..u₂, (cy * (a u ^ 2) ^ (2 - 1 / betaOf σ) + (Nf u ^ 2 / (4 * ε) + |ff u|) +
        |m u| * a u ^ 2) := by
  have hβ := one_lt_betaOf hσ
  have hp1 : 1 / betaOf σ ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hsub : Icc u₁ u₂ ⊆ Icc s t := Icc_subset_Icc h1 h2
  have hsub' : uIcc u₁ u₂ ⊆ uIcc s t := by
    rw [uIcc_of_le h12, uIcc_of_le ((h1.trans h12).trans h2)]
    exact hsub
  have ha' : ContinuousOn a (uIcc u₁ u₂) := by rw [uIcc_of_le h12]; exact ha.mono hsub
  have hb' : ContinuousOn b (uIcc u₁ u₂) := by rw [uIcc_of_le h12]; exact hb.mono hsub
  have hKi : IntervalIntegrable (fun u => cy * (a u ^ 2) ^ (2 - 1 / betaOf σ) +
      (Nf u ^ 2 / (4 * ε) + |ff u|) + |m u| * a u ^ 2) volume u₁ u₂ :=
    ((((ha'.pow 2).rpow_const fun _ _ => Or.inr (by linarith)).intervalIntegrable.const_mul
      cy).add (((hNi.mono_set hsub').div_const _).add (hfi.mono_set hsub').abs)).add
      ((hmi.mono_set hsub').abs.mul_continuousOn (ha'.pow 2))
  have hbi : IntervalIntegrable (fun u => b u ^ 2) volume u₁ u₂ := (hb'.pow 2).intervalIntegrable
  have hle := integral_le_of_le' (f := fun u => Cs * a u ^ (3 - σ) * b u ^ σ + Nf u * b u +
      ff u + m u * a u ^ 2) h12 ((hbi.const_mul (lam + ε)).add hKi) (fun u hu => by
        have := hfm u (hsub hu)
        have : 0 ≤ (a u ^ 2) ^ (2 - 1 / betaOf σ) := Real.rpow_nonneg (by positivity) _
        have : 0 ≤ Nf u ^ 2 / (4 * ε) := by positivity
        have := abs_nonneg (ff u)
        have := abs_nonneg (m u)
        positivity) (fun u hu => by
        obtain ⟨hf0, hm0⟩ := hfm u (hsub hu)
        have e : (a u ^ 2) ^ (2 - 1 / betaOf σ) = a u ^ (4 - 2 / betaOf σ) := by
          rw [← Real.rpow_two, ← Real.rpow_mul (ha0 u)]
          congr 1
          ring
        have hy := hcy (a u) (b u) (ha0 u) (hb0 u)
        have hN : Nf u * b u ≤ ε * b u ^ 2 + Nf u ^ 2 / (4 * ε) := by
          have : 0 ≤ (2 * ε * b u - Nf u) ^ 2 / (4 * ε) := by positivity
          have e2 : (2 * ε * b u - Nf u) ^ 2 / (4 * ε) =
              ε * b u ^ 2 + Nf u ^ 2 / (4 * ε) - Nf u * b u := by
            field_simp
            ring
          linarith
        simp only [e, abs_of_nonneg hf0, abs_of_nonneg hm0]
        linarith)
  rw [intervalIntegral.integral_add (hbi.const_mul _) hKi,
    intervalIntegral.integral_const_mul] at hle
  linarith



lemma sqrt_bound {n B N J : ℝ} (hB : 0 ≤ B) (hJ : 0 ≤ J)
    (h : ∀ ε > 0, n * J ≤ B + ε * J + N ^ 2 / (4 * ε)) : n * J ≤ B + |N| * Real.sqrt J := by
  rcases hJ.eq_or_lt with hJ0 | hJ0
  · rw [← hJ0]
    simpa using hB
  have hx : 0 < Real.sqrt J := Real.sqrt_pos.2 hJ0
  have hJx : J = Real.sqrt J ^ 2 := (Real.sq_sqrt hJ).symm
  rcases (abs_nonneg N).eq_or_lt with hN | hN
  · rw [← hN, zero_mul, add_zero]
    by_contra hc
    push Not at hc
    have h' := h ((n * J - B) / (2 * J)) (div_pos (by linarith) (by positivity))
    have hN2 : N ^ 2 = 0 := by rw [← sq_abs, ← hN]; ring
    have e : (n * J - B) / (2 * J) * J = (n * J - B) / 2 := by field_simp
    rw [e, hN2, zero_div] at h'
    linarith
  · have h' := h (|N| / (2 * Real.sqrt J)) (by positivity)
    have hsq : Real.sqrt J * Real.sqrt J = J := Real.mul_self_sqrt hJ
    have e1 : |N| / (2 * Real.sqrt J) * J = |N| * Real.sqrt J / 2 := by
      field_simp
      linear_combination (-1 : ℝ) * hsq
    have e2 : N ^ 2 / (4 * (|N| / (2 * Real.sqrt J))) = |N| * Real.sqrt J / 2 := by
      rw [← sq_abs]
      field_simp
      ring
    rw [e1, e2] at h'
    linarith

/-! ### E6 on a piece (locked statements against `H1EnergyInterface`) -/

/-- The E6 peak `A²` delivered on a piece: `e (2/ℓ₁)(u₁ M_f²/2 + c_y (P_F²)^{1−p} I_a +
N̄²/(4(n−λ)) + π²)` with `n = 3/4`, `p = 1/β` (`peak_bound_core` after Young and
`N_f b_F ≤ (n−λ) b_F² + N_f²/(4(n−λ))`).  At fixed `φ` with `I_a ≍ μ²`, `M_f ≍ μ`, `N̄, π ≍ μ`
it is `≍ P_F^{2(1−p)} μ²`, so the fixed point `P_F² ≍ A²` is `P_F ≍ μ^{1/p} = μ^β`. -/
def peakSq (σ cy lam Mf PF Ia Nbar piTol : ℝ) : ℝ :=
  Real.exp 1 * (2 / ell1) * (u1 * Mf ^ 2 / 2 + cy * (PF ^ 2) ^ (1 - 1 / betaOf σ) * Ia +
    Nbar ^ 2 / (4 * (3 / 4 - lam)) + piTol ^ 2)

/-- The E6 dissipation budget `J_D` delivered on a piece (`dissipation_root` with
`B = u₁ M_f²/2 + c_y (P_F²)^{1−p} I_a + π² + (ℓ₁/2) A²`, the last term bounding `∫ m a_F²`
through the multiplier quota and the peak).  The leading term is `|N̄|`, not `N̄`: the interface
only constrains `N̄²`, so for `N̄ < 0` the root with `N̄` would not follow. -/
def dissipSq (σ cy lam Mf PF Ia Nbar piTol : ℝ) : ℝ :=
  ((|Nbar| + Real.sqrt (Nbar ^ 2 + 4 * (3 / 4 - lam) *
      (u1 * Mf ^ 2 / 2 + cy * (PF ^ 2) ^ (1 - 1 / betaOf σ) * Ia + piTol ^ 2 +
        ell1 / 2 * peakSq σ cy lam Mf PF Ia Nbar piTol))) / (2 * (3 / 4 - lam))) ^ 2

/-- **E6 on a piece, peak** (locked).  From the `H1EnergyInterface` outputs on a piece `[s, t]`
(leading condition paid), the kinetic integral `∫_s^t a_F² ≤ I_a` (E4), the incoming trace
`a_F(s) ≤ M_f`, Young's constant `c_y` at `λ ∈ (0, 3/4)` and the time-continuity of `a_F, b_F`:
`a_F² ≤ peakSq` on `[s, t]`.  Proof: Young + `N_f b_F ≤ (3/4−λ) b_F² + N_f²/(4(3/4−λ))` turn the
interface inequality into the hypothesis of `peak_bound_core` with `Φ = a_F²`, `M = P_F²`,
`p = 1/β`, `β = N_f²/(4(3/4−λ)) + f_f`. -/
theorem scalar_peak_on_piece {σ Cs μ φ Tp Nbar piTol K₁ : ℝ} {q₁ : Caps → ℝ} {N : ℝ → ℝ}
    (hσ : 0 < σ ∧ σ < 1) (hE1 : H1EnergyInterface σ Cs μ φ Tp Nbar piTol K₁ q₁ N)
    {r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {caps : Caps} {s t : ℝ}
    (hsol : ActualSol μ φ r g y Ty) (hpiece : PieceHyp Tp q₁ r g y Ty caps s t)
    (hlead : K₁ * Real.sqrt caps.PF * caps.yF ^ (3 / 2 : ℝ) * N |r| ≤ 1)
    {Ia Mf cy lam : ℝ} (hlam : 0 < lam ∧ lam < 3 / 4) (hcy0 : 0 ≤ cy)
    (hcy : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      Cs * a ^ (3 - σ) * b ^ σ ≤ lam * b ^ 2 + cy * a ^ (4 - 2 / betaOf σ))
    (hkin : (∫ u in s..t, fastNorm 1 r g y u ^ 2) ≤ Ia) (hin : fastNorm 1 r g y s ≤ Mf)
    (hc1 : ContinuousOn (fastNorm 1 r g y) (Icc s t))
    (hc2 : ContinuousOn (fastNorm 2 r g y) (Icc s t)) :
    ∀ v ∈ Icc s t, fastNorm 1 r g y v ^ 2 ≤ peakSq σ cy lam Mf caps.PF Ia Nbar piTol := by
  obtain ⟨E, Nf, ff, m, hco, hint, hfm, hNi, hfi, hmi, hNb, hfb, hmb⟩ :=
    hE1 r g y Ty caps s t hsol hpiece hlead
  have hst := hpiece.hst
  have hn : 0 < 3 / 4 - lam := by linarith
  have ha0 : ∀ u, 0 ≤ fastNorm 1 r g y u := fun u => hnorm_nonneg _ _
  have hb0 : ∀ u, 0 ≤ fastNorm 2 r g y u := fun u => hnorm_nonneg _ _
  have hℓ : 0 < ell1 := by norm_num [ell1]
  have hβ := one_lt_betaOf hσ
  have hp1 : 1 / betaOf σ ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hEq : ∀ u ∈ uIcc s t, |ff u| = ff u ∧ |m u| = m u := fun u hu => by
    rw [uIcc_of_le hst] at hu
    exact ⟨abs_of_nonneg (hfm u hu).1, abs_of_nonneg (hfm u hu).2⟩
  have hfint : (∫ u in s..t, |ff u|) = ∫ u in s..t, ff u :=
    intervalIntegral.integral_congr fun u hu => (hEq u hu).1
  have hmint : (∫ u in s..t, |m u|) = ∫ u in s..t, m u :=
    intervalIntegral.integral_congr fun u hu => (hEq u hu).2
  have hIa : 0 ≤ Ia := (intervalIntegral.integral_nonneg hst fun u _ => sq_nonneg _).trans hkin
  have hcore := peak_bound_core (Φ := fun u => fastNorm 1 r g y u ^ 2) (E := E)
    (β := fun u => Nf u ^ 2 / (4 * (3 / 4 - lam)) + |ff u|) (m := fun u => |m u|)
    (c := cy) (p := 1 / betaOf σ) (M := caps.PF ^ 2) (I := Ia)
    (S := Nbar ^ 2 / (4 * (3 / 4 - lam)) + piTol ^ 2) hst hℓ hp1 hcy0 (sq_nonneg _) hIa
    (by positivity) (hc1.pow 2) (fun u => sq_nonneg _)
    (fun u hu => pow_le_pow_left₀ (ha0 u) (hpiece.onPrefix.1 u hu).1 2) hkin
    (fun u hu => (hco u hu).1) ((hNi.div_const _).add hfi.abs)
    (fun u => by have := abs_nonneg (ff u); positivity)
    (by
      rw [intervalIntegral.integral_add (hNi.div_const _) hfi.abs, intervalIntegral.integral_div,
        hfint]
      have := div_le_div_of_nonneg_right hNb (by positivity : (0 : ℝ) ≤ 4 * (3 / 4 - lam))
      linarith)
    hmi.abs (fun u => abs_nonneg _) (by rw [hmint]; exact hmb)
    (fun v hv => by
      have h := energy_step (ε := 3 / 4 - lam) hσ hn hlam.1.le hcy0 le_rfl hv.1 hv.2 hc1 hc2
        ha0 hb0 hcy hfm hNi hfi hmi (hint s v le_rfl hv.1 hv.2)
      have e : lam + (3 / 4 - lam) = 3 / 4 := by ring
      rw [e] at h
      linarith)
  intro v hv
  have h := hcore v hv
  have hEs : E s ≤ u1 * Mf ^ 2 / 2 := by
    have h1 := (hco s ⟨le_rfl, hst⟩).2
    have h2 : fastNorm 1 r g y s ^ 2 ≤ Mf ^ 2 := pow_le_pow_left₀ (ha0 s) hin 2
    have : 0 < u1 := by norm_num [u1]
    nlinarith
  unfold peakSq
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  linarith

/-- **E6 on a piece, dissipation** (locked).  Under the hypotheses of `scalar_peak_on_piece`,
`∫_s^t b_F² ≤ dissipSq`.  Proof: the interface inequality on `[s, t]` with Young at `λ`,
Cauchy–Schwarz `∫ N_f b_F ≤ N̄ √J`, `E t ≥ 0`, `E s ≤ u₁ M_f²/2`, `∫ m a_F² ≤ (ℓ₁/2) A²`, then
`dissipation_root` with `n = 3/4 − λ`. -/
theorem scalar_dissipation_on_piece {σ Cs μ φ Tp Nbar piTol K₁ : ℝ} {q₁ : Caps → ℝ}
    {N : ℝ → ℝ} (hσ : 0 < σ ∧ σ < 1) (hE1 : H1EnergyInterface σ Cs μ φ Tp Nbar piTol K₁ q₁ N)
    {r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {caps : Caps} {s t : ℝ}
    (hsol : ActualSol μ φ r g y Ty) (hpiece : PieceHyp Tp q₁ r g y Ty caps s t)
    (hlead : K₁ * Real.sqrt caps.PF * caps.yF ^ (3 / 2 : ℝ) * N |r| ≤ 1)
    {Ia Mf cy lam : ℝ} (hlam : 0 < lam ∧ lam < 3 / 4) (hcy0 : 0 ≤ cy)
    (hcy : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      Cs * a ^ (3 - σ) * b ^ σ ≤ lam * b ^ 2 + cy * a ^ (4 - 2 / betaOf σ))
    (hkin : (∫ u in s..t, fastNorm 1 r g y u ^ 2) ≤ Ia) (hin : fastNorm 1 r g y s ≤ Mf)
    (hc1 : ContinuousOn (fastNorm 1 r g y) (Icc s t))
    (hc2 : ContinuousOn (fastNorm 2 r g y) (Icc s t)) :
    (∫ u in s..t, fastNorm 2 r g y u ^ 2) ≤ dissipSq σ cy lam Mf caps.PF Ia Nbar piTol := by
  unfold dissipSq
  have hpeak := scalar_peak_on_piece hσ hE1 hsol hpiece hlead hlam hcy0 hcy hkin hin hc1 hc2
  obtain ⟨E, Nf, ff, m, hco, hint, hfm, hNi, hfi, hmi, hNb, hfb, hmb⟩ :=
    hE1 r g y Ty caps s t hsol hpiece hlead
  have hst := hpiece.hst
  have hn : 0 < 3 / 4 - lam := by linarith
  have ha0 : ∀ u, 0 ≤ fastNorm 1 r g y u := fun u => hnorm_nonneg _ _
  have hb0 : ∀ u, 0 ≤ fastNorm 2 r g y u := fun u => hnorm_nonneg _ _
  have hℓ : 0 < ell1 := by norm_num [ell1]
  have hu1 : 0 < u1 := by norm_num [u1]
  have hβ := one_lt_betaOf hσ
  have hp1 : 1 / betaOf σ ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  set P := peakSq σ cy lam Mf caps.PF Ia Nbar piTol with hP
  set X := (caps.PF ^ 2) ^ (1 - 1 / betaOf σ) with hX
  have hX0 : 0 ≤ X := Real.rpow_nonneg (sq_nonneg _) _
  have hP0 : 0 ≤ P := (sq_nonneg _).trans (hpeak s ⟨le_rfl, hst⟩)
  have hIa : 0 ≤ Ia := (intervalIntegral.integral_nonneg hst fun u _ => sq_nonneg _).trans hkin
  have hEq : ∀ u ∈ uIcc s t, |ff u| = ff u ∧ |m u| = m u := fun u hu => by
    rw [uIcc_of_le hst] at hu
    exact ⟨abs_of_nonneg (hfm u hu).1, abs_of_nonneg (hfm u hu).2⟩
  have hfint : (∫ u in s..t, |ff u|) = ∫ u in s..t, ff u :=
    intervalIntegral.integral_congr fun u hu => (hEq u hu).1
  have hmint : (∫ u in s..t, |m u|) = ∫ u in s..t, m u :=
    intervalIntegral.integral_congr fun u hu => (hEq u hu).2
  have hEt : 0 ≤ E t := by
    have := (hco t ⟨hst, le_rfl⟩).1
    have := mul_nonneg hℓ.le (sq_nonneg (fastNorm 1 r g y t))
    linarith
  have hEs : E s ≤ u1 * Mf ^ 2 / 2 := by
    have h1 := (hco s ⟨le_rfl, hst⟩).2
    have h2 : fastNorm 1 r g y s ^ 2 ≤ Mf ^ 2 := pow_le_pow_left₀ (ha0 s) hin 2
    nlinarith
  have hm2 : (∫ u in s..t, m u) ≤ ell1 / 2 := by
    rw [div_mul_eq_mul_div, div_le_one hℓ] at hmb
    linarith
  have hc1' : ContinuousOn (fastNorm 1 r g y) (uIcc s t) := by
    rw [uIcc_of_le hst]
    exact hc1
  have hai : IntervalIntegrable (fun u => fastNorm 1 r g y u ^ 2) volume s t :=
    (hc1'.pow 2).intervalIntegrable
  set B := u1 * Mf ^ 2 / 2 + cy * X * Ia + piTol ^ 2 + ell1 / 2 * P with hB
  have hB0 : 0 ≤ B := by positivity
  have key : ∀ ε > 0, (3 / 4 - lam) * (∫ u in s..t, fastNorm 2 r g y u ^ 2) ≤
      B + ε * (∫ u in s..t, fastNorm 2 r g y u ^ 2) + Nbar ^ 2 / (4 * ε) := by
    intro ε hε
    have h := energy_step (ε := ε) hσ hε hlam.1.le hcy0 le_rfl hst le_rfl hc1 hc2 ha0 hb0 hcy
      hfm hNi hfi hmi (hint s t le_rfl hst le_rfl)
    have hKi : IntervalIntegrable (fun u => cy * (fastNorm 1 r g y u ^ 2) ^ (2 - 1 / betaOf σ) +
        (Nf u ^ 2 / (4 * ε) + |ff u|) + |m u| * fastNorm 1 r g y u ^ 2) volume s t :=
      ((((hc1'.pow 2).rpow_const fun _ _ => Or.inr (by linarith)).intervalIntegrable.const_mul
        cy).add ((hNi.div_const _).add hfi.abs)).add (hmi.abs.mul_continuousOn (hc1'.pow 2))
    have hK'i : IntervalIntegrable (fun u => cy * X * fastNorm 1 r g y u ^ 2 +
        Nf u ^ 2 / (4 * ε) + |ff u| + P * |m u|) volume s t :=
      (((hai.const_mul _).add (hNi.div_const _)).add hfi.abs).add (hmi.abs.const_mul _)
    have hKK := intervalIntegral.integral_mono_on hst hKi hK'i fun u hu => by
      have hΦ := hpeak u hu
      have hpow : (fastNorm 1 r g y u ^ 2) ^ (2 - 1 / betaOf σ) ≤
          X * fastNorm 1 r g y u ^ 2 := by
        rw [show (2 - 1 / betaOf σ : ℝ) = (1 - 1 / betaOf σ) + 1 by ring,
          Real.rpow_add' (sq_nonneg _) (by linarith), Real.rpow_one]
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (sq_nonneg _)
          (pow_le_pow_left₀ (ha0 u) (hpiece.onPrefix.1 u hu).1 2) (by linarith)) (sq_nonneg _)
      have h1 := mul_le_mul_of_nonneg_left hpow hcy0
      have h2 := mul_le_mul_of_nonneg_left hΦ (abs_nonneg (m u))
      linarith
    rw [intervalIntegral.integral_add (((hai.const_mul _).add (hNi.div_const _)).add hfi.abs)
      (hmi.abs.const_mul _), intervalIntegral.integral_add ((hai.const_mul _).add
      (hNi.div_const _)) hfi.abs, intervalIntegral.integral_add (hai.const_mul _)
      (hNi.div_const _), intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
      intervalIntegral.integral_const_mul, hfint, hmint] at hKK
    have h3 := mul_le_mul_of_nonneg_left hkin (mul_nonneg hcy0 hX0)
    have h4 := div_le_div_of_nonneg_right hNb (by positivity : (0 : ℝ) ≤ 4 * ε)
    have h5 := mul_le_mul_of_nonneg_left hm2 hP0
    linarith
  have hJ0 : 0 ≤ ∫ u in s..t, fastNorm 2 r g y u ^ 2 :=
    intervalIntegral.integral_nonneg hst fun u _ => sq_nonneg _
  have hroot := dissipation_root hn hB0 (abs_nonneg Nbar) hJ0 (sqrt_bound hB0 hJ0 key)
  rwa [sq_abs] at hroot

end OVNS.Quant

end
