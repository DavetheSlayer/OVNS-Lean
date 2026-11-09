import OddViscousNS.Quant.Energy.Slow.Lattice2D
import OddViscousNS.Trilinear
import OddViscousNS.Young

/-!
# T2–T3: Fourier-side tools of the slow-cap route E7-F (Theorem 1.2, fixed force)

Source: `OddViscousNS_data/reports/t12_slow_fourier_route.md` §2.1; manuscript `forced.tex`
Lemma fg:lem:lady (Ladyzhenskaya on `𝕋²`) and the commutator identities of §2.1 (T3).  Everything
lives on the slow modes `k₃ = 0` of `Mode = ℤ³` (`PiS`), the 2D–3C field `h = PiH s`, `ζ = PiV s`.

## T2: bilinear Fourier Ladyzhenskaya (`lady2d`, `lady2d_field`)
For nonnegative `a, b` supported on the nonzero slow modes with `|k|a, |k|b ∈ ℓ²` (`SlowSeq`),
  `‖a ∗ b‖²_{ℓ²} ≤ 25 ‖a‖ ‖|k|a‖ ‖b‖ ‖|k|b‖`.
Proof (no `ℓ^p` Young): weighted Cauchy–Schwarz with `w_i = λ_i + |·|²`,
`(a∗b)(k)² ≤ (∑_p r₁(p) r₂(k−p)) ((w₁a²)∗(w₂b²))(k)`, `∑_p r₁ r₂ ≤ √(S(λ₁)S(λ₂))` (T1,
`Lattice2D.lean`), Tonelli, and `λ_i = ‖|k|a‖²/‖a‖²`.  The report's constant is `4·127/3 ≈ 169`;
with `S(λ) ≤ (25/4)/λ` we get `c_L² = 25`, i.e. `c_L = 5` (numerically the sharp ratio is
`≤ 2.84`, report §2.1).

## T3: the slow commutator bounds (`pair_slow_vertical_lady`, `pair_slow_horizontal_h2`,
`pair_slow_vertical_h2`)
`⟨Z, Λ^{2σ} B(s,s)⟩ = pair σ Z (Bsym s s)` is the absolutely convergent triad sum
`Re ∑_{p,q} |r|^{2σ} T(p,q)`, `r = −(p+q)` (`pair_eq_tsum`, `inner_Bsym`).  For `Z = PiH s` or
`PiV s` the triad is `triC s Z ω` with the weight `ω(q,r) = |r|^{2σ}` on the pair (`Z`-leg,
test leg).  Subtracting the transport term with the symmetric weight `|q|^σ |r|^σ`, which sums to
zero over each cyclic orbit (`triC_cyc`, divergence of `s`), leaves the commutator symbol
`|r|^σ(|r|^σ − |q|^σ)`, bounded by `|p||r|` (`σ = 1`) and `(|p|² + 2|p||q|)|r|²` (`σ = 2`).  Each
remaining triple sum is `ℓ²` of one factor times `ℓ²` of a convolution (`triple_conv_bound`),
and the convolution is bounded by T2.  With `a = ‖·‖₁`, `b = ‖·‖₂`, `c = ‖·‖₃` of `h`, `ζ`:
* `|⟨h·∇ζ, Δζ⟩| = |pair 1 ζ (Bsym s s)| ≤ 5 a_h a_ζ b_ζ`  (`s ∈ H²`);
* `|⟨P(h·∇h), Δ²h⟩| = |pair 2 h (Bsym s s)| ≤ 15 a_h b_h c_h`  (`s ∈ H³`);
* `|⟨h·∇ζ, Δ²ζ⟩| = |pair 2 ζ (Bsym s s)| ≤ 10 a_h b_ζ c_ζ + 5 b_h b_ζ √(a_ζ c_ζ)`  (`s ∈ H³`),
matching the report's `c_L a_h a_ζ b_ζ`, `3c_L a_h b_h c_h`, `c_L(2a_h b_ζ c_ζ + b_h a_ζ^{1/2} b_ζ
c_ζ^{1/2})` with `c_L = 5`.  The statements mirror `pair_slow_vertical_le` (`Trilinear.lean`): the
slow field is `s` with `PiS s = s`, and the pairings are the ones the energy laws of
`RefSlow.lean` consume.
-/

noncomputable section
namespace OVNS

/-! ### T2: bilinear Fourier Ladyzhenskaya on the slow modes -/

/-- A nonnegative sequence on the lattice, supported on the nonzero slow modes, with
`|k| a ∈ ℓ²`: the coefficient profile `k ↦ |k|^m ‖u k‖` of a mean-zero slow `H^{m+1}` field. -/
structure SlowSeq (a : Mode → ℝ) : Prop where
  /-- `a ≥ 0`. -/
  nonneg : ∀ k, 0 ≤ a k
  /-- `a` vanishes off the slow modes. -/
  slow : ∀ k, k 2 ≠ 0 → a k = 0
  /-- `a` vanishes at the origin (mean zero). -/
  zero : a 0 = 0
  /-- `|k| a ∈ ℓ²`. -/
  grad : Summable fun k => absSq k * a k ^ 2

namespace SlowSeq

variable {a b : Mode → ℝ}

lemma sq_le (ha : SlowSeq a) (k : Mode) : a k ^ 2 ≤ absSq k * a k ^ 2 := by
  by_cases hk : k = 0
  · subst hk
    simp [ha.zero]
  · have := one_le_absSq hk
    nlinarith [sq_nonneg (a k)]

lemma summable_sq (ha : SlowSeq a) : Summable fun k => a k ^ 2 :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _) ha.sq_le ha.grad

lemma tsum_sq_le (ha : SlowSeq a) : ∑' k, a k ^ 2 ≤ ∑' k, absSq k * a k ^ 2 :=
  ha.summable_sq.tsum_le_tsum ha.sq_le ha.grad

lemma tsum_sq_nonneg (_ha : SlowSeq a) : 0 ≤ ∑' k, a k ^ 2 :=
  tsum_nonneg fun _ => sq_nonneg _

lemma tsum_grad_nonneg (_ha : SlowSeq a) : 0 ≤ ∑' k, absSq k * a k ^ 2 :=
  tsum_nonneg fun k => mul_nonneg (absSq_nonneg k) (sq_nonneg _)

/-- A profile with vanishing `ℓ²` norm vanishes. -/
lemma eq_zero_of_tsum_sq (ha : SlowSeq a) (h : ∑' k, a k ^ 2 = 0) : a = 0 := by
  funext k
  have h1 : a k ^ 2 ≤ ∑' k, a k ^ 2 := ha.summable_sq.le_tsum k fun j _ => sq_nonneg _
  rw [h] at h1
  have h2 : a k ^ 2 = 0 := le_antisymm h1 (sq_nonneg _)
  simpa using h2

/-- `√(r_λ(p)) √(λ + |p|²) a p = a p`: the resolvent weight cancels where `a` lives. -/
lemma sqrt_res_mul (ha : SlowSeq a) {t : ℝ} (ht : 0 ≤ t) (p : Mode) :
    Real.sqrt (slowResW t p) * Real.sqrt (t + absSq p) * a p = a p := by
  by_cases hp : p 2 = 0 ∧ p ≠ 0
  · rw [sqrt_slowResW_mul ht hp.1 hp.2, one_mul]
  · have h0 : a p = 0 := by
      by_cases h2 : p 2 = 0
      · have : p = 0 := by
          by_contra h
          exact hp ⟨h2, h⟩
        rw [this]
        exact ha.zero
      · exact ha.slow p h2
    rw [h0, mul_zero]

/-- The weighted profile `(λ + |k|²) a_k²` is summable. -/
lemma summable_weighted (ha : SlowSeq a) (t : ℝ) :
    Summable (fun k => (t + absSq k) * a k ^ 2) := by
  refine ((ha.summable_sq.mul_left t).add ha.grad).congr fun k => ?_
  ring

/-- `∑ (λ + |k|²) a_k² = λ ∑ a² + ∑ |k|² a²`. -/
lemma tsum_weighted (ha : SlowSeq a) (t : ℝ) :
    ∑' k, (t + absSq k) * a k ^ 2 = t * ∑' k, a k ^ 2 + ∑' k, absSq k * a k ^ 2 := by
  rw [← tsum_mul_left, ← (ha.summable_sq.mul_left t).tsum_add ha.grad]
  refine tsum_congr fun k => ?_
  ring

end SlowSeq

variable {a b : Mode → ℝ}

/-- The shear `(k, p) ↦ (p, k − p)` of the lattice square. -/
private def shear : Mode × Mode ≃ Mode × Mode where
  toFun z := (z.2, z.1 - z.2)
  invFun z := (z.1 + z.2, z.1)
  left_inv z := by simp
  right_inv z := by simp

/-- Tonelli for the convolution of two nonnegative summable sequences. -/
private lemma tonelli_conv {α γ : Mode → ℝ} (hα0 : ∀ k, 0 ≤ α k) (hγ0 : ∀ k, 0 ≤ γ k)
    (hα : Summable α) (hγ : Summable γ) :
    Summable (fun k => ∑' p, α p * γ (k - p)) ∧
      ∑' k, ∑' p, α p * γ (k - p) = (∑' k, α k) * ∑' k, γ k := by
  have hG : Summable fun z : Mode × Mode => α z.1 * γ z.2 := hα.mul_of_nonneg hγ hα0 hγ0
  have hF : Summable fun z : Mode × Mode => α z.2 * γ (z.1 - z.2) := shear.summable_iff.2 hG
  refine ⟨hF.prod, ?_⟩
  rw [hα.tsum_mul_tsum hγ hG, ← shear.tsum_eq (fun z : Mode × Mode => α z.1 * γ z.2)]
  exact (hF.tsum_prod).symm

/-- The weighted Cauchy–Schwarz step of T2: with `w_i = λ_i + |·|²` and `r_i = slowResW λ_i`,
`(a ∗ b)(k)² ≤ (∑_p r₁(p) r₂(k−p)) · ((w₁a²) ∗ (w₂b²))(k)`. -/
lemma convR_sq_le_weighted (ha : SlowSeq a) (hb : SlowSeq b) {t₁ t₂ : ℝ} (h1 : 0 ≤ t₁)
    (h2 : 0 ≤ t₂) (k : Mode) :
    convR a b k ^ 2 ≤ (∑' p, slowResW t₁ p * slowResW t₂ (k - p)) *
      ∑' p, (t₁ + absSq p) * a p ^ 2 * ((t₂ + absSq (k - p)) * b (k - p) ^ 2) := by
  set x : Mode → ℝ := fun p => Real.sqrt (slowResW t₁ p) * Real.sqrt (slowResW t₂ (k - p))
    with hx
  set y : Mode → ℝ := fun p =>
    (Real.sqrt (t₁ + absSq p) * a p) * (Real.sqrt (t₂ + absSq (k - p)) * b (k - p)) with hy
  have hx0 : ∀ p, 0 ≤ x p := fun p => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hy0 : ∀ p, 0 ≤ y p := fun p =>
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (ha.nonneg p))
      (mul_nonneg (Real.sqrt_nonneg _) (hb.nonneg _))
  have hxy : ∀ p, x p * y p = a p * b (k - p) := fun p => by
    have e1 := ha.sqrt_res_mul h1 p
    have e2 := hb.sqrt_res_mul h2 (k - p)
    simp only [hx, hy]
    calc Real.sqrt (slowResW t₁ p) * Real.sqrt (slowResW t₂ (k - p)) *
          (Real.sqrt (t₁ + absSq p) * a p * (Real.sqrt (t₂ + absSq (k - p)) * b (k - p)))
        = (Real.sqrt (slowResW t₁ p) * Real.sqrt (t₁ + absSq p) * a p) *
          (Real.sqrt (slowResW t₂ (k - p)) * Real.sqrt (t₂ + absSq (k - p)) * b (k - p)) := by
          ring
      _ = a p * b (k - p) := by rw [e1, e2]
  have hx2 : ∀ p, x p ^ 2 = slowResW t₁ p * slowResW t₂ (k - p) := fun p => by
    simp only [hx]
    rw [mul_pow, Real.sq_sqrt (slowResW_nonneg h1 p), Real.sq_sqrt (slowResW_nonneg h2 _)]
  have hy2 : ∀ p, y p ^ 2 = (t₁ + absSq p) * a p ^ 2 * ((t₂ + absSq (k - p)) * b (k - p) ^ 2) :=
    fun p => by
    simp only [hy]
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (add_nonneg h1 (absSq_nonneg p)),
      Real.sq_sqrt (add_nonneg h2 (absSq_nonneg _))]
  have hxs : Summable fun p => x p ^ 2 := by
    simp only [hx2]
    exact (cs_equiv (slowResW_nonneg h1) (slowResW_nonneg h2) (summable_slowResW_sq h1)
      (summable_slowResW_sq h2) (Equiv.subLeft k)).1
  have hys : Summable fun p => y p ^ 2 := by
    simp only [hy2]
    have hB : ∀ q, (t₂ + absSq q) * b q ^ 2 ≤ ∑' q, (t₂ + absSq q) * b q ^ 2 := fun q =>
      (hb.summable_weighted t₂).le_tsum q fun j _ =>
        mul_nonneg (add_nonneg h2 (absSq_nonneg j)) (sq_nonneg _)
    refine Summable.of_nonneg_of_le (fun p => mul_nonneg
      (mul_nonneg (add_nonneg h1 (absSq_nonneg p)) (sq_nonneg _))
      (mul_nonneg (add_nonneg h2 (absSq_nonneg _)) (sq_nonneg _))) (fun p => ?_)
      ((ha.summable_weighted t₁).mul_right (∑' q, (t₂ + absSq q) * b q ^ 2))
    exact mul_le_mul_of_nonneg_left (hB _)
      (mul_nonneg (add_nonneg h1 (absSq_nonneg p)) (sq_nonneg _))
  have hcs := cs_equiv hx0 hy0 hxs hys (Equiv.refl Mode)
  simp only [Equiv.refl_apply, hxy] at hcs
  have hc0 : 0 ≤ convR a b k := tsum_nonneg fun p => mul_nonneg (ha.nonneg p) (hb.nonneg _)
  have hX0 : 0 ≤ ∑' p, x p ^ 2 := tsum_nonneg fun p => sq_nonneg _
  have hY0 : 0 ≤ ∑' p, y p ^ 2 := tsum_nonneg fun p => sq_nonneg _
  calc convR a b k ^ 2 ≤ (Real.sqrt (∑' p, x p ^ 2) * Real.sqrt (∑' p, y p ^ 2)) ^ 2 :=
        pow_le_pow_left₀ hc0 hcs.2 2
    _ = (∑' p, x p ^ 2) * ∑' p, y p ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hX0, Real.sq_sqrt hY0]
    _ = _ := by simp only [hx2, hy2]

/-- **T2 with free spectral parameters** `λ₁, λ₂ ≥ 0`:
`∑_k (a∗b)(k)² ≤ √(S(λ₁)S(λ₂)) (λ₁‖a‖² + ‖|k|a‖²)(λ₂‖b‖² + ‖|k|b‖²)`. -/
theorem lady2d_weighted (ha : SlowSeq a) (hb : SlowSeq b) {t₁ t₂ : ℝ} (h1 : 0 ≤ t₁)
    (h2 : 0 ≤ t₂) :
    Summable (fun k => convR a b k ^ 2) ∧
      ∑' k, convR a b k ^ 2 ≤
        Real.sqrt ((∑' p, slowResW t₁ p ^ 2) * ∑' p, slowResW t₂ p ^ 2) *
          ((t₁ * ∑' k, a k ^ 2 + ∑' k, absSq k * a k ^ 2) *
            (t₂ * ∑' k, b k ^ 2 + ∑' k, absSq k * b k ^ 2)) := by
  set M := Real.sqrt ((∑' p, slowResW t₁ p ^ 2) * ∑' p, slowResW t₂ p ^ 2) with hM
  have hlat : ∀ k, ∑' p, slowResW t₁ p * slowResW t₂ (k - p) ≤ M := fun k => by
    have h := (cs_equiv (slowResW_nonneg h1) (slowResW_nonneg h2) (summable_slowResW_sq h1)
      (summable_slowResW_sq h2) (Equiv.subLeft k)).2
    simp only [Equiv.subLeft_apply] at h
    rw [hM, Real.sqrt_mul (tsum_nonneg fun p => sq_nonneg _)]
    exact h
  have hα0 : ∀ p, 0 ≤ (t₁ + absSq p) * a p ^ 2 := fun p =>
    mul_nonneg (add_nonneg h1 (absSq_nonneg p)) (sq_nonneg _)
  have hγ0 : ∀ q, 0 ≤ (t₂ + absSq q) * b q ^ 2 := fun q =>
    mul_nonneg (add_nonneg h2 (absSq_nonneg q)) (sq_nonneg _)
  obtain ⟨hTs, hTe⟩ := tonelli_conv hα0 hγ0 (ha.summable_weighted t₁) (hb.summable_weighted t₂)
  have hT0 : ∀ k, 0 ≤ ∑' p, (t₁ + absSq p) * a p ^ 2 * ((t₂ + absSq (k - p)) * b (k - p) ^ 2) :=
    fun k => tsum_nonneg fun p => mul_nonneg (hα0 p) (hγ0 _)
  have hpt : ∀ k, convR a b k ^ 2 ≤
      M * ∑' p, (t₁ + absSq p) * a p ^ 2 * ((t₂ + absSq (k - p)) * b (k - p) ^ 2) := fun k =>
    (convR_sq_le_weighted ha hb h1 h2 k).trans (mul_le_mul_of_nonneg_right (hlat k) (hT0 k))
  have hsum : Summable fun k =>
      M * ∑' p, (t₁ + absSq p) * a p ^ 2 * ((t₂ + absSq (k - p)) * b (k - p) ^ 2) :=
    hTs.mul_left M
  have hS := Summable.of_nonneg_of_le (fun k => sq_nonneg _) hpt hsum
  refine ⟨hS, ?_⟩
  calc ∑' k, convR a b k ^ 2
      ≤ ∑' k, M * ∑' p, (t₁ + absSq p) * a p ^ 2 * ((t₂ + absSq (k - p)) * b (k - p) ^ 2) :=
        hS.tsum_le_tsum hpt hsum
    _ = M * ((t₁ * ∑' k, a k ^ 2 + ∑' k, absSq k * a k ^ 2) *
          (t₂ * ∑' k, b k ^ 2 + ∑' k, absSq k * b k ^ 2)) := by
        rw [tsum_mul_left, hTe, ha.tsum_weighted, hb.tsum_weighted]

/-- **T2: the bilinear Fourier Ladyzhenskaya inequality on the slow modes.**  For nonnegative
`a, b` supported on the nonzero slow modes with `|k|a, |k|b ∈ ℓ²`,
`‖a ∗ b‖²_{ℓ²} ≤ 25 ‖a‖ ‖|k|a‖ ‖b‖ ‖|k|b‖` (report §2.1 (T2) with `c_L² = 25` in place of
`4·127/3`), together with the absolute convergence of every convolution sum. -/
theorem lady2d (ha : SlowSeq a) (hb : SlowSeq b) :
    (∀ k, Summable fun p => a p * b (k - p)) ∧ Summable (fun k => convR a b k ^ 2) ∧
      ∑' k, convR a b k ^ 2 ≤ 25 * Real.sqrt (∑' k, a k ^ 2) *
        Real.sqrt (∑' k, absSq k * a k ^ 2) * Real.sqrt (∑' k, b k ^ 2) *
        Real.sqrt (∑' k, absSq k * b k ^ 2) := by
  have hpt : ∀ k, Summable fun p => a p * b (k - p) := fun k =>
    (convR_le_of_l2 ha.nonneg hb.nonneg ha.summable_sq hb.summable_sq k).1
  set A := ∑' k, a k ^ 2 with hA
  set A₁ := ∑' k, absSq k * a k ^ 2 with hA₁
  set B := ∑' k, b k ^ 2 with hB
  set B₁ := ∑' k, absSq k * b k ^ 2 with hB₁
  have hA0 := ha.tsum_sq_nonneg
  have hB0 := hb.tsum_sq_nonneg
  have hA₁0 := ha.tsum_grad_nonneg
  have hB₁0 := hb.tsum_grad_nonneg
  have hAA := ha.tsum_sq_le
  have hBB := hb.tsum_sq_le
  have hR0 : 0 ≤ 25 * Real.sqrt A * Real.sqrt A₁ * Real.sqrt B * Real.sqrt B₁ := by positivity
  by_cases hAz : A = 0
  · have h0 : a = 0 := ha.eq_zero_of_tsum_sq hAz
    have hc : ∀ k, convR a b k = 0 := fun k => by simp [convR, h0]
    refine ⟨hpt, ?_, ?_⟩
    · simp only [hc]
      simp
    · simp only [hc]
      simpa using hR0
  by_cases hBz : B = 0
  · have h0 : b = 0 := hb.eq_zero_of_tsum_sq hBz
    have hc : ∀ k, convR a b k = 0 := fun k => by simp [convR, h0]
    refine ⟨hpt, ?_, ?_⟩
    · simp only [hc]
      simp
    · simp only [hc]
      simpa using hR0
  have hApos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hAz)
  have hBpos : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hBz)
  have hA₁pos : 0 < A₁ := hApos.trans_le hAA
  have hB₁pos : 0 < B₁ := hBpos.trans_le hBB
  have ht₁ : 0 < A₁ / A := div_pos hA₁pos hApos
  have ht₂ : 0 < B₁ / B := div_pos hB₁pos hBpos
  obtain ⟨hs, hle⟩ := lady2d_weighted ha hb ht₁.le ht₂.le
  refine ⟨hpt, hs, hle.trans ?_⟩
  have e1 : A₁ / A * A + A₁ = 2 * A₁ := by
    field_simp
    ring
  have e2 : B₁ / B * B + B₁ = 2 * B₁ := by
    field_simp
    ring
  rw [e1, e2]
  have hS1 : ∑' p, slowResW (A₁ / A) p ^ 2 ≤ 25 / 4 * (A / A₁) := by
    refine (slow_lattice_sum_le_div ht₁).trans (le_of_eq ?_)
    field_simp
  have hS2 : ∑' p, slowResW (B₁ / B) p ^ 2 ≤ 25 / 4 * (B / B₁) := by
    refine (slow_lattice_sum_le_div ht₂).trans (le_of_eq ?_)
    field_simp
  have hS10 : 0 ≤ ∑' p, slowResW (A₁ / A) p ^ 2 := tsum_nonneg fun p => sq_nonneg _
  have hS20 : 0 ≤ ∑' p, slowResW (B₁ / B) p ^ 2 := tsum_nonneg fun p => sq_nonneg _
  have hprod : (∑' p, slowResW (A₁ / A) p ^ 2) * (∑' p, slowResW (B₁ / B) p ^ 2) *
      (2 * A₁ * (2 * B₁)) ^ 2 ≤ 625 * (A * A₁ * B * B₁) := by
    have h := mul_le_mul hS1 hS2 hS20 (by positivity)
    calc (∑' p, slowResW (A₁ / A) p ^ 2) * (∑' p, slowResW (B₁ / B) p ^ 2) *
          (2 * A₁ * (2 * B₁)) ^ 2
        ≤ 25 / 4 * (A / A₁) * (25 / 4 * (B / B₁)) * (2 * A₁ * (2 * B₁)) ^ 2 :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ = 625 * (A * A₁ * B * B₁) := by
          field_simp
          ring
  have hL : Real.sqrt ((∑' p, slowResW (A₁ / A) p ^ 2) * ∑' p, slowResW (B₁ / B) p ^ 2) *
      (2 * A₁ * (2 * B₁)) = Real.sqrt ((∑' p, slowResW (A₁ / A) p ^ 2) *
        (∑' p, slowResW (B₁ / B) p ^ 2) * (2 * A₁ * (2 * B₁)) ^ 2) := by
    rw [Real.sqrt_mul (mul_nonneg hS10 hS20), Real.sqrt_sq (by positivity)]
  have hR : 25 * Real.sqrt A * Real.sqrt A₁ * Real.sqrt B * Real.sqrt B₁ =
      Real.sqrt (625 * (A * A₁ * B * B₁)) := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_mul hA0, show (625 : ℝ) = 25 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    ring
  rw [hL, hR]
  exact Real.sqrt_le_sqrt hprod

/-! ### Weighted coefficient profiles of fields -/

/-- The weighted coefficient profile `k ↦ |k|^m ‖u k‖` of a field. -/
def wtd (m : ℕ) (u : Field) (k : Mode) : ℝ := absk k ^ m * ‖u k‖

variable {u v W : Field}

lemma wtd_nonneg (m : ℕ) (u : Field) (k : Mode) : 0 ≤ wtd m u k :=
  mul_nonneg (pow_nonneg (absk_nonneg k) m) (norm_nonneg _)

lemma wtd_zero_apply (m : ℕ) (hu0 : u 0 = 0) : wtd m u 0 = 0 := by
  simp [wtd, hu0]

/-- `(|k|^m ‖u k‖)² = |k|^{2m} ‖u k‖²`, the summand of `‖u‖_m²`. -/
lemma wtd_sq (m : ℕ) (hu0 : u 0 = 0) (k : Mode) :
    wtd m u k ^ 2 = sobWeight m k * ‖u k‖ ^ 2 := by
  by_cases hk : k = 0
  · subst hk
    simp [wtd, hu0, sobWeight]
  · have h : sobWeight (m : ℝ) k = (absk k ^ m) ^ 2 := by
      rw [sobWeight, ite_eq_right hk, ← pow_mul,
        show (2 : ℝ) * m = ((m * 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [wtd, mul_pow, h]

/-- `|k|² (|k|^m ‖u k‖)² = |k|^{2(m+1)} ‖u k‖²`, the summand of `‖u‖_{m+1}²`. -/
lemma absSq_mul_wtd_sq (m : ℕ) (hu0 : u 0 = 0) (k : Mode) :
    absSq k * wtd m u k ^ 2 = sobWeight ((m : ℝ) + 1) k * ‖u k‖ ^ 2 := by
  have h := wtd_sq (m + 1) hu0 k
  push_cast at h
  rw [← h, wtd, wtd, pow_succ, ← absk_sq]
  ring

lemma sqrt_tsum_wtd_sq (m : ℕ) (hu0 : u 0 = 0) :
    Real.sqrt (∑' k, wtd m u k ^ 2) = hnorm m u := by
  rw [hnorm]
  congr 1
  exact tsum_congr fun k => wtd_sq m hu0 k

lemma sqrt_tsum_absSq_wtd_sq (m : ℕ) (hu0 : u 0 = 0) :
    Real.sqrt (∑' k, absSq k * wtd m u k ^ 2) = hnorm ((m : ℝ) + 1) u := by
  rw [hnorm]
  congr 1
  exact tsum_congr fun k => absSq_mul_wtd_sq m hu0 k

/-- `∑ (|k|^m ‖u k‖)² = ‖u‖_m²`. -/
lemma tsum_wtd_sq (m : ℕ) (hu0 : u 0 = 0) : ∑' k, wtd m u k ^ 2 = hnorm m u ^ 2 := by
  rw [← sqrt_tsum_wtd_sq m hu0, Real.sq_sqrt (tsum_nonneg fun k => sq_nonneg _)]

/-- `|k|^m ‖u k‖ ∈ ℓ²` for `u ∈ H^m` (mean zero). -/
lemma summable_wtd_sq (m : ℕ) (hu : InH m u) (hu0 : u 0 = 0) : Summable fun k => wtd m u k ^ 2 := by
  have : (fun k => wtd m u k ^ 2) = fun k => sobWeight m k * ‖u k‖ ^ 2 := funext (wtd_sq m hu0)
  rw [this]
  exact hu

/-- The profile `|k|^m ‖u k‖` of a mean-zero slow `H^{m+1}` field is a `SlowSeq`. -/
lemma SlowSeq.ofField (m : ℕ) (hu : InH ((m : ℝ) + 1) u) (hu' : ∀ k, k 2 ≠ 0 → u k = 0)
    (hu0 : u 0 = 0) : SlowSeq (wtd m u) where
  nonneg := wtd_nonneg m u
  slow := fun k hk => by simp [wtd, hu' k hk]
  zero := wtd_zero_apply m hu0
  grad := by
    have : (fun k => absSq k * wtd m u k ^ 2) = fun k => sobWeight ((m : ℝ) + 1) k * ‖u k‖ ^ 2 :=
      funext (absSq_mul_wtd_sq m hu0)
    rw [this]
    exact hu

/-- T2 for the profiles `|k|^i ‖u k‖`, `|k|^j ‖v k‖` of mean-zero slow fields:
`‖(|k|^i û) ∗ (|k|^j v̂)‖²_{ℓ²} ≤ 25 ‖u‖_i ‖u‖_{i+1} ‖v‖_j ‖v‖_{j+1}`. -/
theorem lady2d_wtd (i j : ℕ) (hu : InH ((i : ℝ) + 1) u) (hu' : ∀ k, k 2 ≠ 0 → u k = 0)
    (hu0 : u 0 = 0) (hv : InH ((j : ℝ) + 1) v) (hv' : ∀ k, k 2 ≠ 0 → v k = 0) (hv0 : v 0 = 0) :
    (∀ k, Summable fun p => wtd i u p * wtd j v (k - p)) ∧
      Summable (fun k => convR (wtd i u) (wtd j v) k ^ 2) ∧
      ∑' k, convR (wtd i u) (wtd j v) k ^ 2 ≤
        25 * hnorm i u * hnorm ((i : ℝ) + 1) u * hnorm j v * hnorm ((j : ℝ) + 1) v := by
  obtain ⟨h1, h2, h3⟩ := lady2d (SlowSeq.ofField i hu hu' hu0) (SlowSeq.ofField j hv hv' hv0)
  rw [sqrt_tsum_wtd_sq i hu0, sqrt_tsum_absSq_wtd_sq i hu0, sqrt_tsum_wtd_sq j hv0,
    sqrt_tsum_absSq_wtd_sq j hv0] at h3
  exact ⟨h1, h2, h3⟩

/-- **T2 on fields.**  For mean-zero slow `u, v ∈ H¹`:
`∑_k (∑_p ‖û_p‖ ‖v̂_{k−p}‖)² ≤ 25 ‖u‖₀ ‖u‖₁ ‖v‖₀ ‖v‖₁`, with absolute convergence. -/
theorem lady2d_field (hu : InH 1 u) (hu' : PiS u = u) (hu0 : u 0 = 0) (hv : InH 1 v)
    (hv' : PiS v = v) (hv0 : v 0 = 0) :
    (∀ k, Summable fun p => ‖u p‖ * ‖v (k - p)‖) ∧
      Summable (fun k => (∑' p, ‖u p‖ * ‖v (k - p)‖) ^ 2) ∧
      ∑' k, (∑' p, ‖u p‖ * ‖v (k - p)‖) ^ 2 ≤
        25 * hnorm 0 u * hnorm 1 u * hnorm 0 v * hnorm 1 v := by
  have hu1 : InH (((0 : ℕ) : ℝ) + 1) u := by simpa using hu
  have hv1 : InH (((0 : ℕ) : ℝ) + 1) v := by simpa using hv
  obtain ⟨h1, h2, h3⟩ := lady2d_wtd 0 0 hu1 (fun k hk => slow_zero hu' hk) hu0 hv1
    (fun k hk => slow_zero hv' hk) hv0
  simp only [convR, wtd, pow_zero, one_mul, Nat.cast_zero, zero_add] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-! ### Triple sums bounded through a convolution -/

/-- The canonical triple sum `∑_{p,q} A_p B_q C_{−(p+q)}` is bounded by `‖A‖_{ℓ²} ‖B ∗ C‖_{ℓ²}`
(Cauchy–Schwarz in `p` after summing the convolution in `q`). -/
lemma triple_conv_bound {A B C : Mode → ℝ} (hA : ∀ k, 0 ≤ A k) (hB : ∀ k, 0 ≤ B k)
    (hC : ∀ k, 0 ≤ C k) (hA2 : Summable fun k => A k ^ 2)
    (hBC1 : ∀ k, Summable fun q => B q * C (k - q)) (hBC2 : Summable fun k => convR B C k ^ 2) :
    Summable (fun x : Mode × Mode => A x.1 * B x.2 * C (-(x.1 + x.2))) ∧
      ∑' x : Mode × Mode, A x.1 * B x.2 * C (-(x.1 + x.2)) ≤
        Real.sqrt (∑' k, A k ^ 2) * Real.sqrt (∑' k, convR B C k ^ 2) := by
  have hC0 : ∀ k, 0 ≤ convR B C k := fun k => tsum_nonneg fun q => mul_nonneg (hB q) (hC _)
  have hcs := cs_equiv hA hC0 hA2 hBC2 (Equiv.neg Mode)
  simp only [Equiv.neg_apply] at hcs
  have hin : ∀ p : Mode, Summable fun q => A p * B q * C (-(p + q)) := fun p => by
    refine ((hBC1 (-p)).mul_left (A p)).congr fun q => ?_
    rw [neg_add', mul_assoc]
  have hval : ∀ p : Mode, ∑' q, A p * B q * C (-(p + q)) = A p * convR B C (-p) := fun p => by
    rw [convR, ← tsum_mul_left]
    refine tsum_congr fun q => ?_
    rw [neg_add', mul_assoc]
  have hout : Summable fun p : Mode => ∑' q, A p * B q * C (-(p + q)) := by
    simp only [hval]
    exact hcs.1
  have hs : Summable (fun x : Mode × Mode => A x.1 * B x.2 * C (-(x.1 + x.2))) :=
    (summable_prod_of_nonneg fun x => mul_nonneg (mul_nonneg (hA _) (hB _)) (hC _)).mpr
      ⟨hin, hout⟩
  refine ⟨hs, ?_⟩
  rw [hs.tsum_prod]
  simp only [hval]
  exact hcs.2

lemma summable_swap {G : Mode × Mode → ℝ} (hG : Summable G) :
    Summable fun x : Mode × Mode => G x.swap :=
  (Equiv.prodComm Mode Mode).summable_iff.mpr hG

lemma tsum_swap (G : Mode × Mode → ℝ) : ∑' x : Mode × Mode, G x.swap = ∑' x, G x :=
  (Equiv.prodComm Mode Mode).tsum_eq G

/-- `∑ ½(G x + G x.swap) = ∑ G`. -/
lemma tsum_half_sym {G : Mode × Mode → ℝ} (hG : Summable G) :
    ∑' x : Mode × Mode, (1 / 2) * (G x + G x.swap) = ∑' x, G x := by
  rw [tsum_mul_left, hG.tsum_add (summable_swap hG), tsum_swap]
  ring

/-- The triple sum with the profile `|k|^a ‖u k‖` in the `ℓ²` slot and the convolution of
`|k|^i ‖v k‖`, `|k|^j ‖w k‖`, bounded through T2.  Hypotheses: `u ∈ H^a`, `v ∈ H^{i+1}`,
`w ∈ H^{j+1}`, all mean zero, `v, w` slow. -/
lemma triple_wtd_bound (a i j : ℕ) {u v w : Field} (hu : InH a u) (hu0 : u 0 = 0)
    (hv : InH ((i : ℝ) + 1) v) (hv' : ∀ k, k 2 ≠ 0 → v k = 0) (hv0 : v 0 = 0)
    (hw : InH ((j : ℝ) + 1) w) (hw' : ∀ k, k 2 ≠ 0 → w k = 0) (hw0 : w 0 = 0) :
    Summable (fun x : Mode × Mode => wtd a u x.1 * wtd i v x.2 * wtd j w (-(x.1 + x.2))) ∧
      ∑' x : Mode × Mode, wtd a u x.1 * wtd i v x.2 * wtd j w (-(x.1 + x.2)) ≤
        hnorm a u * Real.sqrt (25 * hnorm i v * hnorm ((i : ℝ) + 1) v * hnorm j w *
          hnorm ((j : ℝ) + 1) w) := by
  obtain ⟨h1, h2, h3⟩ := lady2d_wtd i j hv hv' hv0 hw hw' hw0
  obtain ⟨hs, hle⟩ := triple_conv_bound (wtd_nonneg a u) (wtd_nonneg i v) (wtd_nonneg j w)
    (summable_wtd_sq a hu hu0) h1 h2
  refine ⟨hs, hle.trans ?_⟩
  rw [sqrt_tsum_wtd_sq a hu0]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h3) (hnorm_nonneg _ _)

/-! ### T3: the weighted slow triads -/

/-- The weighted scalar triad of the slow transport term: for a slow field `s`, a component `W`
and a real weight `ω (q, r)` on the pair (`W`-leg, test leg), `r = −(p+q)`,
`½ i [ (ŝ_p·q) ω(q,r) (W_q·W_r) + (ŝ_q·p) ω(p,r) (W_p·W_r) ]`.  With `ω ≡ 1` this is the triad
`tripB s s W` of `⟨W, B(s,s)⟩`; with `ω = |r|^{2σ}` it is the triad of `pair σ W (Bsym s s)`. -/
def triC (s W : Field) (ω : Mode → Mode → ℝ) (p q : Mode) : ℂ :=
  (1 / 2) * Complex.I *
    (dotM (s p) q * ((ω q (-(p + q)) : ℂ) * bd (W q) (W (-(p + q)))) +
      dotM (s q) p * ((ω p (-(p + q)) : ℂ) * bd (W p) (W (-(p + q)))))

variable {s : Field}

lemma tripB_eq_triC (hb : ∀ q r, bd (s q) (W r) = bd (W q) (W r)) (p q : Mode) :
    tripB s s W p q = triC s W (fun _ _ => 1) p q := by
  simp only [tripB, tau, triC, hb, Complex.ofReal_one, one_mul]

/-- The weighted triad of `pair σ W (Bsym s s)`. -/
lemma weight_mul_tripB (hb : ∀ q r, bd (s q) (W r) = bd (W q) (W r)) (σ : ℝ) (p q : Mode) :
    (sobWeight σ (p + q) : ℂ) * tripB s s W p q = triC s W (fun _ r => sobWeight σ r) p q := by
  rw [tripB_eq_triC hb]
  simp only [triC, sobWeight_neg, Complex.ofReal_one, one_mul]
  ring

lemma triC_sub (ω₁ ω₂ : Mode → Mode → ℝ) (p q : Mode) :
    triC s W ω₁ p q - triC s W ω₂ p q = triC s W (fun q r => ω₁ q r - ω₂ q r) p q := by
  simp only [triC]
  push_cast
  ring

/-- The transport cancellation: with the symmetric weight `e_q e_r` the triad sums to zero over
each cyclic orbit `(p,q) → (q,r) → (r,p)`, by `ŝ_p · p = 0` (the Fourier form of
`⟨(s·∇)φ, φ⟩ = 0` for `div s = 0`, `φ = Λ^σ W`). -/
lemma triC_cyc (hs : IsSolenoidal s) (e : Mode → ℝ) (p q : Mode) :
    triC s W (fun q r => e q * e r) p q + triC s W (fun q r => e q * e r) q (-(p + q)) +
      triC s W (fun q r => e q * e r) (-(p + q)) p = 0 := by
  set r := -(p + q) with hr
  have h1 : -(q + r) = p := by
    rw [hr]
    abel
  have h2 : -(r + p) = q := by
    rw [hr]
    abel
  have hp : dotM (s p) q + dotM (s p) r = 0 := by
    rw [← dotM_add_mode, show q + r = -p by rw [hr]; abel, dotM_neg_mode, hs p, neg_zero]
  have hq : dotM (s q) p + dotM (s q) r = 0 := by
    rw [← dotM_add_mode, show p + r = -q by rw [hr]; abel, dotM_neg_mode, hs q, neg_zero]
  have hrr : dotM (s r) p + dotM (s r) q = 0 := by
    rw [← dotM_add_mode, show p + q = -r by rw [hr]; abel, dotM_neg_mode, hs r, neg_zero]
  simp only [triC, h1, h2]
  rw [bd_comm (W r) (W p), bd_comm (W r) (W q), bd_comm (W q) (W p)]
  push_cast
  linear_combination (1 / 2 : ℂ) * Complex.I * ((e q : ℂ) * e r * bd (W q) (W r)) * hp
    + (1 / 2 : ℂ) * Complex.I * ((e p : ℂ) * e r * bd (W p) (W r)) * hq
    + (1 / 2 : ℂ) * Complex.I * ((e p : ℂ) * e q * bd (W p) (W q)) * hrr

/-- `‖ŝ_p·q‖ ‖W_q‖ ≤ ‖ĥ_p‖ |q| ‖W_q‖` for slow `s` and a slow component `W`
(`h = PiH s`; only the horizontal part of `ŝ_p` sees a slow `q`). -/
lemma norm_dotM_mul_norm_le (hs' : PiS s = s) (hW : ∀ k, k 2 ≠ 0 → W k = 0) (p q : Mode) :
    ‖dotM (s p) q‖ * ‖W q‖ ≤ ‖PiH s p‖ * absk q * ‖W q‖ := by
  by_cases hq : q 2 = 0
  · rw [dotM_PiH hs' p hq]
    exact mul_le_mul_of_nonneg_right (norm_dotM_le _ _) (norm_nonneg _)
  · simp [hW q hq]

private lemma mul5_le {a b d f w w' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) (hf : 0 ≤ f)
    (h : w ≤ w') : a * b * w * d * f ≤ a * b * w' * d * f :=
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left h (mul_nonneg ha hb)) hd) hf

/-- The pointwise majorant of the weighted triad. -/
lemma norm_triC_le (hs' : PiS s = s) (hW : ∀ k, k 2 ≠ 0 → W k = 0) (ω : Mode → Mode → ℝ)
    (p q : Mode) :
    ‖triC s W ω p q‖ ≤ (1 / 2) *
      (‖PiH s p‖ * absk q * |ω q (-(p + q))| * ‖W q‖ * ‖W (-(p + q))‖ +
        ‖PiH s q‖ * absk p * |ω p (-(p + q))| * ‖W p‖ * ‖W (-(p + q))‖) := by
  have h6 : ‖(1 / 2 : ℂ) * Complex.I‖ = 1 / 2 := by simp
  rw [triC, norm_mul, h6]
  refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add ?_ ?_)) (by norm_num)
  · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 := norm_dotM_mul_norm_le hs' hW p q
    have h2 := norm_bd_le (W q) (W (-(p + q)))
    calc ‖dotM (s p) q‖ * (|ω q (-(p + q))| * ‖bd (W q) (W (-(p + q)))‖)
        ≤ ‖dotM (s p) q‖ * (|ω q (-(p + q))| * (‖W q‖ * ‖W (-(p + q))‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)) (norm_nonneg _)
      _ = (‖dotM (s p) q‖ * ‖W q‖) * |ω q (-(p + q))| * ‖W (-(p + q))‖ := by ring
      _ ≤ (‖PiH s p‖ * absk q * ‖W q‖) * |ω q (-(p + q))| * ‖W (-(p + q))‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
            (norm_nonneg _)
      _ = _ := by ring
  · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 := norm_dotM_mul_norm_le hs' hW q p
    have h2 := norm_bd_le (W p) (W (-(p + q)))
    calc ‖dotM (s q) p‖ * (|ω p (-(p + q))| * ‖bd (W p) (W (-(p + q)))‖)
        ≤ ‖dotM (s q) p‖ * (|ω p (-(p + q))| * (‖W p‖ * ‖W (-(p + q))‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)) (norm_nonneg _)
      _ = (‖dotM (s q) p‖ * ‖W p‖) * |ω p (-(p + q))| * ‖W (-(p + q))‖ := by ring
      _ ≤ (‖PiH s q‖ * absk p * ‖W p‖) * |ω p (-(p + q))| * ‖W (-(p + q))‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
            (norm_nonneg _)
      _ = _ := by ring

/-! ### The commutator symbols -/

lemma absk_triad_le (p q : Mode) :
    absk (-(p + q)) ≤ absk p + absk q ∧ absk q ≤ absk p + absk (-(p + q)) := by
  refine ⟨by rw [absk_neg]; exact absk_add_le p q, ?_⟩
  have e : absk q = absk (p + -(p + q)) := by
    rw [show p + -(p + q) = -q by abel, absk_neg]
  rw [e]
  exact absk_add_le p _

/-- `σ = 1`: `| |r|² − |q||r| | ≤ |p| |r|` on a triad `p + q + r = 0`. -/
lemma weight_one_bound (p q : Mode) :
    |sobWeight 1 (-(p + q)) - absk q * absk (-(p + q))| ≤ absk p * absk (-(p + q)) := by
  obtain ⟨h1, h2⟩ := absk_triad_le p q
  rw [sobWeight_one, ← absk_sq,
    show absk (-(p + q)) ^ 2 - absk q * absk (-(p + q)) =
      (absk (-(p + q)) - absk q) * absk (-(p + q)) by ring,
    abs_mul, abs_of_nonneg (absk_nonneg _)]
  exact mul_le_mul_of_nonneg_right (abs_le.2 ⟨by linarith, by linarith⟩) (absk_nonneg _)

/-- `σ = 2`: `| |r|⁴ − |q|²|r|² | ≤ (|p|² + 2|p||q|) |r|²` on a triad `p + q + r = 0`. -/
lemma weight_two_bound (p q : Mode) :
    |sobWeight 2 (-(p + q)) - absSq q * absSq (-(p + q))| ≤
      (absk p ^ 2 + 2 * absk p * absk q) * absSq (-(p + q)) := by
  obtain ⟨h1, h2⟩ := absk_triad_le p q
  have hp := absk_nonneg p
  have hq := absk_nonneg q
  have hr := absk_nonneg (-(p + q))
  rw [sobWeight_two, ← absk_sq, ← absk_sq,
    show (absk (-(p + q)) ^ 2) ^ 2 - absk q ^ 2 * absk (-(p + q)) ^ 2 =
      (absk (-(p + q)) - absk q) * ((absk (-(p + q)) + absk q) * absk (-(p + q)) ^ 2) by ring,
    abs_mul, abs_of_nonneg (mul_nonneg (add_nonneg hr hq) (sq_nonneg _))]
  have h3 : |absk (-(p + q)) - absk q| ≤ absk p := abs_le.2 ⟨by linarith, by linarith⟩
  have h4 : absk (-(p + q)) + absk q ≤ absk p + 2 * absk q := by linarith
  calc |absk (-(p + q)) - absk q| * ((absk (-(p + q)) + absk q) * absk (-(p + q)) ^ 2)
      ≤ absk p * ((absk p + 2 * absk q) * absk (-(p + q)) ^ 2) :=
        mul_le_mul h3 (mul_le_mul_of_nonneg_right h4 (sq_nonneg _))
          (mul_nonneg (add_nonneg hr hq) (sq_nonneg _)) hp
    _ = (absk p ^ 2 + 2 * absk p * absk q) * absk (-(p + q)) ^ 2 := by ring

/-! ### The commutator skeleton -/

/-- The commutator skeleton of T3.  If the weighted triad `U = triC s W |r|^{2σ}` of
`pair σ W (Bsym s s)` differs from the cyclically vanishing transport triad
`V = triC s W (e_q e_r)` by a term with a summable symmetrized majorant `½(G + G∘swap)`, and `V`
itself has the summable majorant `½(M + M∘swap)`, then `|pair σ W (Bsym s s)| ≤ ∑ G`. -/
lemma abs_pair_le_of_triads {σ : ℝ} (hs : Adm 2 s) (hW : Adm 2 W)
    (hb : ∀ q r, bd (s q) (W r) = bd (W q) (W r)) (e : Mode → ℝ) {G M : Mode × Mode → ℝ}
    (hG : Summable G) (hM : Summable M)
    (hGle : ∀ x : Mode × Mode,
      ‖triC s W (fun q r => sobWeight σ r - e q * e r) x.1 x.2‖ ≤ (1 / 2) * (G x + G x.swap))
    (hMle : ∀ x : Mode × Mode,
      ‖triC s W (fun q r => e q * e r) x.1 x.2‖ ≤ (1 / 2) * (M x + M x.swap)) :
    |pair σ W (Bsym s s)| ≤ ∑' x, G x := by
  set U : Mode × Mode → ℂ := fun x => triC s W (fun _ r => sobWeight σ r) x.1 x.2 with hU
  set V : Mode × Mode → ℂ := fun x => triC s W (fun q r => e q * e r) x.1 x.2 with hV
  have hUV : ∀ x, U x - V x = triC s W (fun q r => sobWeight σ r - e q * e r) x.1 x.2 :=
    fun x => triC_sub _ _ _ _
  have hGs : Summable fun x : Mode × Mode => (1 / 2) * (G x + G x.swap) :=
    (hG.add (summable_swap hG)).mul_left _
  have hMs : Summable fun x : Mode × Mode => (1 / 2) * (M x + M x.swap) :=
    (hM.add (summable_swap hM)).mul_left _
  have hVs : Summable V := Summable.of_norm_bounded hMs hMle
  have hDs : Summable (fun x => U x - V x) :=
    Summable.of_norm_bounded hGs fun x => by rw [hUV]; exact hGle x
  have hUs : Summable U := by simpa using hDs.add hVs
  have hT : Summable fun x : Mode × Mode =>
      (sobWeight σ (x.1 + x.2) : ℂ) * tripB s s W x.1 x.2 :=
    hUs.congr fun x => (weight_mul_tripB hb σ x.1 x.2).symm
  rw [pair_eq_tsum (tripB s s W) (inner_Bsym hW hs.mz hs.mz) hT]
  have hV0 : ∑' x, V x = 0 := tsum_cyc hVs fun p q => triC_cyc hs.sol e p q
  have hsum : ∑' x : Mode × Mode, (sobWeight σ (x.1 + x.2) : ℂ) * tripB s s W x.1 x.2 =
      ∑' x, (U x - V x) := by
    have e1 : ∑' x : Mode × Mode, (sobWeight σ (x.1 + x.2) : ℂ) * tripB s s W x.1 x.2 =
        ∑' x, U x := tsum_congr fun x => weight_mul_tripB hb σ x.1 x.2
    have e2 : ∑' x, U x = ∑' x, (U x - V x) + ∑' x, V x := by
      rw [← hDs.tsum_add hVs]
      exact tsum_congr fun x => by ring
    rw [e1, e2, hV0, add_zero]
  rw [hsum]
  refine (Complex.abs_re_le_norm _).trans ?_
  have hle : ‖∑' x, (U x - V x)‖ ≤ ∑' x : Mode × Mode, (1 / 2) * (G x + G x.swap) :=
    tsum_of_norm_bounded hGs.hasSum fun x => by rw [hUV]; exact hGle x
  rwa [tsum_half_sym hG] at hle

/-! ### T3a: `|⟨h·∇ζ, Δζ⟩| ≤ 5 a_h a_ζ b_ζ` -/

lemma PiV_fast (u : Field) {k : Mode} (hk : k 2 ≠ 0) : PiV u k = 0 := by
  simp [PiV, hk]

/-- **T3a** (report §2.1 (T3), first line, `c_L = 5`): for a real, mean-zero, divergence-free
slow field `s ∈ H²` with `h = PiH s`, `ζ = PiV s`,
`|⟨h·∇ζ, Δζ⟩| = |pair 1 ζ (Bsym s s)| ≤ 5 ‖h‖₁ ‖ζ‖₁ ‖ζ‖₂`.  The commutator
`|r|² − |q||r| = |r|(|r| − |q|)`, `||r| − |q|| ≤ |p|`, leaves the triple sum
`∑ |p|ĥ_p · |q|ζ̂_q · |r|ζ̂_r ≤ ‖h‖₁ ‖(Λζ̂)∗(Λζ̂)‖_{ℓ²}`, closed by T2.  Replaces the Wiener form
`pair_slow_vertical_le` (`𝒜(h) ‖ζ‖₁ ‖ζ‖₂`) by the `H¹` norm of `h`. -/
theorem pair_slow_vertical_lady (hs : Adm 2 s) (hs' : PiS s = s) :
    |pair 1 (PiV s) (PiV (Bsym s s))| ≤
      5 * hnorm 1 (PiH s) * hnorm 1 (PiV s) * hnorm 2 (PiV s) := by
  rw [pair_PiV]
  have hV := admPiV hs
  have hH := admPiH hs
  have hWs : ∀ k, k 2 ≠ 0 → PiV s k = 0 := fun k hk => PiV_fast s hk
  have hHs : ∀ k, k 2 ≠ 0 → PiH s k = 0 := fun k hk => PiH_fast s hk
  have hW0 : PiV s 0 = 0 := hV.mean
  have hH0 : PiH s 0 = 0 := hH.mean
  have hH1 : InH 1 (PiH s) := hH.inH.mono (by norm_num)
  have hV2 : InH (((1 : ℕ) : ℝ) + 1) (PiV s) := by
    norm_num
    exact hV.inH
  have hH1' : InH (((0 : ℕ) : ℝ) + 1) (PiH s) := by simpa using hH1
  -- the commutator majorant `G(p,q) = |p|‖h_p‖ · |q|‖ζ_q‖ · |r|‖ζ_r‖`
  obtain ⟨hG, hGle⟩ := triple_wtd_bound 1 1 1 (u := PiH s) (v := PiV s) (w := PiV s)
    (by simpa using hH1) hH0 hV2 hWs hW0 hV2 hWs hW0
  -- the transport majorant `M(p,q) = |p|²‖ζ_p‖ · ‖h_q‖ · |r|‖ζ_r‖`
  obtain ⟨hM, -⟩ := triple_wtd_bound 2 0 1 (u := PiV s) (v := PiH s) (w := PiV s)
    (by simpa using hV.inH) hW0 hH1' hHs hH0 hV2 hWs hW0
  have key := abs_pair_le_of_triads (σ := 1) hs hV (bd_slow_PiV hs') absk hG hM ?_ ?_
  · have e2 : ((1 : ℕ) : ℝ) + 1 = 2 := by norm_num
    rw [e2, Nat.cast_one] at hGle
    refine key.trans (hGle.trans (le_of_eq ?_))
    have h0 := hnorm_nonneg 1 (PiV s)
    have h2 := hnorm_nonneg 2 (PiV s)
    rw [show (25 : ℝ) * hnorm 1 (PiV s) * hnorm 2 (PiV s) * hnorm 1 (PiV s) * hnorm 2 (PiV s)
        = (5 * hnorm 1 (PiV s) * hnorm 2 (PiV s)) ^ 2 by ring,
      Real.sqrt_sq (mul_nonneg (mul_nonneg (by norm_num) h0) h2)]
    ring
  · rintro ⟨p, q⟩
    simp only [Prod.swap_prod_mk]
    refine (norm_triC_le hs' hWs _ p q).trans ?_
    have hb1 := weight_one_bound p q
    have hb2 := weight_one_bound q p
    rw [add_comm q p] at hb2
    have hp := absk_nonneg p
    have hq := absk_nonneg q
    have hr := absk_nonneg (-(p + q))
    refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by norm_num)
    · refine (mul5_le (norm_nonneg _) hq (norm_nonneg _) (norm_nonneg _) hb1).trans (le_of_eq ?_)
      simp only [wtd, pow_one]
      ring
    · refine (mul5_le (norm_nonneg _) hp (norm_nonneg _) (norm_nonneg _) hb2).trans (le_of_eq ?_)
      simp only [wtd, pow_one, add_comm q p]
      ring
  · rintro ⟨p, q⟩
    simp only [Prod.swap_prod_mk]
    refine (norm_triC_le hs' hWs _ p q).trans (le_of_eq ?_)
    have hp := absk_nonneg p
    have hq := absk_nonneg q
    have hr := absk_nonneg (-(p + q))
    simp only [wtd, pow_one, pow_zero, one_mul, abs_of_nonneg (mul_nonneg hq hr),
      abs_of_nonneg (mul_nonneg hp hr), add_comm q p]
    ring

/-! ### T3b: `|⟨P(h·∇h), Δ²h⟩| ≤ 15 a_h b_h c_h` -/

/-- **T3b** (report §2.1 (T3), second line, `3c_L = 15`): for a real, mean-zero,
divergence-free slow field `s ∈ H³` with `h = PiH s`,
`|⟨P(h·∇h), Δ²h⟩| = |pair 2 h (Bsym s s)| ≤ 15 ‖h‖₁ ‖h‖₂ ‖h‖₃`.  The commutator
`|r|⁴ − |q|²|r|² = |r|²(|r|² − |q|²)`, `||r|² − |q|²| ≤ |p|² + 2|p||q|`, leaves triple sums of
the shape `∑ |p|ĥ_p · |q|²ĥ_q · |r|²ĥ_r ≤ ‖h‖₁ ‖(Λ²ĥ)∗(Λ²ĥ)‖_{ℓ²} ≤ 5 ‖h‖₁ ‖h‖₂ ‖h‖₃`. -/
theorem pair_slow_horizontal_h2 (hs : Adm 2 s) (hs3 : InH 3 s) (hs' : PiS s = s) :
    |pair 2 (PiH s) (PiH (Bsym s s))| ≤
      15 * hnorm 1 (PiH s) * hnorm 2 (PiH s) * hnorm 3 (PiH s) := by
  rw [pair_PiH]
  have hH := admPiH hs
  have hHs : ∀ k, k 2 ≠ 0 → PiH s k = 0 := fun k hk => PiH_fast s hk
  have hH0 : PiH s 0 = 0 := hH.mean
  have hH3 : InH 3 (PiH s) := hs3.PiH
  have hH1 : InH 1 (PiH s) := hH.inH.mono (by norm_num)
  have hH1' : InH (((0 : ℕ) : ℝ) + 1) (PiH s) := by simpa using hH1
  have hH3' : InH (((2 : ℕ) : ℝ) + 1) (PiH s) := by
    norm_num
    exact hH3
  -- `X(p,q) = |p|‖h_p‖ · |q|²‖h_q‖ · |r|²‖h_r‖`
  obtain ⟨hX, hXle⟩ := triple_wtd_bound 1 2 2 (u := PiH s) (v := PiH s) (w := PiH s)
    (by simpa using hH1) hH0 hH3' hHs hH0 hH3' hHs hH0
  -- `M(p,q) = |p|³‖h_p‖ · ‖h_q‖ · |r|²‖h_r‖`
  obtain ⟨hM, -⟩ := triple_wtd_bound 3 0 2 (u := PiH s) (v := PiH s) (w := PiH s)
    (by simpa using hH3) hH0 hH1' hHs hH0 hH3' hHs hH0
  have key := abs_pair_le_of_triads (σ := 2) hs hH (bd_slow_PiH hs') absSq
    (G := fun x => 3 * (wtd 1 (PiH s) x.1 * wtd 2 (PiH s) x.2 * wtd 2 (PiH s) (-(x.1 + x.2))))
    (hX.mul_left 3) hM ?_ ?_
  · have e3 : ((2 : ℕ) : ℝ) + 1 = 3 := by norm_num
    rw [e3, Nat.cast_one, Nat.cast_ofNat] at hXle
    refine key.trans ?_
    rw [tsum_mul_left]
    refine (mul_le_mul_of_nonneg_left hXle (by norm_num)).trans (le_of_eq ?_)
    have h2 := hnorm_nonneg 2 (PiH s)
    have h3 := hnorm_nonneg 3 (PiH s)
    rw [show (25 : ℝ) * hnorm 2 (PiH s) * hnorm 3 (PiH s) * hnorm 2 (PiH s) * hnorm 3 (PiH s)
        = (5 * hnorm 2 (PiH s) * hnorm 3 (PiH s)) ^ 2 by ring,
      Real.sqrt_sq (mul_nonneg (mul_nonneg (by norm_num) h2) h3)]
    ring
  · rintro ⟨p, q⟩
    simp only [Prod.swap_prod_mk]
    refine (norm_triC_le hs' hHs _ p q).trans ?_
    have hb1 := weight_two_bound p q
    have hb2 := weight_two_bound q p
    rw [add_comm q p] at hb2
    have hp := absk_nonneg p
    have hq := absk_nonneg q
    have hr := absk_nonneg (-(p + q))
    have h1 := mul5_le (norm_nonneg (PiH s p)) hq (norm_nonneg (PiH s q))
      (norm_nonneg (PiH s (-(p + q)))) hb1
    have h2 := mul5_le (norm_nonneg (PiH s q)) hp (norm_nonneg (PiH s p))
      (norm_nonneg (PiH s (-(p + q)))) hb2
    refine mul_le_mul_of_nonneg_left ((add_le_add h1 h2).trans (le_of_eq ?_)) (by norm_num)
    simp only [wtd, pow_one, add_comm q p, ← absk_sq]
    ring
  · rintro ⟨p, q⟩
    simp only [Prod.swap_prod_mk]
    refine (norm_triC_le hs' hHs _ p q).trans (le_of_eq ?_)
    have hp := absSq_nonneg p
    have hq := absSq_nonneg q
    have hr := absSq_nonneg (-(p + q))
    simp only [abs_of_nonneg (mul_nonneg hq hr), abs_of_nonneg (mul_nonneg hp hr)]
    simp only [wtd, pow_zero, one_mul, add_comm q p, ← absk_sq]
    ring

/-! ### T3c: `|⟨h·∇ζ, Δ²ζ⟩| ≤ 10 a_h b_ζ c_ζ + 5 b_h b_ζ √(a_ζ c_ζ)` -/

/-- **T3c** (report §2.1 (T3), third line, `c_L = 5`): for a real, mean-zero, divergence-free
slow field `s ∈ H³` with `h = PiH s`, `ζ = PiV s`,
`|⟨h·∇ζ, Δ²ζ⟩| = |pair 2 ζ (Bsym s s)| ≤ 10 ‖h‖₁ ‖ζ‖₂ ‖ζ‖₃ + 5 ‖h‖₂ ‖ζ‖₂ √(‖ζ‖₁ ‖ζ‖₃)`.
The two pieces of the commutator symbol `(|p|² + 2|p||q|)|r|²` give
`∑ |p|²ĥ_p · |q|ζ̂_q · |r|²ζ̂_r ≤ ‖h‖₂ ‖(Λζ̂)∗(Λ²ζ̂)‖ ≤ 5 ‖h‖₂ √(‖ζ‖₁‖ζ‖₂‖ζ‖₂‖ζ‖₃)` and
`2 ∑ |p|ĥ_p · |q|²ζ̂_q · |r|²ζ̂_r ≤ 2 ‖h‖₁ ‖(Λ²ζ̂)∗(Λ²ζ̂)‖ ≤ 10 ‖h‖₁ ‖ζ‖₂ ‖ζ‖₃`. -/
theorem pair_slow_vertical_h2 (hs : Adm 2 s) (hs3 : InH 3 s) (hs' : PiS s = s) :
    |pair 2 (PiV s) (PiV (Bsym s s))| ≤
      10 * hnorm 1 (PiH s) * hnorm 2 (PiV s) * hnorm 3 (PiV s) +
        5 * hnorm 2 (PiH s) * hnorm 2 (PiV s) * Real.sqrt (hnorm 1 (PiV s) * hnorm 3 (PiV s)) := by
  rw [pair_PiV]
  have hV := admPiV hs
  have hH := admPiH hs
  have hWs : ∀ k, k 2 ≠ 0 → PiV s k = 0 := fun k hk => PiV_fast s hk
  have hHs : ∀ k, k 2 ≠ 0 → PiH s k = 0 := fun k hk => PiH_fast s hk
  have hW0 : PiV s 0 = 0 := hV.mean
  have hH0 : PiH s 0 = 0 := hH.mean
  have hV3 : InH 3 (PiV s) := hs3.PiV
  have hH1 : InH 1 (PiH s) := hH.inH.mono (by norm_num)
  have hH1' : InH (((0 : ℕ) : ℝ) + 1) (PiH s) := by simpa using hH1
  have hV2' : InH (((1 : ℕ) : ℝ) + 1) (PiV s) := by
    norm_num
    exact hV.inH
  have hV3' : InH (((2 : ℕ) : ℝ) + 1) (PiV s) := by
    norm_num
    exact hV3
  -- `Y(p,q) = |p|²‖h_p‖ · |q|‖ζ_q‖ · |r|²‖ζ_r‖`
  obtain ⟨hY, hYle⟩ := triple_wtd_bound 2 1 2 (u := PiH s) (v := PiV s) (w := PiV s)
    (by simpa using hH.inH) hH0 hV2' hWs hW0 hV3' hWs hW0
  -- `X(p,q) = |p|‖h_p‖ · |q|²‖ζ_q‖ · |r|²‖ζ_r‖`
  obtain ⟨hX, hXle⟩ := triple_wtd_bound 1 2 2 (u := PiH s) (v := PiV s) (w := PiV s)
    (by simpa using hH1) hH0 hV3' hWs hW0 hV3' hWs hW0
  -- `M(p,q) = |p|³‖ζ_p‖ · ‖h_q‖ · |r|²‖ζ_r‖`
  obtain ⟨hM, -⟩ := triple_wtd_bound 3 0 2 (u := PiV s) (v := PiH s) (w := PiV s)
    (by simpa using hV3) hW0 hH1' hHs hH0 hV3' hWs hW0
  have key := abs_pair_le_of_triads (σ := 2) hs hV (bd_slow_PiV hs') absSq
    (G := fun x => wtd 2 (PiH s) x.1 * wtd 1 (PiV s) x.2 * wtd 2 (PiV s) (-(x.1 + x.2)) +
      2 * (wtd 1 (PiH s) x.1 * wtd 2 (PiV s) x.2 * wtd 2 (PiV s) (-(x.1 + x.2))))
    (hY.add (hX.mul_left 2)) hM ?_ ?_
  · have e2 : ((1 : ℕ) : ℝ) + 1 = 2 := by norm_num
    have e3 : ((2 : ℕ) : ℝ) + 1 = 3 := by norm_num
    rw [e3, Nat.cast_one, Nat.cast_ofNat] at hXle
    rw [e2, e3, Nat.cast_one, Nat.cast_ofNat] at hYle
    refine key.trans ?_
    rw [hY.tsum_add (hX.mul_left 2), tsum_mul_left]
    have a0 := hnorm_nonneg 1 (PiV s)
    have b0 := hnorm_nonneg 2 (PiV s)
    have c0 := hnorm_nonneg 3 (PiV s)
    have bh0 := hnorm_nonneg 2 (PiH s)
    have ah0 := hnorm_nonneg 1 (PiH s)
    have eX : Real.sqrt (25 * hnorm 2 (PiV s) * hnorm 3 (PiV s) * hnorm 2 (PiV s) * hnorm 3 (PiV s))
        = 5 * hnorm 2 (PiV s) * hnorm 3 (PiV s) := by
      rw [show (25 : ℝ) * hnorm 2 (PiV s) * hnorm 3 (PiV s) * hnorm 2 (PiV s) * hnorm 3 (PiV s)
          = (5 * hnorm 2 (PiV s) * hnorm 3 (PiV s)) ^ 2 by ring,
        Real.sqrt_sq (mul_nonneg (mul_nonneg (by norm_num) b0) c0)]
    have eY : Real.sqrt (25 * hnorm 1 (PiV s) * hnorm 2 (PiV s) * hnorm 2 (PiV s) * hnorm 3 (PiV s))
        = 5 * hnorm 2 (PiV s) * Real.sqrt (hnorm 1 (PiV s) * hnorm 3 (PiV s)) := by
      rw [show (25 : ℝ) * hnorm 1 (PiV s) * hnorm 2 (PiV s) * hnorm 2 (PiV s) * hnorm 3 (PiV s)
          = (5 * hnorm 2 (PiV s)) ^ 2 * (hnorm 1 (PiV s) * hnorm 3 (PiV s)) by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg (by norm_num) b0)]
    rw [eX] at hXle
    rw [eY] at hYle
    have hX2 := mul_le_mul_of_nonneg_left hXle (by norm_num : (0 : ℝ) ≤ 2)
    linarith
  · rintro ⟨p, q⟩
    simp only [Prod.swap_prod_mk]
    refine (norm_triC_le hs' hWs _ p q).trans ?_
    have hb1 := weight_two_bound p q
    have hb2 := weight_two_bound q p
    rw [add_comm q p] at hb2
    have hp := absk_nonneg p
    have hq := absk_nonneg q
    have hr := absk_nonneg (-(p + q))
    have h1 := mul5_le (norm_nonneg (PiH s p)) hq (norm_nonneg (PiV s q))
      (norm_nonneg (PiV s (-(p + q)))) hb1
    have h2 := mul5_le (norm_nonneg (PiH s q)) hp (norm_nonneg (PiV s p))
      (norm_nonneg (PiV s (-(p + q)))) hb2
    refine mul_le_mul_of_nonneg_left ((add_le_add h1 h2).trans (le_of_eq ?_)) (by norm_num)
    simp only [wtd, pow_one, add_comm q p, ← absk_sq]
    ring
  · rintro ⟨p, q⟩
    simp only [Prod.swap_prod_mk]
    refine (norm_triC_le hs' hWs _ p q).trans (le_of_eq ?_)
    have hp := absSq_nonneg p
    have hq := absSq_nonneg q
    have hr := absSq_nonneg (-(p + q))
    simp only [abs_of_nonneg (mul_nonneg hq hr), abs_of_nonneg (mul_nonneg hp hr)]
    simp only [wtd, pow_zero, one_mul, add_comm q p, ← absk_sq]
    ring

end OVNS
