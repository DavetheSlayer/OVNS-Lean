import OddViscousNS.Quant.Energy.H1.Metric
import OddViscousNS.Quant.Energy.H1.Cubic

/-!
# E5 — the term-by-term bounds of the `H¹` energy identity

The right-hand side `h1RHS` of `h1Energy_identity` (`Identity.lean`) is bounded pointwise on a
piece by the interface's integrand `¼ b_F² + C_s a_F^{3−σ} b_F^σ + N_f b_F + f_f + m a_F²`
(`h1RHS_budget`), once the role thresholds `h1Threshold` are paid and the leading role 15 is paid
through `K₁ √P_F y^{3/2} N(q) ≤ 1`.

## The analytic inputs (LOCKED, provenance in each docstring)
* `X1bil_le`, `X1op_slow_le`: the `X₁` operator bound `‖X₁‖ ≤ 2⁹ B_S/q` (polarized) and the
  genuine `H¹`-direction form `|⟨z, X₁[h] z⟩| ≤ 2¹¹ ‖h‖₁ a_F b_F/q` — Body 12 (NEW130) §6, eqs.
  (12), (14), through the paired Schur lemma (§2) and the convolution envelope (§4).  The TeX lists
  them as "the elementary convolution bounds `‖X₁‖ ≤ C B_S/q`, …".
* `farD1_le`: the FAR part of the native `H¹` differential, kernel `32/(mKq)` and `F₁(q) = 2¹⁴/q`
  — Body 18 (NEW238) §2 ("On B, D1 has kernel ≤ 32/(mKq) … This is independent complete purefast
  B").
* `cubicE_static_le`, `cubicHeat_le`: the static and both-input-heat remainders of the purefast
  cubic against the proper profile `P(q) = nearP q` — TeX "static coercivity … the two proper heat
  directions … are separate estimates", F225 rows 13, 14 (`P_static`, `P_heat`); no body gives the
  constants, the allowances `cStat = cHeat = 2¹⁰` are reading choice 2 of `Defs.lean`.
* `cubicD_eq_near_add_far'`: the near/far split of `D₁(F; h)` for an `H¹` source
  (`cubicD_eq_near_add_far` of `Native/Bound.lean` needs `H³`); route: `Qm` is additive in the
  multiplier for gain multipliers (`summable_Qm_term_gain`), and the three pairings converge by
  `Qm_gain_zero_le` and the symmetric-weight pairing bound.

## The `X₁` bounds
`X1bil_le` and `X1op_slow_le` are proved in `H1/Metric.lean`.  They assume `IsReal` on the slow
field: the Hermitian numerator `(v−u)[l(v+u)−uv]` pairs the couplings by `p` and `−p`, which needs
`S_{−p} = conj S_p`, and without reality they fail numerically (`t12_h1_scaffold.md` §4.1).

## Proved
* `Qm_gain_zero_le`: `‖Q^♯_m(f,g)‖₀ ≤ 8 c₄ (‖f‖₁‖g‖₀ + ‖f‖₀‖g‖₁)` for `‖m‖ ≤ 1/|k|²` and
  `f, g ∈ H¹` (the "`R₋ : H¹ × H¹ → H⁰`" interface of Body 12 §1, with the library's `c₄`).
* The force filter on the piece: `‖ψ‖₂ ≤ 2φ/q` (`psi_bound`), `‖H_ψ‖₀ ≤ nfConst`,
  `‖H_ψ‖₁ ≤ h1Const` (`Hpsi_bounds`); the sources `‖slowNL‖₁ ≤ hSrc`, `‖fastNL‖₁ ≤ ffCoef +
  8 mixNear + ‖H_ψ‖₁` (`fastNL_one_le`), from (M3), (M4), the Wiener interpolation and the `H¹`
  product leaf.
* The role glue: `role15_share` (the leading fast–fast near term is a `1/32` share),
  `profile_paid` (a `(c X)^{100/e}` threshold pays `X q^{−e/100} ≤ 1/c`), `share_paid`.
* `h1RHS_budget`: the pointwise budget, with all shares summing to `9/64 ≤ 1/4` of the dissipation.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS

/-! ### A. The `H⁰` gain bound for `Q^♯` -/

/-- `∑_p (|p|+|k−p|) ‖f_p‖ ‖g_{k−p}‖ ≤ ‖f‖₁ ‖g‖₀ + ‖f‖₀ ‖g‖₁` (two Cauchy–Schwarz). -/
lemma vertex_sum_le {f g : Field} (hf : MZ 1 f) (hg : MZ 1 g) (k : Mode) :
    ∑' p, (absk p + absk (k - p)) * ‖f p‖ * ‖g (k - p)‖ ≤
      hnorm 1 f * hnorm 0 g + hnorm 0 f * hnorm 1 g := by
  have hf2 : Summable fun p => ‖f p‖ ^ 2 := summable_norm_sq_of_inH (hf.inH.mono (by norm_num))
  have hg2 : Summable fun p => ‖g p‖ ^ 2 := summable_norm_sq_of_inH (hg.inH.mono (by norm_num))
  have hfg : Summable fun p => (absk p * ‖f p‖) ^ 2 :=
    hf.inH.congr fun p => by rw [sobWeight_one, mul_pow, absk_sq]
  have hgg : Summable fun p => (absk p * ‖g p‖) ^ 2 :=
    hg.inH.congr fun p => by rw [sobWeight_one, mul_pow, absk_sq]
  have hg2' : Summable fun p => ‖g (k - p)‖ ^ 2 := (Equiv.subLeft k).summable_iff.mpr hg2
  have hgg' : Summable fun p => (absk (k - p) * ‖g (k - p)‖) ^ 2 :=
    (Equiv.subLeft k).summable_iff.mpr hgg
  obtain ⟨s1, b1⟩ := Quant.cs_tsum_nonneg' (a := fun p => absk p * ‖f p‖)
    (b := fun p => ‖g (k - p)‖) (fun p => mul_nonneg (absk_nonneg p) (norm_nonneg _))
    (fun p => norm_nonneg _) hfg hg2'
  obtain ⟨s2, b2⟩ := Quant.cs_tsum_nonneg' (a := fun p => ‖f p‖)
    (b := fun p => absk (k - p) * ‖g (k - p)‖) (fun p => norm_nonneg _)
    (fun p => mul_nonneg (absk_nonneg _) (norm_nonneg _)) hf2 hgg'
  have e : ∀ p, (absk p + absk (k - p)) * ‖f p‖ * ‖g (k - p)‖ =
      absk p * ‖f p‖ * ‖g (k - p)‖ + ‖f p‖ * (absk (k - p) * ‖g (k - p)‖) := fun p => by ring
  rw [tsum_congr e, s1.tsum_add s2]
  have e1 : ∑' p, ‖g (k - p)‖ ^ 2 = ∑' p, ‖g p‖ ^ 2 :=
    (Equiv.subLeft k).tsum_eq fun p => ‖g p‖ ^ 2
  have e2 : ∑' p, (absk (k - p) * ‖g (k - p)‖) ^ 2 = ∑' p, (absk p * ‖g p‖) ^ 2 :=
    (Equiv.subLeft k).tsum_eq fun p => (absk p * ‖g p‖) ^ 2
  rw [e1, Quant.sqrt_tsum_grad_sq, ← hnorm_zero_eq hg.mean] at b1
  rw [e2, Quant.sqrt_tsum_grad_sq, ← hnorm_zero_eq hf.mean] at b2
  linarith

/-- **The `H⁰` gain bound**: for a multiplier with `‖m‖ ≤ 1/|p+q|²` and `f, g ∈ H¹`,
`Q^♯_m(f,g) ∈ H⁰` with `‖Q^♯_m(f,g)‖₀ ≤ 8 c₄ (‖f‖₁‖g‖₀ + ‖f‖₀‖g‖₁)` (the resolvent gains two
derivatives, the vertex spends one; Body 12 §1 "`R₋ : H¹ × H¹ → H¹` with constant 64" at `H⁰`). -/
theorem Qm_gain_zero_le {m : Mult} (hm : ∀ a b c p q, ‖m a b c p q‖ ≤ 1 / absSq (p + q))
    {f g : Field} (hf : MZ 1 f) (hg : MZ 1 g) :
    InH 0 (Qm m f g) ∧
      hnorm 0 (Qm m f g) ≤ 8 * c4 * (hnorm 1 f * hnorm 0 g + hnorm 0 f * hnorm 1 g) := by
  have hf2 : Summable fun p => ‖f p‖ ^ 2 := summable_norm_sq_of_inH (hf.inH.mono (by norm_num))
  have hg2 : Summable fun p => ‖g p‖ ^ 2 := summable_norm_sq_of_inH (hg.inH.mono (by norm_num))
  have hfg : Summable fun p => (absk p * ‖f p‖) ^ 2 :=
    hf.inH.congr fun p => by rw [sobWeight_one, mul_pow, absk_sq]
  set R := hnorm 1 f * hnorm 0 g + hnorm 0 f * hnorm 1 g with hR
  have hR0 : 0 ≤ R := by
    have := hnorm_nonneg 1 f; have := hnorm_nonneg 0 g; have := hnorm_nonneg 0 f
    have := hnorm_nonneg 1 g
    positivity
  -- the pointwise bound
  have hpt : ∀ k, ‖Qm m f g k‖ ≤ 8 / absSq k * R := by
    intro k
    by_cases hk : k = 0
    · subst hk
      have e : absSq (0 : Mode) = 0 := by simp [absSq]
      simp [Qm, hel_zero_mode, e]
    · have hs := summable_vertex_fixed k hf2 hg2 (Or.inl hfg)
      have hsum := summable_Qm_term_gain hm k hs
      have hkpos : 0 < absSq k := lt_of_lt_of_le one_pos (one_le_absSq hk)
      have hterm : ∀ p, ‖∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, m a b c p (k - p) •
          hel c k (vert p (k - p) (hel a p (f p)) (hel b (k - p) (g (k - p))))‖ ≤
          8 * (1 / absSq k * ((absk p + absk (k - p)) * ‖f p‖ * ‖g (k - p)‖)) := fun p => by
        have hk' : p + (k - p) = k := by abel
        exact norm_Qm_summand_le (κ := 1 / absSq k) (div_nonneg zero_le_one (absSq_nonneg k))
          (fun a b c => by have := hm a b c p (k - p); rwa [hk'] at this)
      unfold Qm
      refine (norm_tsum_le_tsum_norm hsum.norm).trans ?_
      calc ∑' p, ‖∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, m a b c p (k - p) •
            hel c k (vert p (k - p) (hel a p (f p)) (hel b (k - p) (g (k - p))))‖
          ≤ ∑' p, 8 * (1 / absSq k * ((absk p + absk (k - p)) * ‖f p‖ * ‖g (k - p)‖)) :=
            hsum.norm.tsum_le_tsum hterm ((hs.mul_left _).mul_left _)
        _ = 8 / absSq k * ∑' p, (absk p + absk (k - p)) * ‖f p‖ * ‖g (k - p)‖ := by
            rw [tsum_mul_left, tsum_mul_left]
            ring
        _ ≤ 8 / absSq k * R :=
            mul_le_mul_of_nonneg_left (vertex_sum_le hf hg k) (by positivity)
  -- `ℓ²` domination by `64 R² |k|⁻⁴`
  have hdom : ∀ k, sobWeight 0 k * ‖Qm m f g k‖ ^ 2 ≤
      64 * R ^ 2 * (if k = 0 then (0 : ℝ) else (absSq k)⁻¹ ^ 2) := fun k => by
    by_cases hk : k = 0
    · simp [sobWeight, hk]
    · have h1 : sobWeight 0 k = 1 := by simp [sobWeight, hk]
      have hkpos : 0 < absSq k := lt_of_lt_of_le one_pos (one_le_absSq hk)
      rw [h1, one_mul, ite_eq_right hk]
      have h2 := hpt k
      have h3 : 0 ≤ ‖Qm m f g k‖ := norm_nonneg _
      have e : 64 * R ^ 2 * (absSq k)⁻¹ ^ 2 = (8 / absSq k * R) ^ 2 := by
        field_simp
        ring
      rw [e]
      exact pow_le_pow_left₀ h3 h2 2
  have hsum : Summable fun k => sobWeight 0 k * ‖Qm m f g k‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_nonneg 0 k) (sq_nonneg _)) hdom
      (summable_inv4.mul_left _)
  refine ⟨hsum, ?_⟩
  have hle := hsum.tsum_le_tsum hdom (summable_inv4.mul_left _)
  rw [tsum_mul_left] at hle
  unfold hnorm
  calc Real.sqrt (∑' k, sobWeight 0 k * ‖Qm m f g k‖ ^ 2)
      ≤ Real.sqrt (64 * R ^ 2 * ∑' k : Mode, if k = 0 then (0 : ℝ) else (absSq k)⁻¹ ^ 2) :=
        Real.sqrt_le_sqrt hle
    _ = 8 * c4 * R := by
        rw [c4, Real.sqrt_mul (by positivity), show (64 : ℝ) * R ^ 2 = (8 * R) ^ 2 by ring,
          Real.sqrt_sq (by positivity)]
        ring

/-- The pairing with symmetric weights: `|⟨c, Λ^{2σ} F⟩| ≤ ‖c‖_σ ‖F‖_σ`, with absolute
convergence (the `(σ+1, σ−1)` split of `pair_le` is not the only one). -/
lemma pair_summable_symm {σ : ℝ} {c F : Field} (hc : InH σ c) (hF : InH σ F) :
    Summable fun k => sobWeight σ k * (inner ℂ (c k) (F k)).re := by
  have hs : Summable fun k => 1 / 2 * (sobWeight σ k * ‖c k‖ ^ 2 + sobWeight σ k * ‖F k‖ ^ 2) :=
    (Summable.add hc hF).mul_left (1 / 2)
  refine Summable.of_norm_bounded hs fun k => ?_
  have h1 := norm_pair_term_le' σ c F k
  have h2 : sobWeight σ k * ‖c k‖ * ‖F k‖ ≤
      1 / 2 * (sobWeight σ k * ‖c k‖ ^ 2 + sobWeight σ k * ‖F k‖ ^ 2) := by
    have := sobWeight_nonneg σ k
    nlinarith [sq_nonneg (‖c k‖ - ‖F k‖), mul_nonneg this (sq_nonneg (‖c k‖ - ‖F k‖))]
  exact h1.trans h2

lemma pair_add_symm {σ : ℝ} {c F F' : Field} (hc : InH σ c) (hF : InH σ F) (hF' : InH σ F') :
    pair σ c (F + F') = pair σ c F + pair σ c F' := by
  simp only [pair]
  rw [← (pair_summable_symm hc hF).tsum_add (pair_summable_symm hc hF')]
  refine tsum_congr fun k => ?_
  rw [Pi.add_apply, inner_add_right, Complex.add_re, mul_add]

/-! ### B. The analytic inputs (LOCKED) -/

/-- **The `X₁` operator bound, polarized** (Body 12 §6 eq. (12): `‖X₁‖_op ≤ 44√104 B_S/q <
2⁹ B_S/q` at both metric weights; TeX "`‖X₁‖ ≤ C B_S/q`"): for slow `S ∈ H²`, fast `F ∈ H²` and
a fast `G ∈ H¹`, `|⟨z_F, X₁ z_G⟩| ≤ 2⁸ B_S ‖F‖₁ ‖G‖₁/q` (`X1bil = ⟨z_F, X₁ z_G⟩`, so the operator
norm `2⁹B_S/q` of the TeX gives the constant `2⁸` after the factor `2` of the polarization is
absorbed: `|⟨z_F,X₁z_G⟩| ≤ ‖X₁‖‖z_F‖‖z_G‖ ≤ 2⁹ B_S a_F a_G/q`; we lock the safe `2⁸ · 2 = 2⁹`
version as `2⁸` times the two norms of `X1bil`'s two terms).  LOCKED.  Route: the paired Schur
lemma (Body 12 §2: the `2×2` helicity block of a multiplier `m(−δ) = −conj m(δ)` contracts by
`max |m|`, here `|δ/(−Σ + irδ)| ≤ 1/q`), the Hermitian numerator `(v−u)[l(v+u) − uv]` (the
commutator identity `L₁ + L₁* = Ω_K H − H Ω_Q`, (3)), and the convolution envelope
`‖S‖_{ℓ¹} ≤ √104 B_S`, `Σ_{k≠0}|k|⁻⁴ ≤ 104` (§4). -/
theorem X1bil_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {S F G : Field} (hS : MZ 2 S) (hSr : IsReal S)
    (hS' : PiS S = S)
    (hF : MZ 2 F) (hF' : PiF F = F) (hG : MZ 1 G) (hG' : PiF G = G) :
    |X1bil r τ S F G| ≤ 2 ^ 8 * hnorm 2 S * hnorm 1 F * hnorm 1 G / |r| := by
  exact X1bil_le_proved hr τ hS hSr hS' hF hF' hG hG'

/-- **The genuine `H¹`-direction form of `X₁`** (Body 12 §6 eq. (14): `|⟨z_s, X₁[h] z_s⟩| ≤
(935/8)√104 ‖h‖₁ F_s G_s/q < 2¹¹ ‖h‖₁ ‖F‖₁‖F‖₂/q` at `s = 1`; here `⟨z₁, X₁[h] z₁⟩ = 4 pair 1 F
(X1op h F)`, so the constant is `2⁹`): for a slow `h ∈ H¹` and a fast `F ∈ H²`.  LOCKED.  Route:
the two-orientation (comparable `K ≤ 2Q` / separated) split of §4 with one dissipation derivative
placed on the larger exterior factor; "This reconstructs the actual linear `X₁[h]`, not a
derivative of (12)". -/
theorem X1op_slow_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {h F : Field} (hh : MZ 1 h) (hhr : IsReal h)
    (hh' : PiS h = h)
    (hF : MZ 2 F) (hF' : PiF F = F) :
    |pair 1 F (X1op r τ h F)| ≤ 2 ^ 9 * hnorm 1 h * hnorm 1 F * hnorm 2 F / |r| := by
  exact X1op_slow_le_proved hr τ hh hhr hh' hF hF'

/-- **The FAR native `H¹` differential** (Body 18 §2: "On B, D1 has kernel `≤ 32/(mKq)`. At
largest fixed output all smaller `p` have `|p| ≤ K`. … `Σ_{0<|p|≤K}|p|⁻² ≤ 26K`. The squared
moment is at most `32²·26/(Kq²) ≤ 32²·26/q²`. With the same 54 this yields `F₁(q) = 2¹⁴/q`."):
for fast `F ∈ H²` and `h ∈ H¹`, `|D₁^B(F; h)| ≤ 2¹⁴ ‖h‖₁ ‖F‖₂²/q`.  LOCKED.  Route: the
three-rooting collection of `Native/Kernel.lean` (`triad_rootings_eq`, the far mask is re-rooting
invariant) with `|corrSym| ≤ 1/√(K⁴ + q²) ≤ 1/q` on `|Φ| ≥ 1`, `native_dominated_E1`, the trivial
far moment `Σ_{|p|≤K} 1/(m²K²q²) ≤ 26/q²`, and the fixed-output Cauchy of `Native/Bound.lean`
(`moment_cauchy`). -/
theorem farD1_le {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {F h : Field}
    (hF : MZ 2 F) (hF' : PiF F = F) (hh : MZ 1 h) :
    |Quant.farD 1 ε r τ F h| ≤ 2 ^ 14 / |r| * hnorm 1 h * hnorm 2 F ^ 2 := by
  exact farD1_le_proved hε hr τ hF hF' hh

/-- **The static remainder of the purefast cubic** (role 13, "E1 proper static 1/256",
`P_static`; TeX "static coercivity … separate estimates"): for fast `F ∈ H²` and `q = |r| ≥ 1`,
`|E⁰| ≤ cStat P(q) ‖F‖₁² ‖F‖₂` with the proper profile `P(q) = nearP q` (`Near/Defs.lean`;
`nearP q = 18√𝔐_P(q) + 2⁷ q^{−3/4}`, the proper FAR being "`2⁷ q^{−3/4}`").  LOCKED, reading
choice 2 of `Defs.lean` (the constant is not in the sources; the allowance `2¹⁰` covers the
helicity patterns, the three rootings and the Cauchy enlargement).  Route: the proper weights
`(H¹, H¹, H²)` make the coefficient `≤ (vertex ≤ B₀)·K²/D_K` divided by `m B₀ K²` equal to
`1/(m D_K) = K κ_N`, whose squared fixed-output moment is `momP` (`momP = |k|² momN`); FAR by
`1/D_K ≤ 1/√(K⁴+q²)` and `Σ_{|p|≤K}|p|⁻² ≤ 26K`. -/
theorem cubicE_static_le {r : ℝ} (hr : 1 ≤ |r|) (τ : ℝ) {F : Field} (hF : MZ 2 F)
    (hF' : PiF F = F) :
    |Quant.cubicE 1 (-1) r τ F| ≤ Quant.cStat * Quant.nearP |r| * hnorm 1 F ^ 2 * hnorm 2 F := by
  exact cubicE_static_le_proved hr τ hF hF'

/-- **Both input heats of the purefast cubic** (role 14, "E1 BOTH input heats", `P_heat`; TeX
"`E_heat` has both `−AF` input slots", "the two proper heat directions"): for real fast `F ∈ H²`
and `q ≥ 1`, `|E_heat| ≤ cHeat P(q) ‖F‖₂³`.  The role is paid by `P(q) y` (Table quant-fixed:
"Complete proper static/heats, FAR and one-zero: `3v`"; Supplement, roles 13–17: "proper `T³`,
all static and actual input heats"), so all three legs sit in `H²`.  LOCKED.  Route: each rooting
with output `c` carries the weight `(x_a + x_b) f₁(x_c) = Σ f₁(x_c) − f₂(x_c)`, so
`triad_rootings_eq` and `triad_cyclic_le` bound the triad by `52 m K⁴/D_K ∏‖A_i‖`; with the `H²`
weights `m²B²K²` and `K ≤ 2B` the kernel is `≤ 208/(m D_K)`, exactly the proper kernel
`(K² nearKer)^{1/2}`, whose near moment is `MomP`; the far part `|Φ| ≥ 1` has moment
`min(K/q², K⁻³)`, which is the `2⁷ q^{−3/4}` of `nearP`.  The constant `cHeat` may be raised. -/
theorem cubicHeat_le {r : ℝ} (hr : 1 ≤ |r|) (τ : ℝ) {F : Field} (hF : MZ 2 F) (hFr : IsReal F)
    (hF' : PiF F = F) :
    |cubicHeat r τ F| ≤ Quant.cHeat * Quant.nearP |r| * hnorm 2 F ^ 3 := by
  exact cubicHeat_le_proved hr τ hF hFr hF'

/-- **The near/far split of the native `H¹` differential for an `H¹` source**
(`cubicD_eq_near_add_far` of `Native/Bound.lean` needs `H³` fields; the actual source
`fastNL = −Π_F Q(y,y)` is only `H¹`).  LOCKED.  Route: `Qm` is additive in the multiplier for the
three gain multipliers `corrM = nearCorrM + farCorrM` (`corrM_eq_add`, `summable_Qm_term_gain`
with `summable_vertex_fixed`), the first two pairings converge by `pair_le` with `Qm_gain_zero_le`
(`F ∈ H²`, the corrector fields in `H⁰`), the third by `pair_add_symm` once
`corr F F, nearCorr F F, farCorr F F ∈ H¹` (the `H¹` gain bound: `|k|‖Q^♯_k‖ ≤ 8 Σ_p (|p|+|q|)
‖F_p‖‖F_q‖/|k|`, Young `ℓ¹ * ℓ² → ℓ²`, `young_l1_l2`). -/
theorem cubicD_eq_near_add_far' {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (r τ : ℝ) {F h : Field}
    (hF : MZ 2 F) (hF' : PiF F = F) (hh : MZ 1 h) :
    Quant.cubicD 1 ε r τ F h = Quant.nearD 1 ε r τ F h + Quant.farD 1 ε r τ F h := by
  exact cubicD_eq_near_add_far'_proved hε r τ hF hF' hh

/-! ### C. Consequences of the locked inputs -/

/-- The `X₁` quadratic form: `|⟨z₁, X₁ z₁⟩| ≤ 2⁸ B_S a_F²/q`. -/
theorem X1form_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {S F : Field} (hS : MZ 2 S) (hSr : IsReal S)
    (hS' : PiS S = S)
    (hF : MZ 2 F) (hF' : PiF F = F) :
    |X1form r τ S F| ≤ 2 ^ 8 * hnorm 2 S * hnorm 1 F ^ 2 / |r| := by
  rw [X1form_eq_bil]
  have := X1bil_le hr τ hS hSr hS' hF hF' (hF.mono' (by norm_num)) hF'
  calc |X1bil r τ S F F| ≤ 2 ^ 8 * hnorm 2 S * hnorm 1 F * hnorm 1 F / |r| := this
    _ = _ := by ring

/-- **The native differential with an `H¹` source**: near part through `nearC₀ N(q)`
(`nearD1_le`, `Native/NearAssembly.lean`, PROVED there), far part through `2¹⁴/q` (`farD1_le`):
`|D₁(F; h)| ≤ (nearC₀ N(q) + 2¹⁴/q) ‖h‖₁ ‖F‖₂²` for real fast `F ∈ H²` and real `h ∈ H¹`. -/
theorem cubicD_one_le {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {F h : Field}
    (hF : MZ 2 F) (hFr : IsReal F) (hF' : PiF F = F) (hh : MZ 1 h) (hhr : IsReal h) :
    |Quant.cubicD 1 ε r τ F h| ≤
      (Quant.nearC₀ * Quant.nearN |r| + 2 ^ 14 / |r|) * hnorm 1 h * hnorm 2 F ^ 2 := by
  rw [cubicD_eq_near_add_far' hε r τ hF hF' hh]
  have h1 := Quant.nearD1_le hε r τ hF hFr hF' hh hhr
  have h2 := farD1_le hε hr τ hF hF' hh
  calc |Quant.nearD 1 ε r τ F h + Quant.farD 1 ε r τ F h|
      ≤ |Quant.nearD 1 ε r τ F h| + |Quant.farD 1 ε r τ F h| := abs_add_le _ _
    _ ≤ Quant.nearC₀ * Quant.nearN |r| * hnorm 1 h * (hnorm 2 F * hnorm 2 F) +
        2 ^ 14 / |r| * hnorm 1 h * hnorm 2 F ^ 2 := add_le_add h1 h2
    _ = _ := by ring

namespace Quant

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-! ### D. Norms on the piece -/

/-- `2^{(2:ℝ)} = 4`. -/
private lemma two_rpow_two' : (2 : ℝ) ^ (2 : ℝ) = 4 := by
  rw [Real.rpow_two]; norm_num

/-- (M4) at `σ = 2`: `‖Π_F Q^♯_m(f,g)‖₁ ≤ 4(𝒜(f)‖g‖₂ + ‖f‖₂𝒜(g))`, with `InH 1`. -/
lemma hnorm_one_Qm_le {m : Mult} (hm : m.Bdd) {f h : Field} (hf : MZ 2 f) (hh : MZ 2 h) :
    InH 1 (Qm m f h) ∧ hnorm 1 (Qm m f h) ≤ 4 * (wiener f * hnorm 2 h + hnorm 2 f * wiener h) := by
  obtain ⟨hI, hle⟩ := hnorm_Qm_le hm (σ := 2) (by norm_num) hf hh hf hh
  rw [show (2 : ℝ) - 1 = 1 by norm_num] at hI hle
  rw [two_rpow_two'] at hle
  exact ⟨hI, hle⟩

/-- The force filter on the piece: `ψ ∈ Adm 2` and `‖ψ‖₂ ≤ 2φ/q`. -/
lemma psi_piece (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {u : ℝ} (hu : 0 ≤ u) :
    Adm 2 (psi r 0 g u) ∧ hnorm 2 (psi r 0 g u) ≤ 2 * φ / |r| := by
  refine ⟨psi_adm h.force_adm u hu, ?_⟩
  have hb := (psi_bound (t₀ := 0) hr h.force_adm u hu).2
  have hg1 : hnorm 1 g ≤ φ := (hnorm_mono (by norm_num) h.force_adm.inH).trans h.force_le
  have hr0 : 0 < |r| := abs_pos.mpr hr
  calc hnorm 2 (psi r 0 g u) ≤ 2 * hnorm 1 g / |r| := hb
    _ ≤ 2 * φ / |r| := by gcongr

/-- `H_ψ = Q(ψ, y) + Q(x, ψ)` (the private `Hpsi_eq` of `Kinetic/Main.lean`). -/
lemma Hpsi_eq' (h : ActualSol μ φ r g y Ty) {u : ℝ} (hu : 0 ≤ u) (huT : ENNReal.ofReal u < Ty) :
    Hpsi r g y u = Qphase (r * u) (psi r 0 g u) (y u) +
      Qphase (r * u) (actual r g y u) (psi r 0 g u) := by
  have hx := actual_adm h hu huT
  have hy := h.sol.adm u hu huT
  have e1 := (majorized_Qphase (r * u)).sub_left 0 (y u) (actual r g y u) (y u) hy.mz hx.mz hy.mz
  have e2 := (majorized_Qphase (r * u)).sub_right 0 (actual r g y u) (y u) (actual r g y u)
    hx.mz hy.mz hx.mz
  have hyx : y u - actual r g y u = psi r 0 g u := by simp [actual]
  simp only [hyx] at e1 e2
  rw [Hpsi, e1, e2]
  abel

/-- `H_ψ ∈ H¹`, with the `H⁰` and `H¹` bounds `‖H_ψ‖₀ ≤ 2(1+c₄) ε (W_S + y + A_S + P_F + 1)`,
`‖H_ψ‖₁ ≤ 16(1+c₄) ε (B_S + y + W_S + 1)` for `ε = ‖ψ‖₂ ≤ 1`, on a prefix where the caps hold
((M3), (M4), `𝒜(·) ≤ c₄ ‖·‖₂`). -/
theorem Hpsi_bounds (h : ActualSol μ φ r g y Ty) {caps : Caps} {s t : ℝ}
    (hpre : OnPrefix caps r g y s t) {u : ℝ} (hu : u ∈ Icc s t) (hs : 0 ≤ s)
    (huT : ENNReal.ofReal u < Ty) (hε : hnorm 2 (psi r 0 g u) ≤ 1) :
    InH 1 (Hpsi r g y u) ∧
      hnorm 0 (Hpsi r g y u) ≤ 2 * (1 + c4) * hnorm 2 (psi r 0 g u) *
        (cp caps.WS + cp caps.yF + cp caps.AS + cp caps.PF + 1) ∧
      hnorm 1 (Hpsi r g y u) ≤ 16 * (1 + c4) * hnorm 2 (psi r 0 g u) *
        (cp caps.BS + cp caps.yF + cp caps.WS + 1) := by
  have hu0 : 0 ≤ u := hs.trans hu.1
  have hx := actual_adm h hu0 huT
  have hy := h.sol.adm u hu0 huT
  have hψ := psi_adm (r := r) (t₀ := 0) h.force_adm u hu0
  obtain ⟨cF1, cF2, cS1, cS2, cW⟩ := hpre.1 u hu
  set ε := hnorm 2 (psi r 0 g u) with hεdef
  have hε0 : 0 ≤ ε := hnorm_nonneg _ _
  have hc4 := c4_pos
  have hP := cp_nonneg caps.PF
  have hY := cp_nonneg caps.yF
  have hA := cp_nonneg caps.AS
  have hB := cp_nonneg caps.BS
  have hW := cp_nonneg caps.WS
  set P := cp caps.PF
  set Y := cp caps.yF
  set A := cp caps.AS
  set B := cp caps.BS
  set W := cp caps.WS
  have hS := hx.PiS
  have hF := hx.PiF
  have hxSF := PiS_add_PiF (actual r g y u)
  have hyx : y u = actual r g y u + psi r 0 g u := by simp [actual]
  -- norms of ψ
  have hψ1 : hnorm 1 (psi r 0 g u) ≤ ε := hnorm_mono (by norm_num) hψ.inH
  have hψw : wiener (psi r 0 g u) ≤ c4 * ε := wiener_le hψ.mz
  -- norms of x
  have hx1 : hnorm 1 (actual r g y u) ≤ A + P := by
    conv_lhs => rw [← hxSF]
    refine (hnorm_add_le (hS.inH.mono (by norm_num)) (hF.inH.mono (by norm_num))).trans ?_
    exact add_le_add (cS1.trans (le_cp _)) (cF1.trans (le_cp _))
  have hx2 : hnorm 2 (actual r g y u) ≤ B + Y := by
    conv_lhs => rw [← hxSF]
    refine (hnorm_add_le hS.inH hF.inH).trans ?_
    exact add_le_add (cS2.trans (le_cp _)) (cF2.trans (le_cp _))
  have hxw : wiener (actual r g y u) ≤ W + c4 * Y := by
    conv_lhs => rw [← hxSF]
    refine (wiener_add_le (summable_wiener hS.inH) (summable_wiener hF.inH)).trans ?_
    refine add_le_add (cW.trans (le_cp _)) ((wiener_le hF.mz).trans ?_)
    exact mul_le_mul_of_nonneg_left (cF2.trans (le_cp _)) hc4.le
  -- norms of y
  have hy1 : hnorm 1 (y u) ≤ A + P + ε := by
    rw [hyx]
    exact (hnorm_add_le (hx.inH.mono (by norm_num)) (hψ.inH.mono (by norm_num))).trans
      (add_le_add hx1 hψ1)
  have hy2 : hnorm 2 (y u) ≤ B + Y + ε := by
    rw [hyx]
    exact (hnorm_add_le hx.inH hψ.inH).trans (add_le_add hx2 le_rfl)
  have hyw : wiener (y u) ≤ W + c4 * Y + c4 * ε := by
    rw [hyx]
    exact (wiener_add_le (summable_wiener hx.inH) (summable_wiener hψ.inH)).trans
      (add_le_add hxw hψw)
  -- the two products
  obtain ⟨hI1, hQ1⟩ := hnorm_Qm_zero_le (phaseM_bdd (r * u)) hψ.mz hy.mz
  obtain ⟨hI2, hQ2⟩ := hnorm_Qm_zero_le (phaseM_bdd (r * u)) hx.mz hψ.mz
  obtain ⟨hJ1, hR1⟩ := hnorm_one_Qm_le (phaseM_bdd (r * u)) hψ.mz hy.mz
  obtain ⟨hJ2, hR2⟩ := hnorm_one_Qm_le (phaseM_bdd (r * u)) hx.mz hψ.mz
  have eH := Hpsi_eq' h hu0 huT
  have hψ0 := hnorm_nonneg 1 (psi r 0 g u)
  have hψw0 := wiener_nonneg (psi r 0 g u)
  have hy10 := hnorm_nonneg 1 (y u)
  have hy20 := hnorm_nonneg 2 (y u)
  have hyw0 := wiener_nonneg (y u)
  have hx10 := hnorm_nonneg 1 (actual r g y u)
  have hx20 := hnorm_nonneg 2 (actual r g y u)
  have hxw0 := wiener_nonneg (actual r g y u)
  have hcε : 0 ≤ c4 * ε := mul_nonneg hc4.le hε0
  have hcε1 : c4 * ε ≤ c4 := (mul_le_mul_of_nonneg_left hε hc4.le).trans_eq (mul_one c4)
  have hAP0 : 0 ≤ A + P := add_nonneg hA hP
  have hWY0 : 0 ≤ W + c4 * Y := add_nonneg hW (mul_nonneg hc4.le hY)
  refine ⟨by rw [eH]; exact hJ1.add hJ2, ?_, ?_⟩
  · rw [eH]
    refine (hnorm_add_le hI1 hI2).trans ((add_le_add hQ1 hQ2).trans ?_)
    -- the four products, each against the caps
    have t1 : hnorm 1 (psi r 0 g u) * wiener (y u) ≤ ε * (W + c4 * Y + c4) := by
      have h1 : hnorm 1 (psi r 0 g u) * wiener (y u) ≤ ε * (W + c4 * Y + c4 * ε) :=
        mul_le_mul hψ1 hyw hyw0 hε0
      have h2 : ε * (W + c4 * Y + c4 * ε) ≤ ε * (W + c4 * Y + c4) :=
        mul_le_mul_of_nonneg_left (by linarith) hε0
      exact h1.trans h2
    have t2 : wiener (psi r 0 g u) * hnorm 1 (y u) ≤ c4 * ε * (A + P + 1) := by
      have h1 : wiener (psi r 0 g u) * hnorm 1 (y u) ≤ c4 * ε * (A + P + ε) :=
        mul_le_mul hψw hy1 hy10 hcε
      have h2 : c4 * ε * (A + P + ε) ≤ c4 * ε * (A + P + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hcε
      exact h1.trans h2
    have t3 : hnorm 1 (actual r g y u) * wiener (psi r 0 g u) ≤ (A + P) * (c4 * ε) :=
      mul_le_mul hx1 hψw hψw0 hAP0
    have t4 : wiener (actual r g y u) * hnorm 1 (psi r 0 g u) ≤ (W + c4 * Y) * ε :=
      mul_le_mul hxw hψ1 hψ0 hWY0
    have hrest : 0 ≤ 2 * ε * Y + 2 * ε * A + 2 * ε * P + 2 * ε + 2 * (c4 * ε) * W := by positivity
    have e : 2 * (1 + c4) * ε * (W + Y + A + P + 1) =
        ε * (W + c4 * Y + c4) + c4 * ε * (A + P + 1) + (A + P) * (c4 * ε) + (W + c4 * Y) * ε +
          (2 * ε * Y + 2 * ε * A + 2 * ε * P + 2 * ε + 2 * (c4 * ε) * W) := by ring
    linarith
  · rw [eH]
    refine (hnorm_add_le hJ1 hJ2).trans ((add_le_add hR1 hR2).trans ?_)
    have t1 : wiener (psi r 0 g u) * hnorm 2 (y u) ≤ c4 * ε * (B + Y + 1) := by
      have h1 : wiener (psi r 0 g u) * hnorm 2 (y u) ≤ c4 * ε * (B + Y + ε) :=
        mul_le_mul hψw hy2 hy20 hcε
      have h2 : c4 * ε * (B + Y + ε) ≤ c4 * ε * (B + Y + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hcε
      exact h1.trans h2
    have t2 : hnorm 2 (psi r 0 g u) * wiener (y u) ≤ ε * (W + c4 * Y + c4) := by
      have h1 : hnorm 2 (psi r 0 g u) * wiener (y u) ≤ ε * (W + c4 * Y + c4 * ε) :=
        mul_le_mul le_rfl hyw hyw0 hε0
      have h2 : ε * (W + c4 * Y + c4 * ε) ≤ ε * (W + c4 * Y + c4) :=
        mul_le_mul_of_nonneg_left (by linarith) hε0
      exact h1.trans h2
    have t3 : wiener (actual r g y u) * hnorm 2 (psi r 0 g u) ≤ (W + c4 * Y) * ε :=
      mul_le_mul hxw le_rfl hε0 hWY0
    have t4 : hnorm 2 (actual r g y u) * wiener (psi r 0 g u) ≤ (B + Y) * (c4 * ε) :=
      mul_le_mul hx2 hψw hψw0 (add_nonneg hB hY)
    have hrest : 0 ≤ 16 * ε * B + 16 * ε * Y + 8 * ε * W + 16 * ε + 8 * (c4 * ε) * B +
        8 * (c4 * ε) + 16 * (c4 * ε) * W := by positivity
    have e : 16 * (1 + c4) * ε * (B + Y + W + 1) =
        4 * (c4 * ε * (B + Y + 1) + ε * (W + c4 * Y + c4)) +
          4 * ((W + c4 * Y) * ε + (B + Y) * (c4 * ε)) +
          (16 * ε * B + 16 * ε * Y + 8 * ε * W + 16 * ε + 8 * (c4 * ε) * B + 8 * (c4 * ε) +
            16 * (c4 * ε) * W) := by ring
    linarith

/-- The slow source on the piece: `slowNL ∈ H¹` (mean zero, slow) and
`‖slowNL‖₁ ≤ 8 𝒜(y)‖y‖₂ + ‖g‖₁ ≤ hSrc φ caps` once `‖ψ‖₂ ≤ 1`. -/
theorem slowNL_one_le (h : ActualSol μ φ r g y Ty) {caps : Caps} {s t : ℝ}
    (hpre : OnPrefix caps r g y s t) {u : ℝ} (hu : u ∈ Icc s t) (hs : 0 ≤ s)
    (huT : ENNReal.ofReal u < Ty) (hε : hnorm 2 (psi r 0 g u) ≤ 1) :
    MZ 1 (slowNL r g y u) ∧ hnorm 1 (slowNL r g y u) ≤ hSrc φ caps := by
  have hu0 : 0 ≤ u := hs.trans hu.1
  have hx := actual_adm h hu0 huT
  have hy := h.sol.adm u hu0 huT
  have hψ := psi_adm (r := r) (t₀ := 0) h.force_adm u hu0
  obtain ⟨cF1, cF2, cS1, cS2, cW⟩ := hpre.1 u hu
  have hc4 := c4_pos
  have hY := cp_nonneg caps.yF
  have hB := cp_nonneg caps.BS
  have hW := cp_nonneg caps.WS
  obtain ⟨hJ, hR⟩ := hnorm_one_Qm_le (phaseM_bdd (r * u)) hy.mz hy.mz
  have hg1 : InH 1 g := h.force_adm.inH.mono (by norm_num)
  have hI : InH 1 (slowNL r g y u) := hJ.PiS.neg.add hg1.PiS
  have hQ0 : Qphase (r * u) (y u) (y u) 0 = 0 := by simp [Qphase, Qm, hel_zero_mode]
  refine ⟨⟨hI, by simp [slowNL, PiS, h.force_adm.mean, hQ0]⟩, ?_⟩
  -- the caps
  have hxSF := PiS_add_PiF (actual r g y u)
  have hyx : y u = actual r g y u + psi r 0 g u := by simp [actual]
  have hx2 : hnorm 2 (actual r g y u) ≤ cp caps.BS + cp caps.yF := by
    conv_lhs => rw [← hxSF]
    refine (hnorm_add_le hx.PiS.inH hx.PiF.inH).trans ?_
    exact add_le_add (cS2.trans (le_cp _)) (cF2.trans (le_cp _))
  have hxw : wiener (actual r g y u) ≤ cp caps.WS + c4 * cp caps.yF := by
    conv_lhs => rw [← hxSF]
    refine (wiener_add_le (summable_wiener hx.PiS.inH) (summable_wiener hx.PiF.inH)).trans ?_
    refine add_le_add (cW.trans (le_cp _)) ((wiener_le hx.PiF.mz).trans ?_)
    exact mul_le_mul_of_nonneg_left (cF2.trans (le_cp _)) hc4.le
  have hy2 : hnorm 2 (y u) ≤ cp caps.BS + cp caps.yF + 1 := by
    rw [hyx]
    exact (hnorm_add_le hx.inH hψ.inH).trans (add_le_add hx2 hε)
  have hyw : wiener (y u) ≤ cp caps.WS + c4 * cp caps.yF + c4 := by
    rw [hyx]
    refine (wiener_add_le (summable_wiener hx.inH) (summable_wiener hψ.inH)).trans
      (add_le_add hxw ((wiener_le hψ.mz).trans ?_))
    exact (mul_le_mul_of_nonneg_left hε hc4.le).trans_eq (mul_one c4)
  have hg : hnorm 1 (PiS g) ≤ φ :=
    (hnorm_PiS_le hg1).trans ((hnorm_mono (by norm_num) h.force_adm.inH).trans h.force_le)
  have hy20 := hnorm_nonneg 2 (y u)
  have hyw0 := wiener_nonneg (y u)
  have h1 : hnorm 1 (PiS (Qm (phaseM (r * u)) (y u) (y u))) ≤
      8 * (wiener (y u) * hnorm 2 (y u)) :=
    (hnorm_PiS_le hJ).trans (hR.trans (le_of_eq (by ring)))
  have h2 : wiener (y u) * hnorm 2 (y u) ≤
      (cp caps.WS + c4 * cp caps.yF + c4) * (cp caps.BS + cp caps.yF + 1) :=
    mul_le_mul hyw hy2 hy20 (add_nonneg (add_nonneg hW (mul_nonneg hc4.le hY)) hc4.le)
  have e : hSrc φ caps =
      8 * ((cp caps.WS + c4 * cp caps.yF + c4) * (cp caps.BS + cp caps.yF + 1)) + φ := by
    unfold hSrc; ring
  rw [e]
  unfold slowNL
  refine (hnorm_add_le hJ.PiS.neg hg1.PiS).trans ?_
  rw [hnorm_neg]
  linarith

/-- The fast source on the piece: `fastNL ∈ H¹` (mean zero, fast) and
`‖fastNL‖₁ ≤ ‖Π_F Q(F,F)‖₁ + 2‖Π_F Q(S,F)‖₁ + ‖Π_F H_ψ‖₁ ≤ c_{Q1}√(ab) b + 8(W_S b + c_I B_S √(ab))
+ ‖H_ψ‖₁` (the slow–slow part has no fast output). -/
theorem fastNL_one_le (h : ActualSol μ φ r g y Ty) {caps : Caps} {s t : ℝ}
    (hpre : OnPrefix caps r g y s t) {u : ℝ} (hu : u ∈ Icc s t) (hs : 0 ≤ s)
    (huT : ENNReal.ofReal u < Ty) :
    MZ 1 (fastNL r g y u) ∧ hnorm 1 (fastNL r g y u) ≤
      cQ1 * Real.sqrt (fastNorm 1 r g y u * fastNorm 2 r g y u) * fastNorm 2 r g y u +
        8 * (cp caps.WS * fastNorm 2 r g y u +
          cI * cp caps.BS * Real.sqrt (fastNorm 1 r g y u * fastNorm 2 r g y u)) +
        hnorm 1 (Hpsi r g y u) := by
  have hu0 : 0 ≤ u := hs.trans hu.1
  have hx := actual_adm h hu0 huT
  have hy := h.sol.adm u hu0 huT
  obtain ⟨cF1, cF2, cS1, cS2, cW⟩ := hpre.1 u hu
  set S := PiS (actual r g y u) with hSdef
  set F := PiF (actual r g y u) with hFdef
  have hS : Adm 2 S := hx.PiS
  have hF : Adm 2 F := hx.PiF
  have hS' : PiS S = S := by
    funext k; by_cases hk : k 2 = 0 <;> simp [hSdef, PiS, hk]
  have hF' : PiF F = F := by
    funext k; by_cases hk : k 2 = 0 <;> simp [hFdef, PiF, hk]
  have hM := majorized_Qphase (r * u)
  have hx' : actual r g y u = S + F := (PiS_add_PiF _).symm
  have hsum : MZ 2 (S + F) := by rw [← hx']; exact hx.mz
  have hcomm : Qphase (r * u) F S = Qphase (r * u) S F :=
    Qm_comm_of_symm (phaseM_symm _) hF.mz hS.mz
  have hsplit : Qphase (r * u) (actual r g y u) (actual r g y u) =
      Qphase (r * u) S S + Qphase (r * u) S F + Qphase (r * u) S F + Qphase (r * u) F F := by
    conv_lhs => rw [hx']
    rw [hM.add_left 0 _ _ _ hS.mz hF.mz hsum, hM.add_right 0 _ _ _ hS.mz hS.mz hF.mz,
      hM.add_right 0 _ _ _ hF.mz hS.mz hF.mz, hcomm]
    abel
  have hyy : Qphase (r * u) (y u) (y u) =
      Qphase (r * u) (actual r g y u) (actual r g y u) + Hpsi r g y u := by simp [Hpsi]
  -- `H¹` membership of the pieces
  obtain ⟨hJSF, hRSF⟩ := hnorm_one_Qm_le (phaseM_bdd (r * u)) hS.mz hF.mz
  obtain ⟨hJFF, -⟩ := hnorm_one_Qm_le (phaseM_bdd (r * u)) hF.mz hF.mz
  obtain ⟨hJyy, -⟩ := hnorm_one_Qm_le (phaseM_bdd (r * u)) hy.mz hy.mz
  obtain ⟨hJxx, -⟩ := hnorm_one_Qm_le (phaseM_bdd (r * u)) hx.mz hx.mz
  have hJH : InH 1 (Hpsi r g y u) := hJyy.sub hJxx
  refine ⟨⟨hJyy.PiF.neg, by simp [fastNL, PiF]⟩, ?_⟩
  -- `Π_F Q(S,S) = 0`
  have hSS0 : PiF (Qphase (r * u) S S) = 0 := by
    funext k
    by_cases hk : k 2 = 0
    · simp [PiF, hk]
    · simp only [PiF, hk, ite_false, Pi.zero_apply]
      exact Qphase_slow_slow (r * u) hS' hk
  have ePiF : PiF (Qphase (r * u) (y u) (y u)) = PiF (Qphase (r * u) S F) +
      PiF (Qphase (r * u) S F) + PiF (Qphase (r * u) F F) + PiF (Hpsi r g y u) := by
    rw [hyy, hsplit]
    have e : ∀ A B : Field, PiF (A + B) = PiF A + PiF B := fun A B => by
      funext k; by_cases hk : k 2 = 0 <;> simp [PiF, hk]
    rw [e, e, e, e, hSS0, zero_add]
  set a := fastNorm 1 r g y u with hadef
  set b := fastNorm 2 r g y u with hbdef
  -- the mixed bound
  have hmix : hnorm 1 (PiF (Qphase (r * u) S F)) ≤
      4 * (cp caps.WS * b + cI * cp caps.BS * Real.sqrt (a * b)) := by
    refine (hnorm_PiF_le hJSF).trans (hRSF.trans ?_)
    have h1 : wiener S ≤ cp caps.WS := cW.trans (le_cp _)
    have h2 : hnorm 2 S ≤ cp caps.BS := cS2.trans (le_cp _)
    have h3 := wiener_le_cI hF.mz
    have hb0 : 0 ≤ b := hnorm_nonneg _ _
    have hcI := cI_pos
    have hsq := Real.sqrt_nonneg (hnorm 1 F * hnorm 2 F)
    have hw0 := wiener_nonneg F
    have hW := cp_nonneg caps.WS
    have hB := cp_nonneg caps.BS
    have eab : a * b = hnorm 1 F * hnorm 2 F := rfl
    have t1 : wiener S * hnorm 2 F ≤ cp caps.WS * b := mul_le_mul_of_nonneg_right h1 hb0
    have t2 : hnorm 2 S * wiener F ≤ cp caps.BS * (cI * Real.sqrt (hnorm 1 F * hnorm 2 F)) :=
      mul_le_mul h2 h3 hw0 hB
    rw [eab]
    linarith
  have hff : hnorm 1 (PiF (Qphase (r * u) F F)) ≤ cQ1 * Real.sqrt (a * b) * b :=
    hnorm_one_PiF_Qphase_le (r * u) hF.mz
  have hH : hnorm 1 (PiF (Hpsi r g y u)) ≤ hnorm 1 (Hpsi r g y u) := hnorm_PiF_le hJH
  have hI1 : InH 1 (PiF (Qphase (r * u) S F)) := hJSF.PiF
  have hI2 : InH 1 (PiF (Qphase (r * u) F F)) := hJFF.PiF
  have hI3 : InH 1 (PiF (Hpsi r g y u)) := hJH.PiF
  have h12 := hnorm_add_le hI1 hI1
  have h123 := hnorm_add_le (hI1.add hI1) hI2
  have h1234 := hnorm_add_le ((hI1.add hI1).add hI2) hI3
  unfold fastNL
  rw [hnorm_neg, ePiF]
  linarith

/-! ### E. Threshold and profile algebra -/

/-- A threshold `c X ≤ q` pays the share `X/q ≤ 1/c`. -/
lemma share_paid {X q c : ℝ} (_hX : 0 ≤ X) (hc : 0 < c) (hq0 : 0 < q) (hq : c * X ≤ q) :
    X / q ≤ 1 / c := by
  rw [div_le_div_iff₀ hq0 hc]
  linarith

/-- A threshold `(c X)^{1/e} ≤ q` (`q ≥ 1`, `0 < e`) pays the profile duty `c X q^{−e} ≤ 1`. -/
lemma profile_paid {X q c e : ℝ} (hX : 0 ≤ X) (hc : 0 ≤ c) (he : 0 < e) (hq1 : 1 ≤ q)
    (hq : (c * X) ^ (1 / e) ≤ q) : c * X * q ^ (-e) ≤ 1 := by
  have hq0 : 0 < q := by linarith
  have hcX : 0 ≤ c * X := mul_nonneg hc hX
  have h1 : c * X ≤ q ^ e := by
    have := Real.rpow_le_rpow (Real.rpow_nonneg hcX _) hq he.le
    rwa [← Real.rpow_mul hcX, one_div_mul_cancel he.ne', Real.rpow_one] at this
  rw [Real.rpow_neg hq0.le, ← div_eq_mul_inv, div_le_one (Real.rpow_pos_of_pos hq0 e)]
  exact h1

/-- `y^{3/2} = √y · y`. -/
lemma rpow_three_halves {Y : ℝ} (hY : 0 ≤ Y) : Y ^ (3 / 2 : ℝ) = Real.sqrt Y * Y := by
  rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add' hY (by norm_num),
    Real.rpow_one]

/-- `√(ab) b ≤ √P y^{3/2}` for `0 ≤ a ≤ P`, `0 ≤ b ≤ y`. -/
lemma sqrt_mul_le_leading {a b P Y : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ha : a ≤ P) (hb : b ≤ Y) :
    Real.sqrt (a * b) * b ≤ Real.sqrt P * Y ^ (3 / 2 : ℝ) := by
  have hY0 : 0 ≤ Y := hb0.trans hb
  rw [rpow_three_halves hY0, Real.sqrt_mul ha0]
  have h1 : Real.sqrt a ≤ Real.sqrt P := Real.sqrt_le_sqrt ha
  have h2 : Real.sqrt b ≤ Real.sqrt Y := Real.sqrt_le_sqrt hb
  have h3 := Real.sqrt_nonneg a
  have h4 := Real.sqrt_nonneg b
  have h5 := Real.sqrt_nonneg P
  have h6 := Real.sqrt_nonneg Y
  have h7 : Real.sqrt a * Real.sqrt b ≤ Real.sqrt P * Real.sqrt Y := mul_le_mul h1 h2 h4 h5
  calc Real.sqrt a * Real.sqrt b * b ≤ Real.sqrt P * Real.sqrt Y * Y :=
        mul_le_mul h7 hb hb0 (mul_nonneg h5 h6)
    _ = _ := by ring

/-- `N(q) ≤ 2¹⁰` (`𝔐_N ≤ 108`, `96√108 < 1024`). -/
lemma nearN_le_two_pow_ten (q : ℝ) : nearN q ≤ 2 ^ 10 := by
  unfold nearN
  have h1 : Real.sqrt (MomN q) ≤ Real.sqrt 108 := Real.sqrt_le_sqrt (MomN_le_const q)
  have h2 : Real.sqrt 108 ≤ 10.4 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  linarith

/-- `P(q) ≥ 0` for `q ≥ 0`. -/
lemma nearP_nonneg {q : ℝ} (hq : 0 ≤ q) : 0 ≤ nearP q := by
  unfold nearP
  have := Real.sqrt_nonneg (MomP q)
  have := Real.rpow_nonneg hq (-(3 : ℝ) / 4)
  positivity

/-! ### F. The shares -/

/-- The slow-source share: `2¹⁰ hS a b/q ≤ (2⁹hS/q) a² + b²/64`. -/
lemma share_slow {a b q hS : ℝ} (_ha0 : 0 ≤ a) (_hb0 : 0 ≤ b) (hq0 : 0 < q) (hhS : 0 ≤ hS)
    (hK : 2 ^ 9 * hS / q ≤ 1 / 64) :
    2 ^ 10 * hS * a * b / q ≤ 2 ^ 9 * hS / q * a ^ 2 + 1 / 64 * b ^ 2 := by
  set K := 2 ^ 9 * hS / q with hKdef
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  have e : 2 ^ 10 * hS * a * b / q = K * (2 * (a * b)) := by
    rw [hKdef]; field_simp
  have hab : 2 * (a * b) ≤ a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg (a - b)]
  have h1 : K * (2 * (a * b)) ≤ K * (a ^ 2 + b ^ 2) := mul_le_mul_of_nonneg_left hab hK0
  have h2 : K * b ^ 2 ≤ 1 / 64 * b ^ 2 := mul_le_mul_of_nonneg_right hK (sq_nonneg b)
  have e2 : K * (a ^ 2 + b ^ 2) = K * a ^ 2 + K * b ^ 2 := by ring
  rw [e]
  linarith

/-- The fast–fast metric–`Q` share: `2⁸ B a c_Q √(ab) b/q ≤ b²/64`. -/
lemma share_bil_ff {a b q B P cQ' : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hab : a ≤ b) (haP : a ≤ P)
    (hq0 : 0 < q) (hB : 0 ≤ B) (hcQ : 0 ≤ cQ') (hQ : 2 ^ 8 * (cQ' * B * P) / q ≤ 1 / 64) :
    2 ^ 8 * B * a * (cQ' * Real.sqrt (a * b) * b) / q ≤ 1 / 64 * b ^ 2 := by
  have hP : 0 ≤ P := ha0.trans haP
  have hsq_le_b : Real.sqrt (a * b) ≤ b := by
    rw [Real.sqrt_le_left hb0]
    nlinarith [mul_le_mul_of_nonneg_right hab hb0]
  have h2' : a * (Real.sqrt (a * b) * b) ≤ P * b ^ 2 := by
    have h3 : Real.sqrt (a * b) * b ≤ b * b := mul_le_mul_of_nonneg_right hsq_le_b hb0
    have h4 : a * (Real.sqrt (a * b) * b) ≤ P * (b * b) :=
      mul_le_mul haP h3 (mul_nonneg (Real.sqrt_nonneg _) hb0) hP
    linarith [show P * (b * b) = P * b ^ 2 by ring]
  have hK0 : 0 ≤ 2 ^ 8 * cQ' * B / q := by positivity
  have h5 := mul_le_mul_of_nonneg_left h2' hK0
  calc 2 ^ 8 * B * a * (cQ' * Real.sqrt (a * b) * b) / q
      = 2 ^ 8 * cQ' * B / q * (a * (Real.sqrt (a * b) * b)) := by ring
    _ ≤ 2 ^ 8 * cQ' * B / q * (P * b ^ 2) := h5
    _ = 2 ^ 8 * (cQ' * B * P) / q * b ^ 2 := by ring
    _ ≤ 1 / 64 * b ^ 2 := mul_le_mul_of_nonneg_right hQ (sq_nonneg b)

/-- The slow–fast metric–`Q` share: `2⁸ B a · 8(W b + c_I B √(ab))/q ≤ (2¹⁰(BW + c_I B²)/q)(a² + b²)`
and the `b²` part is `≤ b²/64`. -/
lemma share_bil_sf {a b q B W cI' : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hab : a ≤ b) (hq0 : 0 < q)
    (hB : 0 ≤ B) (hW : 0 ≤ W) (hcI : 0 ≤ cI')
    (hSF : 2 ^ 10 * (B * W + cI' * B ^ 2) / q ≤ 1 / 64) :
    2 ^ 8 * B * a * (8 * (W * b + cI' * B * Real.sqrt (a * b))) / q ≤
      2 ^ 10 * (B * W + cI' * B ^ 2) / q * a ^ 2 + 1 / 64 * b ^ 2 := by
  have hsq_le_b : Real.sqrt (a * b) ≤ b := by
    rw [Real.sqrt_le_left hb0]
    nlinarith [mul_le_mul_of_nonneg_right hab hb0]
  have hab2 : a * b ≤ 1 / 2 * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a - b)]
  have hasq : a * Real.sqrt (a * b) ≤ 1 / 2 * (a ^ 2 + b ^ 2) :=
    (mul_le_mul_of_nonneg_left hsq_le_b ha0).trans hab2
  have t1 : W * (a * b) ≤ W * (1 / 2 * (a ^ 2 + b ^ 2)) := mul_le_mul_of_nonneg_left hab2 hW
  have t2 : cI' * B * (a * Real.sqrt (a * b)) ≤ cI' * B * (1 / 2 * (a ^ 2 + b ^ 2)) :=
    mul_le_mul_of_nonneg_left hasq (mul_nonneg hcI hB)
  have h2' : a * (8 * (W * b + cI' * B * Real.sqrt (a * b))) ≤
      8 * ((W + cI' * B) * (1 / 2 * (a ^ 2 + b ^ 2))) := by
    have e1 : a * (8 * (W * b + cI' * B * Real.sqrt (a * b))) =
        8 * (W * (a * b) + cI' * B * (a * Real.sqrt (a * b))) := by ring
    have e2 : 8 * ((W + cI' * B) * (1 / 2 * (a ^ 2 + b ^ 2))) =
        8 * (W * (1 / 2 * (a ^ 2 + b ^ 2)) + cI' * B * (1 / 2 * (a ^ 2 + b ^ 2))) := by ring
    rw [e1, e2]
    linarith
  set K := 2 ^ 10 * (B * W + cI' * B ^ 2) / q with hKdef
  have hK0 : 0 ≤ 2 ^ 8 * B / q := by positivity
  have h4 := mul_le_mul_of_nonneg_left h2' hK0
  have e : 2 ^ 8 * B * a * (8 * (W * b + cI' * B * Real.sqrt (a * b))) / q =
      2 ^ 8 * B / q * (a * (8 * (W * b + cI' * B * Real.sqrt (a * b)))) := by ring
  have e2 : 2 ^ 8 * B / q * (8 * ((W + cI' * B) * (1 / 2 * (a ^ 2 + b ^ 2)))) =
      K * a ^ 2 + K * b ^ 2 := by
    rw [hKdef]; ring
  have h5 : K * b ^ 2 ≤ 1 / 64 * b ^ 2 := mul_le_mul_of_nonneg_right hSF (sq_nonneg b)
  rw [e]
  linarith

/-- The metric–force share: `2⁸ B a h1/q ≤ (2⁷B/q) a² + 2⁸ B h1²/q`. -/
lemma share_bil_force {a q B h1 : ℝ} (_ha0 : 0 ≤ a) (hq0 : 0 < q) (hB : 0 ≤ B) (_hh1 : 0 ≤ h1) :
    2 ^ 8 * B * a * h1 / q ≤ 2 ^ 7 * B / q * a ^ 2 + 2 ^ 8 * B * h1 ^ 2 / q := by
  have h2' : a * h1 ≤ 1 / 2 * (a ^ 2 + h1 ^ 2) := by nlinarith [sq_nonneg (a - h1)]
  have hK0 : 0 ≤ 2 ^ 8 * B / q := by positivity
  have h3 := mul_le_mul_of_nonneg_left h2' hK0
  have e : 2 ^ 8 * B * a * h1 / q = 2 ^ 8 * B / q * (a * h1) := by ring
  have e2 : 2 ^ 8 * B / q * (1 / 2 * (a ^ 2 + h1 ^ 2)) =
      2 ^ 7 * B / q * a ^ 2 + 2 ^ 8 * B * h1 ^ 2 / q / 2 := by ring
  have h5 : 0 ≤ 2 ^ 8 * B * h1 ^ 2 / q := by positivity
  rw [e]
  linarith

/-- The heat share: `cH P(q) b³ ≤ b²/64`. -/
lemma share_heat {b Y Pq cH' : ℝ} (hb0 : 0 ≤ b) (hbY : b ≤ Y) (hcH : 0 ≤ cH') (hPq0 : 0 ≤ Pq)
    (hheat : cH' * Y * Pq ≤ 1 / 64) : cH' * Pq * b ^ 3 ≤ 1 / 64 * b ^ 2 := by
  have h1 : cH' * Pq * b ≤ cH' * Y * Pq := by
    have := mul_le_mul_of_nonneg_left hbY (mul_nonneg hcH hPq0)
    linarith [show cH' * Pq * Y = cH' * Y * Pq by ring]
  have h2 := mul_le_mul_of_nonneg_right (h1.trans hheat) (sq_nonneg b)
  have e : cH' * Pq * b ^ 3 = cH' * Pq * b * b ^ 2 := by ring
  rw [e]
  exact h2.trans_eq rfl

/-- The near share of the native differential: `N(q) N1 b² ≤ (1/32 + 1/64 + 1/64) b²`. -/
lemma share_near {a b P Y B W Nq h1 cQ' cI' : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (haP : a ≤ P)
    (hbY : b ≤ Y) (hB : 0 ≤ B) (hW : 0 ≤ W) (hN0 : 0 ≤ Nq) (hcQ : 0 ≤ cQ') (hcI : 0 ≤ cI')
    (hK : cQ' * Real.sqrt P * Y ^ (3 / 2 : ℝ) * Nq ≤ 1 / 32)
    (hmix : 8 * (W * Y + cI' * B * Real.sqrt (P * Y)) * Nq ≤ 1 / 64) (hNh : Nq * h1 ≤ 1 / 64) :
    Nq * (cQ' * Real.sqrt (a * b) * b + 8 * (W * b + cI' * B * Real.sqrt (a * b)) + h1) * b ^ 2 ≤
      (1 / 32 + 1 / 64 + 1 / 64) * b ^ 2 := by
  have hP : 0 ≤ P := ha0.trans haP
  have hlead : Real.sqrt (a * b) * b ≤ Real.sqrt P * Y ^ (3 / 2 : ℝ) :=
    sqrt_mul_le_leading ha0 hb0 haP hbY
  have hsqPY' : Real.sqrt (a * b) ≤ Real.sqrt (P * Y) :=
    Real.sqrt_le_sqrt (mul_le_mul haP hbY hb0 hP)
  have hWb : W * b ≤ W * Y := mul_le_mul_of_nonneg_left hbY hW
  have t1 : Nq * (cQ' * Real.sqrt (a * b) * b) ≤ 1 / 32 := by
    have := mul_le_mul_of_nonneg_left hlead (mul_nonneg hN0 hcQ)
    calc Nq * (cQ' * Real.sqrt (a * b) * b) = Nq * cQ' * (Real.sqrt (a * b) * b) := by ring
      _ ≤ Nq * cQ' * (Real.sqrt P * Y ^ (3 / 2 : ℝ)) := this
      _ = cQ' * Real.sqrt P * Y ^ (3 / 2 : ℝ) * Nq := by ring
      _ ≤ 1 / 32 := hK
  have t2 : Nq * (8 * (W * b + cI' * B * Real.sqrt (a * b))) ≤ 1 / 64 := by
    have e2 : cI' * B * Real.sqrt (a * b) ≤ cI' * B * Real.sqrt (P * Y) :=
      mul_le_mul_of_nonneg_left hsqPY' (mul_nonneg hcI hB)
    have h8 : 8 * (W * b + cI' * B * Real.sqrt (a * b)) ≤
        8 * (W * Y + cI' * B * Real.sqrt (P * Y)) := by linarith
    calc Nq * (8 * (W * b + cI' * B * Real.sqrt (a * b)))
        ≤ Nq * (8 * (W * Y + cI' * B * Real.sqrt (P * Y))) := mul_le_mul_of_nonneg_left h8 hN0
      _ = 8 * (W * Y + cI' * B * Real.sqrt (P * Y)) * Nq := by ring
      _ ≤ 1 / 64 := hmix
  have e : Nq * (cQ' * Real.sqrt (a * b) * b + 8 * (W * b + cI' * B * Real.sqrt (a * b)) + h1) =
      Nq * (cQ' * Real.sqrt (a * b) * b) + Nq * (8 * (W * b + cI' * B * Real.sqrt (a * b))) +
        Nq * h1 := by ring
  have h3 : Nq * (cQ' * Real.sqrt (a * b) * b + 8 * (W * b + cI' * B * Real.sqrt (a * b)) + h1) ≤
      1 / 32 + 1 / 64 + 1 / 64 := by
    rw [e]
    linarith
  exact mul_le_mul_of_nonneg_right h3 (sq_nonneg b)

/-- The far share: `(2¹⁴/q) N1 b² ≤ b²/64` once `N1 ≤ N1cap` and `2¹⁴ N1cap/q ≤ 1/64`. -/
lemma share_far {b q N1 N1cap : ℝ} (hq0 : 0 < q) (hN1 : 0 ≤ N1) (hle : N1 ≤ N1cap)
    (hfar : 2 ^ 14 * N1cap / q ≤ 1 / 64) : 2 ^ 14 / q * N1 * b ^ 2 ≤ 1 / 64 * b ^ 2 := by
  have _ := hN1
  have h : 2 ^ 14 / q * N1 ≤ 1 / 64 := by
    calc 2 ^ 14 / q * N1 ≤ 2 ^ 14 / q * N1cap :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = 2 ^ 14 * N1cap / q := by ring
      _ ≤ 1 / 64 := hfar
  exact mul_le_mul_of_nonneg_right h (sq_nonneg b)

/-- The source bound is dominated by its cap: `N1 ≤ N1cap` (`h1 ≤ 1`). -/
lemma src_le_cap {a b P Y B W h1 cQ' cI' : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (haP : a ≤ P)
    (hbY : b ≤ Y) (hB : 0 ≤ B) (hW : 0 ≤ W) (hcQ : 0 ≤ cQ') (hcI : 0 ≤ cI') (hh1 : h1 ≤ 1) :
    cQ' * Real.sqrt (a * b) * b + 8 * (W * b + cI' * B * Real.sqrt (a * b)) + h1 ≤
      cQ' * Real.sqrt P * Y ^ (3 / 2 : ℝ) + 8 * (W * Y + cI' * B * Real.sqrt (P * Y)) + 1 := by
  have hP : 0 ≤ P := ha0.trans haP
  have hlead : Real.sqrt (a * b) * b ≤ Real.sqrt P * Y ^ (3 / 2 : ℝ) :=
    sqrt_mul_le_leading ha0 hb0 haP hbY
  have hsqPY' : Real.sqrt (a * b) ≤ Real.sqrt (P * Y) :=
    Real.sqrt_le_sqrt (mul_le_mul haP hbY hb0 hP)
  have hWb : W * b ≤ W * Y := mul_le_mul_of_nonneg_left hbY hW
  have e1 : cQ' * Real.sqrt (a * b) * b ≤ cQ' * Real.sqrt P * Y ^ (3 / 2 : ℝ) := by
    have := mul_le_mul_of_nonneg_left hlead hcQ
    calc cQ' * Real.sqrt (a * b) * b = cQ' * (Real.sqrt (a * b) * b) := by ring
      _ ≤ cQ' * (Real.sqrt P * Y ^ (3 / 2 : ℝ)) := this
      _ = _ := by ring
  have e2 : cI' * B * Real.sqrt (a * b) ≤ cI' * B * Real.sqrt (P * Y) :=
    mul_le_mul_of_nonneg_left hsqPY' (mul_nonneg hcI hB)
  linarith

/-- **The real-number core of the budget**: the six remainders are absorbed,
`Tres + Tf + Tslow + Tbil + Theat + TD ≤ (9/64) b² + cub + nf b + 2⁸ B h1²/q +
((2⁹ hS + 2¹⁰(BW + c_I B²) + 2⁷ B)/q) a²`. -/
theorem budget_core {a b q P Y B W Nq Pq hS h1 nf cub Tres Tf Tslow Tbil Theat TD cI' cQ' cH' : ℝ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hab : a ≤ b) (hq0 : 0 < q) (hB : 0 ≤ B) (hW : 0 ≤ W)
    (haP : a ≤ P) (hbY : b ≤ Y) (hN0 : 0 ≤ Nq) (hPq0 : 0 ≤ Pq) (hhS : 0 ≤ hS) (hh1 : 0 ≤ h1)
    (hh1' : h1 ≤ 1) (hcI : 0 ≤ cI') (hcQ : 0 ≤ cQ') (hcH : 0 ≤ cH')
    (hTres : Tres ≤ cub) (hTf : Tf ≤ nf * b)
    (hTslow : Tslow ≤ 2 ^ 10 * hS * a * b / q)
    (hTbil : Tbil ≤ 2 ^ 8 * B * a *
      (cQ' * Real.sqrt (a * b) * b + 8 * (W * b + cI' * B * Real.sqrt (a * b)) + h1) / q)
    (hTheat : Theat ≤ cH' * Pq * b ^ 3)
    (hTD : TD ≤ (Nq + 2 ^ 14 / q) *
      (cQ' * Real.sqrt (a * b) * b + 8 * (W * b + cI' * B * Real.sqrt (a * b)) + h1) * b ^ 2)
    (hK : cQ' * Real.sqrt P * Y ^ (3 / 2 : ℝ) * Nq ≤ 1 / 32)
    (hmix : 8 * (W * Y + cI' * B * Real.sqrt (P * Y)) * Nq ≤ 1 / 64)
    (hNh : Nq * h1 ≤ 1 / 64) (hheat : cH' * Y * Pq ≤ 1 / 64)
    (hslow : 2 ^ 9 * hS / q ≤ 1 / 64) (hQ : 2 ^ 8 * (cQ' * B * P) / q ≤ 1 / 64)
    (hSF : 2 ^ 10 * (B * W + cI' * B ^ 2) / q ≤ 1 / 64)
    (hfar : 2 ^ 14 * (cQ' * Real.sqrt P * Y ^ (3 / 2 : ℝ) +
      8 * (W * Y + cI' * B * Real.sqrt (P * Y)) + 1) / q ≤ 1 / 64) :
    Tres + Tf + Tslow + Tbil + Theat + TD ≤ 9 / 64 * b ^ 2 + cub + nf * b + 2 ^ 8 * B * h1 ^ 2 / q +
      (2 ^ 9 * hS + 2 ^ 10 * (B * W + cI' * B ^ 2) + 2 ^ 7 * B) / q * a ^ 2 := by
  have hN10 : 0 ≤ cQ' * Real.sqrt (a * b) * b + 8 * (W * b + cI' * B * Real.sqrt (a * b)) + h1 := by
    have := Real.sqrt_nonneg (a * b)
    positivity
  have s1 := share_slow ha0 hb0 hq0 hhS hslow
  have s2 := share_bil_ff ha0 hb0 hab haP hq0 hB hcQ hQ
  have s3 := share_bil_sf ha0 hb0 hab hq0 hB hW hcI hSF
  have s4 := share_bil_force ha0 hq0 hB hh1
  have s5 := share_heat hb0 hbY hcH hPq0 hheat
  have s6 := share_near ha0 hb0 haP hbY hB hW hN0 hcQ hcI hK hmix hNh
  have s7 := share_far (b := b) hq0 hN10 (src_le_cap ha0 hb0 haP hbY hB hW hcQ hcI hh1') hfar
  have eb : 2 ^ 8 * B * a *
      (cQ' * Real.sqrt (a * b) * b + 8 * (W * b + cI' * B * Real.sqrt (a * b)) + h1) / q =
      2 ^ 8 * B * a * (cQ' * Real.sqrt (a * b) * b) / q +
        2 ^ 8 * B * a * (8 * (W * b + cI' * B * Real.sqrt (a * b))) / q +
        2 ^ 8 * B * a * h1 / q := by ring
  have eD : (Nq + 2 ^ 14 / q) *
      (cQ' * Real.sqrt (a * b) * b + 8 * (W * b + cI' * B * Real.sqrt (a * b)) + h1) * b ^ 2 =
      Nq * (cQ' * Real.sqrt (a * b) * b + 8 * (W * b + cI' * B * Real.sqrt (a * b)) + h1) * b ^ 2 +
        2 ^ 14 / q * (cQ' * Real.sqrt (a * b) * b + 8 * (W * b + cI' * B * Real.sqrt (a * b)) + h1)
          * b ^ 2 := by ring
  have em : (2 ^ 9 * hS + 2 ^ 10 * (B * W + cI' * B ^ 2) + 2 ^ 7 * B) / q * a ^ 2 =
      2 ^ 9 * hS / q * a ^ 2 + 2 ^ 10 * (B * W + cI' * B ^ 2) / q * a ^ 2 +
        2 ^ 7 * B / q * a ^ 2 := by ring
  rw [eb] at hTbil
  rw [eD] at hTD
  rw [em]
  linarith

/-- The threshold form of `share_paid`: `c X ≤ R ≤ q` pays `X/q ≤ 1/c`. -/
lemma share_paid_le {X q c R : ℝ} (hX : 0 ≤ X) (hc : 0 < c) (hq0 : 0 < q) (hR : c * X ≤ R)
    (hq : R ≤ q) : X / q ≤ 1 / c :=
  share_paid hX hc hq0 (hR.trans hq)

/-- The profile form: `Y^{1/e} ≤ q`, `Nq ≤ pC q^{−e}` and `K X pC = Y` pay `X Nq ≤ 1/K`. -/
lemma profile_share {Nq pC q e E X K Y : ℝ} (hX : 0 ≤ X) (hpC : 0 ≤ pC) (he : 0 < e)
    (hE : 1 / e = E) (hq1 : 1 ≤ q) (hNle : Nq ≤ pC * q ^ (-e)) (hK : 0 < K)
    (hY : K * X * pC = Y) (hq : Y ^ E ≤ q) : X * Nq ≤ 1 / K := by
  have hq0 : 0 < q := by linarith
  have hY0 : 0 ≤ Y := by rw [← hY]; positivity
  have h1 : Y ≤ q ^ e := by
    have := Real.rpow_le_rpow (Real.rpow_nonneg hY0 _) hq he.le
    rwa [← Real.rpow_mul hY0, ← hE, one_div_mul_cancel he.ne', Real.rpow_one] at this
  have hqe : 0 < q ^ e := Real.rpow_pos_of_pos hq0 e
  calc X * Nq ≤ X * (pC * q ^ (-e)) := mul_le_mul_of_nonneg_left hNle hX
    _ = (X * pC) / q ^ e := by rw [Real.rpow_neg hq0.le]; ring
    _ ≤ 1 / K := by
        rw [div_le_div_iff₀ hqe hK]
        calc X * pC * K = Y := by rw [← hY]; ring
          _ ≤ 1 * q ^ e := by rw [one_mul]; exact h1

/-- The leading role 15 in share form, the caps replaced by their nonnegative parts. -/
lemma share_leading {caps : Caps} {Nq : ℝ}
    (hK : h1K₁ * Real.sqrt caps.PF * caps.yF ^ (3 / 2 : ℝ) * Nq ≤ 1) :
    cQ1 * Real.sqrt (cp caps.PF) * cp caps.yF ^ (3 / 2 : ℝ) * (nearC₀ * Nq) ≤ 1 / 32 := by
  rcases le_or_gt 0 caps.PF with hP' | hP'
  · rcases le_or_gt 0 caps.yF with hY' | hY'
    · have e1 : cp caps.PF = caps.PF := max_eq_left hP'
      have e2 : cp caps.yF = caps.yF := max_eq_left hY'
      rw [e1, e2]
      unfold h1K₁ at hK
      have e3 : cQ1 * Real.sqrt caps.PF * caps.yF ^ (3 / 2 : ℝ) * (nearC₀ * Nq) =
          1 / 32 * (32 * nearC₀ * cQ1 * Real.sqrt caps.PF * caps.yF ^ (3 / 2 : ℝ) * Nq) := by
        ring
      rw [e3]
      linarith only [hK]
    · have : cp caps.yF = 0 := max_eq_right hY'.le
      rw [this, Real.zero_rpow (by norm_num)]
      simp
  · have : cp caps.PF = 0 := max_eq_right hP'.le
    rw [this, Real.sqrt_zero]
    simp

/-- The mixed near partner of role 15, through `N(q) ≤ profC q^{−49/100}`. -/
lemma share_mix {caps : Caps} {q : ℝ} (hq1 : 1 ≤ q) (hq : role15mix caps ≤ q) :
    8 * mixNear caps * (nearC₀ * nearN q) ≤ 1 / 64 := by
  have h := profile_share (Nq := nearN q) (X := 8 * mixNear caps * nearC₀) (K := 64)
    (e := 49 / 100) (E := 100 / 49) (Y := 2 ^ 9 * nearC₀ * profC * mixNear caps)
    (mul_nonneg (mul_nonneg (by norm_num) (mixNear_nonneg caps)) nearC₀_pos.le) profC_pos.le
    (by norm_num) (by norm_num) hq1 (nearN_le_profC hq1) (by norm_num) (by ring) hq
  rwa [mul_assoc] at h

/-- Role 14 (both input heats), through `P(q) ≤ profC q^{−29/100}`. -/
lemma share_heat_role {caps : Caps} {q : ℝ} (hq1 : 1 ≤ q) (hq : role14 caps ≤ q) :
    cHeat * cp caps.yF * nearP q ≤ 1 / 64 :=
  profile_share (Nq := nearP q) (X := cHeat * cp caps.yF) (K := 64) (e := 29 / 100)
    (E := 100 / 29) (Y := 2 ^ 6 * cHeat * profC * cp caps.yF)
    (mul_nonneg (by unfold cHeat; positivity) (cp_nonneg _)) profC_pos.le (by norm_num)
    (by norm_num) hq1 (nearP_le_profC hq1) (by norm_num) (by ring) hq

/-- Role 13 (static coercivity), through `P(q) ≤ profC q^{−29/100}`. -/
lemma share_static_role {caps : Caps} {q : ℝ} (hq1 : 1 ≤ q) (hq : role13 caps ≤ q) :
    2 * cStat * cp caps.yF * nearP q ≤ 1 / 128 :=
  profile_share (Nq := nearP q) (X := 2 * cStat * cp caps.yF) (K := 128) (e := 29 / 100)
    (E := 100 / 29) (Y := 2 ^ 8 * cStat * profC * cp caps.yF)
    (mul_nonneg (mul_nonneg (by norm_num) (by unfold cStat; positivity)) (cp_nonneg _))
    profC_pos.le (by norm_num) (by norm_num) hq1 (nearP_le_profC hq1) (by norm_num) (by ring) hq

/-- The force package: `Z = 2²² a b f t Sc` (`a, b, f, t, Sc ≥ 1`) dominates `2φ`, the `H¹` duty
`2¹⁶ N (32 b φ T₁)` and the `H⁰` duty `t (4 b φ T₂)` for `φ ≤ f`, `N ≤ a`, `T₁, T₂ ≤ Sc`. -/
lemma force_package {N a b φ f t Sc T₁ T₂ : ℝ} (_hN : 0 ≤ N) (hNa : N ≤ a) (ha : 1 ≤ a)
    (hb : 1 ≤ b) (hφ : 0 ≤ φ) (hφf : φ ≤ f) (hf : 1 ≤ f) (ht : 1 ≤ t) (hSc : 1 ≤ Sc)
    (hT₁0 : 0 ≤ T₁) (hT₁ : T₁ ≤ Sc) (hT₂0 : 0 ≤ T₂) (hT₂ : T₂ ≤ Sc) :
    2 * φ ≤ 2 ^ 22 * a * b * f * t * Sc ∧
      2 ^ 16 * N * (32 * b * φ * T₁) ≤ 2 ^ 22 * a * b * f * t * Sc ∧
      t * (4 * b * φ * T₂) ≤ 2 ^ 22 * a * b * f * t * Sc := by
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hf0 : 0 ≤ f := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hS0 : 0 ≤ Sc := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ a * b * t * Sc :=
      one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le ha hb) ht) hSc
    calc 2 * φ ≤ 2 ^ 22 * f * 1 := by norm_num; linarith
      _ ≤ 2 ^ 22 * f * (a * b * t * Sc) := by gcongr
      _ = _ := by ring
  · calc 2 ^ 16 * N * (32 * b * φ * T₁) = 2 ^ 21 * (N * b * φ * T₁) := by ring
      _ ≤ 2 ^ 21 * (a * b * f * Sc) := by gcongr
      _ ≤ 2 ^ 21 * (a * b * f * Sc) * (2 * t) :=
          le_mul_of_one_le_right (by positivity) (by linarith)
      _ = _ := by ring
  · calc t * (4 * b * φ * T₂) = 4 * (t * b * φ * T₂) := by ring
      _ ≤ 4 * (t * b * f * Sc) := by gcongr
      _ ≤ 4 * (t * b * f * Sc) * (2 ^ 20 * a) :=
          le_mul_of_one_le_right (by positivity) (by norm_num; linarith)
      _ = _ := by ring

/-- The force shares from role force. -/
lemma shares_force {Tp φ : ℝ} (hTp : 0 ≤ Tp) (hφ : 0 ≤ φ) {caps : Caps} {r : ℝ} (hr0 : 0 < |r|)
    (hq : roleForce Tp φ caps ≤ |r|) :
    2 * φ / |r| ≤ 1 ∧ h1Const φ caps r ≤ 1 / (2 ^ 16 * nearC₀) ∧
      nfConst φ caps r ≤ 1 / (1 + Tp) := by
  have hc4 := c4_pos
  have hC0 := nearC₀_pos
  have hP := cp_nonneg caps.PF
  have hY := cp_nonneg caps.yF
  have hA := cp_nonneg caps.AS
  have hB := cp_nonneg caps.BS
  have hW := cp_nonneg caps.WS
  obtain ⟨h1, h2, h3⟩ := force_package (N := nearC₀) (a := 1 + nearC₀) (b := 1 + c4) (φ := φ)
    (f := 1 + φ) (t := 1 + Tp)
    (Sc := cp caps.BS + cp caps.yF + cp caps.WS + cp caps.AS + cp caps.PF + 1)
    (T₁ := cp caps.BS + cp caps.yF + cp caps.WS + 1)
    (T₂ := cp caps.WS + cp caps.yF + cp caps.AS + cp caps.PF + 1)
    hC0.le (by linarith only []) (by linarith only [hC0]) (by linarith only [hc4]) hφ
    (by linarith only []) (by linarith only [hφ]) (by linarith only [hTp])
    (by linarith only [hP, hY, hA, hB, hW]) (by linarith only [hB, hY, hW])
    (by linarith only [hA, hP]) (by linarith only [hP, hY, hA, hW])
    (by linarith only [hB])
  replace hq : 2 ^ 22 * (1 + nearC₀) * (1 + c4) * (1 + φ) * (1 + Tp) *
      (cp caps.BS + cp caps.yF + cp caps.WS + cp caps.AS + cp caps.PF + 1) ≤ |r| := hq
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_one hr0]
    exact h1.trans hq
  · refine share_paid_le ?_ (by positivity) hr0 h2 hq
    positivity
  · refine share_paid_le ?_ (by positivity) hr0 h3 hq
    positivity

/-- The share forms of the duties from the thresholds `h1Threshold` and the leading hypothesis. -/
theorem shares_of_threshold {Tp μ φ : ℝ} (hTp : 0 ≤ Tp) (hφ : 0 ≤ φ) {caps : Caps} {r : ℝ}
    (hthr : h1Threshold Tp μ φ caps ≤ |r|)
    (hK : h1K₁ * Real.sqrt caps.PF * caps.yF ^ (3 / 2 : ℝ) * nearN |r| ≤ 1) :
    1 ≤ |r| ∧
    cQ1 * Real.sqrt (cp caps.PF) * cp caps.yF ^ (3 / 2 : ℝ) * (nearC₀ * nearN |r|) ≤ 1 / 32 ∧
    8 * mixNear caps * (nearC₀ * nearN |r|) ≤ 1 / 64 ∧
    cHeat * cp caps.yF * nearP |r| ≤ 1 / 64 ∧
    2 * cStat * cp caps.yF * nearP |r| ≤ 1 / 128 ∧
    2 ^ 9 * hSrc φ caps / |r| ≤ 1 / 64 ∧
    2 ^ 8 * (cQ1 * cp caps.BS * cp caps.PF) / |r| ≤ 1 / 64 ∧
    2 ^ 10 * (cp caps.BS * cp caps.WS + cI * cp caps.BS ^ 2) / |r| ≤ 1 / 64 ∧
    2 ^ 14 * srcAll caps / |r| ≤ 1 / 64 ∧
    2 ^ 8 * cp caps.BS / |r| ≤ 1 / 2 ^ 20 ∧
    mCoef φ caps / |r| ≤ 1 / (4 * (1 + Tp)) ∧
    2 * φ / |r| ≤ 1 ∧
    h1Const φ caps r ≤ 1 / (2 ^ 16 * nearC₀) ∧
    nfConst φ caps r ≤ 1 / (1 + Tp) := by
  obtain ⟨r9, r13, r14, r15, r28o, r28Q, r28SF, r28s, r28t, rF⟩ := role_le_h1Threshold hTp hφ caps
  have hr1 : 1 ≤ |r| := (one_le_h1Threshold (μ := μ) hTp hφ caps).trans hthr
  have hr0 : 0 < |r| := by linarith only [hr1]
  have hP := cp_nonneg caps.PF
  have hB := cp_nonneg caps.BS
  have hW := cp_nonneg caps.WS
  have hcI := cI_pos
  have hcQ := cQ1_pos
  obtain ⟨sψ, sh1, snf⟩ := shares_force hTp hφ hr0 (rF.trans hthr)
  refine ⟨hr1, share_leading hK, share_mix hr1 (r15.trans hthr), share_heat_role hr1 (r14.trans hthr),
    share_static_role hr1 (r13.trans hthr), ?_, ?_, ?_, ?_, ?_, ?_, sψ, sh1, snf⟩
  · exact share_paid_le (mul_nonneg (by norm_num) (hSrc_nonneg hφ caps)) (by norm_num) hr0
      (le_of_eq (by unfold role28src; ring)) (r28s.trans hthr)
  · have h0 : 0 ≤ cQ1 * cp caps.BS * cp caps.PF := mul_nonneg (mul_nonneg hcQ.le hB) hP
    refine share_paid_le (mul_nonneg (by norm_num) h0) (by norm_num) hr0 ?_ (r28Q.trans hthr)
    unfold role28Q
    linarith only [h0]
  · have h0 : 0 ≤ cp caps.BS * cp caps.WS + cI * cp caps.BS ^ 2 :=
      add_nonneg (mul_nonneg hB hW) (mul_nonneg hcI.le (sq_nonneg _))
    refine share_paid_le (mul_nonneg (by norm_num) h0) (by norm_num) hr0 ?_ (r28SF.trans hthr)
    unfold role28SF
    linarith only [h0]
  · exact share_paid_le (mul_nonneg (by norm_num) (srcAll_nonneg caps)) (by norm_num) hr0
      (le_of_eq (by unfold role9; ring)) (r9.trans hthr)
  · refine share_paid_le (mul_nonneg (by norm_num) hB) (by norm_num) hr0 ?_ (r28o.trans hthr)
    unfold role28op
    linarith only [hB]
  · exact share_paid_le (mCoef_nonneg hφ caps) (by linarith only [hTp]) hr0 le_rfl
      (r28t.trans hthr)

/-! ### G. The pointwise budget along the solution -/

/-- The six term bounds of `h1RHS` at a time `u` of the piece (`N1` is the bound of
`‖fastNL‖₁`, `fastNL_one_le`). -/
theorem h1RHS_terms (h : ActualSol μ φ r g y Ty) {Tp σ Cs : ℝ} (hTp : 0 ≤ Tp) (hφ : 0 ≤ φ)
    (hres : ResH1 σ Cs) {caps : Caps} {s t : ℝ}
    (hP : PieceHyp Tp (h1Threshold Tp μ φ) r g y Ty caps s t)
    (hK : h1K₁ * Real.sqrt caps.PF * caps.yF ^ (3 / 2 : ℝ) * nearN |r| ≤ 1)
    {u : ℝ} (hu : u ∈ Icc s t) :
    -pair 1 (PiF (actual r g y u)) (Qres (PiF (actual r g y u)) (PiF (actual r g y u))) ≤
        Cs * fastNorm 1 r g y u ^ (3 - σ) * fastNorm 2 r g y u ^ σ ∧
      -pair 1 (PiF (actual r g y u)) (Hpsi r g y u) ≤ nfConst φ caps r * fastNorm 2 r g y u ∧
      2 * pair 1 (PiF (actual r g y u)) (X1op r (r * u) (slowNL r g y u) (PiF (actual r g y u))) ≤
        2 ^ 10 * hSrc φ caps * fastNorm 1 r g y u * fastNorm 2 r g y u / |r| ∧
      X1bil r (r * u) (PiS (actual r g y u)) (PiF (actual r g y u)) (fastNL r g y u) ≤
        2 ^ 8 * cp caps.BS * fastNorm 1 r g y u *
          (cQ1 * Real.sqrt (fastNorm 1 r g y u * fastNorm 2 r g y u) * fastNorm 2 r g y u +
            8 * (cp caps.WS * fastNorm 2 r g y u +
              cI * cp caps.BS * Real.sqrt (fastNorm 1 r g y u * fastNorm 2 r g y u)) +
            h1Const φ caps r) / |r| ∧
      -cubicHeat r (r * u) (PiF (actual r g y u)) ≤
        cHeat * nearP |r| * fastNorm 2 r g y u ^ 3 ∧
      cubicD 1 (-1) r (r * u) (PiF (actual r g y u)) (fastNL r g y u) ≤
        (nearC₀ * nearN |r| + 2 ^ 14 / |r|) *
          (cQ1 * Real.sqrt (fastNorm 1 r g y u * fastNorm 2 r g y u) * fastNorm 2 r g y u +
            8 * (cp caps.WS * fastNorm 2 r g y u +
              cI * cp caps.BS * Real.sqrt (fastNorm 1 r g y u * fastNorm 2 r g y u)) +
            h1Const φ caps r) * fastNorm 2 r g y u ^ 2 := by
  obtain ⟨hr1, -, -, -, -, -, -, -, -, -, -, sψ, sh1, -⟩ := shares_of_threshold hTp hφ hP.thr hK
  have hr0 : 0 < |r| := by linarith
  have hr : r ≠ 0 := fun h0 => by rw [h0, abs_zero] at hr0; exact lt_irrefl _ hr0
  have hu0 : 0 ≤ u := hP.hs.trans hu.1
  have huT := lt_lifespan hu.2 hP.ht
  have hx := actual_adm h hu0 huT
  obtain ⟨cF1, cF2, cS1, cS2, cW⟩ := hP.onPrefix.1 u hu
  set F := PiF (actual r g y u) with hFdef
  set S := PiS (actual r g y u) with hSdef
  set a := fastNorm 1 r g y u with hadef
  set b := fastNorm 2 r g y u with hbdef
  set N1 := cQ1 * Real.sqrt (a * b) * b + 8 * (cp caps.WS * b + cI * cp caps.BS * Real.sqrt (a * b))
    + h1Const φ caps r with hN1def
  have hF : Adm 2 F := hx.PiF
  have hS : Adm 2 S := hx.PiS
  have hF' : PiF F = F := by
    funext k; by_cases hk : k 2 = 0 <;> simp [hFdef, PiF, hk]
  have hS' : PiS S = S := by
    funext k; by_cases hk : k 2 = 0 <;> simp [hSdef, PiS, hk]
  obtain ⟨hψ, hψle⟩ := psi_piece h hr hu0
  have hε : hnorm 2 (psi r 0 g u) ≤ 1 := hψle.trans sψ
  obtain ⟨hHI, hH0, hH1⟩ := Hpsi_bounds h hP.onPrefix hu hP.hs huT hε
  have hc4 := c4_pos
  have hW := cp_nonneg caps.WS
  have hY := cp_nonneg caps.yF
  have hA := cp_nonneg caps.AS
  have hPc := cp_nonneg caps.PF
  have hB := cp_nonneg caps.BS
  have hψ0 := hnorm_nonneg 2 (psi r 0 g u)
  have hH0' : hnorm 0 (Hpsi r g y u) ≤ nfConst φ caps r := by
    refine hH0.trans ?_
    unfold nfConst
    have e : 4 * (1 + c4) * φ * (cp caps.WS + cp caps.yF + cp caps.AS + cp caps.PF + 1) / |r| =
        2 * (1 + c4) * (2 * φ / |r|) * (cp caps.WS + cp caps.yF + cp caps.AS + cp caps.PF + 1) := by
      ring
    rw [e]
    have h5 : 0 ≤ cp caps.WS + cp caps.yF + cp caps.AS + cp caps.PF + 1 := by linarith
    have h6 : 0 ≤ 2 * (1 + c4) := by linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hψle h6) h5
  have hH1' : hnorm 1 (Hpsi r g y u) ≤ h1Const φ caps r := by
    refine hH1.trans ?_
    unfold h1Const
    have e : 32 * (1 + c4) * φ * (cp caps.BS + cp caps.yF + cp caps.WS + 1) / |r| =
        16 * (1 + c4) * (2 * φ / |r|) * (cp caps.BS + cp caps.yF + cp caps.WS + 1) := by
      ring
    rw [e]
    have h5 : 0 ≤ cp caps.BS + cp caps.yF + cp caps.WS + 1 := by linarith
    have h6 : 0 ≤ 16 * (1 + c4) := by linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hψle h6) h5
  obtain ⟨hslowMZ, hslowle⟩ := slowNL_one_le h hP.onPrefix hu hP.hs huT hε
  obtain ⟨hfastMZ, hfastle⟩ := fastNL_one_le h hP.onPrefix hu hP.hs huT
  obtain ⟨hfastR, -, -⟩ := fastNL_l2 h hu0 huT
  have hN1 : hnorm 1 (fastNL r g y u) ≤ N1 := hfastle.trans (by rw [hN1def]; linarith)
  have ha0 : 0 ≤ a := hnorm_nonneg _ _
  have hb0 : 0 ≤ b := hnorm_nonneg _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (neg_le_abs _).trans (hres F hF hF')
  · have hF1 : InH (1 + 1) F := hF.inH.mono (by norm_num)
    have hH : InH (1 - 1) (Hpsi r g y u) := hHI.mono (by norm_num)
    have := (pair_le hF1 hH).2
    rw [show (1 : ℝ) + 1 = 2 by norm_num, show (1 : ℝ) - 1 = 0 by norm_num] at this
    calc -pair 1 F (Hpsi r g y u) ≤ |pair 1 F (Hpsi r g y u)| := neg_le_abs _
      _ ≤ hnorm 2 F * hnorm 0 (Hpsi r g y u) := this
      _ ≤ b * nfConst φ caps r := mul_le_mul_of_nonneg_left hH0' hb0
      _ = _ := mul_comm _ _
  · have h1 := X1op_slow_le hr (r * u) hslowMZ (slowNL_l2 h hu0 huT).1 (PiS_slowNL u) hF.mz hF'
    have h2 : 2 * pair 1 F (X1op r (r * u) (slowNL r g y u) F) ≤
        2 * |pair 1 F (X1op r (r * u) (slowNL r g y u) F)| := by
      linarith [le_abs_self (pair 1 F (X1op r (r * u) (slowNL r g y u) F))]
    refine h2.trans ((mul_le_mul_of_nonneg_left h1 (by norm_num)).trans ?_)
    have hS0 := hSrc_nonneg hφ caps
    have h4 : 0 ≤ 2 ^ 9 * a * b / |r| := by positivity
    have h3 : 2 ^ 9 * hnorm 1 (slowNL r g y u) * a * b / |r| ≤ 2 ^ 9 * hSrc φ caps * a * b / |r| := by
      have := mul_le_mul_of_nonneg_left hslowle h4
      calc 2 ^ 9 * hnorm 1 (slowNL r g y u) * a * b / |r|
          = 2 ^ 9 * a * b / |r| * hnorm 1 (slowNL r g y u) := by ring
        _ ≤ 2 ^ 9 * a * b / |r| * hSrc φ caps := this
        _ = _ := by ring
    calc 2 * (2 ^ 9 * hnorm 1 (slowNL r g y u) * a * b / |r|)
        ≤ 2 * (2 ^ 9 * hSrc φ caps * a * b / |r|) := mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ = _ := by ring
  · have h1 := X1bil_le hr (r * u) hS.mz hS.real hS' hF.mz hF' hfastMZ (PiF_fastNL u)
    have hBS : hnorm 2 S ≤ cp caps.BS := cS2.trans (le_cp _)
    refine (le_abs_self _).trans (h1.trans ?_)
    have h4 : 0 ≤ 2 ^ 8 * a / |r| := by positivity
    have h5 : hnorm 2 S * hnorm 1 (fastNL r g y u) ≤ cp caps.BS * N1 :=
      mul_le_mul hBS hN1 (hnorm_nonneg _ _) hB
    calc 2 ^ 8 * hnorm 2 S * a * hnorm 1 (fastNL r g y u) / |r|
        = 2 ^ 8 * a / |r| * (hnorm 2 S * hnorm 1 (fastNL r g y u)) := by ring
      _ ≤ 2 ^ 8 * a / |r| * (cp caps.BS * N1) := mul_le_mul_of_nonneg_left h5 h4
      _ = _ := by ring
  · have h1 : |cubicHeat r (r * u) F| ≤ cHeat * nearP |r| * b ^ 3 :=
      cubicHeat_le hr1 (r * u) hF.mz hF.real hF'
    exact (neg_le_abs _).trans h1
  · have h1 := cubicD_one_le (Or.inr rfl) hr (r * u) hF.mz hF.real hF' hfastMZ hfastR
    have hN := nearN_nonneg |r|
    have hC := nearC₀_pos
    refine (le_abs_self _).trans (h1.trans ?_)
    have h4 : 0 ≤ (nearC₀ * nearN |r| + 2 ^ 14 / |r|) * b ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hN1 h4
    calc (nearC₀ * nearN |r| + 2 ^ 14 / |r|) * hnorm 1 (fastNL r g y u) * b ^ 2
        = (nearC₀ * nearN |r| + 2 ^ 14 / |r|) * b ^ 2 * hnorm 1 (fastNL r g y u) := by ring
      _ ≤ (nearC₀ * nearN |r| + 2 ^ 14 / |r|) * b ^ 2 * N1 := this
      _ = _ := by ring

/-- The near–force share `nearC₀ N(q) h1 ≤ 1/64` from `h1 ≤ 1/(2¹⁶ nearC₀)` (`N(q) ≤ 2¹⁰`). -/
lemma share_nearForce {φ r : ℝ} (hφ : 0 ≤ φ) {caps : Caps}
    (sh1 : h1Const φ caps r ≤ 1 / (2 ^ 16 * nearC₀)) :
    nearC₀ * nearN |r| * h1Const φ caps r ≤ 1 / 64 := by
  have h1 := nearN_le_two_pow_ten |r|
  have hC := nearC₀_pos
  have h3 : nearC₀ * nearN |r| ≤ nearC₀ * 2 ^ 10 := mul_le_mul_of_nonneg_left h1 hC.le
  have h2 : nearC₀ * 2 ^ 10 * (1 / (2 ^ 16 * nearC₀)) = 1 / 64 := by
    field_simp
    ring
  calc nearC₀ * nearN |r| * h1Const φ caps r ≤ nearC₀ * 2 ^ 10 * (1 / (2 ^ 16 * nearC₀)) :=
        mul_le_mul h3 sh1 (h1Const_nonneg hφ caps r) (by positivity)
    _ = 1 / 64 := h2

/-- `h1 ≤ 1` from `h1 ≤ 1/(2¹⁶ nearC₀)`. -/
lemma h1Const_le_one {φ r : ℝ} {caps : Caps} (sh1 : h1Const φ caps r ≤ 1 / (2 ^ 16 * nearC₀)) :
    h1Const φ caps r ≤ 1 := by
  refine sh1.trans ?_
  have hC := nearC₀_pos
  have hC1 := one_le_nearC₀
  rw [div_le_one (by positivity)]
  linarith only [hC1]

/-- The source sum of `budget_core` is `srcAll`. -/
lemma srcAll_eq (caps : Caps) : cQ1 * Real.sqrt (cp caps.PF) * cp caps.yF ^ (3 / 2 : ℝ) +
    8 * (cp caps.WS * cp caps.yF + cI * cp caps.BS * Real.sqrt (cp caps.PF * cp caps.yF)) + 1 =
    srcAll caps := by
  unfold srcAll ffCoef mixNear
  ring

/-- The multiplier of `budget_core` is below `mConst`. -/
lemma budget_mult_le (φ : ℝ) (caps : Caps) {r a : ℝ} (hr0 : 0 < |r|) :
    (2 ^ 9 * hSrc φ caps + 2 ^ 10 * (cp caps.BS * cp caps.WS + cI * cp caps.BS ^ 2) +
      2 ^ 7 * cp caps.BS) / |r| * a ^ 2 ≤ mConst φ caps r * a ^ 2 := by
  unfold mConst mCoef
  have hB := cp_nonneg caps.BS
  have hW := cp_nonneg caps.WS
  have hcI := cI_pos
  have h0 : 0 ≤ cp caps.BS * cp caps.WS + cI * cp caps.BS ^ 2 :=
    add_nonneg (mul_nonneg hB hW) (mul_nonneg hcI.le (sq_nonneg _))
  have h1 : 2 ^ 9 * hSrc φ caps + 2 ^ 10 * (cp caps.BS * cp caps.WS + cI * cp caps.BS ^ 2) +
      2 ^ 7 * cp caps.BS ≤ 2 ^ 9 * hSrc φ caps +
      2 ^ 12 * (cp caps.BS * cp caps.WS + cI * cp caps.BS ^ 2) + 2 ^ 8 * cp caps.BS := by
    linarith only [h0, hB]
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h1 hr0.le) (sq_nonneg a)

/-- The bookkeeping of `h1RHS`: it is the sum of the six terms of `h1RHS_terms`. -/
lemma h1RHS_eq_six (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) :
    h1RHS r g y u = -pair 1 (PiF (actual r g y u))
          (Qres (PiF (actual r g y u)) (PiF (actual r g y u))) +
        (-pair 1 (PiF (actual r g y u)) (Hpsi r g y u)) +
        2 * pair 1 (PiF (actual r g y u))
          (X1op r (r * u) (slowNL r g y u) (PiF (actual r g y u))) +
        X1bil r (r * u) (PiS (actual r g y u)) (PiF (actual r g y u)) (fastNL r g y u) +
        (-cubicHeat r (r * u) (PiF (actual r g y u))) +
        cubicD 1 (-1) r (r * u) (PiF (actual r g y u)) (fastNL r g y u) := by
  unfold h1RHS X1bil
  ring

/-- **The pointwise budget** (TeX eq. quant-h1-energy at `n = 3/4`): on a piece where the caps
hold, the thresholds are paid and the leading role 15 is paid, for every `u ∈ [s,t]`,
`h1RHS u ≤ ¼ b_F² + C_s a_F^{3−σ} b_F^σ + N_f b_F + f_f + m a_F²` with the constant sources
`N_f = nfConst`, `f_f = ffConst`, `m = mConst`. -/
theorem h1RHS_budget (h : ActualSol μ φ r g y Ty) {Tp σ Cs : ℝ} (hTp : 0 ≤ Tp) (hφ : 0 ≤ φ)
    (hres : ResH1 σ Cs) {caps : Caps} {s t : ℝ}
    (hP : PieceHyp Tp (h1Threshold Tp μ φ) r g y Ty caps s t)
    (hK : h1K₁ * Real.sqrt caps.PF * caps.yF ^ (3 / 2 : ℝ) * nearN |r| ≤ 1)
    {u : ℝ} (hu : u ∈ Icc s t) :
    h1RHS r g y u ≤ 1 / 4 * fastNorm 2 r g y u ^ 2 +
      Cs * fastNorm 1 r g y u ^ (3 - σ) * fastNorm 2 r g y u ^ σ +
      nfConst φ caps r * fastNorm 2 r g y u + ffConst φ caps r +
      mConst φ caps r * fastNorm 1 r g y u ^ 2 := by
  obtain ⟨hr1, sK, smix, sheat, -, sslow, sQ, sSF, sfar, -, -, -, sh1, -⟩ :=
    shares_of_threshold hTp hφ hP.thr hK
  obtain ⟨hTres, hTf, hTslow, hTbil, hTheat, hTD⟩ := h1RHS_terms h hTp hφ hres hP hK hu
  have hr0 : 0 < |r| := by linarith only [hr1]
  have hu0 : 0 ≤ u := hP.hs.trans hu.1
  have huT := lt_lifespan hu.2 hP.ht
  have hx := actual_adm h hu0 huT
  obtain ⟨cF1, cF2, -, -, -⟩ := hP.onPrefix.1 u hu
  have hab : fastNorm 1 r g y u ≤ fastNorm 2 r g y u := hnorm_mono (by norm_num) hx.PiF.inH
  have hsrc : 2 ^ 14 * (cQ1 * Real.sqrt (cp caps.PF) * cp caps.yF ^ (3 / 2 : ℝ) +
      8 * (cp caps.WS * cp caps.yF + cI * cp caps.BS * Real.sqrt (cp caps.PF * cp caps.yF)) + 1) /
        |r| ≤ 1 / 64 := by
    rw [srcAll_eq]
    exact sfar
  have hcH : 0 ≤ cHeat := by unfold cHeat; positivity
  have ha0 : 0 ≤ fastNorm 1 r g y u := hnorm_nonneg _ _
  have hb0 : 0 ≤ fastNorm 2 r g y u := hnorm_nonneg _ _
  have hcore := budget_core ha0 hb0 hab hr0 (cp_nonneg _)
    (cp_nonneg _) (cF1.trans (le_cp _)) (cF2.trans (le_cp _))
    (mul_nonneg nearC₀_pos.le (nearN_nonneg _)) (nearP_nonneg (abs_nonneg r))
    (hSrc_nonneg hφ caps) (h1Const_nonneg hφ caps r) (h1Const_le_one sh1)
    cI_pos.le cQ1_pos.le hcH hTres hTf hTslow hTbil hTheat hTD sK smix
    (share_nearForce hφ sh1) sheat sslow sQ sSF hsrc
  have hm := budget_mult_le φ caps (a := fastNorm 1 r g y u) hr0
  have hff : 2 ^ 8 * cp caps.BS * h1Const φ caps r ^ 2 / |r| = ffConst φ caps r := rfl
  rw [hff] at hcore
  rw [h1RHS_eq_six]
  have hb2 := sq_nonneg (fastNorm 2 r g y u)
  linarith only [hcore, hm, hb2]

end Quant

end OVNS

end
