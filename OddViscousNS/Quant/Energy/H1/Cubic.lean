import OddViscousNS.Quant.Energy.H1.Identity

/-!
# E5 — the purefast cubic inputs of the `H¹` energy: near/far additivity, FAR, static, heats

Proofs of four of the six analytic inputs of `H1/Bounds.lean`, restated verbatim with the suffix
`_proved` (`cubicD_eq_near_add_far'`, `farD1_le`, `cubicE_static_le`, `cubicHeat_le`).

* **A, B. Additivity.**  `Qm` is additive in the gain multipliers `corrM = nearCorrM + farCorrM`
  (`Qm_add_mult_gain`); the first two pairings of `D₁` converge by `pair_le`, the third by the
  symmetric-weight pairing.  `Qm_gain_inH_zero`, `pair_add_symm'` are private copies of the
  corresponding facts of `Bounds.lean`.
* **C. The absolute bound** `abs_pair_Qm_le`: no reality; a pairing is below any summable majorant
  of `|p+q|² ‖Z_{p+q}‖ Σ_{a,b,c}‖m‖ ½(|p|+|q|) ‖X_p‖ ‖Y_q‖`.
* **D, E. FAR.**  `c₄² = Σ|k|⁻⁴ ≤ 52` (`c4_le`, through the sup-norm shells).  On `|Φ| ≥ 1` the
  multiplier is `≤ 1/q`.  `|p| + |q|` is split by `2|p||q| ≤ |p|² + |q|²` against `H¹ × H² × H²`;
  each term has one `ℓ¹` slot, and `|D₁^B| ≤ 32 c₄ ‖h‖₁ ‖F‖₂²/q ≤ 2⁸ ‖h‖₁ ‖F‖₂²/q`.
* **F, G. The proper kernels at the longest leg `L`, `K = |L|`.**  `propKer = K κ_N` has moment
  `momP`, `farKer = 1/(m √(K⁴+q²))` has moment `≤ 52 K/(K⁴+q²) ≤ 52 q^{−3/2}`
  (`sum_inv_minLeg_sq_le`).  One helicity: `1/(m D_K) ≤ propKer + farKer` (`ker_le`).  The box sums
  (`boxK`) are summed by `moment_cauchy`; the regions are the positions of the longest leg.
* **H. Static.**  With `H²` on the longest leg, each position of the output has kernel
  `≤ 4/(m D_K)` (`staticKer_big`, `staticKer_out`), without cancellation or reality, so
  `|E⁰| ≤ 96 (√𝔐_P + 8 q^{−3/4}) a_F² b_F`.
* **I. Heats.**  For real `F`, the three rootings carry `(x_a + x_b) f₁(x_c) = Σ f₁(x_c) − f₂(x_c)`
  (`heatTerm_eq`), so by `cyc3_le` they are at most `52 m K⁴/D_K ∏‖F‖`, and with the `H²` weights
  `|E_heat| ≤ 1664 (√𝔐_P + 8 q^{−3/4}) b_F³`.

The locked constants `F₁ = 2¹⁴/q`, `cStat = cHeat = 2¹⁰` are all reached.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS

/-! ### A. The `H⁰` gain bound and the symmetric pairing (private copies of `H1/Bounds.lean`) -/

/-- `∑_p (|p|+|k−p|) ‖f_p‖ ‖g_{k−p}‖ ≤ ‖f‖₁ ‖g‖₀ + ‖f‖₀ ‖g‖₁` (two Cauchy–Schwarz). -/
private lemma vertex_sum_le' {f g : Field} (hf : MZ 1 f) (hg : MZ 1 g) (k : Mode) :
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

/-- `Q^♯_m(f,g) ∈ H⁰` for a gain multiplier and `f, g ∈ H¹` (`Qm_gain_zero_le` of `Bounds.lean`). -/
private lemma Qm_gain_inH_zero {m : Mult} (hm : ∀ a b c p q, ‖m a b c p q‖ ≤ 1 / absSq (p + q))
    {f g : Field} (hf : MZ 1 f) (hg : MZ 1 g) : InH 0 (Qm m f g) := by
  have hf2 : Summable fun p => ‖f p‖ ^ 2 := summable_norm_sq_of_inH (hf.inH.mono (by norm_num))
  have hg2 : Summable fun p => ‖g p‖ ^ 2 := summable_norm_sq_of_inH (hg.inH.mono (by norm_num))
  have hfg : Summable fun p => (absk p * ‖f p‖) ^ 2 :=
    hf.inH.congr fun p => by rw [sobWeight_one, mul_pow, absk_sq]
  set R := hnorm 1 f * hnorm 0 g + hnorm 0 f * hnorm 1 g with hR
  have hR0 : 0 ≤ R := by
    have := hnorm_nonneg 1 f; have := hnorm_nonneg 0 g; have := hnorm_nonneg 0 f
    have := hnorm_nonneg 1 g
    positivity
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
            mul_le_mul_of_nonneg_left (vertex_sum_le' hf hg k) (by positivity)
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
  exact Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_nonneg 0 k) (sq_nonneg _)) hdom
    (summable_inv4.mul_left _)

/-- The pairing with symmetric weights converges absolutely. -/
private lemma pair_summable_symm' {σ : ℝ} {c F : Field} (hc : InH σ c) (hF : InH σ F) :
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

/-- `pair σ c` is additive for symmetric weights. -/
private lemma pair_add_symm' {σ : ℝ} {c F F' : Field} (hc : InH σ c) (hF : InH σ F)
    (hF' : InH σ F') : pair σ c (F + F') = pair σ c F + pair σ c F' := by
  simp only [pair]
  rw [← (pair_summable_symm' hc hF).tsum_add (pair_summable_symm' hc hF')]
  refine tsum_congr fun k => ?_
  rw [Pi.add_apply, inner_add_right, Complex.add_re, mul_add]

/-! ### B. The near/far split for an `H¹` source -/

/-- The output-heat gain of the near corrector multiplier. -/
private lemma nearCorrM_gain {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (r τ : ℝ) (a b c : Sgn) (p q : Mode) :
    ‖Quant.nearCorrM ε r τ a b c p q‖ ≤ 1 / absSq (p + q) := by
  unfold Quant.nearCorrM
  split_ifs with h0
  · exact Quant.norm_corrSym_le hε r τ a b c h0.1
  · rw [norm_zero]
    exact div_nonneg zero_le_one (absSq_nonneg _)

/-- The output-heat gain of the far corrector multiplier. -/
private lemma farCorrM_gain {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (r τ : ℝ) (a b c : Sgn) (p q : Mode) :
    ‖Quant.farCorrM ε r τ a b c p q‖ ≤ 1 / absSq (p + q) := by
  unfold Quant.farCorrM
  split_ifs with h0
  · exact Quant.norm_corrSym_le hε r τ a b c h0.1
  · rw [norm_zero]
    exact div_nonneg zero_le_one (absSq_nonneg _)

/-- `Qm` is additive in a gain multiplier, for `H¹` inputs. -/
private lemma Qm_add_mult_gain {m m₁ m₂ : Mult} {X Y : Field}
    (h₁ : ∀ a b c p q, ‖m₁ a b c p q‖ ≤ 1 / absSq (p + q))
    (h₂ : ∀ a b c p q, ‖m₂ a b c p q‖ ≤ 1 / absSq (p + q))
    (hm : ∀ a b c p q, m a b c p q = m₁ a b c p q + m₂ a b c p q) (hX : MZ 1 X) (hY : MZ 1 Y) :
    Qm m X Y = Qm m₁ X Y + Qm m₂ X Y := by
  have hX2 : Summable fun p => ‖X p‖ ^ 2 := summable_norm_sq_of_inH (hX.inH.mono (by norm_num))
  have hY2 : Summable fun p => ‖Y p‖ ^ 2 := summable_norm_sq_of_inH (hY.inH.mono (by norm_num))
  have hXg : Summable fun p => (absk p * ‖X p‖) ^ 2 :=
    hX.inH.congr fun p => by rw [sobWeight_one, mul_pow, absk_sq]
  funext k
  rw [Pi.add_apply]
  unfold Qm
  have hs := summable_vertex_fixed k hX2 hY2 (Or.inl hXg)
  rw [← (summable_Qm_term_gain h₁ k hs).tsum_add (summable_Qm_term_gain h₂ k hs)]
  refine tsum_congr fun p => ?_
  simp only [hm, add_smul, Finset.sum_add_distrib]

/-- **The near/far split of the native `H¹` differential for an `H¹` source**: `Qm` is additive
in the multiplier for the gain multipliers `corrM = nearCorrM + farCorrM`, the first two pairings
converge by `pair_le`, the third by the symmetric pairing with the `H¹` corrector fields. -/
theorem cubicD_eq_near_add_far'_proved {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (r τ : ℝ) {F h : Field}
    (hF : MZ 2 F) (_hF' : PiF F = F) (hh : MZ 1 h) :
    Quant.cubicD 1 ε r τ F h = Quant.nearD 1 ε r τ F h + Quant.farD 1 ε r τ F h := by
  have hF1 : MZ 1 F := hF.mono' (by norm_num)
  have hG : MZ 1 (PiF h) := hh.PiF'
  have hN := nearCorrM_gain hε r τ
  have hB := farCorrM_gain hε r τ
  have hadd := Quant.corrM_eq_add ε r τ
  have e1 : Quant.corr ε r τ (PiF h) F =
      Quant.nearCorr ε r τ (PiF h) F + Quant.farCorr ε r τ (PiF h) F :=
    Qm_add_mult_gain hN hB hadd hG hF1
  have e2 : Quant.corr ε r τ F (PiF h) =
      Quant.nearCorr ε r τ F (PiF h) + Quant.farCorr ε r τ F (PiF h) :=
    Qm_add_mult_gain hN hB hadd hF1 hG
  have e3 : Quant.corr ε r τ F F = Quant.nearCorr ε r τ F F + Quant.farCorr ε r τ F F :=
    Qm_add_mult_gain hN hB hadd hF1 hF1
  have hF2' : InH ((1 : ℝ) + 1) F := by convert hF.inH using 1; norm_num
  have h0 : ∀ {f g : Field} {m : Mult}, (∀ a b c p q, ‖m a b c p q‖ ≤ 1 / absSq (p + q)) →
      MZ 1 f → MZ 1 g → InH ((1 : ℝ) - 1) (Qm m f g) := fun hm hf hg => by
    have := Qm_gain_inH_zero hm hf hg
    convert this using 1
    norm_num
  have h1 : ∀ {m : Mult}, m.Bdd → InH 1 (Qm m F F) := fun hm => by
    have := (hnorm_Qm_le hm (σ := 2) (by norm_num) hF hF hF hF).1
    convert this using 1
    norm_num
  unfold Quant.cubicD Quant.nearD Quant.farD
  rw [e1, e2, e3]
  simp only [Nat.cast_one]
  have p1 : pair 1 F (Quant.nearCorr ε r τ (PiF h) F + Quant.farCorr ε r τ (PiF h) F) =
      pair 1 F (Quant.nearCorr ε r τ (PiF h) F) + pair 1 F (Quant.farCorr ε r τ (PiF h) F) :=
    pair_add hF2' (h0 hN hG hF1) (h0 hB hG hF1)
  have p2 : pair 1 F (Quant.nearCorr ε r τ F (PiF h) + Quant.farCorr ε r τ F (PiF h)) =
      pair 1 F (Quant.nearCorr ε r τ F (PiF h)) + pair 1 F (Quant.farCorr ε r τ F (PiF h)) :=
    pair_add hF2' (h0 hN hF1 hG) (h0 hB hF1 hG)
  have p3 : pair 1 (PiF h) (Quant.nearCorr ε r τ F F + Quant.farCorr ε r τ F F) =
      pair 1 (PiF h) (Quant.nearCorr ε r τ F F) + pair 1 (PiF h) (Quant.farCorr ε r τ F F) :=
    pair_add_symm' hG.inH (h1 (Quant.nearCorrM_bdd hε r τ)) (h1 (Quant.farCorrM_bdd hε r τ))
  rw [p1, p2, p3]
  ring

/-! ### C. The absolute bound of a pairing -/

/-- The total size of a multiplier on a triad, over the eight helicities. -/
private def Mnorm (m : Mult) (p q : Mode) : ℝ := ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, ‖m a b c p q‖

/-- The size of a multiplier is nonnegative. -/
private lemma Mnorm_nonneg (m : Mult) (p q : Mode) : 0 ≤ Mnorm m p q :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    norm_nonneg _

/-- The summand of `Q^♯_m(X,Y)_k` at `p`, by the size of the multiplier on the triad. -/
private lemma norm_summand_le (m : Mult) (X Y : Field) (k p : Mode) :
    ‖∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, m a b c p (k - p) •
        hel c k (vert p (k - p) (hel a p (X p)) (hel b (k - p) (Y (k - p))))‖ ≤
      Mnorm m p (k - p) * (1 / 2 * ((absk p + absk (k - p)) * (‖X p‖ * ‖Y (k - p)‖))) := by
  set E := 1 / 2 * ((absk p + absk (k - p)) * (‖X p‖ * ‖Y (k - p)‖)) with hE
  have hterm : ∀ a b c, ‖m a b c p (k - p) •
      hel c k (vert p (k - p) (hel a p (X p)) (hel b (k - p) (Y (k - p))))‖ ≤
      ‖m a b c p (k - p)‖ * E := by
    intro a b c
    rw [norm_smul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine (norm_hel_le _ _ _).trans ((norm_vert_le₁ _ _ _ _).trans ?_)
    have h1 := norm_hel_le a p (X p)
    have h2 := norm_hel_le b (k - p) (Y (k - p))
    have h3 : ‖hel a p (X p)‖ * ‖hel b (k - p) (Y (k - p))‖ ≤ ‖X p‖ * ‖Y (k - p)‖ :=
      mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
    have hA : 0 ≤ absk (k - p) + absk p := add_nonneg (absk_nonneg _) (absk_nonneg _)
    calc 1 / 2 * (absk (k - p) + absk p) * (‖hel a p (X p)‖ * ‖hel b (k - p) (Y (k - p))‖)
        ≤ 1 / 2 * (absk (k - p) + absk p) * (‖X p‖ * ‖Y (k - p)‖) :=
          mul_le_mul_of_nonneg_left h3 (by linarith)
      _ = E := by rw [hE]; ring
  refine (norm_sum_le_of_le _ fun a _ => norm_sum_le_of_le _ fun b _ =>
    norm_sum_le_of_le _ fun c _ => hterm a b c).trans (le_of_eq ?_)
  simp only [Mnorm, Finset.sum_mul]

/-- The shear `(k, p) ↦ (p, k − p)` of the lattice square. -/
private def shearK : Mode × Mode ≃ Mode × Mode where
  toFun x := (x.2, x.1 - x.2)
  invFun y := (y.1 + y.2, y.1)
  left_inv x := by ext <;> simp
  right_inv y := by ext <;> simp

/-- **The absolute bound of a pairing** (no reality): if the triad majorant of
`pair 1 Z (Q^♯_m(X,Y))`, with the output weight `|p+q|²`, is below a summable `B`, then the
pairing is below `∑ B`. -/
private lemma abs_pair_Qm_le {m : Mult} (hm : ∀ a b c p q, ‖m a b c p q‖ ≤ 1 / absSq (p + q))
    {X Y Z : Field} (hX2 : Summable fun p => ‖X p‖ ^ 2) (hY2 : Summable fun p => ‖Y p‖ ^ 2)
    (hg : (Summable fun p => (absk p * ‖X p‖) ^ 2) ∨ Summable fun p => (absk p * ‖Y p‖) ^ 2)
    {B : Mode × Mode → ℝ} (hB : Summable B)
    (hpt : ∀ x : Mode × Mode, sobWeight 1 (x.1 + x.2) * ‖Z (x.1 + x.2)‖ *
        (Mnorm m x.1 x.2 * (1 / 2 * ((absk x.1 + absk x.2) * (‖X x.1‖ * ‖Y x.2‖)))) ≤ B x) :
    |pair 1 Z (Qm m X Y)| ≤ ∑' x, B x := by
  have hB' : Summable fun y : Mode × Mode => B (y.2, y.1 - y.2) := shearK.summable_iff.mpr hB
  have hfib : ∀ k, Summable fun p => B (p, k - p) := fun k => hB'.prod_factor k
  have hout : Summable fun k => ∑' p, B (p, k - p) := hB'.prod
  have hval : ∑' k, ∑' p, B (p, k - p) = ∑' x, B x := by
    rw [← shearK.tsum_eq B]
    exact hB'.tsum_prod.symm
  have hG : ∀ k, |sobWeight 1 k * (inner ℂ (Z k) (Qm m X Y k)).re| ≤ ∑' p, B (p, k - p) := by
    intro k
    have hw := sobWeight_nonneg 1 k
    have hs := summable_Qm_term_gain hm k (summable_vertex_fixed k hX2 hY2 hg)
    have h1 : ‖Qm m X Y k‖ ≤ ∑' p, ‖∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, m a b c p (k - p) •
        hel c k (vert p (k - p) (hel a p (X p)) (hel b (k - p) (Y (k - p))))‖ :=
      norm_tsum_le_tsum_norm hs.norm
    have h2 : |(inner ℂ (Z k) (Qm m X Y k)).re| ≤ ‖Z k‖ * ‖Qm m X Y k‖ :=
      (Complex.abs_re_le_norm _).trans (norm_inner_le_norm (𝕜 := ℂ) _ _)
    rw [abs_mul, abs_of_nonneg hw]
    calc sobWeight 1 k * |(inner ℂ (Z k) (Qm m X Y k)).re|
        ≤ sobWeight 1 k * (‖Z k‖ * ∑' p, ‖∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, m a b c p (k - p) •
            hel c k (vert p (k - p) (hel a p (X p)) (hel b (k - p) (Y (k - p))))‖) := by
          refine mul_le_mul_of_nonneg_left (h2.trans ?_) hw
          exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = ∑' p, sobWeight 1 k * ‖Z k‖ * ‖∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, m a b c p (k - p) •
            hel c k (vert p (k - p) (hel a p (X p)) (hel b (k - p) (Y (k - p))))‖ := by
          rw [tsum_mul_left]
          ring
      _ ≤ ∑' p, B (p, k - p) := by
          refine (hs.norm.mul_left _).tsum_le_tsum (fun p => ?_) (hfib k)
          have h3 := hpt (p, k - p)
          have e : p + (k - p) = k := by abel
          simp only [e] at h3
          refine le_trans (mul_le_mul_of_nonneg_left (norm_summand_le m X Y k p) ?_) h3
          exact mul_nonneg hw (norm_nonneg _)
  have hS : Summable fun k => ‖sobWeight 1 k * (inner ℂ (Z k) (Qm m X Y k)).re‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => by
      rw [Real.norm_eq_abs]
      exact hG k) hout
  calc |pair 1 Z (Qm m X Y)| = ‖∑' k, sobWeight 1 k * (inner ℂ (Z k) (Qm m X Y k)).re‖ := rfl
    _ ≤ ∑' k, ‖sobWeight 1 k * (inner ℂ (Z k) (Qm m X Y k)).re‖ := norm_tsum_le_tsum_norm hS
    _ ≤ ∑' k, ∑' p, B (p, k - p) := hS.tsum_le_tsum (fun k => by
        rw [Real.norm_eq_abs]
        exact hG k) hout
    _ = ∑' x, B x := hval

/-! ### D. The lattice constant and the `ℓ¹` weights -/

/-- The sup-norm shell `‖p‖_∞ = n` contributes at most `26/n²` to `Σ |p|⁻⁴`. -/
private lemma shell_four_le {R n : ℕ} (hn : n ∈ Finset.Icc 1 R) :
    ∑ p ∈ ((Quant.modeBox R).erase 0).filter (fun p => Quant.supNorm p = n), (absSq p)⁻¹ ^ 2 ≤
      26 * ((n : ℝ) ^ 2)⁻¹ := by
  have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
  have hn1' : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast Nat.one_le_pow 2 n hn1
  have hnR : (0 : ℝ) < (n : ℝ) ^ 2 := by linarith
  have hcard : (((Quant.modeBox R).erase 0).filter (fun p => Quant.supNorm p = n)).card ≤
      24 * n ^ 2 + 2 := by
    refine le_trans (Finset.card_le_card ?_) (Quant.card_shell_le (R := R) hn1)
    intro p hp
    rw [Finset.mem_filter, Finset.mem_erase] at hp
    exact Finset.mem_filter.2 ⟨hp.1.2, hp.2⟩
  have hinv : ((n : ℝ) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn1'
  have hinv0 : 0 ≤ ((n : ℝ) ^ 2)⁻¹ := inv_nonneg.2 hnR.le
  calc ∑ p ∈ ((Quant.modeBox R).erase 0).filter (fun p => Quant.supNorm p = n), (absSq p)⁻¹ ^ 2
      ≤ ∑ p ∈ ((Quant.modeBox R).erase 0).filter (fun p => Quant.supNorm p = n),
          ((((n : ℝ)) ^ 2)⁻¹) ^ 2 := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hp' := (Finset.mem_filter.1 hp).2
        have := Quant.sq_supNorm_le_absSq p
        rw [hp'] at this
        exact pow_le_pow_left₀ (inv_nonneg.2 (absSq_nonneg p)) (inv_anti₀ hnR this) 2
    _ = ((((Quant.modeBox R).erase 0).filter (fun p => Quant.supNorm p = n)).card : ℝ) *
          ((((n : ℝ)) ^ 2)⁻¹) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((24 * n ^ 2 + 2 : ℕ) : ℝ) * ((((n : ℝ)) ^ 2)⁻¹) ^ 2 := by
        gcongr
    _ = (24 + 2 * ((n : ℝ) ^ 2)⁻¹) * ((n : ℝ) ^ 2)⁻¹ := by
        push_cast
        field_simp
    _ ≤ 26 * ((n : ℝ) ^ 2)⁻¹ := by
        refine mul_le_mul_of_nonneg_right ?_ hinv0
        linarith

/-- `Σ_{p ≠ 0, ‖p‖_∞ ≤ R} |p|⁻⁴ ≤ 52`. -/
private lemma lattice_sum_four (R : ℕ) : ∑ p ∈ (Quant.modeBox R).erase 0, (absSq p)⁻¹ ^ 2 ≤ 52 := by
  classical
  have hmaps : ∀ p ∈ (Quant.modeBox R).erase 0, Quant.supNorm p ∈ Finset.Icc 1 R := by
    intro p hp
    rw [Finset.mem_erase, Quant.mem_modeBox_iff_supNorm_le] at hp
    exact Finset.mem_Icc.2 ⟨Quant.one_le_supNorm hp.1, hp.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have e : Finset.Icc 1 R = Finset.Ioo 0 (R + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioo]
    omega
  calc ∑ n ∈ Finset.Icc 1 R, ∑ p ∈ ((Quant.modeBox R).erase 0).filter
        (fun p => Quant.supNorm p = n), (absSq p)⁻¹ ^ 2
      ≤ ∑ n ∈ Finset.Icc 1 R, 26 * ((n : ℝ) ^ 2)⁻¹ := Finset.sum_le_sum fun n hn => shell_four_le hn
    _ = 26 * ∑ n ∈ Finset.Ioo 0 (R + 1), ((n : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum, e]
    _ ≤ 26 * (2 / (((0 : ℕ) : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (sum_Ioo_inv_sq_le 0 (R + 1)) (by norm_num)
    _ = 52 := by norm_num

/-- `c₄² = Σ_{k≠0}|k|⁻⁴ ≤ 52`, so `c₄ ≤ 8`. -/
private lemma c4_le : c4 ≤ 8 := by
  have hsum : ∑' k : Mode, (if k = 0 then (0 : ℝ) else (absSq k)⁻¹ ^ 2) ≤ 52 := by
    refine Real.tsum_le_of_sum_le (fun k => ?_) fun s => ?_
    · show 0 ≤ if k = 0 then (0 : ℝ) else (absSq k)⁻¹ ^ 2
      split_ifs
      · exact le_rfl
      · exact sq_nonneg _
    have h0 : ∀ k : Mode, 0 ≤ (if k = 0 then (0 : ℝ) else (absSq k)⁻¹ ^ 2) := fun k => by
      split_ifs
      · exact le_rfl
      · exact sq_nonneg _
    set R := s.sup Quant.supNorm with hR
    have hsub : s ⊆ Quant.modeBox R := fun k hk =>
      Quant.mem_modeBox_iff_supNorm_le.2 (Finset.le_sup (f := Quant.supNorm) hk)
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => h0 k).trans ?_
    rw [← Finset.sum_erase (Quant.modeBox R) (a := (0 : Mode)) (by simp)]
    refine le_trans (le_of_eq ?_) (lattice_sum_four R)
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [ite_eq_right (Finset.mem_erase.1 hk).1]
  rw [c4, show (8 : ℝ) = Real.sqrt (8 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_le_sqrt (hsum.trans (by norm_num))

/-- The `ℓ¹` sequence `‖G_k‖/|k|` of an `H¹` field. -/
private def wInv (G : Field) (k : Mode) : ℝ := ‖G k‖ / absk k

/-- The sequence `‖G_k‖/|k|` is nonnegative. -/
private lemma wInv_nonneg (G : Field) (k : Mode) : 0 ≤ wInv G k :=
  div_nonneg (norm_nonneg _) (absk_nonneg k)

/-- `Σ_k ‖G_k‖/|k| ≤ c₄ ‖G‖₁`. -/
private lemma wInv_facts {G : Field} (hG : MZ 1 G) :
    Summable (wInv G) ∧ ∑' k, wInv G k ≤ c4 * hnorm 1 G := by
  set w : Mode → ℝ := fun k => if k = 0 then 0 else (absSq k)⁻¹ with hw
  have hw0 : ∀ k, 0 ≤ w k := fun k => by
    simp only [hw]
    split_ifs
    · exact le_rfl
    · exact inv_nonneg.2 (absSq_nonneg k)
  have hw2 : (fun k => w k ^ 2) = fun k : Mode => if k = 0 then (0 : ℝ) else (absSq k)⁻¹ ^ 2 := by
    funext k
    simp only [hw]
    split_ifs <;> simp
  have hG2 : Summable fun k => (absk k * ‖G k‖) ^ 2 :=
    hG.inH.congr fun k => by rw [sobWeight_one, mul_pow, absk_sq]
  obtain ⟨hs, hle⟩ := Quant.cs_tsum_nonneg' hw0
    (fun k => mul_nonneg (absk_nonneg k) (norm_nonneg (G k)))
    (by rw [hw2]; exact summable_inv4) hG2
  have e : wInv G = fun k => w k * (absk k * ‖G k‖) := by
    funext k
    simp only [hw, wInv]
    by_cases hk : k = 0
    · subst hk
      simp [hG.mean]
    · rw [ite_eq_right hk, ← absk_sq]
      have : absk k ≠ 0 := fun h => hk (absk_eq_zero.1 h)
      field_simp
  rw [e]
  refine ⟨hs, hle.trans (le_of_eq ?_)⟩
  rw [hw2, Quant.sqrt_tsum_grad_sq]
  rfl

/-- The reflected output sequence is `ℓ²` with the same norm. -/
private lemma refl_facts {a : Mode → ℝ} (ha : Summable fun k => a k ^ 2) (f : Mode → ℝ)
    (hf : ∀ k, f (-k) = a k) :
    (Summable fun k => f k ^ 2) ∧ Real.sqrt (∑' k, f k ^ 2) = Real.sqrt (∑' k, a k ^ 2) := by
  have e : ∀ k, f k = a (-k) := fun k => by rw [← hf, neg_neg]
  simp only [e]
  refine ⟨(Equiv.neg Mode).summable_iff.mpr ha, ?_⟩
  have e2 : ∑' k, a (-k) ^ 2 = ∑' k, a k ^ 2 := (Equiv.neg Mode).tsum_eq fun k => a k ^ 2
  rw [e2]

/-! ### E. The FAR native differential -/

/-- On `|Φ| ≥ 1` the corrector multiplier is at most `1/q`. -/
private lemma norm_farCorrM_le {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {r : ℝ} (hr : r ≠ 0) (τ : ℝ)
    (a b c : Sgn) (p q : Mode) : ‖Quant.farCorrM ε r τ a b c p q‖ ≤ 1 / |r| := by
  have hq : 0 < |r| := abs_pos.2 hr
  unfold Quant.farCorrM
  split_ifs with h
  · rw [Quant.norm_corrSym hε]
    apply one_div_le_one_div_of_le hq
    have h1 : |r| ≤ |r * Phi a b c p q| := by
      rw [abs_mul]
      exact le_mul_of_one_le_right hq.le h.2
    exact h1.trans (Real.abs_le_sqrt (by nlinarith [sq_nonneg (absSq (p + q))]))
  · rw [norm_zero]
    positivity

/-- The eight helicities of the far multiplier: at most `8/q`. -/
private lemma Mnorm_far_le {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {r : ℝ} (hr : r ≠ 0) (τ : ℝ)
    (p q : Mode) : Mnorm (Quant.farCorrM ε r τ) p q ≤ 8 / |r| := by
  unfold Mnorm
  calc _ ≤ ∑ _a : Sgn, ∑ _b : Sgn, ∑ _c : Sgn, 1 / |r| :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun c _ =>
          norm_farCorrM_le hε hr τ a b c p q
    _ = 8 / |r| := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
        push_cast
        ring

/-- A pairing with the far corrector, by a majorant of the output-weighted vertex sum. -/
private lemma abs_pair_far_le {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {r : ℝ} (hr : r ≠ 0) (τ : ℝ)
    {X Y Z : Field} (hX2 : Summable fun p => ‖X p‖ ^ 2) (hY2 : Summable fun p => ‖Y p‖ ^ 2)
    (hg : (Summable fun p => (absk p * ‖X p‖) ^ 2) ∨ Summable fun p => (absk p * ‖Y p‖) ^ 2)
    {B : Mode × Mode → ℝ} (hB : Summable B)
    (hpt : ∀ x : Mode × Mode, absSq (x.1 + x.2) * ‖Z (x.1 + x.2)‖ *
        ((absk x.1 + absk x.2) * (‖X x.1‖ * ‖Y x.2‖)) ≤ B x) :
    |pair 1 Z (Quant.farCorr ε r τ X Y)| ≤ 4 / |r| * ∑' x, B x := by
  have hq : 0 < |r| := abs_pos.2 hr
  rw [← tsum_mul_left]
  refine abs_pair_Qm_le (farCorrM_gain hε r τ) hX2 hY2 hg (hB.mul_left _) fun x => ?_
  have h1 := hpt x
  rw [sobWeight_one]
  have hP : 0 ≤ (absk x.1 + absk x.2) * (‖X x.1‖ * ‖Y x.2‖) :=
    mul_nonneg (add_nonneg (absk_nonneg _) (absk_nonneg _)) (by positivity)
  have hS : 0 ≤ absSq (x.1 + x.2) * ‖Z (x.1 + x.2)‖ :=
    mul_nonneg (absSq_nonneg _) (norm_nonneg _)
  have h2 := Mnorm_far_le hε hr τ x.1 x.2
  have e : Mnorm (Quant.farCorrM ε r τ) x.1 x.2 *
      (1 / 2 * ((absk x.1 + absk x.2) * (‖X x.1‖ * ‖Y x.2‖))) ≤
      4 / |r| * ((absk x.1 + absk x.2) * (‖X x.1‖ * ‖Y x.2‖)) := by
    calc _ ≤ 8 / |r| * (1 / 2 * ((absk x.1 + absk x.2) * (‖X x.1‖ * ‖Y x.2‖))) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = _ := by ring
  calc _ ≤ absSq (x.1 + x.2) * ‖Z (x.1 + x.2)‖ *
        (4 / |r| * ((absk x.1 + absk x.2) * (‖X x.1‖ * ‖Y x.2‖))) :=
        mul_le_mul_of_nonneg_left e hS
    _ = 4 / |r| * (absSq (x.1 + x.2) * ‖Z (x.1 + x.2)‖ *
        ((absk x.1 + absk x.2) * (‖X x.1‖ * ‖Y x.2‖))) := by ring
    _ ≤ 4 / |r| * B x := mul_le_mul_of_nonneg_left h1 (by positivity)

/-- `(P + Q) g f ≤ (3/2) P g f + ½ (g/P)(Q² f)`, from `2PQ ≤ P² + Q²`. -/
private lemma vertex_split {P Q g f : ℝ} (hP : 0 < P) (hg : 0 ≤ g) (hf : 0 ≤ f) :
    (P + Q) * (g * f) ≤ 3 / 2 * (P * g * f) + 1 / 2 * (g / P * (Q ^ 2 * f)) := by
  have e : 3 / 2 * (P * g * f) + 1 / 2 * (g / P * (Q ^ 2 * f)) - (P + Q) * (g * f) =
      g * f / (2 * P) * (P - Q) ^ 2 := by
    field_simp
    ring
  have h0 : 0 ≤ g * f / (2 * P) * (P - Q) ^ 2 := by positivity
  linarith

/-- The majorant of `|p+q|² ‖Z_{p+q}‖ (|p|+|q|) ‖G_p‖ ‖F_q‖`, `G ∈ H¹`, `F, Z ∈ H²`. -/
private def farB₁ (G F Z : Field) (x : Mode × Mode) : ℝ :=
  3 / 2 * ((absk x.1 * ‖G x.1‖) * ‖F x.2‖ * (absSq (-(x.1 + x.2)) * ‖Z (-(-(x.1 + x.2)))‖)) +
    1 / 2 * (wInv G x.1 * (absSq x.2 * ‖F x.2‖) * (absSq (-(x.1 + x.2)) * ‖Z (-(-(x.1 + x.2)))‖))

/-- The pointwise bound by `farB₁`. -/
private lemma farB₁_pt {G : Field} (hG : G 0 = 0) (F Z : Field) (x : Mode × Mode) :
    absSq (x.1 + x.2) * ‖Z (x.1 + x.2)‖ * ((absk x.1 + absk x.2) * (‖G x.1‖ * ‖F x.2‖)) ≤
      farB₁ G F Z x := by
  obtain ⟨p, q⟩ := x
  simp only [farB₁, neg_neg, absSq_neg, wInv]
  have hS : 0 ≤ absSq (p + q) * ‖Z (p + q)‖ := mul_nonneg (absSq_nonneg _) (norm_nonneg _)
  by_cases hp : p = 0
  · subst hp
    simp [hG]
  · have hP : 0 < absk p := lt_of_lt_of_le one_pos (one_le_absk hp)
    have h := mul_le_mul_of_nonneg_left
      (vertex_split (Q := absk q) hP (norm_nonneg (G p)) (norm_nonneg (F q))) hS
    rw [absk_sq] at h
    refine h.trans (le_of_eq ?_)
    ring

/-- `farB₁` sums to at most `2 c₄ ‖G‖₁ ‖F‖₂ ‖Z‖₂`, with one `ℓ¹` slot in each term. -/
private lemma farB₁_facts {G F Z : Field} (hG : MZ 1 G) (hF : MZ 2 F) (hZ : MZ 2 Z) :
    Summable (farB₁ G F Z) ∧
      ∑' x, farB₁ G F Z x ≤ 2 * c4 * hnorm 1 G * hnorm 2 F * hnorm 2 Z := by
  have hg0 : ∀ k, 0 ≤ absk k * ‖G k‖ := fun k => mul_nonneg (absk_nonneg k) (norm_nonneg _)
  have hh0 : ∀ k, 0 ≤ absSq k * ‖F k‖ := fun k => mul_nonneg (absSq_nonneg k) (norm_nonneg _)
  have hc0 : ∀ k, 0 ≤ absSq k * ‖Z (-k)‖ := fun k => mul_nonneg (absSq_nonneg k) (norm_nonneg _)
  have hn0 : ∀ k, 0 ≤ ‖F k‖ := fun k => norm_nonneg _
  have hg2 : Summable fun k => (absk k * ‖G k‖) ^ 2 :=
    hG.inH.congr fun k => by rw [sobWeight_one, mul_pow, absk_sq]
  have hh2 := summable_hess hF.inH
  obtain ⟨hc2, hcn⟩ := refl_facts (summable_hess hZ.inH) (fun k => absSq k * ‖Z (-k)‖)
    fun k => by simp [absSq_neg]
  obtain ⟨sW, bW⟩ := wInv_facts hG
  obtain ⟨s1, b1⟩ := summable_tri_second (a := fun k => absk k * ‖G k‖) (b := fun k => ‖F k‖)
    (c := fun k => absSq k * ‖Z (-k)‖) hg0 hn0 hc0 hg2 hc2 (summable_wiener hF.inH)
  obtain ⟨s2, b2⟩ := summable_tri_first (b := wInv G) (a := fun k => absSq k * ‖F k‖)
    (c := fun k => absSq k * ‖Z (-k)‖) (wInv_nonneg G) hh0 hc0 sW hh2 hc2
  have hs := (s1.mul_left (3 / 2)).add (s2.mul_left (1 / 2))
  refine ⟨hs, ?_⟩
  have e : ∑' x, farB₁ G F Z x =
      3 / 2 * ∑' x : Mode × Mode, (absk x.1 * ‖G x.1‖) * ‖F x.2‖ *
          (absSq (-(x.1 + x.2)) * ‖Z (-(-(x.1 + x.2)))‖) +
        1 / 2 * ∑' x : Mode × Mode, wInv G x.1 * (absSq x.2 * ‖F x.2‖) *
          (absSq (-(x.1 + x.2)) * ‖Z (-(-(x.1 + x.2)))‖) := by
    rw [← tsum_mul_left, ← tsum_mul_left]
    exact (s1.mul_left (3 / 2)).tsum_add (s2.mul_left (1 / 2))
  rw [e]
  rw [hcn, sqrt_tsum_hess_sq hZ.inH] at b1 b2
  rw [Quant.sqrt_tsum_grad_sq] at b1
  rw [sqrt_tsum_hess_sq hF.inH] at b2
  have hw := wiener_le hF
  have hg := hnorm_nonneg 1 G
  have hb := hnorm_nonneg 2 F
  have hz := hnorm_nonneg 2 Z
  have b1' := b1.trans (mul_le_mul_of_nonneg_right hw (mul_nonneg hg hz))
  have b2' := b2.trans (mul_le_mul_of_nonneg_right bW (mul_nonneg hb hz))
  nlinarith [b1', b2']

/-- The majorant of `|p+q|² ‖G_{p+q}‖ (|p|+|q|) ‖F_p‖ ‖F_q‖`. -/
private def farB₃ (G F : Field) (x : Mode × Mode) : ℝ :=
  2 * ((absSq x.1 * ‖F x.1‖) * ‖F x.2‖ * (absk (-(x.1 + x.2)) * ‖G (-(-(x.1 + x.2)))‖) +
    ‖F x.1‖ * (absSq x.2 * ‖F x.2‖) * (absk (-(x.1 + x.2)) * ‖G (-(-(x.1 + x.2)))‖))

/-- The pointwise bound by `farB₃` (`|p+q| ≤ |p| + |q|`). -/
private lemma farB₃_pt (G F : Field) (x : Mode × Mode) :
    absSq (x.1 + x.2) * ‖G (x.1 + x.2)‖ * ((absk x.1 + absk x.2) * (‖F x.1‖ * ‖F x.2‖)) ≤
      farB₃ G F x := by
  obtain ⟨p, q⟩ := x
  simp only [farB₃, neg_neg, absk_neg]
  have hL := absk_add_le p q
  have hP := absk_nonneg p
  have hQ := absk_nonneg q
  have hk := absk_nonneg (p + q)
  rw [← absk_sq, ← absk_sq, ← absk_sq]
  set L := absk (p + q)
  set P := absk p
  set Q := absk q
  have hN : 0 ≤ L * ‖G (p + q)‖ * (‖F p‖ * ‖F q‖) := by positivity
  have h1 : L * (P + Q) ≤ 2 * (P ^ 2 + Q ^ 2) := by nlinarith [sq_nonneg (P - Q)]
  have h2 := mul_le_mul_of_nonneg_right h1 hN
  calc L ^ 2 * ‖G (p + q)‖ * ((P + Q) * (‖F p‖ * ‖F q‖))
      = L * (P + Q) * (L * ‖G (p + q)‖ * (‖F p‖ * ‖F q‖)) := by ring
    _ ≤ _ := h2
    _ = _ := by ring

/-- `farB₃` sums to at most `4 c₄ ‖G‖₁ ‖F‖₂²`. -/
private lemma farB₃_facts {G F : Field} (hG : MZ 1 G) (hF : MZ 2 F) :
    Summable (farB₃ G F) ∧ ∑' x, farB₃ G F x ≤ 4 * c4 * hnorm 1 G * hnorm 2 F ^ 2 := by
  have hh0 : ∀ k, 0 ≤ absSq k * ‖F k‖ := fun k => mul_nonneg (absSq_nonneg k) (norm_nonneg _)
  have hc0 : ∀ k, 0 ≤ absk k * ‖G (-k)‖ := fun k => mul_nonneg (absk_nonneg k) (norm_nonneg _)
  have hn0 : ∀ k, 0 ≤ ‖F k‖ := fun k => norm_nonneg _
  have hg2 : Summable fun k => (absk k * ‖G k‖) ^ 2 :=
    hG.inH.congr fun k => by rw [sobWeight_one, mul_pow, absk_sq]
  have hh2 := summable_hess hF.inH
  obtain ⟨hc2, hcn⟩ := refl_facts hg2 (fun k => absk k * ‖G (-k)‖) fun k => by simp [absk_neg]
  have hF1 := summable_wiener hF.inH
  obtain ⟨s1, b1⟩ := summable_tri_second (a := fun k => absSq k * ‖F k‖) (b := fun k => ‖F k‖)
    (c := fun k => absk k * ‖G (-k)‖) hh0 hn0 hc0 hh2 hc2 hF1
  obtain ⟨s2, b2⟩ := summable_tri_first (b := fun k => ‖F k‖) (a := fun k => absSq k * ‖F k‖)
    (c := fun k => absk k * ‖G (-k)‖) hn0 hh0 hc0 hF1 hh2 hc2
  have hs := (s1.add s2).mul_left 2
  refine ⟨hs, ?_⟩
  have e : ∑' x, farB₃ G F x =
      2 * (∑' x : Mode × Mode, (absSq x.1 * ‖F x.1‖) * ‖F x.2‖ *
            (absk (-(x.1 + x.2)) * ‖G (-(-(x.1 + x.2)))‖) +
          ∑' x : Mode × Mode, ‖F x.1‖ * (absSq x.2 * ‖F x.2‖) *
            (absk (-(x.1 + x.2)) * ‖G (-(-(x.1 + x.2)))‖)) := by
    rw [← s1.tsum_add s2, ← tsum_mul_left]
    rfl
  rw [e]
  rw [hcn, Quant.sqrt_tsum_grad_sq, sqrt_tsum_hess_sq hF.inH] at b1 b2
  have hw := wiener_le hF
  have hg := hnorm_nonneg 1 G
  have hb := hnorm_nonneg 2 F
  have b1' := b1.trans (mul_le_mul_of_nonneg_right hw (mul_nonneg hb hg))
  have b2' := b2.trans (mul_le_mul_of_nonneg_right hw (mul_nonneg hb hg))
  nlinarith [b1', b2']

/-- **The FAR native `H¹` differential**: `|D₁^B(F; h)| ≤ 2¹⁴ ‖h‖₁ ‖F‖₂²/q` (in fact `2⁸`), for
fast `F ∈ H²` and `h ∈ H¹`; no reality.  On `|Φ| ≥ 1` the corrector multiplier is at most `1/q`,
so each pairing is an absolute triple sum, summed by Young with one `ℓ¹` slot (`|p|⁻²`
is `ℓ²`, `c₄ ≤ 8`). -/
theorem farD1_le_proved {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {F h : Field}
    (hF : MZ 2 F) (_hF' : PiF F = F) (hh : MZ 1 h) :
    |Quant.farD 1 ε r τ F h| ≤ 2 ^ 14 / |r| * hnorm 1 h * hnorm 2 F ^ 2 := by
  have hq : 0 < |r| := abs_pos.2 hr
  have hG : MZ 1 (PiF h) := hh.PiF'
  set G := PiF h with hGdef
  have hF1 : MZ 1 F := hF.mono' (by norm_num)
  have l2 : ∀ {X : Field}, MZ 1 X → Summable fun p => ‖X p‖ ^ 2 := fun hX =>
    summable_norm_sq_of_inH (hX.inH.mono (by norm_num))
  have gr : ∀ {X : Field}, MZ 1 X → Summable fun p => (absk p * ‖X p‖) ^ 2 := fun hX =>
    hX.inH.congr fun p => by rw [sobWeight_one, mul_pow, absk_sq]
  obtain ⟨s₁, b₁⟩ := farB₁_facts hG hF hF
  obtain ⟨s₃, b₃⟩ := farB₃_facts hG hF
  have p₁ := abs_pair_far_le hε hr τ (X := G) (Y := F) (Z := F) (l2 hG) (l2 hF1) (Or.inl (gr hG))
    s₁ (farB₁_pt hG.mean F F)
  have p₂ := abs_pair_far_le hε hr τ (X := F) (Y := G) (Z := F) (l2 hF1) (l2 hG) (Or.inr (gr hG))
    ((Equiv.prodComm Mode Mode).summable_iff.mpr s₁) (fun x => by
      have h1 := farB₁_pt hG.mean F F (x.2, x.1)
      simp only [add_comm x.2 x.1] at h1
      refine le_trans (le_of_eq ?_) h1
      ring)
  have p₃ := abs_pair_far_le hε hr τ (X := F) (Y := F) (Z := G) (l2 hF1) (l2 hF1) (Or.inl (gr hF1))
    s₃ (farB₃_pt G F)
  have e₂ : ∑' x, (farB₁ G F F ∘ Equiv.prodComm Mode Mode) x = ∑' x, farB₁ G F F x :=
    (Equiv.prodComm Mode Mode).tsum_eq _
  rw [e₂] at p₂
  have hgh : hnorm 1 G ≤ hnorm 1 h := hnorm_PiF_le hh.inH
  have hb := hnorm_nonneg 2 F
  have hg := hnorm_nonneg 1 G
  have hc := c4_pos
  have hc8 := c4_le
  have h4 : 0 ≤ 4 / |r| := by positivity
  have hT : |Quant.farD 1 ε r τ F h| ≤ 4 / |r| * (2 * c4 * hnorm 1 G * hnorm 2 F * hnorm 2 F) +
      4 / |r| * (2 * c4 * hnorm 1 G * hnorm 2 F * hnorm 2 F) +
      4 / |r| * (4 * c4 * hnorm 1 G * hnorm 2 F ^ 2) := by
    unfold Quant.farD
    simp only [Nat.cast_one]
    refine (abs_add_three _ _ _).trans (add_le_add (add_le_add ?_ ?_) ?_)
    · exact p₁.trans (mul_le_mul_of_nonneg_left b₁ h4)
    · exact p₂.trans (mul_le_mul_of_nonneg_left b₁ h4)
    · exact p₃.trans (mul_le_mul_of_nonneg_left b₃ h4)
  refine hT.trans ?_
  have hP : 0 ≤ hnorm 2 F ^ 2 / |r| := by positivity
  have e : 4 / |r| * (2 * c4 * hnorm 1 G * hnorm 2 F * hnorm 2 F) +
      4 / |r| * (2 * c4 * hnorm 1 G * hnorm 2 F * hnorm 2 F) +
      4 / |r| * (4 * c4 * hnorm 1 G * hnorm 2 F ^ 2) =
      32 * c4 * hnorm 1 G * (hnorm 2 F ^ 2 / |r|) := by
    ring
  have e' : 2 ^ 14 / |r| * hnorm 1 h * hnorm 2 F ^ 2 =
      2 ^ 14 * hnorm 1 h * (hnorm 2 F ^ 2 / |r|) := by
    ring
  rw [e, e']
  refine mul_le_mul_of_nonneg_right ?_ hP
  calc 32 * c4 * hnorm 1 G ≤ 32 * 8 * hnorm 1 h := by gcongr
    _ ≤ 2 ^ 14 * hnorm 1 h := by
        have := hnorm_nonneg 1 h
        nlinarith

/-! ### F. The proper kernels, their moments and the box sums -/

namespace Quant

/-- The proper near kernel `K κ_N` at the longest leg `L`. -/
private def propKer (q : ℝ) (L u : Mode) : ℝ := absk L * nearKerSum q L u

/-- The far kernel `1/(m √(K⁴ + q²))` at the longest leg `L`. -/
private def farKer (q : ℝ) (L u : Mode) : ℝ :=
  1 / (minLeg u L * Real.sqrt (absk L ^ 4 + q ^ 2))

/-- The proper near kernel is nonnegative. -/
private lemma propKer_nonneg (q : ℝ) (L u : Mode) : 0 ≤ propKer q L u :=
  mul_nonneg (absk_nonneg L) (nearKerSum_nonneg q L u)

/-- The far kernel is nonnegative. -/
private lemma farKer_nonneg (q : ℝ) (L u : Mode) : 0 ≤ farKer q L u := by
  unfold farKer minLeg
  have h1 := le_min (absk_nonneg u) (absk_nonneg (L - u))
  positivity

/-- The moment of the proper near kernel is `momP`. -/
private lemma sum_propKer_sq (q : ℝ) (L : Mode) :
    ∑ u ∈ nearBox L, propKer q L u ^ 2 ≤ MomP q := by
  refine le_trans (le_of_eq ?_) (momP_le_MomP q L)
  simp only [propKer, mul_pow, ← Finset.mul_sum, sum_nearKerSum_sq, momP]

/-- `θ = q^{−3/4}`: `θ² √q³ = 1`. -/
private lemma theta_sq {q : ℝ} (hq : 0 < q) :
    (q ^ (-(3 : ℝ) / 4)) ^ 2 * Real.sqrt q ^ 3 = 1 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hq.le,
    ← Real.rpow_mul hq.le, ← Real.rpow_add hq]
  norm_num

/-- The Lorentzian against the length: `K/(K⁴ + q²) ≤ q^{−3/2}`. -/
private lemma length_div_le {q K : ℝ} (hq : 0 < q) (hK : 0 ≤ K) :
    K / (K ^ 4 + q ^ 2) ≤ (q ^ (-(3 : ℝ) / 4)) ^ 2 := by
  set s := Real.sqrt q with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hq
  have hs2 : q = s ^ 2 := (Real.sq_sqrt hq.le).symm
  set θ2 := (q ^ (-(3 : ℝ) / 4)) ^ 2 with hθ
  have hθ0 : 0 ≤ θ2 := sq_nonneg _
  have h1 : θ2 * s ^ 3 = 1 := theta_sq hq
  have hden : 0 < K ^ 4 + q ^ 2 := by positivity
  rw [div_le_iff₀ hden, hs2]
  have h2 : K * s ^ 3 ≤ K ^ 4 + s ^ 4 := by
    rcases le_total K s with h | h
    · have : K * s ^ 3 ≤ s * s ^ 3 := mul_le_mul_of_nonneg_right h (by positivity)
      nlinarith [pow_nonneg hK 4]
    · have h3 : s ^ 3 ≤ K ^ 3 := pow_le_pow_left₀ hs0.le h 3
      have : K * s ^ 3 ≤ K * K ^ 3 := mul_le_mul_of_nonneg_left h3 hK
      nlinarith [pow_nonneg hs0.le 4]
  calc K = K * (θ2 * s ^ 3) := by rw [h1, mul_one]
    _ = θ2 * (K * s ^ 3) := by ring
    _ ≤ θ2 * (K ^ 4 + s ^ 4) := mul_le_mul_of_nonneg_left h2 hθ0
    _ = θ2 * (K ^ 4 + (s ^ 2) ^ 2) := by ring

/-- The moment of the far kernel: `Σ_{u ∈ box} 1/(m²(K⁴ + q²)) ≤ 52 K/(K⁴ + q²) ≤ 52 q^{−3/2}`. -/
private lemma sum_farKer_sq {q : ℝ} (hq : 0 < q) (L : Mode) :
    ∑ u ∈ nearBox L, farKer q L u ^ 2 ≤ 52 * (q ^ (-(3 : ℝ) / 4)) ^ 2 := by
  set K := absk L with hK
  have hK0 : 0 ≤ K := absk_nonneg L
  have hden : 0 < K ^ 4 + q ^ 2 := by positivity
  have e : ∀ u, farKer q L u ^ 2 = (K ^ 4 + q ^ 2)⁻¹ * (minLeg u L ^ 2)⁻¹ := fun u => by
    unfold farKer
    rw [div_pow, mul_pow, Real.sq_sqrt hden.le]
    simp only [one_pow, one_div, mul_inv]
    ring
  simp only [e, ← Finset.mul_sum]
  have h1 := sum_inv_minLeg_sq_le L
  have h2 := length_div_le hq hK0
  calc (K ^ 4 + q ^ 2)⁻¹ * ∑ u ∈ nearBox L, (minLeg u L ^ 2)⁻¹
      ≤ (K ^ 4 + q ^ 2)⁻¹ * (52 * K) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hden.le)
    _ = 52 * (K / (K ^ 4 + q ^ 2)) := by
        rw [div_eq_inv_mul]
        ring
    _ ≤ 52 * (q ^ (-(3 : ℝ) / 4)) ^ 2 := by gcongr

/-- `√(52 θ²) ≤ 8 θ`. -/
private lemma sqrt_farMom_le {θ : ℝ} (hθ : 0 ≤ θ) : Real.sqrt (52 * θ ^ 2) ≤ 8 * θ := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [sq_nonneg θ]

/-- The summand `U_L κ(L, u) V_u W_{L−u}` of a box sum, on `u ∈ nearBox L`. -/
private def boxK (κ : Mode → Mode → ℝ) (U V W : Mode → ℝ) (y : Mode × Mode) : ℝ :=
  if y.2 ∈ nearBox y.1 then U y.1 * (κ y.1 y.2 * (V y.2 * W (y.1 - y.2))) else 0

/-- A box term on the box. -/
private lemma boxK_of_mem {κ : Mode → Mode → ℝ} {U V W : Mode → ℝ} {k u : Mode}
    (hu : u ∈ nearBox k) : boxK κ U V W (k, u) = U k * (κ k u * (V u * W (k - u))) :=
  ite_eq_left hu

/-- Box terms are nonnegative. -/
private lemma boxK_nonneg {κ : Mode → Mode → ℝ} (hκ : ∀ k p, 0 ≤ κ k p) {U V W : Mode → ℝ}
    (hU : ∀ k, 0 ≤ U k) (hV : ∀ k, 0 ≤ V k) (hW : ∀ k, 0 ≤ W k) (y : Mode × Mode) :
    0 ≤ boxK κ U V W y := by
  unfold boxK
  split_ifs
  · exact mul_nonneg (hU _) (mul_nonneg (hκ _ _) (mul_nonneg (hV _) (hW _)))
  · exact le_rfl

/-- The box sum over the lattice square, by `moment_cauchy`. -/
private lemma boxK_tsum_le {κ : Mode → Mode → ℝ} {M : ℝ} (hκ : ∀ k p, 0 ≤ κ k p)
    (hM : ∀ k, ∑ p ∈ nearBox k, κ k p ^ 2 ≤ M) {U V W : Mode → ℝ} (hU : ∀ k, 0 ≤ U k)
    (hV : ∀ k, 0 ≤ V k) (hW : ∀ k, 0 ≤ W k) (hU2 : Summable fun k => U k ^ 2)
    (hV2 : Summable fun k => V k ^ 2) (hW2 : Summable fun k => W k ^ 2) :
    Summable (boxK κ U V W) ∧ ∑' y, boxK κ U V W y ≤
      Real.sqrt M *
        (Real.sqrt (∑' k, U k ^ 2) * Real.sqrt (∑' k, V k ^ 2) * Real.sqrt (∑' k, W k ^ 2)) := by
  obtain ⟨hs, hle⟩ := moment_cauchy hκ hM hU hV hW hU2 hV2 hW2
  have h0 : ∀ k, ∀ u ∉ nearBox k, boxK κ U V W (k, u) = 0 := fun k u hu => ite_eq_right hu
  have hfib : ∀ k, Summable fun u => boxK κ U V W (k, u) := fun k =>
    summable_of_ne_finset_zero (h0 k)
  have hval : ∀ k, ∑' u, boxK κ U V W (k, u) =
      U k * ∑ p ∈ nearBox k, κ k p * (V p * W (k - p)) := fun k => by
    rw [tsum_eq_sum (h0 k), Finset.mul_sum]
    exact Finset.sum_congr rfl fun u hu => boxK_of_mem hu
  have hsum : Summable (boxK κ U V W) :=
    (summable_prod_of_nonneg (boxK_nonneg hκ hU hV hW)).2
      ⟨hfib, by simpa only [Function.comp_def, hval] using hs⟩
  refine ⟨hsum, ?_⟩
  rw [hsum.tsum_prod]
  simpa only [hval] using hle

/-- The weighted amplitude is nonnegative. -/
private lemma wt_nonneg' (n : ℕ) (X : Field) (k : Mode) : 0 ≤ wt n X k :=
  mul_nonneg (pow_nonneg (absk_nonneg k) n) (norm_nonneg _)

/-- The reflected weighted amplitude is nonnegative. -/
private lemma wtN_nonneg' (n : ℕ) (X : Field) (k : Mode) : 0 ≤ wtN n X k :=
  mul_nonneg (pow_nonneg (absk_nonneg k) n) (norm_nonneg _)

/-- The square of the weighted amplitude is the Sobolev summand. -/
private lemma wt_sq' (n : ℕ) {X : Field} (hX : X 0 = 0) (k : Mode) :
    wt n X k ^ 2 = sobWeight n k * ‖X k‖ ^ 2 := by
  by_cases hk : k = 0
  · subst hk
    simp [wt, hX]
  · have e : (2 * (n : ℝ)) = ((2 * n : ℕ) : ℝ) := by push_cast; ring
    have hw : sobWeight n k = absk k ^ (2 * (n : ℝ)) := by simp [sobWeight, hk]
    rw [hw, e, Real.rpow_natCast, wt, mul_pow, ← pow_mul, mul_comm n 2]

/-- The weighted amplitude is `ℓ²` with norm `‖X‖_s`. -/
private lemma wt_facts' {n : ℕ} {s : ℝ} (hs : s = n) {X : Field} (hX : MZ s X) :
    (Summable fun k => wt n X k ^ 2) ∧ Real.sqrt (∑' k, wt n X k ^ 2) = hnorm s X := by
  subst hs
  have e : (fun k => wt n X k ^ 2) = fun k => sobWeight n k * ‖X k‖ ^ 2 :=
    funext (wt_sq' n hX.mean)
  rw [e]
  exact ⟨hX.inH, rfl⟩

/-- The reflected weighted amplitude is `ℓ²` with norm `‖X‖_s`. -/
private lemma wtN_facts' {n : ℕ} {s : ℝ} (hs : s = n) {X : Field} (hX : MZ s X) :
    (Summable fun k => wtN n X k ^ 2) ∧ Real.sqrt (∑' k, wtN n X k ^ 2) = hnorm s X := by
  obtain ⟨h1, h2⟩ := wt_facts' hs hX
  have e : ∀ k, wtN n X k ^ 2 = wt n X (-k) ^ 2 := fun k => by simp only [wtN, wt, absk_neg]
  simp only [e]
  refine ⟨(Equiv.neg Mode).summable_iff.mpr h1, ?_⟩
  rw [← h2, ← (Equiv.neg Mode).tsum_eq fun k => wt n X k ^ 2]
  rfl

/-! ### G. The regions: the longest leg of a fast triad -/

/-- Summability along a permutation (with `e` opaque). -/
private lemma perm_summable {b : Mode × Mode → ℝ} (e : Equiv.Perm (Mode × Mode))
    (h : Summable b) : Summable fun x => b (e x) :=
  e.summable_iff.mpr h

/-- The sum along a permutation (with `e` opaque). -/
private lemma perm_tsum {b : Mode × Mode → ℝ} (e : Equiv.Perm (Mode × Mode)) :
    ∑' x, b (e x) = ∑' x, b x :=
  e.tsum_eq b

/-- `(p, q) ↦ (−p, q)`: the longest leg `−p`. -/
private def eA : Equiv.Perm (Mode × Mode) :=
  Function.Involutive.toPerm (fun x => (-x.1, x.2)) fun x => Prod.ext (by simp) rfl

/-- `(p, q) ↦ (−q, p)`: the longest leg `−q`. -/
private def eB : Equiv.Perm (Mode × Mode) where
  toFun x := (-x.2, x.1)
  invFun x := (x.2, -x.1)
  left_inv x := Prod.ext rfl (by simp)
  right_inv x := Prod.ext (by simp) rfl

/-- `(p, q) ↦ (p + q, p)`: the longest leg `p + q`. -/
private def eC : Equiv.Perm (Mode × Mode) where
  toFun x := (x.1 + x.2, x.1)
  invFun x := (x.2, x.1 - x.2)
  left_inv x := Prod.ext rfl (by simp)
  right_inv x := Prod.ext (by simp) rfl

/-- At least one leg of a triad is the longest. -/
private lemma regions' (p q : Mode) :
    (absk q ≤ absk p ∧ absk (p + q) ≤ absk p) ∨ (absk p ≤ absk q ∧ absk (p + q) ≤ absk q) ∨
      (absk p ≤ absk (p + q) ∧ absk q ≤ absk (p + q)) := by
  rcases le_total (absk p) (absk q) with h1 | h1 <;>
    rcases le_total (absk q) (absk (p + q)) with h2 | h2 <;>
    rcases le_total (absk p) (absk (p + q)) with h3 | h3
  · exact Or.inr (Or.inr ⟨h3, h2⟩)
  · exact Or.inr (Or.inr ⟨h1.trans h2, h2⟩)
  · exact Or.inr (Or.inl ⟨h1, h2⟩)
  · exact Or.inr (Or.inl ⟨h1, h2⟩)
  · exact Or.inr (Or.inr ⟨h3, h2⟩)
  · exact Or.inl ⟨h1, h3⟩
  · exact Or.inl ⟨h1, h2.trans h1⟩
  · exact Or.inl ⟨h1, h3⟩

/-- The helicity pattern of the near set: the phase of a triad with output `k`. -/
private lemma exists_pat' (α β γ : Sgn) (u k : Mode) :
    ∃ s₁ s₂, |lam α u + lam β (k - u) + lam γ (-k)| = |nearPhi s₁ s₂ u k| := by
  cases γ
  · refine ⟨!α, !β, ?_⟩
    have e : lam false k = -lam true k := by simpa using lam_not true k
    simp only [nearPhi, lam_not, lam_neg, e]
    rw [← abs_neg]
    congr 1
    ring
  · refine ⟨α, β, ?_⟩
    simp only [nearPhi, lam_neg]
    congr 1

/-- The third leg of region `A`. -/
private lemma sub_A' (p q : Mode) : -p - q = -(p + q) := by abel

/-- The third leg of region `B`. -/
private lemma sub_B' (p q : Mode) : -q - p = -(p + q) := by abel

/-- The data of region `A`: the longest leg is `p`. -/
private lemma regA {p q : Mode} (hp3 : p 2 ≠ 0) (hq3 : q 2 ≠ 0) (hr3 : (-(p + q)) 2 ≠ 0)
    (h1 : absk q ≤ absk p) (h2 : absk (p + q) ≤ absk p) :
    q ∈ nearBox (-p) ∧ minLeg q (-p) = min (absk q) (absk (p + q)) ∧
      ∀ a b c, ∃ s₁ s₂, |Phi a b c p q| = |nearPhi s₁ s₂ q (-p)| := by
  refine ⟨mem_nearBox.2 ⟨by simpa using hp3, hq3, by rw [sub_A']; exact hr3, by rwa [absk_neg],
    by rw [sub_A', absk_neg, absk_neg]; exact h2⟩, by rw [minLeg, sub_A', absk_neg], ?_⟩
  intro a b c
  obtain ⟨s₁, s₂, h⟩ := exists_pat' b c a q (-p)
  refine ⟨s₁, s₂, ?_⟩
  rw [← h, sub_A', neg_neg, lam_neg, Phi]
  congr 1
  ring

/-- The data of region `B`: the longest leg is `q`. -/
private lemma regB {p q : Mode} (hp3 : p 2 ≠ 0) (hq3 : q 2 ≠ 0) (hr3 : (-(p + q)) 2 ≠ 0)
    (h1 : absk p ≤ absk q) (h2 : absk (p + q) ≤ absk q) :
    p ∈ nearBox (-q) ∧ minLeg p (-q) = min (absk p) (absk (p + q)) ∧
      ∀ a b c, ∃ s₁ s₂, |Phi a b c p q| = |nearPhi s₁ s₂ p (-q)| := by
  refine ⟨mem_nearBox.2 ⟨by simpa using hq3, hp3, by rw [sub_B']; exact hr3, by rwa [absk_neg],
    by rw [sub_B', absk_neg, absk_neg]; exact h2⟩, by rw [minLeg, sub_B', absk_neg], ?_⟩
  intro a b c
  obtain ⟨s₁, s₂, h⟩ := exists_pat' a c b p (-q)
  refine ⟨s₁, s₂, ?_⟩
  rw [← h, sub_B', neg_neg, lam_neg, Phi]
  congr 1
  ring

/-- The data of region `C`: the longest leg is the output `p + q`. -/
private lemma regC {p q : Mode} (hp3 : p 2 ≠ 0) (hq3 : q 2 ≠ 0) (hr3 : (-(p + q)) 2 ≠ 0)
    (h1 : absk p ≤ absk (p + q)) (h2 : absk q ≤ absk (p + q)) :
    p ∈ nearBox (p + q) ∧ minLeg p (p + q) = min (absk p) (absk q) ∧
      ∀ a b c, ∃ s₁ s₂, |Phi a b c p q| = |nearPhi s₁ s₂ p (p + q)| := by
  have e : p + q - p = q := by abel
  have hk3 : (p + q) 2 ≠ 0 := fun h => hr3 (by simp only [Pi.neg_apply, h, neg_zero])
  refine ⟨mem_nearBox.2 ⟨hk3, hp3, by rw [e]; exact hq3, h1, by rw [e]; exact h2⟩,
    by rw [minLeg, e], ?_⟩
  intro a b c
  obtain ⟨s₁, s₂, h⟩ := exists_pat' a b c p (p + q)
  refine ⟨s₁, s₂, ?_⟩
  rw [← h, e, lam_neg, Phi]
  congr 1

/-- One helicity at the longest leg: `1/(m √(K⁴ + (rΦ)²))` is below the proper near kernel on
`0 < |Φ| < 1` and below the far kernel on `|Φ| ≥ 1`. -/
private lemma ker_le (r : ℝ) {Φ : ℝ} {L u : Mode} (hu : u ∈ nearBox L) {s₁ s₂ : Sgn}
    (hΦ : |Φ| = |nearPhi s₁ s₂ u L|) (h0 : Φ ≠ 0) :
    1 / (minLeg u L * Real.sqrt (absk L ^ 4 + (r * Φ) ^ 2)) ≤
      propKer |r| L u + farKer |r| L u := by
  have hm : 0 < minLeg u L := minLeg_pos hu
  have hK : 0 < absk L := lt_of_lt_of_le one_pos (one_le_absk_of_mem_nearBox hu).1
  have hP := propKer_nonneg |r| L u
  have hB := farKer_nonneg |r| L u
  set m := minLeg u L with hmdef
  set K := absk L with hKdef
  have hD : 0 < Real.sqrt (K ^ 4 + (r * Φ) ^ 2) := Real.sqrt_pos.2 (by positivity)
  rcases lt_or_ge |Φ| 1 with h1 | h1
  · have h := kerB_le_nearKerSum 1 r Φ hu hΦ (abs_pos.2 h0) h1
    have e : kerB 1 (r * Φ) m K =
        13 * m ^ 2 * K ^ 2 * (1 / (m * Real.sqrt (K ^ 4 + (r * Φ) ^ 2))) := by
      unfold kerB
      field_simp
    rw [e] at h
    have e2 : 13 * m ^ 2 * K ^ (2 * 1 + 1) * nearKerSum |r| L u =
        13 * m ^ 2 * K ^ 2 * propKer |r| L u := by
      unfold propKer
      ring
    rw [e2] at h
    have := le_of_mul_le_mul_left h (by positivity)
    linarith
  · have h2 : Real.sqrt (K ^ 4 + |r| ^ 2) ≤ Real.sqrt (K ^ 4 + (r * Φ) ^ 2) := by
      refine Real.sqrt_le_sqrt ?_
      have : |r| ^ 2 ≤ (r * Φ) ^ 2 := by
        rw [mul_pow, sq_abs, ← sq_abs Φ]
        have : 1 ≤ |Φ| ^ 2 := one_le_pow₀ h1
        nlinarith [sq_nonneg r]
      linarith
    have h3 : 0 < Real.sqrt (K ^ 4 + |r| ^ 2) := Real.sqrt_pos.2 (by positivity)
    have h4 : 1 / (m * Real.sqrt (K ^ 4 + (r * Φ) ^ 2)) ≤ farKer |r| L u := by
      unfold farKer
      exact one_div_le_one_div_of_le (by positivity)
        (mul_le_mul_of_nonneg_left h2 hm.le)
    linarith

open Classical in
/-- The helicity sum of the kernels at the longest leg. -/
private def kerS (r : ℝ) (L u p q : Mode) : ℝ :=
  ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, if NonRes a b c p q then
    1 / (minLeg u L * Real.sqrt (absk L ^ 4 + (r * Phi a b c p q) ^ 2)) else 0

open Classical in
/-- Over the eight helicities, the kernels at the longest leg are below `8 (K κ_N + κ_B)`. -/
private lemma kerS_le (r : ℝ) {p q L u : Mode} (hu : u ∈ nearBox L)
    (hpat : ∀ a b c, ∃ s₁ s₂, |Phi a b c p q| = |nearPhi s₁ s₂ u L|) :
    kerS r L u p q ≤ 8 * (propKer |r| L u + farKer |r| L u) := by
  set A := propKer |r| L u + farKer |r| L u with hA
  have hA0 : 0 ≤ A := add_nonneg (propKer_nonneg _ _ _) (farKer_nonneg _ _ _)
  have hterm : ∀ a b c, (if NonRes a b c p q then
      1 / (minLeg u L * Real.sqrt (absk L ^ 4 + (r * Phi a b c p q) ^ 2)) else 0) ≤ A := by
    intro a b c
    split_ifs with hN
    · obtain ⟨s₁, s₂, hs⟩ := hpat a b c
      exact ker_le r hu hs hN.2
    · exact hA0
  unfold kerS
  calc _ ≤ ∑ _a : Sgn, ∑ _b : Sgn, ∑ _c : Sgn, A :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun c _ =>
          hterm a b c
    _ = 8 * A := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
        push_cast
        ring

/-! ### H. The static remainder -/

open Classical in
/-- The exact modulus of the corrector multiplier. -/
private lemma norm_corrM_eq {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (r τ : ℝ) (a b c : Sgn) (p q : Mode) :
    ‖corrM ε r τ a b c p q‖ = if NonRes a b c p q then
      1 / Real.sqrt (absSq (p + q) ^ 2 + (r * Phi a b c p q) ^ 2) else 0 := by
  unfold corrM
  split_ifs with h
  · exact norm_corrSym hε r τ a b c p q
  · simp

/-- The output on a leg which is not the longest: the proper kernel, with the three legs
`y, ℓ ≤ K ≤ y + ℓ` (`ℓ` the output, `K` the longest leg). -/
private lemma staticKer_out {K y ℓ : ℝ} (z : ℝ) (hy : 0 < y) (hℓ : 0 < ℓ) (hyK : y ≤ K)
    (hℓK : ℓ ≤ K) (htri : K ≤ y + ℓ) :
    ℓ ^ 2 * ((K + y) / 2) * (1 / Real.sqrt (ℓ ^ 4 + z ^ 2)) ≤
      4 * (K ^ 2 * y * ℓ) * (1 / (min y ℓ * Real.sqrt (K ^ 4 + z ^ 2))) := by
  have hK : 0 < K := hy.trans_le hyK
  have hDℓ : 0 < Real.sqrt (ℓ ^ 4 + z ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hDK : 0 < Real.sqrt (K ^ 4 + z ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hm : 0 < min y ℓ := lt_min hy hℓ
  rw [mul_one_div, mul_one_div, div_le_div_iff₀ hDℓ (by positivity)]
  have hmean : (K + y) / 2 ≤ K := by linarith
  rcases le_total y ℓ with h | h
  · rw [min_eq_left h]
    have h4 : Real.sqrt (K ^ 4 + z ^ 2) ≤ 4 * Real.sqrt (ℓ ^ 4 + z ^ 2) :=
      sqrt_quartic_le hK.le (by linarith) z
    set A := Real.sqrt (K ^ 4 + z ^ 2)
    set B := Real.sqrt (ℓ ^ 4 + z ^ 2)
    calc ℓ ^ 2 * ((K + y) / 2) * (y * A) ≤ ℓ ^ 2 * K * (y * (4 * B)) := by gcongr
      _ = 4 * (ℓ * K * y * ℓ * B) := by ring
      _ ≤ 4 * (K * K * y * ℓ * B) := by gcongr
      _ = 4 * (K ^ 2 * y * ℓ) * B := by ring
  · rw [min_eq_right h]
    have h4 : ℓ ^ 2 * Real.sqrt (K ^ 4 + z ^ 2) ≤ K ^ 2 * Real.sqrt (ℓ ^ 4 + z ^ 2) := by
      have hsq : (ℓ ^ 2 * Real.sqrt (K ^ 4 + z ^ 2)) ^ 2 ≤
          (K ^ 2 * Real.sqrt (ℓ ^ 4 + z ^ 2)) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
        have h5 : ℓ ^ 4 ≤ K ^ 4 := pow_le_pow_left₀ hℓ.le hℓK 4
        nlinarith [mul_le_mul_of_nonneg_right h5 (sq_nonneg z)]
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
    have hK2y : K ≤ 2 * y := by linarith
    set A := Real.sqrt (K ^ 4 + z ^ 2)
    set B := Real.sqrt (ℓ ^ 4 + z ^ 2)
    calc ℓ ^ 2 * ((K + y) / 2) * (ℓ * A) = ((K + y) / 2) * ℓ * (ℓ ^ 2 * A) := by ring
      _ ≤ K * ℓ * (K ^ 2 * B) := by gcongr
      _ = K * K * K * ℓ * B := by ring
      _ ≤ K * K * (2 * y) * ℓ * B := by gcongr
      _ ≤ 4 * (K ^ 2 * y * ℓ) * B := by
          have : 0 ≤ K * K * y * ℓ * B := by positivity
          nlinarith

/-- The output on the longest leg: the proper kernel. -/
private lemma staticKer_big {K x y : ℝ} (z : ℝ) (hx : 0 < x) (hy : 0 < y) (hxK : x ≤ K) :
    K ^ 2 * ((x + y) / 2) * (1 / Real.sqrt (K ^ 4 + z ^ 2)) ≤
      4 * (K ^ 2 * x * y) * (1 / (min x y * Real.sqrt (K ^ 4 + z ^ 2))) := by
  have hK : 0 < K := hx.trans_le hxK
  have hDK : 0 < Real.sqrt (K ^ 4 + z ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hm : 0 < min x y := lt_min hx hy
  rw [mul_one_div, mul_one_div, div_le_div_iff₀ hDK (by positivity)]
  have key : (x + y) / 2 * min x y ≤ 4 * (x * y) := by
    rcases le_total x y with h | h
    · rw [min_eq_left h]
      nlinarith [mul_pos hx hy]
    · rw [min_eq_right h]
      nlinarith [mul_pos hx hy]
  set A := Real.sqrt (K ^ 4 + z ^ 2)
  calc K ^ 2 * ((x + y) / 2) * (min x y * A) = K ^ 2 * A * ((x + y) / 2 * min x y) := by ring
    _ ≤ K ^ 2 * A * (4 * (x * y)) := by gcongr
    _ = 4 * (K ^ 2 * x * y) * A := by ring

open Classical in
/-- The helicity sum of the static multiplier at a triad, against the kernels at the longest
leg. -/
private lemma static_core (r τ : ℝ) {p q L u : Mode} {C : ℝ}
    (hw : ∀ z : ℝ, absk (p + q) ^ 2 * ((absk p + absk q) / 2) *
        (1 / Real.sqrt (absk (p + q) ^ 4 + z ^ 2)) ≤
      C * (1 / (minLeg u L * Real.sqrt (absk L ^ 4 + z ^ 2)))) :
    absSq (p + q) * ((absk p + absk q) / 2) * Mnorm (corrM (-1) r τ) p q ≤
      C * kerS r L u p q := by
  have e : absSq (p + q) ^ 2 = absk (p + q) ^ 4 := by
    rw [← absk_sq]
    ring
  unfold Mnorm kerS
  simp only [Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun c _ => ?_
  rw [norm_corrM_eq (Or.inr rfl)]
  split_ifs with h
  · rw [e, ← absk_sq (p + q)]
    exact hw _
  · simp

/-- The three box terms of the static remainder at a triad. -/
private def statB (κ : Mode → Mode → ℝ) (F : Field) (x : Mode × Mode) : ℝ :=
  boxK κ (wtN 2 F) (wt 1 F) (wtN 1 F) (eA x) + boxK κ (wtN 2 F) (wt 1 F) (wtN 1 F) (eB x) +
    boxK κ (wt 2 F) (wt 1 F) (wt 1 F) (eC x)

/-- The box terms of the static remainder are nonnegative. -/
private lemma statB_parts_nonneg {κ : Mode → Mode → ℝ} (hκ : ∀ k p, 0 ≤ κ k p) (F : Field)
    (x : Mode × Mode) :
    0 ≤ boxK κ (wtN 2 F) (wt 1 F) (wtN 1 F) (eA x) ∧
      0 ≤ boxK κ (wtN 2 F) (wt 1 F) (wtN 1 F) (eB x) ∧
      0 ≤ boxK κ (wt 2 F) (wt 1 F) (wt 1 F) (eC x) :=
  ⟨boxK_nonneg hκ (wtN_nonneg' 2 F) (wt_nonneg' 1 F) (wtN_nonneg' 1 F) _,
    boxK_nonneg hκ (wtN_nonneg' 2 F) (wt_nonneg' 1 F) (wtN_nonneg' 1 F) _,
    boxK_nonneg hκ (wt_nonneg' 2 F) (wt_nonneg' 1 F) (wt_nonneg' 1 F) _⟩

/-- The sum of the static box terms, by the three `moment_cauchy`. -/
private lemma statB_facts {κ : Mode → Mode → ℝ} {M : ℝ} (hκ : ∀ k p, 0 ≤ κ k p)
    (hM : ∀ k, ∑ p ∈ nearBox k, κ k p ^ 2 ≤ M) {F : Field} (hF : MZ 2 F) :
    Summable (statB κ F) ∧
      ∑' x, statB κ F x ≤ 3 * (Real.sqrt M * (hnorm 2 F * hnorm 1 F * hnorm 1 F)) := by
  have hF1 : MZ 1 F := hF.mono' (by norm_num)
  obtain ⟨uN, uNn⟩ := wtN_facts' (n := 2) (s := 2) (by norm_num) hF
  obtain ⟨u2, u2n⟩ := wt_facts' (n := 2) (s := 2) (by norm_num) hF
  obtain ⟨v1, v1n⟩ := wt_facts' (n := 1) (s := 1) (by norm_num) hF1
  obtain ⟨w1, w1n⟩ := wtN_facts' (n := 1) (s := 1) (by norm_num) hF1
  obtain ⟨sA, bA⟩ := boxK_tsum_le hκ hM (wtN_nonneg' 2 F) (wt_nonneg' 1 F) (wtN_nonneg' 1 F)
    uN v1 w1
  obtain ⟨sC, bC⟩ := boxK_tsum_le hκ hM (wt_nonneg' 2 F) (wt_nonneg' 1 F) (wt_nonneg' 1 F)
    u2 v1 v1
  rw [uNn, v1n, w1n] at bA
  rw [u2n, v1n] at bC
  have s1 := perm_summable eA sA
  have s2 := perm_summable eB sA
  have s3 := perm_summable eC sC
  have hs : Summable (statB κ F) := (s1.add s2).add s3
  refine ⟨hs, ?_⟩
  have e : ∑' x, statB κ F x = ∑' x, boxK κ (wtN 2 F) (wt 1 F) (wtN 1 F) (eA x) +
      ∑' x, boxK κ (wtN 2 F) (wt 1 F) (wtN 1 F) (eB x) +
      ∑' x, boxK κ (wt 2 F) (wt 1 F) (wt 1 F) (eC x) := by
    rw [← s1.tsum_add s2, ← (s1.add s2).tsum_add s3]
    exact tsum_congr fun x => rfl
  rw [e, perm_tsum eA, perm_tsum eB, perm_tsum eC]
  set A := ∑' y, boxK κ (wtN 2 F) (wt 1 F) (wtN 1 F) y
  set C := ∑' y, boxK κ (wt 2 F) (wt 1 F) (wt 1 F) y
  set R := Real.sqrt M * (hnorm 2 F * hnorm 1 F * hnorm 1 F)
  have : A + A + C ≤ R + R + R := add_le_add (add_le_add bA bA) bC
  linarith

/-- The common last step of a region of the static remainder. -/
private lemma static_finish {W S Pr A P B C D : ℝ} (hPr : 0 ≤ Pr) (hW : 0 ≤ W)
    (h : A ≤ 4 * W * S) (hS : S ≤ 8 * (P + B)) (hC : C = W * P * Pr) (hD : D = W * B * Pr) :
    A * Pr ≤ 32 * (C + D) := by
  have h1 : A ≤ 32 * W * (P + B) := by
    refine h.trans ?_
    nlinarith [mul_le_mul_of_nonneg_left hS hW]
  have h2 := mul_le_mul_of_nonneg_right h1 hPr
  rw [hC, hD]
  nlinarith [h2]

/-- **The pointwise domination of the static remainder.** -/
private lemma static_point (r τ : ℝ) {F : Field} (hF : PiF F = F) (x : Mode × Mode) :
    sobWeight 1 (x.1 + x.2) * ‖F (x.1 + x.2)‖ * (Mnorm (corrM (-1) r τ) x.1 x.2 *
        (1 / 2 * ((absk x.1 + absk x.2) * (‖F x.1‖ * ‖F x.2‖)))) ≤
      32 * (statB (propKer |r|) F x + statB (farKer |r|) F x) := by
  obtain ⟨p, q⟩ := x
  simp only
  obtain ⟨a1, a2, a3⟩ := statB_parts_nonneg (propKer_nonneg |r|) F (p, q)
  obtain ⟨b1, b2, b3⟩ := statB_parts_nonneg (farKer_nonneg |r|) F (p, q)
  have hR : 0 ≤ statB (propKer |r|) F (p, q) + statB (farKer |r|) F (p, q) := by
    unfold statB
    linarith
  rw [sobWeight_one]
  set Pr := ‖F p‖ * ‖F q‖ * ‖F (p + q)‖ with hPr
  have hPr0 : 0 ≤ Pr := by positivity
  have hE : absSq (p + q) * ‖F (p + q)‖ * (Mnorm (corrM (-1) r τ) p q *
      (1 / 2 * ((absk p + absk q) * (‖F p‖ * ‖F q‖)))) =
      absSq (p + q) * ((absk p + absk q) / 2) * Mnorm (corrM (-1) r τ) p q * Pr := by
    rw [hPr]
    ring
  rw [hE]
  by_cases hfast : p 2 ≠ 0 ∧ q 2 ≠ 0 ∧ (-(p + q)) 2 ≠ 0
  swap
  · have hPrz : Pr = 0 := by
      by_cases h1 : p 2 = 0
      · rw [hPr, fast_zero hF h1]
        simp
      by_cases h2 : q 2 = 0
      · rw [hPr, fast_zero hF h2]
        simp
      have h3 : (-(p + q)) 2 = 0 := by
        by_contra h3
        exact hfast ⟨h1, h2, h3⟩
      have h4 : (p + q) 2 = 0 := by
        rw [Pi.neg_apply, neg_eq_zero] at h3
        exact h3
      rw [hPr, fast_zero hF h4]
      simp
    rw [hPrz, mul_zero]
    linarith
  obtain ⟨hp3, hq3, hr3⟩ := hfast
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp3
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq3
  have hk0 : p + q ≠ 0 := fun h => hr3 (by simp [h])
  have hP : 0 < absk p := lt_of_lt_of_le one_pos (one_le_absk hp0)
  have hQ : 0 < absk q := lt_of_lt_of_le one_pos (one_le_absk hq0)
  have hL : 0 < absk (p + q) := lt_of_lt_of_le one_pos (one_le_absk hk0)
  have htA : absk p ≤ absk q + absk (p + q) := by
    have h := absk_add_le (p + q) (-q)
    rw [show p + q + -q = p by abel, absk_neg] at h
    linarith
  have htB : absk q ≤ absk p + absk (p + q) := by
    have h := absk_add_le (p + q) (-p)
    rw [show p + q + -p = q by abel, absk_neg] at h
    linarith
  rcases regions' p q with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨hu, hm, hpat⟩ := regA hp3 hq3 hr3 h1 h2
    have hcore := static_core r τ (p := p) (q := q) (L := -p) (u := q)
      (C := 4 * (absk p ^ 2 * absk q * absk (p + q))) (fun z => by
        rw [hm, absk_neg]
        exact staticKer_out z hQ hL h1 h2 htA)
    have hk := kerS_le r hu hpat
    have e : ∀ κ : Mode → Mode → ℝ, boxK κ (wtN 2 F) (wt 1 F) (wtN 1 F) (eA (p, q)) =
        absk p ^ 2 * absk q * absk (p + q) * κ (-p) q * Pr := fun κ => by
      show boxK κ (wtN 2 F) (wt 1 F) (wtN 1 F) (-p, q) = _
      rw [boxK_of_mem hu]
      simp only [wtN, wt, neg_neg, absk_neg, sub_A', pow_one, hPr]
      ring
    have := static_finish hPr0 (by positivity) hcore hk (e _) (e _)
    unfold statB
    linarith
  · obtain ⟨hu, hm, hpat⟩ := regB hp3 hq3 hr3 h1 h2
    have hcore := static_core r τ (p := p) (q := q) (L := -q) (u := p)
      (C := 4 * (absk q ^ 2 * absk p * absk (p + q))) (fun z => by
        rw [hm, absk_neg, add_comm (absk p) (absk q)]
        exact staticKer_out z hP hL h1 h2 htB)
    have hk := kerS_le r hu hpat
    have e : ∀ κ : Mode → Mode → ℝ, boxK κ (wtN 2 F) (wt 1 F) (wtN 1 F) (eB (p, q)) =
        absk q ^ 2 * absk p * absk (p + q) * κ (-q) p * Pr := fun κ => by
      show boxK κ (wtN 2 F) (wt 1 F) (wtN 1 F) (-q, p) = _
      rw [boxK_of_mem hu]
      simp only [wtN, wt, neg_neg, absk_neg, sub_B', pow_one, hPr]
      ring
    have := static_finish hPr0 (by positivity) hcore hk (e _) (e _)
    unfold statB
    linarith
  · obtain ⟨hu, hm, hpat⟩ := regC hp3 hq3 hr3 h1 h2
    have hcore := static_core r τ (p := p) (q := q) (L := p + q) (u := p)
      (C := 4 * (absk (p + q) ^ 2 * absk p * absk q)) (fun z => by
        rw [hm]
        exact staticKer_big z hP hQ h1)
    have hk := kerS_le r hu hpat
    have e : ∀ κ : Mode → Mode → ℝ, boxK κ (wt 2 F) (wt 1 F) (wt 1 F) (eC (p, q)) =
        absk (p + q) ^ 2 * absk p * absk q * κ (p + q) p * Pr := fun κ => by
      show boxK κ (wt 2 F) (wt 1 F) (wt 1 F) (p + q, p) = _
      rw [boxK_of_mem hu]
      simp only [wt, add_sub_cancel_left, pow_one, hPr]
      ring
    have := static_finish hPr0 (by positivity) hcore hk (e _) (e _)
    unfold statB
    linarith

end Quant

/-- **The static remainder of the purefast cubic** (role 13): for fast `F ∈ H²` and `q = |r| ≥ 1`,
`|E⁰| ≤ cStat P(q) ‖F‖₁² ‖F‖₂` with `P(q) = nearP q`.  No cancellation, no reality: the proper
weights `(H¹, H¹, H²)`, with `H²` on the longest leg, give the kernel `4/(m D_K)` on each of the
three positions of the output; the near part is `momP`, the far part `Σ_{u ∈ box} 1/(m²(K⁴+q²)) ≤
52 K/(K⁴+q²) ≤ 52 q^{−3/2}`. -/
theorem cubicE_static_le_proved {r : ℝ} (hr : 1 ≤ |r|) (τ : ℝ) {F : Field} (hF : MZ 2 F)
    (hF' : PiF F = F) :
    |Quant.cubicE 1 (-1) r τ F| ≤ Quant.cStat * Quant.nearP |r| * hnorm 1 F ^ 2 * hnorm 2 F := by
  have hq : 0 < |r| := by linarith
  have hF1 : MZ 1 F := hF.mono' (by norm_num)
  set θ := |r| ^ (-(3 : ℝ) / 4) with hθ
  have hθ0 : 0 ≤ θ := Real.rpow_nonneg hq.le _
  obtain ⟨sP, bP⟩ := Quant.statB_facts (κ := Quant.propKer |r|) (M := Quant.MomP |r|)
    (Quant.propKer_nonneg _) (Quant.sum_propKer_sq _) hF
  obtain ⟨sB, bB⟩ := Quant.statB_facts (κ := Quant.farKer |r|) (M := 52 * θ ^ 2)
    (Quant.farKer_nonneg _) (Quant.sum_farKer_sq hq) hF
  have hl2 : Summable fun p => ‖F p‖ ^ 2 := summable_norm_sq_of_inH (hF.inH.mono (by norm_num))
  have hgr : Summable fun p => (absk p * ‖F p‖) ^ 2 :=
    hF1.inH.congr fun p => by rw [sobWeight_one, mul_pow, absk_sq]
  have key := abs_pair_Qm_le (m := Quant.corrM (-1) r τ) (X := F) (Y := F) (Z := F)
    (Quant.corrM_gain (-1) r τ (Or.inr rfl)) hl2 hl2 (Or.inl hgr) ((sP.add sB).mul_left 32)
    (Quant.static_point r τ hF')
  have hE : Quant.cubicE 1 (-1) r τ F = pair 1 F (Qm (Quant.corrM (-1) r τ) F F) := by
    unfold Quant.cubicE Quant.corr
    simp only [Nat.cast_one]
  rw [hE]
  refine key.trans ?_
  rw [tsum_mul_left, sP.tsum_add sB]
  have hS0 := Real.sqrt_nonneg (Quant.MomP |r|)
  have hT := Quant.sqrt_farMom_le hθ0
  set S := Real.sqrt (Quant.MomP |r|)
  set T := Real.sqrt (52 * θ ^ 2)
  have hT0 : 0 ≤ T := Real.sqrt_nonneg _
  have hW : 0 ≤ hnorm 2 F * hnorm 1 F * hnorm 1 F := by
    have := hnorm_nonneg 2 F
    have := hnorm_nonneg 1 F
    positivity
  set W := hnorm 2 F * hnorm 1 F * hnorm 1 F with hWdef
  have e : Quant.cStat * Quant.nearP |r| * hnorm 1 F ^ 2 * hnorm 2 F =
      2 ^ 10 * (18 * S + 2 ^ 7 * θ) * W := by
    unfold Quant.cStat Quant.nearP
    rw [hWdef]
    ring
  rw [e]
  have h1 : 32 * (3 * (S * W) + 3 * (T * W)) ≤ 32 * (3 * (S * W) + 3 * (8 * θ * W)) := by
    gcongr
  have h2 : 0 ≤ S * W := mul_nonneg hS0 hW
  have h3 : 0 ≤ θ * W := mul_nonneg hθ0 hW
  calc 32 * (∑' x, Quant.statB (Quant.propKer |r|) F x + ∑' x, Quant.statB (Quant.farKer |r|) F x)
      ≤ 32 * (3 * (S * W) + 3 * (T * W)) := by gcongr
    _ ≤ 2 ^ 10 * (18 * S + 2 ^ 7 * θ) * W := by nlinarith

/-! ### I. The two input heats -/

namespace Quant

/-- One rooting of the heat remainder at `(p, q)`: both input heats, the output weight. -/
private def heatTri (r τ : ℝ) (F : Field) (x : Mode × Mode) : ℂ :=
  tripT (corrM (-1) r τ) (lapF F) F (lapF F) x.1 x.2 +
    tripT (corrM (-1) r τ) F (lapF F) (lapF F) x.1 x.2

/-- The three rootings of the heat remainder. -/
private def heatTerm (r τ : ℝ) (F : Field) (x : Mode × Mode) : ℂ :=
  heatTri r τ F x + heatTri r τ F (rho (rho x)) + heatTri r τ F (rho x)

/-- The input and output weights of a heat rooting factor out of the triad summand. -/
private lemma heatTri_factor (r τ : ℝ) (F : Field) (p q : Mode) :
    heatTri r τ F (p, q) = ((absSq p + absSq q : ℝ) : ℂ) *
      ((absSq (p + q) : ℂ) * tripT (corrM (-1) r τ) F F F p q) := by
  simp only [heatTri, tripT_lapF_left, tripT_lapF_mid, tripT_lapF_right]
  push_cast
  ring

open Classical in
/-- The output weight turns the resolvent into `f₁(|p+q|²)`. -/
private lemma heat_coef (r τ : ℝ) (a b c : Sgn) (p q : Mode) :
    (absSq (p + q) : ℂ) * corrM (-1) r τ a b c p q =
      if NonRes a b c p q then
        phaseM τ a b c p q * fres 1 (-1) (r * Phi a b c p q) (absSq (p + q)) else 0 := by
  unfold corrM fres corrSym
  split_ifs
  · ring
  · simp

open Classical in
/-- One rooting, helicity by helicity. -/
private lemma heatTri_root (r τ : ℝ) (F : Field) (p q : Mode) :
    heatTri r τ F (p, q) = ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn,
      ((absSq p + absSq q : ℝ) : ℂ) * (if NonRes a b c p q then
        phaseM τ a b c p q * fres 1 (-1) (r * Phi a b c p q) (absSq (p + q)) else 0) *
        tau p q (hel a p (F p)) (hel b q (F q)) (hel c (-(p + q)) (F (-(p + q)))) := by
  rw [heatTri_factor, tripT]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  rw [← heat_coef]
  ring

/-- A heat rooting vanishes with one of its three amplitudes. -/
private lemma heatTri_zero (r τ : ℝ) (F : Field) {p q : Mode}
    (h : ‖F p‖ * ‖F q‖ * ‖F (-(p + q))‖ = 0) : heatTri r τ F (p, q) = 0 := by
  have hb := norm_tripT_le (corrM_bdd (Or.inr rfl) r τ) F F F p q
  have e : (absk p + absk q) * ‖F p‖ * ‖F q‖ * ‖F (-(p + q))‖ =
      (absk p + absk q) * (‖F p‖ * ‖F q‖ * ‖F (-(p + q))‖) := by ring
  rw [e, h, mul_zero, mul_zero] at hb
  have h0 : tripT (corrM (-1) r τ) F F F p q = 0 := norm_le_zero_iff.mp hb
  rw [heatTri_factor, h0]
  simp

/-- The re-rooting of the outer mask. -/
private lemma nonRes_cyc {p q : Mode} (hp : p ≠ 0) (hk : p + q ≠ 0) (a b c : Sgn) :
    NonRes a b c p q ↔ NonRes b c a q (-(p + q)) := by
  have h : q + -(p + q) = -p := by abel
  simp only [NonRes, h, neg_ne_zero, ← Phi_cyc, hp, hk, ne_eq, not_false_eq_true, true_and]

/-- The phase only depends on `Φ`. -/
private lemma phaseM_congr' {τ : ℝ} {a b c a' b' c' : Sgn} {p q p' q' : Mode}
    (h : Phi a b c p q = Phi a' b' c' p' q') :
    phaseM τ a b c p q = phaseM τ a' b' c' p' q' := by
  simp only [phaseM, h]

/-- `f₂(s) = s f₁(s)`. -/
private lemma fres_two (ε z s : ℝ) : fres 2 ε z s = (s : ℂ) * fres 1 ε z s := by
  simp only [fres]
  ring

open Classical in
/-- **The heat term on a nondegenerate triad**: each rooting with output `c` carries the weight
`(x_a + x_b) f₁(x_c) = Σ f₁(x_c) − f₂(x_c)`, `x_i = |ℓ_i|²`, `Σ = x₀ + x₁ + x₂`, so the three
rootings collect into `Σ cyc3₁ − cyc3₂`. -/
private lemma heatTerm_eq (r τ : ℝ) (F : Field) {p q : Mode} (hp : p ≠ 0) (hq : q ≠ 0)
    (hk : p + q ≠ 0) :
    heatTerm r τ F (p, q) = ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn,
      if NonRes a b c p q then phaseM τ a b c p q *
        (((absSq p + absSq q + absSq (p + q) : ℝ) : ℂ) *
          cyc3 1 (-1) (r * Phi a b c p q) p q (-(p + q)) a b c (F p) (F q) (F (-(p + q))) -
          cyc3 2 (-1) (r * Phi a b c p q) p q (-(p + q)) a b c (F p) (F q) (F (-(p + q))))
      else 0 := by
  have hSk : absSq (p + q) = absSq (-(p + q)) := (absSq_neg _).symm
  rw [hSk]
  set s := -(p + q) with hs
  have e1 : -(q + s) = p := by rw [hs]; abel
  have e2 : -(s + p) = q := by rw [hs]; abel
  have e3 : q + s = -p := by rw [hs]; abel
  have e4 : s + p = -q := by rw [hs]; abel
  have hrho : rho (p, q) = (q, s) := rfl
  have hrho2 : rho (q, s) = (s, p) := Prod.ext rfl e1
  have hm1 : (-p : Mode) ≠ 0 := neg_ne_zero.2 hp
  have T1 : heatTri r τ F (p, q) = ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn,
      ((absSq p + absSq q : ℝ) : ℂ) * (if NonRes a b c p q then
        phaseM τ a b c p q * fres 1 (-1) (r * Phi a b c p q) (absSq s) else 0) *
        tau p q (hel a p (F p)) (hel b q (F q)) (hel c s (F s)) := by
    rw [heatTri_root, ← hSk]
  have T2 : heatTri r τ F (s, p) = ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn,
      ((absSq s + absSq p : ℝ) : ℂ) * (if NonRes c a b s p then
        phaseM τ c a b s p * fres 1 (-1) (r * Phi c a b s p) (absSq q) else 0) *
        tau s p (hel c s (F s)) (hel a p (F p)) (hel b q (F q)) := by
    rw [heatTri_root, e2, e4, absSq_neg q]
    exact sum3_rot' fun a b c => ((absSq s + absSq p : ℝ) : ℂ) * (if NonRes a b c s p then
        phaseM τ a b c s p * fres 1 (-1) (r * Phi a b c s p) (absSq q) else 0) *
        tau s p (hel a s (F s)) (hel b p (F p)) (hel c q (F q))
  have T3 : heatTri r τ F (q, s) = ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn,
      ((absSq q + absSq s : ℝ) : ℂ) * (if NonRes b c a q s then
        phaseM τ b c a q s * fres 1 (-1) (r * Phi b c a q s) (absSq p) else 0) *
        tau q s (hel b q (F q)) (hel c s (F s)) (hel a p (F p)) := by
    rw [heatTri_root, e1, e3, absSq_neg p]
    exact sum3_rot fun a b c => ((absSq q + absSq s : ℝ) : ℂ) * (if NonRes a b c q s then
        phaseM τ a b c q s * fres 1 (-1) (r * Phi a b c q s) (absSq p) else 0) *
        tau q s (hel a q (F q)) (hel b s (F s)) (hel c p (F p))
  unfold heatTerm
  rw [hrho, hrho2, T1, T2, T3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hP2 : Phi a b c p q = Phi b c a q s := Phi_cyc a b c p q
  have hP3 : Phi b c a q s = Phi c a b s p := by
    have := Phi_cyc b c a q s
    rwa [e1] at this
  have hN2 : NonRes a b c p q ↔ NonRes b c a q s := nonRes_cyc hp hk a b c
  have hN3 : NonRes b c a q s ↔ NonRes c a b s p := by
    have := nonRes_cyc hq (by rw [e3]; exact hm1 : q + s ≠ 0) b c a
    rwa [e1] at this
  have hph2 : phaseM τ a b c p q = phaseM τ b c a q s := phaseM_congr' hP2
  have hph3 : phaseM τ b c a q s = phaseM τ c a b s p := phaseM_congr' hP3
  rw [← hP3, ← hP2, ← hph3, ← hph2]
  by_cases hN : NonRes a b c p q
  · rw [ite_eq_left hN, ite_eq_left (hN3.1 (hN2.1 hN)), ite_eq_left (hN2.1 hN), ite_eq_left hN]
    unfold cyc3
    simp only [fres_two]
    push_cast
    ring
  · rw [ite_eq_right hN, ite_eq_right fun h => hN (hN2.2 (hN3.2 h)),
      ite_eq_right fun h => hN (hN2.2 h), ite_eq_right hN]
    ring

open Classical in
/-- The pointwise bound of the heat term, with `mn` the shortest and `mx` the longest leg:
`|Σ cyc3₁ − cyc3₂| ≤ 3K² · 13 m K²/D_K + 13 m K⁴/D_K = 52 m K⁴/D_K`. -/
private lemma norm_heatTerm_le (r τ : ℝ) (F : Field) {p q L u : Mode} (hu : u ∈ nearBox L)
    (hp : p ≠ 0) (hq : q ≠ 0) (hk : p + q ≠ 0)
    (hmn : absk p ≤ minLeg u L ∨ absk q ≤ minLeg u L ∨ absk (p + q) ≤ minLeg u L)
    (hmx : absk p ≤ absk L ∧ absk q ≤ absk L ∧ absk (p + q) ≤ absk L) :
    ‖heatTerm r τ F (p, q)‖ ≤ 52 * (minLeg u L ^ 2 * absk L ^ 4) * kerS r L u p q *
      (‖F p‖ * ‖F q‖ * ‖F (-(p + q))‖) := by
  have hm : 0 < minLeg u L := minLeg_pos hu
  have hK : 0 < absk L := lt_of_lt_of_le one_pos (one_le_absk_of_mem_nearBox hu).1
  have hmn' : absk p ≤ minLeg u L ∨ absk q ≤ minLeg u L ∨ absk (-(p + q)) ≤ minLeg u L := by
    rwa [absk_neg]
  have hmx' : absk p ≤ absk L ∧ absk q ≤ absk L ∧ absk (-(p + q)) ≤ absk L := by rwa [absk_neg]
  have hS : absSq p + absSq q + absSq (p + q) ≤ 3 * absk L ^ 2 := by
    obtain ⟨h1, h2, h3⟩ := hmx
    have e1 := pow_le_pow_left₀ (absk_nonneg p) h1 2
    have e2 := pow_le_pow_left₀ (absk_nonneg q) h2 2
    have e3 := pow_le_pow_left₀ (absk_nonneg (p + q)) h3 2
    rw [absk_sq] at e1 e2 e3
    linarith
  have hS0 : 0 ≤ absSq p + absSq q + absSq (p + q) :=
    add_nonneg (add_nonneg (absSq_nonneg _) (absSq_nonneg _)) (absSq_nonneg _)
  have hPr0 : 0 ≤ ‖F p‖ * ‖F q‖ * ‖F (-(p + q))‖ := by positivity
  rw [heatTerm_eq r τ F hp hq hk]
  unfold kerS
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine norm_sum_le_of_le _ fun a _ => norm_sum_le_of_le _ fun b _ =>
    norm_sum_le_of_le _ fun c _ => ?_
  split_ifs with hN
  · set z := r * Phi a b c p q with hz
    have hD : 0 < Real.sqrt (absk L ^ 4 + z ^ 2) := Real.sqrt_pos.2 (by positivity)
    rw [norm_mul, show ‖phaseM τ a b c p q‖ = 1 from by
      rw [phaseM, mul_comm, Complex.norm_exp_ofReal_mul_I], one_mul]
    have c1 := cyc3_le (j := 1) (Or.inl rfl) (ε := -1) (Or.inr rfl) z (ℓ0 := p) (ℓ1 := q)
      (ℓ2 := -(p + q)) (by abel) hp hq (neg_ne_zero.2 hk) a b c (F p) (F q) (F (-(p + q))) hmn' hmx'
    have c2 := cyc3_le (j := 2) (Or.inr rfl) (ε := -1) (Or.inr rfl) z (ℓ0 := p) (ℓ1 := q)
      (ℓ2 := -(p + q)) (by abel) hp hq (neg_ne_zero.2 hk) a b c (F p) (F q) (F (-(p + q))) hmn' hmx'
    have hk1 : 0 ≤ kerB 1 z (minLeg u L) (absk L) := kerB_nonneg _ _ hm.le hK.le
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hS0]
    have h1 := mul_le_mul hS c1 (norm_nonneg _) (by positivity)
    refine (add_le_add h1 c2).trans (le_of_eq ?_)
    unfold kerB
    field_simp
    ring
  · simp

/-- The `H²` weights: `m² K⁴ ≤ 4 x² y² K²`, for `m = min(x, y)`, `K ≤ x + y`. -/
private lemma wt_heat {K x y : ℝ} (hK : 0 ≤ K) (h : K ≤ x + y) :
    min x y ^ 2 * K ^ 4 ≤ 4 * (x ^ 2 * y ^ 2 * K ^ 2) := by
  rcases le_total x y with hxy | hxy
  · rw [min_eq_left hxy]
    have h2 : K ^ 2 ≤ (2 * y) ^ 2 := pow_le_pow_left₀ hK (by linarith) 2
    have h3 : 0 ≤ x ^ 2 * K ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 h3]
  · rw [min_eq_right hxy]
    have h2 : K ^ 2 ≤ (2 * x) ^ 2 := pow_le_pow_left₀ hK (by linarith) 2
    have h3 : 0 ≤ y ^ 2 * K ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 h3]

/-- The three box terms of the heat remainder at a triad. -/
private def heatB (κ : Mode → Mode → ℝ) (F : Field) (x : Mode × Mode) : ℝ :=
  boxK κ (wtN 2 F) (wt 2 F) (wt 2 F) (eA x) + boxK κ (wtN 2 F) (wt 2 F) (wt 2 F) (eB x) +
    boxK κ (wtN 2 F) (wt 2 F) (wt 2 F) (eC x)

/-- The box terms of the heat remainder are nonnegative. -/
private lemma heatB_parts_nonneg {κ : Mode → Mode → ℝ} (hκ : ∀ k p, 0 ≤ κ k p) (F : Field)
    (y : Mode × Mode) : 0 ≤ boxK κ (wtN 2 F) (wt 2 F) (wt 2 F) y :=
  boxK_nonneg hκ (wtN_nonneg' 2 F) (wt_nonneg' 2 F) (wt_nonneg' 2 F) _

/-- The sum of the heat box terms, by the three `moment_cauchy`. -/
private lemma heatB_facts {κ : Mode → Mode → ℝ} {M : ℝ} (hκ : ∀ k p, 0 ≤ κ k p)
    (hM : ∀ k, ∑ p ∈ nearBox k, κ k p ^ 2 ≤ M) {F : Field} (hF : MZ 2 F) :
    Summable (heatB κ F) ∧
      ∑' x, heatB κ F x ≤ 3 * (Real.sqrt M * (hnorm 2 F * hnorm 2 F * hnorm 2 F)) := by
  obtain ⟨uN, uNn⟩ := wtN_facts' (n := 2) (s := 2) (by norm_num) hF
  obtain ⟨u2, u2n⟩ := wt_facts' (n := 2) (s := 2) (by norm_num) hF
  obtain ⟨sA, bA⟩ := boxK_tsum_le hκ hM (wtN_nonneg' 2 F) (wt_nonneg' 2 F) (wt_nonneg' 2 F)
    uN u2 u2
  rw [uNn, u2n] at bA
  have s1 := perm_summable eA sA
  have s2 := perm_summable eB sA
  have s3 := perm_summable eC sA
  have hs : Summable (heatB κ F) := (s1.add s2).add s3
  refine ⟨hs, ?_⟩
  have e : ∑' x, heatB κ F x = ∑' x, boxK κ (wtN 2 F) (wt 2 F) (wt 2 F) (eA x) +
      ∑' x, boxK κ (wtN 2 F) (wt 2 F) (wt 2 F) (eB x) +
      ∑' x, boxK κ (wtN 2 F) (wt 2 F) (wt 2 F) (eC x) := by
    rw [← s1.tsum_add s2, ← (s1.add s2).tsum_add s3]
    exact tsum_congr fun x => rfl
  rw [e, perm_tsum eA, perm_tsum eB, perm_tsum eC]
  set A := ∑' y, boxK κ (wtN 2 F) (wt 2 F) (wt 2 F) y
  set R := Real.sqrt M * (hnorm 2 F * hnorm 2 F * hnorm 2 F)
  have : A + A + A ≤ R + R + R := add_le_add (add_le_add bA bA) bA
  linarith

/-- The common last step of a region of the heat remainder. -/
private lemma heat_finish {X Wt Km S Pr P B C D : ℝ} (hPr : 0 ≤ Pr) (hS : 0 ≤ S)
    (hN : X ≤ 52 * Km * S * Pr) (hw : Km ≤ 4 * Wt) (hS' : S ≤ 8 * (P + B)) (hWt : 0 ≤ Wt)
    (hC : C = Wt * P * Pr) (hD : D = Wt * B * Pr) : X ≤ 1664 * (C + D) := by
  have h1 : Km * S ≤ 4 * Wt * (8 * (P + B)) :=
    (mul_le_mul_of_nonneg_right hw hS).trans
      (mul_le_mul_of_nonneg_left hS' (by positivity))
  have h2 := mul_le_mul_of_nonneg_right h1 hPr
  rw [hC, hD]
  nlinarith [h2]

/-- **The pointwise domination of the heat term.** -/
private lemma heat_point (r τ : ℝ) {F : Field} (hF : PiF F = F) (x : Mode × Mode) :
    ‖heatTerm r τ F x‖ ≤ 1664 * (heatB (propKer |r|) F x + heatB (farKer |r|) F x) := by
  obtain ⟨p, q⟩ := x
  have a1 := heatB_parts_nonneg (propKer_nonneg |r|) F (eA (p, q))
  have a2 := heatB_parts_nonneg (propKer_nonneg |r|) F (eB (p, q))
  have a3 := heatB_parts_nonneg (propKer_nonneg |r|) F (eC (p, q))
  have b1 := heatB_parts_nonneg (farKer_nonneg |r|) F (eA (p, q))
  have b2 := heatB_parts_nonneg (farKer_nonneg |r|) F (eB (p, q))
  have b3 := heatB_parts_nonneg (farKer_nonneg |r|) F (eC (p, q))
  set Pr := ‖F p‖ * ‖F q‖ * ‖F (-(p + q))‖ with hPr
  have hPr0 : 0 ≤ Pr := by positivity
  by_cases hfast : p 2 ≠ 0 ∧ q 2 ≠ 0 ∧ (-(p + q)) 2 ≠ 0
  swap
  · have hPrz : Pr = 0 := by
      by_cases h1 : p 2 = 0
      · rw [hPr, fast_zero hF h1]
        simp
      by_cases h2 : q 2 = 0
      · rw [hPr, fast_zero hF h2]
        simp
      have h3 : (-(p + q)) 2 = 0 := by
        by_contra h3
        exact hfast ⟨h1, h2, h3⟩
      rw [hPr, fast_zero hF h3]
      simp
    have e1 : rho (p, q) = (q, -(p + q)) := rfl
    have e2 : rho (q, -(p + q)) = (-(p + q), p) := Prod.ext rfl (by
      change -(q + -(p + q)) = p
      abel)
    have z1 : heatTri r τ F (p, q) = 0 := heatTri_zero r τ F hPrz
    have z2 : heatTri r τ F (q, -(p + q)) = 0 := heatTri_zero r τ F (by
      have e : -(q + -(p + q)) = p := by abel
      rw [e, ← hPrz, hPr]
      ring)
    have z3 : heatTri r τ F (-(p + q), p) = 0 := heatTri_zero r τ F (by
      have e : -(-(p + q) + p) = q := by abel
      rw [e, ← hPrz, hPr]
      ring)
    have h0 : heatTerm r τ F (p, q) = 0 := by
      unfold heatTerm
      rw [e1, e2, z1, z2, z3]
      simp
    rw [h0, norm_zero]
    unfold heatB
    linarith
  obtain ⟨hp3, hq3, hr3⟩ := hfast
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp3
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq3
  have hk0 : p + q ≠ 0 := fun h => hr3 (by simp [h])
  have htA : absk p ≤ absk q + absk (p + q) := by
    have h := absk_add_le (p + q) (-q)
    rw [show p + q + -q = p by abel, absk_neg] at h
    linarith
  have htB : absk q ≤ absk p + absk (p + q) := by
    have h := absk_add_le (p + q) (-p)
    rw [show p + q + -p = q by abel, absk_neg] at h
    linarith
  have hS0 : ∀ L u, 0 ≤ kerS r L u p q := fun L u =>
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun c _ => by
      have := Real.sqrt_nonneg (absk L ^ 4 + (r * Phi a b c p q) ^ 2)
      have h0 : 0 ≤ minLeg u L := le_min (absk_nonneg _) (absk_nonneg _)
      split_ifs <;> positivity
  have hw3 : 0 ≤ absk p ^ 2 * absk q ^ 2 * absk (p + q) ^ 2 := by positivity
  rcases regions' p q with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨hu, hm, hpat⟩ := regA hp3 hq3 hr3 h1 h2
    have hN := norm_heatTerm_le r τ F hu hp0 hq0 hk0 (by
        rw [hm]
        rcases min_choice (absk q) (absk (p + q)) with h | h
        · exact Or.inr (Or.inl h.ge)
        · exact Or.inr (Or.inr h.ge))
      (by rw [absk_neg]; exact ⟨le_rfl, h1, h2⟩)
    have hw : minLeg q (-p) ^ 2 * absk (-p) ^ 4 ≤
        4 * (absk p ^ 2 * absk q ^ 2 * absk (p + q) ^ 2) := by
      rw [hm, absk_neg]
      refine (wt_heat (absk_nonneg p) htA).trans (le_of_eq ?_)
      ring
    have e : ∀ κ : Mode → Mode → ℝ, boxK κ (wtN 2 F) (wt 2 F) (wt 2 F) (eA (p, q)) =
        absk p ^ 2 * absk q ^ 2 * absk (p + q) ^ 2 * κ (-p) q * Pr := fun κ => by
      show boxK κ (wtN 2 F) (wt 2 F) (wt 2 F) (-p, q) = _
      rw [boxK_of_mem hu]
      simp only [wtN, wt, neg_neg, absk_neg, sub_A', hPr]
      ring
    have := heat_finish hPr0 (hS0 _ _) hN hw (kerS_le r hu hpat) hw3 (e _) (e _)
    unfold heatB
    linarith
  · obtain ⟨hu, hm, hpat⟩ := regB hp3 hq3 hr3 h1 h2
    have hN := norm_heatTerm_le r τ F hu hp0 hq0 hk0 (by
        rw [hm]
        rcases min_choice (absk p) (absk (p + q)) with h | h
        · exact Or.inl h.ge
        · exact Or.inr (Or.inr h.ge))
      (by rw [absk_neg]; exact ⟨h1, le_rfl, h2⟩)
    have hw : minLeg p (-q) ^ 2 * absk (-q) ^ 4 ≤
        4 * (absk p ^ 2 * absk q ^ 2 * absk (p + q) ^ 2) := by
      rw [hm, absk_neg]
      refine (wt_heat (absk_nonneg q) htB).trans (le_of_eq ?_)
      ring
    have e : ∀ κ : Mode → Mode → ℝ, boxK κ (wtN 2 F) (wt 2 F) (wt 2 F) (eB (p, q)) =
        absk p ^ 2 * absk q ^ 2 * absk (p + q) ^ 2 * κ (-q) p * Pr := fun κ => by
      show boxK κ (wtN 2 F) (wt 2 F) (wt 2 F) (-q, p) = _
      rw [boxK_of_mem hu]
      simp only [wtN, wt, neg_neg, absk_neg, sub_B', hPr]
      ring
    have := heat_finish hPr0 (hS0 _ _) hN hw (kerS_le r hu hpat) hw3 (e _) (e _)
    unfold heatB
    linarith
  · obtain ⟨hu, hm, hpat⟩ := regC hp3 hq3 hr3 h1 h2
    have hN := norm_heatTerm_le r τ F hu hp0 hq0 hk0 (by
        rw [hm]
        rcases min_choice (absk p) (absk q) with h | h
        · exact Or.inl h.ge
        · exact Or.inr (Or.inl h.ge))
      ⟨h1, h2, le_rfl⟩
    have hw : minLeg p (p + q) ^ 2 * absk (p + q) ^ 4 ≤
        4 * (absk p ^ 2 * absk q ^ 2 * absk (p + q) ^ 2) := by
      rw [hm]
      exact wt_heat (absk_nonneg _) (absk_add_le p q)
    have e : ∀ κ : Mode → Mode → ℝ, boxK κ (wtN 2 F) (wt 2 F) (wt 2 F) (eC (p, q)) =
        absk p ^ 2 * absk q ^ 2 * absk (p + q) ^ 2 * κ (p + q) p * Pr := fun κ => by
      show boxK κ (wtN 2 F) (wt 2 F) (wt 2 F) (p + q, p) = _
      rw [boxK_of_mem hu]
      simp only [wtN, wt, add_sub_cancel_left, hPr]
      ring
    have := heat_finish hPr0 (hS0 _ _) hN hw (kerS_le r hu hpat) hw3 (e _) (e _)
    unfold heatB
    linarith

end Quant

/-- **Both input heats of the purefast cubic** (role 14): for real fast `F ∈ H²` and `q ≥ 1`,
`|E_heat| ≤ cHeat P(q) ‖F‖₂³`.  Each rooting with output `c` carries the weight
`(x_a + x_b) f₁(x_c) = Σ f₁(x_c) − f₂(x_c)`, so the sum of the three rootings is
`Σ cyc3₁ − cyc3₂`, at most `52 m K⁴/D_K ∏‖F‖`; with the `H²` weights and `K ≤ 2B` the kernel is
`208/(m D_K)`.  The near part has moment `MomP`, the far part `≤ 52 q^{−3/2}`. -/
theorem cubicHeat_le_proved {r : ℝ} (hr : 1 ≤ |r|) (τ : ℝ) {F : Field} (hF : MZ 2 F)
    (hFr : IsReal F) (hF' : PiF F = F) :
    |cubicHeat r τ F| ≤ Quant.cHeat * Quant.nearP |r| * hnorm 2 F ^ 3 := by
  have hq : 0 < |r| := by linarith
  set θ := |r| ^ (-(3 : ℝ) / 4) with hθ
  have hθ0 : 0 ≤ θ := Real.rpow_nonneg hq.le _
  set M := Quant.corrM (-1) r τ with hMdef
  have hm : ∀ a b c p q, ‖M a b c p q‖ ≤ 1 / absSq (p + q) :=
    Quant.corrM_gain (-1) r τ (Or.inr rfl)
  have hF1 : MZ 1 F := hF.mono' (by norm_num)
  have hn2 : Summable fun p => ‖F p‖ ^ 2 := summable_norm_sq_of_inH (hF.inH.mono (by norm_num))
  have hgr : Summable fun p => (absk p * ‖F p‖) ^ 2 :=
    hF1.inH.congr fun p => by rw [sobWeight_one, mul_pow, absk_sq]
  have hl1 : Summable fun k => ‖F k‖ := summable_wiener hF.inH
  have hlap2 : Summable fun k => ‖lapF F k‖ ^ 2 := (lapF_l2 hF.inH).1
  have hn0 : ∀ (V : Field) (k : Mode), 0 ≤ ‖V k‖ := fun V k => norm_nonneg _
  obtain ⟨g1, -⟩ := gradTri_bound_first (α := fun k => ‖lapF F k‖) (β := fun k => ‖F k‖)
    (γ := fun k => ‖F k‖) (hn0 _) (hn0 _) (hn0 _) hlap2 hl1 hgr hl1 hgr
  obtain ⟨g2, -⟩ := gradTri_bound_mid (α := fun k => ‖F k‖) (β := fun k => ‖lapF F k‖)
    (γ := fun k => ‖F k‖) (hn0 _) (hn0 _) (hn0 _) hl1 hgr hlap2 hl1 hgr
  have hs1 : Summable fun x : Mode × Mode => tripT M (lapF F) F (lapF F) x.1 x.2 :=
    Summable.of_norm_bounded (g1.mul_left 8) fun x => norm_tripT_gain_lap hm (lapF F) F F x.1 x.2
  have hs2 : Summable fun x : Mode × Mode => tripT M F (lapF F) (lapF F) x.1 x.2 :=
    Summable.of_norm_bounded (g2.mul_left 8) fun x => norm_tripT_gain_lap hm F (lapF F) F x.1 x.2
  have hp1 := pair_one_eq_re_tsum_gain hm hFr hlap2 hn2 (Or.inr hgr) hs1
  have hp2 := pair_one_eq_re_tsum_gain hm hFr hn2 hlap2 (Or.inl hgr) hs2
  set H := Quant.heatTri r τ F with hH
  have hHs : Summable H := hs1.add hs2
  have hE : cubicHeat r τ F = (∑' x, H x).re := by
    have e : ∑' x, H x = ∑' x : Mode × Mode, tripT M (lapF F) F (lapF F) x.1 x.2 +
        ∑' x : Mode × Mode, tripT M F (lapF F) (lapF F) x.1 x.2 := hs1.tsum_add hs2
    rw [e, Complex.add_re, ← hp1, ← hp2]
    rfl
  have h1 : Summable fun x => H (rho x) := rho.summable_iff.mpr hHs
  have h2 : Summable fun x => H (rho (rho x)) := rho.summable_iff.mpr h1
  have e1 : ∑' x, H (rho x) = ∑' x, H x := rho.tsum_eq H
  have e2 : ∑' x, H (rho (rho x)) = ∑' x, H x := by
    rw [rho.tsum_eq fun y => H (rho y), e1]
  have hT : ∑' x, Quant.heatTerm r τ F x = 3 * ∑' x, H x := by
    have e : ∑' x, Quant.heatTerm r τ F x =
        ∑' x, H x + ∑' x, H (rho (rho x)) + ∑' x, H (rho x) := by
      rw [← hHs.tsum_add h2, ← (hHs.add h2).tsum_add h1]
      rfl
    rw [e, e1, e2]
    ring
  obtain ⟨sP, bP⟩ := Quant.heatB_facts (κ := Quant.propKer |r|) (M := Quant.MomP |r|)
    (Quant.propKer_nonneg _) (Quant.sum_propKer_sq _) hF
  obtain ⟨sB, bB⟩ := Quant.heatB_facts (κ := Quant.farKer |r|) (M := 52 * θ ^ 2)
    (Quant.farKer_nonneg _) (Quant.sum_farKer_sq hq) hF
  have hS : Summable fun x => 1664 * (Quant.heatB (Quant.propKer |r|) F x +
      Quant.heatB (Quant.farKer |r|) F x) := (sP.add sB).mul_left 1664
  have hpt := Quant.heat_point r τ hF'
  have hNs := Summable.of_nonneg_of_le (fun x => norm_nonneg _) hpt hS
  have hN : ‖∑' x, Quant.heatTerm r τ F x‖ ≤
      1664 * (∑' x, Quant.heatB (Quant.propKer |r|) F x +
        ∑' x, Quant.heatB (Quant.farKer |r|) F x) := by
    rw [← sP.tsum_add sB, ← tsum_mul_left]
    exact (norm_tsum_le_tsum_norm hNs).trans (hNs.tsum_le_tsum hpt hS)
  rw [hT, norm_mul] at hN
  have h3 : ‖(3 : ℂ)‖ = 3 := by simp
  rw [h3] at hN
  rw [hE]
  have hS0 := Real.sqrt_nonneg (Quant.MomP |r|)
  have hT0 := Quant.sqrt_farMom_le hθ0
  set S := Real.sqrt (Quant.MomP |r|)
  set T := Real.sqrt (52 * θ ^ 2)
  have hW : 0 ≤ hnorm 2 F * hnorm 2 F * hnorm 2 F := by
    have := hnorm_nonneg 2 F
    positivity
  set W := hnorm 2 F * hnorm 2 F * hnorm 2 F with hWdef
  have e : Quant.cHeat * Quant.nearP |r| * hnorm 2 F ^ 3 = 2 ^ 10 * (18 * S + 2 ^ 7 * θ) * W := by
    unfold Quant.cHeat Quant.nearP
    rw [hWdef]
    ring
  rw [e]
  have h4 := (Complex.abs_re_le_norm (∑' x, H x))
  have h5 : 3 * ‖∑' x, H x‖ ≤ 1664 * (3 * (S * W) + 3 * (T * W)) :=
    hN.trans (by gcongr)
  have h6 : T * W ≤ 8 * θ * W := by gcongr
  have h7 : 0 ≤ S * W := mul_nonneg hS0 hW
  have h8 : 0 ≤ θ * W := mul_nonneg hθ0 hW
  nlinarith

end OVNS

end
