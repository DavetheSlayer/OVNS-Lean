import OddViscousNS.Quant.Joint.Metric.PathForm

/-!
# The identity of a two-leaf form along the actual solution (step J5, node N13)

`Fam.identity`: for a family `𝔉` with `Fam.Bd`, along the actual solution, at `s = 1, 2`,
`⟨z, O(S, S) z⟩(t) − ⟨z, O(S, S) z⟩(t₀) = ∫ [⟨z, P T(S, S) P z⟩ + ⟨N_z, O z⟩ + ⟨z, O N_z⟩ +
⟨z, O(N_S, S) z⟩ + ⟨z, O(S, N_S) z⟩]`, the integrand in `L¹`.

Here `N_z = A^{s/2} fastNL`, `N_S = slowNL`: the full non-heat right-hand sides, with `𝓛`, the
fast-fast product and the filter still inside.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

open OVNS.Quant.H2 (integral_tsum_deriv_ae summable_wtd_one sobWeight_three Qm_one_le
  exists_Qphase_one_bound ae_inH3_split fast_h2_law slow_c3_integrable)

noncomputable section

namespace OVNS.Quant.Metric

namespace Fam

variable {𝔉 : Fam} {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {ρ : I3 → ℝ} {K₁ K₂ : ℝ}

/-- One term of the actual path has the derivative of the family. -/
lemma T_hasDeriv (h : ActualSol μ φ r g y Ty) (s : ℕ) (x : I3) {a b : ℝ} (ha : 0 ≤ a) (hb : ENNReal.ofReal b < Ty) {u : ℝ} (hu : u ∈ Icc a b) :
    HasDerivWithinAt (fun v => 𝔉.T r x (zp s r g y v x.1) (zp s r g y v (inJ₂ x))
      (Sp r g y v x.2.1) (Sp r g y v x.2.2) (r * v)) (𝔉.rhsT s r g y u x) (Icc a b) u := by
  have hu0 : 0 ≤ u := ha.trans hu.1
  have huT := lt_lifespan hu.2 hb
  have hsub : Icc a b ⊆ Ici 0 := fun v hv => ha.trans hv.1
  have hzero : ∀ {f : ℝ → ℂ}, (∀ v, f v = 0) → 𝔉.rhsT s r g y u x = 0 →
      HasDerivWithinAt f (𝔉.rhsT s r g y u x) (Icc a b) u := fun {f} h0 h1 => by
    have e : f = fun _ => 0 := funext h0
    rw [e, h1]
    exact hasDerivWithinAt_const _ _ _
  by_cases hA : x.2.1 2 = 0
  · by_cases hB' : x.2.2 2 = 0
    · by_cases hj : inJ₂ x 2 = 0
      · have hz : ∀ v, zp s r g y v (inJ₂ x) = 0 := fun v => fast_zero (PiF_zp s r g y v) hj
        have hN : Nzp s r g y u (inJ₂ x) = 0 := fast_zero (PiF_Nzp s r g y u) hj
        refine hzero (fun v => by rw [hz, T_zero_F]) ?_
        simp only [rhsT, hz, hN, T_zero_F, srcT_zero_F, add_zero]
      · have hact : Act x := ⟨hA, hB', hj⟩
        have hj0 : inJ₂ x ≠ 0 := fun h0 => hj (by rw [h0]; rfl)
        have hH : 0 < Hx x := heat4_pos hj0 _ _
        exact term_hasDeriv (L2 := absSq x.1) (J2 := absSq (inJ₂ x)) (Ha := absSq x.2.1)
          (Hb := absSq x.2.2) rfl hH (𝔉.cov x hA hB')
          ((zp_hasDeriv h s _ hu0 huT).mono hsub) ((zp_hasDeriv h s _ hu0 huT).mono hsub)
          ((Sp_hasDeriv h _ hu0 huT).mono hsub) ((Sp_hasDeriv h _ hu0 huT).mono hsub)
    · have hz : ∀ v, Sp r g y v x.2.2 = 0 := fun v => slow_zero (PiS_Sp r g y v) hB'
      have hN : slowNL r g y u x.2.2 = 0 := slow_zero (PiS_slowNL u) hB'
      refine hzero (fun v => by rw [hz, T_zero_r]) ?_
      simp only [rhsT, hz, hN, T_zero_r, srcT_zero_r, add_zero]
  · have hz : ∀ v, Sp r g y v x.2.1 = 0 := fun v => slow_zero (PiS_Sp r g y v) hA
    have hN : slowNL r g y u x.2.1 = 0 := slow_zero (PiS_slowNL u) hA
    refine hzero (fun v => by rw [hz, T_zero_l]) ?_
    simp only [rhsT, hz, hN, T_zero_l, srcT_zero_l, add_zero]

/-- The derivative family is continuous in time. -/
lemma rhsT_continuousOn (h : ActualSol μ φ r g y Ty) (s : ℕ) (x : I3) {a b : ℝ} (ha : 0 ≤ a)
    (hb : ENNReal.ofReal b < Ty) (hab : a ≤ b) :
    ContinuousOn (fun u => 𝔉.rhsT s r g y u x) (Icc a b) := by
  have hb0 := ha.trans hab
  have hsub : Icc a b ⊆ Icc 0 b := Icc_subset_Icc_left ha
  have hmem : ∀ u ∈ Icc a b, 0 ≤ u ∧ ENNReal.ofReal u < Ty := fun u hu =>
    ⟨ha.trans hu.1, lt_lifespan hu.2 hb⟩
  have hI : Icc a b ⊆ Ici 0 := fun v hv => ha.trans hv.1
  have cz : ∀ k, ContinuousOn (fun u => zp s r g y u k) (Icc a b) := fun k u hu =>
    ((zp_hasDeriv h s k (hmem u hu).1 (hmem u hu).2).mono hI).continuousWithinAt
  have cS : ∀ k, ContinuousOn (fun u => Sp r g y u k) (Icc a b) := fun k u hu =>
    ((Sp_hasDeriv h k (hmem u hu).1 (hmem u hu).2).mono hI).continuousWithinAt
  have cN : ∀ k, ContinuousOn (fun u => Nzp s r g y u k) (Icc a b) := fun k => by
    have h1 := ((fastNL_mode_continuousOn h hb0 hb k).mono hsub).const_smul
      ((absk k ^ s : ℝ) : ℂ)
    exact h1
  have cNs : ∀ k, ContinuousOn (fun u => slowNL r g y u k) (Icc a b) := fun k =>
    (slowNL_mode_continuousOn h hb0 hb k).mono hsub
  by_cases hA : x.2.1 2 = 0
  · by_cases hB' : x.2.2 2 = 0
    · have hc := 𝔉.cov x hA hB'
      have t1 : ContinuousOn (fun u => 𝔉.srcT x (zp s r g y u x.1) (zp s r g y u (inJ₂ x))
          (Sp r g y u x.2.1) (Sp r g y u x.2.2) (r * u)) (Icc a b) :=
        source_continuousOn hc (cz x.1) (cz (inJ₂ x)) (cS x.2.1) (cS x.2.2)
      have t2 : ContinuousOn (fun u => 𝔉.T r x (Nzp s r g y u x.1) (zp s r g y u (inJ₂ x))
          (Sp r g y u x.2.1) (Sp r g y u x.2.2) (r * u)) (Icc a b) :=
        oTerm_continuousOn hc (cN x.1) (cz (inJ₂ x)) (cS x.2.1) (cS x.2.2)
      have t3 : ContinuousOn (fun u => 𝔉.T r x (zp s r g y u x.1) (Nzp s r g y u (inJ₂ x))
          (Sp r g y u x.2.1) (Sp r g y u x.2.2) (r * u)) (Icc a b) :=
        oTerm_continuousOn hc (cz x.1) (cN (inJ₂ x)) (cS x.2.1) (cS x.2.2)
      have t4 : ContinuousOn (fun u => 𝔉.T r x (zp s r g y u x.1) (zp s r g y u (inJ₂ x))
          (slowNL r g y u x.2.1) (Sp r g y u x.2.2) (r * u)) (Icc a b) :=
        oTerm_continuousOn hc (cz x.1) (cz (inJ₂ x)) (cNs x.2.1) (cS x.2.2)
      have t5 : ContinuousOn (fun u => 𝔉.T r x (zp s r g y u x.1) (zp s r g y u (inJ₂ x))
          (Sp r g y u x.2.1) (slowNL r g y u x.2.2) (r * u)) (Icc a b) :=
        oTerm_continuousOn hc (cz x.1) (cz (inJ₂ x)) (cS x.2.1) (cNs x.2.2)
      unfold rhsT
      exact ((((t1.add t2).add t3).add t4).add t5)
    · have e : (fun u => 𝔉.rhsT s r g y u x) = fun _ => 0 := by
        funext u
        have hz : Sp r g y u x.2.2 = 0 := slow_zero (PiS_Sp r g y u) hB'
        have hN : slowNL r g y u x.2.2 = 0 := slow_zero (PiS_slowNL u) hB'
        simp only [rhsT, hz, hN, T_zero_r, srcT_zero_r, add_zero]
      rw [e]
      exact continuousOn_const
  · have e : (fun u => 𝔉.rhsT s r g y u x) = fun _ => 0 := by
      funext u
      have hz : Sp r g y u x.2.1 = 0 := slow_zero (PiS_Sp r g y u) hA
      have hN : slowNL r g y u x.2.1 = 0 := slow_zero (PiS_slowNL u) hA
      simp only [rhsT, hz, hN, T_zero_l, srcT_zero_l, add_zero]
    rw [e]
    exact continuousOn_const

/-- The energy coordinates of an `H³` fast field. -/
lemma z_facts {s : ℕ} (hs : s ≤ 2) {F : Field} (hF : MZ 3 F) :
    (Summable fun k => ‖zOf s F k‖ ^ 2) ∧ l2n (zOf s F) = hnorm s F ∧ InH 1 (zOf s F) ∧
      hnorm 1 (zOf s F) = hnorm ((s : ℝ) + 1) F := by
  have hn : ∀ k, ‖zOf s F k‖ = wtd s F k := fun k => by
    simp only [zOf, norm_smul, Complex.norm_real, Real.norm_of_nonneg
      (pow_nonneg (absk_nonneg k) s), wtd]
  have h1 : InH ((s : ℕ) : ℝ) F := hF.inH.mono (by
    have : (s : ℝ) ≤ 2 := by exact_mod_cast hs
    linarith)
  have h2 : InH (((s + 1 : ℕ)) : ℝ) F := hF.inH.mono (by
    have : (s : ℝ) ≤ 2 := by exact_mod_cast hs
    push_cast
    linarith)
  have e1 := summable_wtd_sq s h1 hF.mean
  have e2 := sqrt_tsum_wtd_sq (u := F) s hF.mean
  have e3 := summable_wtd_sq (s + 1) h2 hF.mean
  have e4 := sqrt_tsum_wtd_sq (u := F) (s + 1) hF.mean
  have hw : ∀ k, sobWeight 1 k * ‖zOf s F k‖ ^ 2 = wtd (s + 1) F k ^ 2 := fun k => by
    rw [hn, sobWeight_one, wtd, wtd, ← absk_sq k]
    ring
  refine ⟨by simpa only [hn] using e1, ?_, ?_, ?_⟩
  · simp only [l2n, hn]
    exact e2
  · exact e3.congr fun k => (hw k).symm
  · simp only [hnorm, hw]
    rw [e4]
    push_cast
    rfl

/-- `cls₂` is monotone. -/
lemma cls2_mono {W₁ W₂ U₁ U₂ w₁ w₂ u₁ u₂ : ℝ} (h1 : W₁ ≤ w₁) (h2 : W₂ ≤ w₂) (h3 : U₁ ≤ u₁)
    (h4 : U₂ ≤ u₂) (p1 : 0 ≤ W₁) (p2 : 0 ≤ W₂) (p3 : 0 ≤ U₁) (p4 : 0 ≤ U₂) :
    cls2 W₁ W₂ U₁ U₂ ≤ cls2 w₁ w₂ u₁ u₂ := by
  have hc := c4_pos
  have q1 := p1.trans h1
  have q2 := p3.trans h3
  simp only [cls2]
  gcongr

/-- The arithmetic of the dominating function. -/
lemma total_le {K₁ K₂ A A1 B W c n₁ n₂ Q X : ℝ} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hA0 : 0 ≤ A)
    (hA : A ≤ Q) (hA10 : 0 ≤ A1) (hA1 : A1 ≤ X) (hB0 : 0 ≤ B) (hB : B ≤ Q) (hW0 : 0 ≤ W)
    (hW : W ≤ Q ^ 2) (hc0 : 0 ≤ c) (hc : c ≤ X) (hn10 : 0 ≤ n₁) (hn1 : n₁ ≤ Q) (hn20 : 0 ≤ n₂)
    (hn2 : n₂ ≤ Q) (hc4 : c4 ≤ Q) (hQ : 1 ≤ Q) (hX : 1 ≤ X) :
    K₂ * (A1 * A * cls2 W W B B + A * A * cls2 (c4 * c) W c B + A * A * cls2 W (c4 * c) B c) +
      2 * K₁ * (n₁ * A * cls2 W W B B + A * n₁ * cls2 W W B B +
        A * A * cls2 (c4 * n₂) W n₂ B + A * A * cls2 W (c4 * n₂) B n₂) ≤
      (18 * K₂ + 48 * K₁) * Q ^ 6 * X := by
  have _ := hA10
  have hc40 := c4_pos.le
  have hQ0 : 0 ≤ Q := by linarith
  have hX0 : 0 ≤ X := by linarith
  have a0 : cls2 (Q ^ 2) (Q ^ 2) Q Q ≤ 6 * Q ^ 4 := by
    simp only [cls2]
    have h1 : c4 * (Q * Q ^ 2 + Q ^ 2 * Q) ≤ Q * (Q * Q ^ 2 + Q ^ 2 * Q) := by gcongr
    have h2 : c4 ^ 2 * (Q * Q) ≤ Q ^ 2 * (Q * Q) := by gcongr
    nlinarith only [h1, h2]
  have a1 : cls2 W W B B ≤ 6 * Q ^ 4 := (cls2_mono hW hW hB hB hW0 hW0 hB0 hB0).trans a0
  have a2 : cls2 (c4 * c) W c B ≤ 6 * Q ^ 3 * X := by
    refine (cls2_mono (w₁ := Q * X) (w₂ := Q ^ 2) (u₁ := X) (u₂ := Q) (by gcongr) hW hc hB
      (by positivity) hW0 hc0 hB0).trans ?_
    simp only [cls2]
    have h1 : c4 * (X * Q ^ 2 + Q * X * Q) ≤ Q * (X * Q ^ 2 + Q * X * Q) := by gcongr
    have h2 : c4 ^ 2 * (X * Q) ≤ Q ^ 2 * (X * Q) := by gcongr
    nlinarith only [h1, h2]
  have a3 : cls2 W (c4 * c) B c ≤ 6 * Q ^ 3 * X := by
    refine (cls2_mono (w₁ := Q ^ 2) (w₂ := Q * X) (u₁ := Q) (u₂ := X) hW (by gcongr) hB hc
      hW0 (by positivity) hB0 hc0).trans ?_
    simp only [cls2]
    have h1 : c4 * (Q * (Q * X) + Q ^ 2 * X) ≤ Q * (Q * (Q * X) + Q ^ 2 * X) := by gcongr
    have h2 : c4 ^ 2 * (Q * X) ≤ Q ^ 2 * (Q * X) := by gcongr
    nlinarith only [h1, h2]
  have a4 : cls2 (c4 * n₂) W n₂ B ≤ 6 * Q ^ 4 := by
    refine (cls2_mono (w₁ := Q ^ 2) (w₂ := Q ^ 2) (u₁ := Q) (u₂ := Q) ?_ hW hn2 hB
      (by positivity) hW0 hn20 hB0).trans a0
    calc c4 * n₂ ≤ Q * Q := by gcongr
      _ = Q ^ 2 := by ring
  have a5 : cls2 W (c4 * n₂) B n₂ ≤ 6 * Q ^ 4 := by
    refine (cls2_mono (w₁ := Q ^ 2) (w₂ := Q ^ 2) (u₁ := Q) (u₂ := Q) hW ?_ hB hn2
      hW0 (by positivity) hB0 hn20).trans a0
    calc c4 * n₂ ≤ Q * Q := by gcongr
      _ = Q ^ 2 := by ring
  have hcl0 : 0 ≤ Q ^ 3 * X := by positivity
  have b1 : A1 * A * cls2 W W B B ≤ X * Q * (6 * Q ^ 4) := by
    have : 0 ≤ cls2 W W B B := by simp only [cls2]; positivity
    gcongr
  have b2 : A * A * cls2 (c4 * c) W c B ≤ Q * Q * (6 * Q ^ 3 * X) := by
    have : 0 ≤ cls2 (c4 * c) W c B := by simp only [cls2]; positivity
    gcongr
  have b3 : A * A * cls2 W (c4 * c) B c ≤ Q * Q * (6 * Q ^ 3 * X) := by
    have : 0 ≤ cls2 W (c4 * c) B c := by simp only [cls2]; positivity
    gcongr
  have b4 : n₁ * A * cls2 W W B B ≤ Q * Q * (6 * Q ^ 4) := by
    have : 0 ≤ cls2 W W B B := by simp only [cls2]; positivity
    gcongr
  have b5 : A * n₁ * cls2 W W B B ≤ Q * Q * (6 * Q ^ 4) := by
    have : 0 ≤ cls2 W W B B := by simp only [cls2]; positivity
    gcongr
  have b6 : A * A * cls2 (c4 * n₂) W n₂ B ≤ Q * Q * (6 * Q ^ 4) := by
    have : 0 ≤ cls2 (c4 * n₂) W n₂ B := by simp only [cls2]; positivity
    gcongr
  have b7 : A * A * cls2 W (c4 * n₂) B n₂ ≤ Q * Q * (6 * Q ^ 4) := by
    have : 0 ≤ cls2 W (c4 * n₂) B n₂ := by simp only [cls2]; positivity
    gcongr
  have c1 : K₂ * (A1 * A * cls2 W W B B + A * A * cls2 (c4 * c) W c B +
      A * A * cls2 W (c4 * c) B c) ≤ K₂ * (18 * Q ^ 6 * X) := by
    refine mul_le_mul_of_nonneg_left ?_ hK₂
    have h1 : X * Q * (6 * Q ^ 4) ≤ 6 * Q ^ 6 * X := by
      have : Q ^ 5 ≤ Q ^ 6 := pow_le_pow_right₀ hQ (by norm_num)
      have h2 := mul_le_mul_of_nonneg_right this hX0
      nlinarith only [h2]
    have e : Q * Q * (6 * Q ^ 3 * X) = 6 * Q ^ 5 * X := by ring
    have h3 : 6 * Q ^ 5 * X ≤ 6 * Q ^ 6 * X := by
      have : Q ^ 5 ≤ Q ^ 6 := pow_le_pow_right₀ hQ (by norm_num)
      gcongr
    linarith
  have c2 : 2 * K₁ * (n₁ * A * cls2 W W B B + A * n₁ * cls2 W W B B +
      A * A * cls2 (c4 * n₂) W n₂ B + A * A * cls2 W (c4 * n₂) B n₂) ≤
      2 * K₁ * (24 * Q ^ 6 * X) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have e : Q * Q * (6 * Q ^ 4) = 6 * Q ^ 6 := by ring
    have h1 : 6 * Q ^ 6 ≤ 6 * Q ^ 6 * X := le_mul_of_one_le_right (by positivity) hX
    linarith
  calc _ ≤ K₂ * (18 * Q ^ 6 * X) + 2 * K₁ * (24 * Q ^ 6 * X) := add_le_add c1 c2
    _ = _ := by ring

/-- The sup bounds on a piece. -/
lemma path_sup (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {a b : ℝ} (ha : 0 ≤ a)
    (hb : ENNReal.ofReal b < Ty) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u ∈ Icc a b, MZ 2 (Sp r g y u) ∧ MZ 2 (Fp r g y u) ∧
      hnorm 2 (Sp r g y u) ≤ M ∧ hnorm 2 (Fp r g y u) ≤ M ∧
      InH 1 (fastNL r g y u) ∧ InH 1 (slowNL r g y u) ∧ hnorm 1 (fastNL r g y u) ≤ M ∧
      hnorm 1 (slowNL r g y u) ≤ M ∧ slowNL r g y u 0 = 0 := by
  obtain ⟨M₁, hM₁0, hM₁⟩ := exists_actual_bound h hr hb
  obtain ⟨D, hD0, hD⟩ := exists_Qphase_one_bound h hb
  have hg1 : InH 1 g := h.force_adm.inH.mono (by norm_num)
  have hg0 := hnorm_nonneg 1 g
  refine ⟨M₁ + D + hnorm 1 g, by positivity, fun u hu => ?_⟩
  have hu0 : 0 ≤ u := ha.trans hu.1
  have huT := lt_lifespan hu.2 hb
  have hx := actual_adm h hu0 huT
  obtain ⟨hI, hle⟩ := hD u ⟨hu0, hu.2⟩
  have h1 := hM₁ u ⟨hu0, hu.2⟩
  have hQ0 : Qphase (r * u) (y u) (y u) 0 = 0 := by simp [Qphase, Qm, hel_zero_mode]
  have e1 : fastNL r g y u = -PiF (Qphase (r * u) (y u) (y u)) := rfl
  have e2 : slowNL r g y u = -PiS (Qphase (r * u) (y u) (y u)) + PiS g := rfl
  refine ⟨hx.PiS.mz, hx.PiF.mz, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hnorm_PiS_le hx.inH).trans (by linarith)
  · exact (hnorm_PiF_le hx.inH).trans (by linarith)
  · rw [e1]
    exact hI.PiF.neg
  · rw [e2]
    exact hI.PiS.neg.add hg1.PiS
  · rw [e1, hnorm_neg]
    refine (hnorm_PiF_le hI).trans ?_
    linarith
  · rw [e2]
    refine (hnorm_add_le hI.PiS.neg hg1.PiS).trans ?_
    rw [hnorm_neg]
    have := hnorm_PiS_le hI
    have := hnorm_PiS_le hg1
    linarith
  · simp [slowNL, PiS, h.force_adm.mean, hQ0]

/-- **The identity of a form along the actual solution**, at both weights: the integrand is in
`L¹`, and the increment of `⟨z, O(S, S) z⟩` is the integral of the source plus the four insertions. -/
theorem identity (hB : 𝔉.Bd r ρ K₁ K₂) {s : ℕ} (hs : s = 1 ∨ s = 2)
    (h : ActualSol μ φ r g y Ty) (hr : r ≠ 0) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : ENNReal.ofReal b < Ty) :
    IntervalIntegrable (𝔉.rhs s r g y) volume a b ∧
      𝔉.val s r g y b - 𝔉.val s r g y a = ∫ u in a..b, 𝔉.rhs s r g y u := by
  obtain ⟨M, hM0, hM⟩ := path_sup h hr ha hb
  have hK₁ := hB.K₁0
  have hK₂ := hB.K₂0
  have hc := c4_pos
  set Q : ℝ := 1 + M + c4 + c4 * M with hQ
  have hQ1 : 1 ≤ Q := by
    have : 0 ≤ c4 * M := by positivity
    simp only [hQ]
    linarith
  set Cg : ℝ := (18 * K₂ + 48 * K₁) * Q ^ 6 with hCg
  have hCg0 : 0 ≤ Cg := by positivity
  set gf : ℝ → ℝ := fun u => Cg * (2 + (hnorm 3 (Fp r g y u) ^ 2 + hnorm 3 (Sp r g y u) ^ 2)) with hgf
  have hgi : IntervalIntegrable gf volume a b :=
    (intervalIntegrable_const.add ((fast_h2_law h ha hab hb).1.add
      (slow_c3_integrable h ha hab hb))).const_mul Cg
  have hgood : ∀ᵐ u ∂(volume.restrict (Icc a b)), InH 3 (Fp r g y u) ∧ InH 3 (Sp r g y u) :=
    ae_inH3_split h ha hab hb
  have hsl : ∀ u ∈ Icc a b, InH 3 (Fp r g y u) ∧ InH 3 (Sp r g y u) →
      SB (maj K₁ K₂ (zp s r g y u) (fastNL r g y u) (slowNL r g y u) (Sp r g y u)) (gf u) := by
    intro u hu hu3
    obtain ⟨hS2, hF2, hSM, hFM, hN1, hNs1, hNM, hNsM, hNs0⟩ := hM u hu
    have hF3 : MZ 3 (Fp r g y u) := ⟨hu3.1, hF2.mean⟩
    have hS3 : MZ 3 (Sp r g y u) := ⟨hu3.2, hS2.mean⟩
    have hsle : s ≤ 2 := by omega
    obtain ⟨z1, z2, z3, z4⟩ := z_facts hsle hF3
    have hsb := sb_maj hK₁ hK₂ z1 z3 hN1 hNs1 hS3
    refine hsb.mono_bd ?_
    have hs' : ((s : ℕ) : ℝ) ≤ 2 := by exact_mod_cast hsle
    have hA : l2n (zOf s (Fp r g y u)) ≤ Q := by
      rw [z2]
      have h1 := hnorm_mono hs' hF2.inH
      have : 0 ≤ c4 * M := by positivity
      simp only [hQ]
      linarith
    have hA1 : hnorm 1 (zOf s (Fp r g y u)) ≤ 1 + hnorm 3 (Fp r g y u) + hnorm 3 (Sp r g y u) := by
      rw [z4]
      have h1 := hnorm_mono (show (s : ℝ) + 1 ≤ 3 by linarith) hF3.inH
      have := hnorm_nonneg 3 (Sp r g y u)
      linarith
    have hX1 : 1 ≤ 1 + hnorm 3 (Fp r g y u) + hnorm 3 (Sp r g y u) := by
      have := hnorm_nonneg 3 (Fp r g y u)
      have := hnorm_nonneg 3 (Sp r g y u)
      linarith
    have hW : wiener (Sp r g y u) ≤ Q ^ 2 := by
      have h1 := wiener_le hS2
      have h2 : c4 * hnorm 2 (Sp r g y u) ≤ c4 * M := mul_le_mul_of_nonneg_left hSM hc.le
      have h3 : c4 * M ≤ Q := by
        simp only [hQ]
        linarith
      have h4 : Q ≤ Q ^ 2 := by nlinarith only [hQ1]
      linarith
    have hle := total_le (A := l2n (zOf s (Fp r g y u))) (A1 := hnorm 1 (zOf s (Fp r g y u)))
      (B := hnorm 2 (Sp r g y u)) (W := wiener (Sp r g y u)) (c := hnorm 3 (Sp r g y u))
      (n₁ := hnorm 1 (fastNL r g y u)) (n₂ := hnorm 1 (slowNL r g y u)) (Q := Q)
      (X := 1 + hnorm 3 (Fp r g y u) + hnorm 3 (Sp r g y u)) hK₁ hK₂ (l2n_nonneg _) hA
      (hnorm_nonneg _ _) hA1 (hnorm_nonneg _ _) ?_ (wiener_nonneg _) hW (hnorm_nonneg _ _) ?_
      (hnorm_nonneg _ _) ?_ (hnorm_nonneg _ _) ?_ ?_ hQ1 hX1
    · refine hle.trans ?_
      simp only [hgf]
      refine mul_le_mul_of_nonneg_left ?_ hCg0
      nlinarith only [sq_nonneg (hnorm 3 (Fp r g y u) - 1), sq_nonneg (hnorm 3 (Sp r g y u) - 1)]
    · have : 0 ≤ c4 * M := by positivity
      simp only [hQ]
      linarith
    · have := hnorm_nonneg 3 (Fp r g y u)
      linarith
    · have : 0 ≤ c4 * M := by positivity
      simp only [hQ]
      linarith
    · have : 0 ≤ c4 * M := by positivity
      simp only [hQ]
      linarith
    · have : 0 ≤ c4 * M := by positivity
      simp only [hQ]
      linarith
  have hle5 : ∀ u ∈ Icc a b, ∀ x : I3, ‖𝔉.rhsT s r g y u x‖ ≤
      5 * maj K₁ K₂ (zp s r g y u) (fastNL r g y u) (slowNL r g y u) (Sp r g y u) x := by
    intro u hu x
    obtain ⟨t1, t2, t3, t4, t5⟩ := terms_le hB hs u (hM u hu).2.2.2.2.2.2.2.2 x
    have hn : ∀ a b c d e : ℂ, ‖a + b + c + d + e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ :=
      fun a b c d e => (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)) le_rfl)
    unfold rhsT
    refine (hn _ _ _ _ _).trans ?_
    linarith
  have hdom : ∀ᵐ u ∂(volume.restrict (Icc a b)),
      Summable (fun x => ‖𝔉.rhsT s r g y u x‖) ∧ ∑' x, ‖𝔉.rhsT s r g y u x‖ ≤ 5 * gf u := by
    filter_upwards [hgood, ae_restrict_mem measurableSet_Icc] with u hu3 hu
    have hsb := (hsl u hu hu3).const_mul (by norm_num : (0 : ℝ) ≤ 5)
    exact (hsb.of_le (fun x => norm_nonneg _) (hle5 u hu)).imp id id
  have hend : ∀ c ∈ Icc a b, Summable fun x : I3 => 𝔉.T r x (zp s r g y c x.1)
      (zp s r g y c (inJ₂ x)) (Sp r g y c x.2.1) (Sp r g y c x.2.2) (r * c) := by
    intro c hc'
    obtain ⟨hS2, hF2, -⟩ := hM c hc'
    have hsle : s ≤ 2 := by omega
    have hzs : Summable fun k => ‖zp s r g y c k‖ ^ 2 := by
      have h1 : InH ((s : ℕ) : ℝ) (Fp r g y c) := hF2.inH.mono (by exact_mod_cast hsle)
      have e1 := summable_wtd_sq s h1 hF2.mean
      refine e1.congr fun k => ?_
      simp only [zp, zOf, norm_smul, Complex.norm_real, Real.norm_of_nonneg
        (pow_nonneg (absk_nonneg k) s), wtd]
    have hsb := sb_maj₀ (K₁ := K₁) hK₁ (l2B_nrm hzs) (l2B_nrm hzs) (l1B_nrm hS2.inH)
      (l1B_nrm hS2.inH) (l2B_up hS2.inH) (l2B_up hS2.inH)
    exact Summable.of_norm_bounded hsb.1 fun x =>
      T_le_maj₀ hB (PiS_Sp r g y c) (PiS_Sp r g y c) (PiF_zp s r g y c) x
  have hgi5 : IntervalIntegrable (fun u => 5 * gf u) volume a b := hgi.const_mul 5
  obtain ⟨hI, key⟩ := integral_tsum_deriv_ae (T := fun u x => 𝔉.T r x (zp s r g y u x.1)
    (zp s r g y u (inJ₂ x)) (Sp r g y u x.2.1) (Sp r g y u x.2.2) (r * u))
    (T' := fun u x => 𝔉.rhsT s r g y u x) hab
    (fun x u hu => T_hasDeriv h s x ha hb hu) (fun x => rhsT_continuousOn h s x ha hb hab)
    (hend a ⟨le_rfl, hab⟩) (hend b ⟨hab, le_rfl⟩) hgi5 hdom
  have hsplit : ∀ᵐ u, u ∈ uIoc a b → ∑' x, 𝔉.rhsT s r g y u x = 𝔉.rhs s r g y u := by
    rw [uIoc_of_le hab]
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 hgood] with u hu3 hmem
    have hu := Ioc_subset_Icc_self hmem
    have hsb := hsl u hu (hu3 hu)
    have ht := fun x => terms_le hB hs u (hM u hu).2.2.2.2.2.2.2.2 x
    have s1 := Summable.of_norm_bounded hsb.1 fun x => (ht x).1
    have s2 := Summable.of_norm_bounded hsb.1 fun x => (ht x).2.1
    have s3 := Summable.of_norm_bounded hsb.1 fun x => (ht x).2.2.1
    have s4 := Summable.of_norm_bounded hsb.1 fun x => (ht x).2.2.2.1
    have s5 := Summable.of_norm_bounded hsb.1 fun x => (ht x).2.2.2.2
    simp only [rhs, src, form]
    rw [← s1.tsum_add s2, ← (s1.add s2).tsum_add s3, ← ((s1.add s2).add s3).tsum_add s4,
      ← (((s1.add s2).add s3).add s4).tsum_add s5]
    rfl
  refine ⟨?_, ?_⟩
  · refine hI.congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    exact hsplit
  · have e : ∫ u in a..b, ∑' x, 𝔉.rhsT s r g y u x = ∫ u in a..b, 𝔉.rhs s r g y u :=
      intervalIntegral.integral_congr_ae hsplit
    rw [← e, ← key]
    rfl

end Fam

end OVNS.Quant.Metric

end
