import OddViscousNS.Quant.Joint.Metric.Path3Main

/-!
# The identity of a three-leaf form on the actual path (step J5, node N13, part 2)
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

open OVNS.Quant.H2 (integral_tsum_deriv_ae slow_c3_integrable fast_h2_law ae_inH3_split)

noncomputable section

namespace OVNS.Quant.Metric

namespace Fam3

variable {𝔉 : Fam3} {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {K : ℝ}

/-- One term of the actual path has the derivative of the family. -/
lemma T_hasDeriv (h : ActualSol μ φ r g y Ty) (s : ℕ) (x : I4) {a b : ℝ} (ha : 0 ≤ a)
    (hb : ENNReal.ofReal b < Ty) {u : ℝ} (hu : u ∈ Icc a b) :
    HasDerivWithinAt (fun v => 𝔉.T r x (zp s r g y v x.1) (zp s r g y v (inJ x))
      (Sp r g y v x.2.1) (Sp r g y v x.2.2.1) (Sp r g y v x.2.2.2) (r * v))
      (𝔉.rhsT s r g y u x) (Icc a b) u := by
  have hu0 : 0 ≤ u := ha.trans hu.1
  have huT := lt_lifespan hu.2 hb
  have hsub : Icc a b ⊆ Ici 0 := fun v hv => ha.trans hv.1
  have hzero : ∀ {f : ℝ → ℂ}, (∀ v, f v = 0) → 𝔉.rhsT s r g y u x = 0 →
      HasDerivWithinAt f (𝔉.rhsT s r g y u x) (Icc a b) u := fun {f} h0 h1 => by
    have e : f = fun _ => 0 := funext h0
    rw [e, h1]
    exact hasDerivWithinAt_const _ _ _
  by_cases hA : x.2.1 2 = 0
  swap
  · have hz : ∀ v, Sp r g y v x.2.1 = 0 := fun v => slow_zero (Fam.PiS_Sp r g y v) hA
    have hN : slowNL r g y u x.2.1 = 0 := slow_zero (PiS_slowNL u) hA
    refine hzero (fun v => by rw [hz, T_zero₁]) ?_
    simp only [rhsT, hz, hN, T_zero₁, srcT_zero₁, add_zero]
  by_cases hB : x.2.2.1 2 = 0
  swap
  · have hz : ∀ v, Sp r g y v x.2.2.1 = 0 := fun v => slow_zero (Fam.PiS_Sp r g y v) hB
    have hN : slowNL r g y u x.2.2.1 = 0 := slow_zero (PiS_slowNL u) hB
    refine hzero (fun v => by rw [hz, T_zero₂]) ?_
    simp only [rhsT, hz, hN, T_zero₂, srcT_zero₂, add_zero]
  by_cases hC : x.2.2.2 2 = 0
  swap
  · have hz : ∀ v, Sp r g y v x.2.2.2 = 0 := fun v => slow_zero (Fam.PiS_Sp r g y v) hC
    have hN : slowNL r g y u x.2.2.2 = 0 := slow_zero (PiS_slowNL u) hC
    refine hzero (fun v => by rw [hz, T_zero₃]) ?_
    simp only [rhsT, hz, hN, T_zero₃, srcT_zero₃, add_zero]
  by_cases hj : inJ x 2 = 0
  · have hz : ∀ v, zp s r g y v (inJ x) = 0 := fun v => fast_zero (Fam.PiF_zp s r g y v) hj
    have hN : Nzp s r g y u (inJ x) = 0 := fast_zero (Fam.PiF_Nzp s r g y u) hj
    refine hzero (fun v => by rw [hz, T_zero_F]) ?_
    simp only [rhsT, hz, hN, T_zero_F, srcT_zero_F, add_zero]
  exact term_hasDeriv₃ (Hx₃_pos ⟨hA, hB, hC, hj⟩) ⟨hA, hB, hC⟩
    ((zp_hasDeriv h s _ hu0 huT).mono hsub) ((zp_hasDeriv h s _ hu0 huT).mono hsub)
    ((Sp_hasDeriv h _ hu0 huT).mono hsub) ((Sp_hasDeriv h _ hu0 huT).mono hsub)
    ((Sp_hasDeriv h _ hu0 huT).mono hsub)

/-- A channel is continuous along continuous paths. -/
lemma core_continuousOn (x : I4) (c e : Sgn) {G F t v w : ℝ → V3} {K' : Set ℝ}
    (hG : ContinuousOn G K') (hF : ContinuousOn F K') (ht : ContinuousOn t K')
    (hv : ContinuousOn v K') (hw : ContinuousOn w K') :
    ContinuousOn (fun u => core₃ 𝔉 x c e (G u) (F u) (t u) (v u) (w u)) K' := by
  have h1 : ContinuousOn (fun u => 𝔉.A0 x (t u) (v u)) K' :=
    (𝔉.A0 x).continuous₂.comp_continuousOn (ht.prodMk hv)
  have h2 : ContinuousOn (fun u => 𝔉.E0 x (w u)) K' :=
    (𝔉.E0 x).continuous.comp_continuousOn hw
  have h3 : ContinuousOn (fun u => 𝔉.A0 x (t u) (v u) ∘L 𝔉.E0 x (w u)) K' := h1.clm_comp h2
  have h4 : ContinuousOn (fun u => helL e (inJ x) (F u)) K' :=
    (helL e (inJ x)).continuous.comp_continuousOn hF
  have h5 := h3.clm_apply h4
  have h6 : ContinuousOn (fun u => helL c x.1 ((𝔉.A0 x (t u) (v u) ∘L 𝔉.E0 x (w u))
      (helL e (inJ x) (F u)))) K' := (helL c x.1).continuous.comp_continuousOn h5
  exact hG.inner h6

/-- The term is continuous along continuous paths. -/
lemma T_continuousOn {x : I4} (hc : x.2.1 2 = 0 ∧ x.2.2.1 2 = 0 ∧ x.2.2.2 2 = 0)
    {G F t v w : ℝ → V3} {K' : Set ℝ} (hG : ContinuousOn G K') (hF : ContinuousOn F K')
    (ht : ContinuousOn t K') (hv : ContinuousOn v K') (hw : ContinuousOn w K') :
    ContinuousOn (fun u => 𝔉.T r x (G u) (F u) (t u) (v u) (w u) (r * u)) K' := by
  have hP : ∀ φ : ℝ, Continuous fun u : ℝ => chP r u φ := fun φ => by
    unfold chP
    fun_prop
  have hexp : (fun u => 𝔉.T r x (G u) (F u) (t u) (v u) (w u) (r * u)) = fun u =>
      ∑ c : Sgn, ∑ e : Sgn, resolv (-1) (Hx₃ x) (r * outerPhi c e x.1 (inJ x)) *
        (chP r u (outerPhi c e x.1 (inJ x)) * core₃ 𝔉 x c e (G u) (F u) (t u) (v u) (w u)) :=
    funext fun u => T_eq hc _ _ _ _ _ u
  rw [hexp]
  exact continuousOn_finsetSum _ fun c _ => continuousOn_finsetSum _ fun e _ =>
    continuousOn_const.mul ((hP _).continuousOn.mul (core_continuousOn x c e hG hF ht hv hw))

/-- The source term is continuous along continuous paths. -/
lemma srcT_continuousOn {x : I4} (hc : x.2.1 2 = 0 ∧ x.2.2.1 2 = 0 ∧ x.2.2.2 2 = 0)
    {G F t v w : ℝ → V3} {K' : Set ℝ} (hG : ContinuousOn G K') (hF : ContinuousOn F K')
    (ht : ContinuousOn t K') (hv : ContinuousOn v K') (hw : ContinuousOn w K') :
    ContinuousOn (fun u => 𝔉.srcT x (G u) (F u) (t u) (v u) (w u) (r * u)) K' := by
  have hP : ∀ φ : ℝ, Continuous fun u : ℝ => chP r u φ := fun φ => by
    unfold chP
    fun_prop
  have hexp : (fun u => 𝔉.srcT x (G u) (F u) (t u) (v u) (w u) (r * u)) = fun u =>
      ∑ c : Sgn, ∑ e : Sgn, chP r u (outerPhi c e x.1 (inJ x)) *
        core₃ 𝔉 x c e (G u) (F u) (t u) (v u) (w u) :=
    funext fun u => srcT_eq₃ hc _ _ _ _ _ u
  rw [hexp]
  exact continuousOn_finsetSum _ fun c _ => continuousOn_finsetSum _ fun e _ =>
    (hP _).continuousOn.mul (core_continuousOn x c e hG hF ht hv hw)

/-- The derivative family is continuous in time. -/
lemma rhsT_continuousOn (h : ActualSol μ φ r g y Ty) (s : ℕ) (x : I4) {a b : ℝ} (ha : 0 ≤ a)
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
  have hz1 : ∀ {f : ℝ → ℂ}, (∀ u, f u = 0) → ContinuousOn f (Icc a b) := fun {f} h0 => by
    have e : f = fun _ => 0 := funext h0
    rw [e]
    exact continuousOn_const
  by_cases hA : x.2.1 2 = 0
  swap
  · refine hz1 fun u => ?_
    have hz : Sp r g y u x.2.1 = 0 := slow_zero (Fam.PiS_Sp r g y u) hA
    have hN : slowNL r g y u x.2.1 = 0 := slow_zero (PiS_slowNL u) hA
    simp only [rhsT, hz, hN, T_zero₁, srcT_zero₁, add_zero]
  by_cases hB : x.2.2.1 2 = 0
  swap
  · refine hz1 fun u => ?_
    have hz : Sp r g y u x.2.2.1 = 0 := slow_zero (Fam.PiS_Sp r g y u) hB
    have hN : slowNL r g y u x.2.2.1 = 0 := slow_zero (PiS_slowNL u) hB
    simp only [rhsT, hz, hN, T_zero₂, srcT_zero₂, add_zero]
  by_cases hC : x.2.2.2 2 = 0
  swap
  · refine hz1 fun u => ?_
    have hz : Sp r g y u x.2.2.2 = 0 := slow_zero (Fam.PiS_Sp r g y u) hC
    have hN : slowNL r g y u x.2.2.2 = 0 := slow_zero (PiS_slowNL u) hC
    simp only [rhsT, hz, hN, T_zero₃, srcT_zero₃, add_zero]
  have hc : x.2.1 2 = 0 ∧ x.2.2.1 2 = 0 ∧ x.2.2.2 2 = 0 := ⟨hA, hB, hC⟩
  have t1 := srcT_continuousOn (𝔉 := 𝔉) (r := r) hc (cz x.1) (cz (inJ x)) (cS x.2.1) (cS x.2.2.1)
    (cS x.2.2.2)
  have t2 := T_continuousOn (𝔉 := 𝔉) (r := r) hc (cN x.1) (cz (inJ x)) (cS x.2.1) (cS x.2.2.1)
    (cS x.2.2.2)
  have t3 := T_continuousOn (𝔉 := 𝔉) (r := r) hc (cz x.1) (cN (inJ x)) (cS x.2.1) (cS x.2.2.1)
    (cS x.2.2.2)
  have t4 := T_continuousOn (𝔉 := 𝔉) (r := r) hc (cz x.1) (cz (inJ x)) (cNs x.2.1) (cS x.2.2.1)
    (cS x.2.2.2)
  have t5 := T_continuousOn (𝔉 := 𝔉) (r := r) hc (cz x.1) (cz (inJ x)) (cS x.2.1) (cNs x.2.2.1)
    (cS x.2.2.2)
  have t6 := T_continuousOn (𝔉 := 𝔉) (r := r) hc (cz x.1) (cz (inJ x)) (cS x.2.1) (cS x.2.2.1)
    (cNs x.2.2.2)
  exact ((((t1.add t2).add t3).add t4).add t5).add t6

/-- `cls₃` is monotone. -/
lemma cls3_mono {W₁ W₂ W₃ U₁ U₂ U₃ w₁ w₂ w₃ u₁ u₂ u₃ : ℝ} (h1 : W₁ ≤ w₁) (h2 : W₂ ≤ w₂)
    (h3 : W₃ ≤ w₃) (h4 : U₁ ≤ u₁) (h5 : U₂ ≤ u₂) (h6 : U₃ ≤ u₃) (p1 : 0 ≤ W₁) (p2 : 0 ≤ W₂)
    (p3 : 0 ≤ W₃) (p4 : 0 ≤ U₁) (p5 : 0 ≤ U₂) (p6 : 0 ≤ U₃) :
    cls3 W₁ W₂ W₃ U₁ U₂ U₃ ≤ cls3 w₁ w₂ w₃ u₁ u₂ u₃ := by
  have hc := c4_pos
  have q1 := p1.trans h1
  have q2 := p2.trans h2
  have q3 := p3.trans h3
  have q4 := p4.trans h4
  have q5 := p5.trans h5
  have q6 := p6.trans h6
  simp only [cls3]
  gcongr

/-- A closed bound of `cls₃`, with one entry `(R, T)` of the first slot size. -/
lemma cls3_closed {Q X : ℝ} (hc4 : c4 ≤ Q) (hQ : 1 ≤ Q) (hX : 1 ≤ X) :
    cls3 (Q * X) (Q ^ 2) (Q ^ 2) X Q Q ≤ 10 * Q ^ 5 * X ∧
      cls3 (Q ^ 2) (Q * X) (Q ^ 2) Q X Q ≤ 10 * Q ^ 5 * X ∧
      cls3 (Q ^ 2) (Q ^ 2) (Q * X) Q Q X ≤ 10 * Q ^ 5 * X ∧
      cls3 (Q ^ 2) (Q ^ 2) (Q ^ 2) Q Q Q ≤ 10 * Q ^ 6 := by
  have hc := c4_pos
  have hQ0 : 0 ≤ Q := by linarith
  have hX0 : 0 ≤ X := by linarith
  have a1 : c4 * Q ^ 4 ≤ Q * Q ^ 4 := by gcongr
  have a2 : c4 ^ 2 * Q ^ 3 ≤ Q ^ 2 * Q ^ 3 := by gcongr
  have a3 : c4 ^ 2 * Q ^ 4 ≤ Q ^ 2 * Q ^ 4 := by gcongr
  have a4 : c4 * Q ^ 5 ≤ Q * Q ^ 5 := by gcongr
  have b1 := mul_le_mul_of_nonneg_right a1 hX0
  have b2 := mul_le_mul_of_nonneg_right a2 hX0
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [cls3]
  · nlinarith only [b1, b2]
  · nlinarith only [b1, b2]
  · nlinarith only [b1, b2]
  · nlinarith only [a3, a4]

/-- The arithmetic of the dominating function. -/
lemma total_le {K A A1 B W c n₁ n₂ Q X : ℝ} (hK : 0 ≤ K) (hA0 : 0 ≤ A) (hA : A ≤ Q)
    (hA1 : A1 ≤ X) (hB0 : 0 ≤ B) (hB : B ≤ Q) (hW0 : 0 ≤ W) (hW : W ≤ Q ^ 2) (hc0 : 0 ≤ c)
    (hc : c ≤ X) (hn10 : 0 ≤ n₁) (hn1 : n₁ ≤ Q) (hn20 : 0 ≤ n₂) (hn2 : n₂ ≤ Q) (hc4 : c4 ≤ Q)
    (hQ : 1 ≤ Q) (hX : 1 ≤ X) :
    K * (A1 * A * cls3 W W W B B B + A * A * cls3 (c4 * c) W W c B B +
        A * A * cls3 W (c4 * c) W B c B + A * A * cls3 W W (c4 * c) B B c) +
      16 * K * (n₁ * A * cls3 W W W B B B + A * n₁ * cls3 W W W B B B +
        A * A * cls3 (c4 * n₂) W W n₂ B B + A * A * cls3 W (c4 * n₂) W B n₂ B +
        A * A * cls3 W W (c4 * n₂) B B n₂) ≤ 840 * K * Q ^ 8 * X := by
  have hc40 := c4_pos.le
  have hQ0 : 0 ≤ Q := by linarith
  have hX0 : 0 ≤ X := by linarith
  obtain ⟨c1, c2, c3, c0⟩ := cls3_closed hc4 hQ hX
  have hcc : c4 * c ≤ Q * X := mul_le_mul hc4 hc hc0 hQ0
  have hcn : c4 * n₂ ≤ Q ^ 2 := by
    calc c4 * n₂ ≤ Q * Q := mul_le_mul hc4 hn2 hn20 hQ0
      _ = Q ^ 2 := by ring
  have d0 := cls3_mono hW hW hW hB hB hB hW0 hW0 hW0 hB0 hB0 hB0
  have d1 := cls3_mono hcc hW hW hc hB hB (by positivity) hW0 hW0 hc0 hB0 hB0
  have d2 := cls3_mono hW hcc hW hB hc hB hW0 (by positivity) hW0 hB0 hc0 hB0
  have d3 := cls3_mono hW hW hcc hB hB hc hW0 hW0 (by positivity) hB0 hB0 hc0
  have d4 := cls3_mono hcn hW hW hn2 hB hB (by positivity) hW0 hW0 hn20 hB0 hB0
  have d5 := cls3_mono hW hcn hW hB hn2 hB hW0 (by positivity) hW0 hB0 hn20 hB0
  have d6 := cls3_mono hW hW hcn hB hB hn2 hW0 hW0 (by positivity) hB0 hB0 hn20
  have nnW : ∀ {a b c' d e f : ℝ}, 0 ≤ a → 0 ≤ b → 0 ≤ c' → 0 ≤ d → 0 ≤ e → 0 ≤ f →
      0 ≤ cls3 a b c' d e f := fun h1 h2 h3 h4 h5 h6 => by
    simp only [cls3]
    positivity
  have q5 : Q ^ 5 * X ≤ Q ^ 8 * X :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hQ (by norm_num)) hX0
  have q6 : Q ^ 8 ≤ Q ^ 8 * X := le_mul_of_one_le_right (by positivity) hX
  have mulA : ∀ {Y Z P₁ P₂ : ℝ}, 0 ≤ Y → Y ≤ Z → 0 ≤ P₁ → P₁ ≤ Q → 0 ≤ P₂ → P₂ ≤ Q →
      P₁ * P₂ * Y ≤ Q * Q * Z := fun h1 h2 h3 h4 h5 h6 =>
    mul_le_mul (mul_le_mul h4 h6 h5 hQ0) h2 h1 (by positivity)
  have e1 : A * A * cls3 (c4 * c) W W c B B ≤ Q * Q * (10 * Q ^ 5 * X) :=
    mulA (nnW (by positivity) hW0 hW0 hc0 hB0 hB0) (d1.trans c1) hA0 hA hA0 hA
  have e2 : A * A * cls3 W (c4 * c) W B c B ≤ Q * Q * (10 * Q ^ 5 * X) :=
    mulA (nnW hW0 (by positivity) hW0 hB0 hc0 hB0) (d2.trans c2) hA0 hA hA0 hA
  have e3 : A * A * cls3 W W (c4 * c) B B c ≤ Q * Q * (10 * Q ^ 5 * X) :=
    mulA (nnW hW0 hW0 (by positivity) hB0 hB0 hc0) (d3.trans c3) hA0 hA hA0 hA
  have e4 : n₁ * A * cls3 W W W B B B ≤ Q * Q * (10 * Q ^ 6) :=
    mulA (nnW hW0 hW0 hW0 hB0 hB0 hB0) (d0.trans c0) hn10 hn1 hA0 hA
  have e5 : A * n₁ * cls3 W W W B B B ≤ Q * Q * (10 * Q ^ 6) :=
    mulA (nnW hW0 hW0 hW0 hB0 hB0 hB0) (d0.trans c0) hA0 hA hn10 hn1
  have e6 : A * A * cls3 (c4 * n₂) W W n₂ B B ≤ Q * Q * (10 * Q ^ 6) :=
    mulA (nnW (by positivity) hW0 hW0 hn20 hB0 hB0) (d4.trans c0) hA0 hA hA0 hA
  have e7 : A * A * cls3 W (c4 * n₂) W B n₂ B ≤ Q * Q * (10 * Q ^ 6) :=
    mulA (nnW hW0 (by positivity) hW0 hB0 hn20 hB0) (d5.trans c0) hA0 hA hA0 hA
  have e8 : A * A * cls3 W W (c4 * n₂) B B n₂ ≤ Q * Q * (10 * Q ^ 6) :=
    mulA (nnW hW0 hW0 (by positivity) hB0 hB0 hn20) (d6.trans c0) hA0 hA hA0 hA
  have e0 : A1 * A * cls3 W W W B B B ≤ X * Q * (10 * Q ^ 6) :=
    mul_le_mul (mul_le_mul hA1 hA hA0 hX0) (d0.trans c0) (nnW hW0 hW0 hW0 hB0 hB0 hB0)
      (by positivity)
  have hp1 : X * Q * (10 * Q ^ 6) ≤ 10 * (Q ^ 8 * X) := by
    have : Q ^ 7 * X ≤ Q ^ 8 * X :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hQ (by norm_num)) hX0
    nlinarith only [this]
  have hp2 : Q * Q * (10 * Q ^ 5 * X) ≤ 10 * (Q ^ 8 * X) := by
    have : Q ^ 7 * X ≤ Q ^ 8 * X :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hQ (by norm_num)) hX0
    nlinarith only [this]
  have hp3 : Q * Q * (10 * Q ^ 6) ≤ 10 * (Q ^ 8 * X) := by
    nlinarith only [q6]
  have g1 : A1 * A * cls3 W W W B B B + A * A * cls3 (c4 * c) W W c B B +
      A * A * cls3 W (c4 * c) W B c B + A * A * cls3 W W (c4 * c) B B c ≤ 40 * (Q ^ 8 * X) := by
    linarith
  have g2 : n₁ * A * cls3 W W W B B B + A * n₁ * cls3 W W W B B B +
      A * A * cls3 (c4 * n₂) W W n₂ B B + A * A * cls3 W (c4 * n₂) W B n₂ B +
      A * A * cls3 W W (c4 * n₂) B B n₂ ≤ 50 * (Q ^ 8 * X) := by
    linarith
  have h1 := mul_le_mul_of_nonneg_left g1 hK
  have h2 := mul_le_mul_of_nonneg_left g2 (by positivity : 0 ≤ 16 * K)
  calc _ ≤ K * (40 * (Q ^ 8 * X)) + 16 * K * (50 * (Q ^ 8 * X)) := add_le_add h1 h2
    _ = _ := by ring

/-- **The identity of a three-leaf form along the actual solution**, at both weights: the integrand
is in `L¹`, and the increment of `⟨z, O(S, S, S) z⟩` is the integral of the source plus the five
insertions. -/
theorem identity (hB : 𝔉.Bd K) {s : ℕ} (hs : s = 1 ∨ s = 2) (h : ActualSol μ φ r g y Ty)
    (hr : r ≠ 0) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : ENNReal.ofReal b < Ty) :
    IntervalIntegrable (𝔉.rhs s r g y) volume a b ∧
      𝔉.val s r g y b - 𝔉.val s r g y a = ∫ u in a..b, 𝔉.rhs s r g y u := by
  obtain ⟨M, hM0, hM⟩ := Fam.path_sup h hr ha hb
  have hK := hB.K0
  have hc := c4_pos
  set Q : ℝ := 1 + M + c4 + c4 * M with hQ
  have hcM : 0 ≤ c4 * M := by positivity
  have hQ1 : 1 ≤ Q := by
    simp only [hQ]
    linarith
  set Cg : ℝ := 840 * K * Q ^ 8 with hCg
  have hCg0 : 0 ≤ Cg := by positivity
  set gf : ℝ → ℝ := fun u => Cg * (2 + (hnorm 3 (Fp r g y u) ^ 2 + hnorm 3 (Sp r g y u) ^ 2)) with hgf
  have hgi : IntervalIntegrable gf volume a b :=
    (intervalIntegrable_const.add ((fast_h2_law h ha hab hb).1.add
      (slow_c3_integrable h ha hab hb))).const_mul Cg
  have hgood : ∀ᵐ u ∂(volume.restrict (Icc a b)), InH 3 (Fp r g y u) ∧ InH 3 (Sp r g y u) :=
    ae_inH3_split h ha hab hb
  have hsl : ∀ u ∈ Icc a b, InH 3 (Fp r g y u) ∧ InH 3 (Sp r g y u) →
      SB (maj K (zp s r g y u) (fastNL r g y u) (slowNL r g y u) (Sp r g y u)) (gf u) := by
    intro u hu hu3
    obtain ⟨hS2, hF2, hSM, hFM, hN1, hNs1, hNM, hNsM, hNs0⟩ := hM u hu
    have hF3 : MZ 3 (Fp r g y u) := ⟨hu3.1, hF2.mean⟩
    have hS3 : MZ 3 (Sp r g y u) := ⟨hu3.2, hS2.mean⟩
    have hsle : s ≤ 2 := by omega
    obtain ⟨z1, z2, z3, z4⟩ := Fam.z_facts hsle hF3
    have hsb := sb_maj hK z1 z3 hN1 hNs1 hS3
    refine hsb.mono_bd ?_
    have hs' : ((s : ℕ) : ℝ) ≤ 2 := by exact_mod_cast hsle
    have hA : l2n (zOf s (Fp r g y u)) ≤ Q := by
      rw [z2]
      have h1 := hnorm_mono hs' hF2.inH
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
      (X := 1 + hnorm 3 (Fp r g y u) + hnorm 3 (Sp r g y u)) hK (l2n_nonneg _) hA
      hA1 (hnorm_nonneg _ _) ?_ (wiener_nonneg _) hW (hnorm_nonneg _ _) ?_
      (hnorm_nonneg _ _) ?_ (hnorm_nonneg _ _) ?_ ?_ hQ1 hX1
    · refine hle.trans ?_
      simp only [hgf, hCg]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      nlinarith only [sq_nonneg (hnorm 3 (Fp r g y u) - 1), sq_nonneg (hnorm 3 (Sp r g y u) - 1)]
    · simp only [hQ]
      linarith
    · have := hnorm_nonneg 3 (Fp r g y u)
      linarith
    · simp only [hQ]
      linarith
    · simp only [hQ]
      linarith
    · simp only [hQ]
      linarith
  have hle6 : ∀ u ∈ Icc a b, ∀ x : I4, ‖𝔉.rhsT s r g y u x‖ ≤
      6 * maj K (zp s r g y u) (fastNL r g y u) (slowNL r g y u) (Sp r g y u) x := by
    intro u hu x
    obtain ⟨t1, t2, t3, t4, t5, t6⟩ := terms_le hB hs u (hM u hu).2.2.2.2.2.2.2.2 x
    have hn : ∀ a b c d e f : ℂ, ‖a + b + c + d + e + f‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ :=
      fun a b c d e f => by
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    unfold rhsT
    refine (hn _ _ _ _ _ _).trans ?_
    linarith
  have hdom : ∀ᵐ u ∂(volume.restrict (Icc a b)),
      Summable (fun x => ‖𝔉.rhsT s r g y u x‖) ∧ ∑' x, ‖𝔉.rhsT s r g y u x‖ ≤ 6 * gf u := by
    filter_upwards [hgood, ae_restrict_mem measurableSet_Icc] with u hu3 hu
    have hsb := (hsl u hu hu3).const_mul (by norm_num : (0 : ℝ) ≤ 6)
    exact (hsb.of_le (fun x => norm_nonneg _) (hle6 u hu)).imp id id
  have hend : ∀ c ∈ Icc a b, Summable fun x : I4 => 𝔉.T r x (zp s r g y c x.1)
      (zp s r g y c (inJ x)) (Sp r g y c x.2.1) (Sp r g y c x.2.2.1) (Sp r g y c x.2.2.2)
        (r * c) := by
    intro c hc'
    obtain ⟨hS2, hF2, -⟩ := hM c hc'
    have hsle : s ≤ 2 := by omega
    have hzs : Summable fun k => ‖zp s r g y c k‖ ^ 2 := by
      have h1 : InH ((s : ℕ) : ℝ) (Fp r g y c) := hF2.inH.mono (by exact_mod_cast hsle)
      have e1 := summable_wtd_sq s h1 hF2.mean
      refine e1.congr fun k => ?_
      simp only [zp, zOf, norm_smul, Complex.norm_real, Real.norm_of_nonneg
        (pow_nonneg (absk_nonneg k) s), wtd]
    have W := l1B_nrm hS2.inH
    have U := l2B_up hS2.inH
    have hsb := (pos3_E3 (l2B_nrm hzs) (l2B_nrm hzs) W W W U U U).const_mul
      (by positivity : 0 ≤ 16 * K)
    refine Summable.of_norm_bounded hsb.1 fun x => ?_
    refine T_form_le (Fam.PiS_Sp r g y c) (Fam.PiS_Sp r g y c) (Fam.PiS_Sp r g y c)
      (Fam.PiF_zp s r g y c) (B := fun x => 16 * K * (Phi₃ (nrm (zp s r g y c)) (nrm (zp s r g y c))
        (nrm (Sp r g y c)) (nrm (Sp r g y c)) (nrm (Sp r g y c)) x * E3 x))
      (fun x => mul_nonneg (by positivity) (Phi₃_E3_nonneg
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) x)) (fun x hx => ?_) x
    refine (norm_T_le hB hx).trans ?_
    have hρ : rho₃ x ≤ 1 := by
      unfold rho₃
      exact (div_le_one (Hx₃_pos hx)).2 (sum_facts x).1
    have hE := E3_nonneg x
    have hn : 0 ≤ ‖zp s r g y c x.1‖ * ‖zp s r g y c (inJ x)‖ * (‖Sp r g y c x.2.1‖ *
        ‖Sp r g y c x.2.2.1‖ * ‖Sp r g y c x.2.2.2‖) * E3 x := by positivity
    have e : 16 * K * (Phi₃ (nrm (zp s r g y c)) (nrm (zp s r g y c)) (nrm (Sp r g y c))
        (nrm (Sp r g y c)) (nrm (Sp r g y c)) x * E3 x) = 16 * K * (‖zp s r g y c x.1‖ *
        ‖zp s r g y c (inJ x)‖ * (‖Sp r g y c x.2.1‖ * ‖Sp r g y c x.2.2.1‖ *
          ‖Sp r g y c x.2.2.2‖) * E3 x) := by
      simp only [Phi₃, nrm]
    rw [e]
    have h1 : ‖zp s r g y c x.1‖ * ‖zp s r g y c (inJ x)‖ * (‖Sp r g y c x.2.1‖ *
        ‖Sp r g y c x.2.2.1‖ * ‖Sp r g y c x.2.2.2‖) * rho₃ x * E3 x ≤
        ‖zp s r g y c x.1‖ * ‖zp s r g y c (inJ x)‖ * (‖Sp r g y c x.2.1‖ *
        ‖Sp r g y c x.2.2.1‖ * ‖Sp r g y c x.2.2.2‖) * E3 x := by
      have := mul_le_mul_of_nonneg_left hρ hn
      nlinarith only [this]
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 4 * K)
    refine h2.trans ?_
    have := mul_nonneg hK hn
    nlinarith only [this]
  have hgi6 : IntervalIntegrable (fun u => 6 * gf u) volume a b := hgi.const_mul 6
  obtain ⟨hI, key⟩ := integral_tsum_deriv_ae (T := fun u x => 𝔉.T r x (zp s r g y u x.1)
    (zp s r g y u (inJ x)) (Sp r g y u x.2.1) (Sp r g y u x.2.2.1) (Sp r g y u x.2.2.2) (r * u))
    (T' := fun u x => 𝔉.rhsT s r g y u x) hab
    (fun x u hu => T_hasDeriv h s x ha hb hu) (fun x => rhsT_continuousOn h s x ha hb hab)
    (hend a ⟨le_rfl, hab⟩) (hend b ⟨hab, le_rfl⟩) hgi6 hdom
  have hsplit : ∀ᵐ u, u ∈ uIoc a b → ∑' x, 𝔉.rhsT s r g y u x = 𝔉.rhs s r g y u := by
    rw [uIoc_of_le hab]
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 hgood] with u hu3 hmem
    have hu := Ioc_subset_Icc_self hmem
    have hsb := hsl u hu (hu3 hu)
    have ht := fun x => terms_le (𝔉 := 𝔉) (K := K) hB hs u (hM u hu).2.2.2.2.2.2.2.2 x
    have s1 := Summable.of_norm_bounded hsb.1 fun x => (ht x).1
    have s2 := Summable.of_norm_bounded hsb.1 fun x => (ht x).2.1
    have s3 := Summable.of_norm_bounded hsb.1 fun x => (ht x).2.2.1
    have s4 := Summable.of_norm_bounded hsb.1 fun x => (ht x).2.2.2.1
    have s5 := Summable.of_norm_bounded hsb.1 fun x => (ht x).2.2.2.2.1
    have s6 := Summable.of_norm_bounded hsb.1 fun x => (ht x).2.2.2.2.2
    simp only [rhs, src, form]
    rw [← s1.tsum_add s2, ← (s1.add s2).tsum_add s3, ← ((s1.add s2).add s3).tsum_add s4,
      ← (((s1.add s2).add s3).add s4).tsum_add s5,
      ← ((((s1.add s2).add s3).add s4).add s5).tsum_add s6]
    rfl
  refine ⟨?_, ?_⟩
  · refine hI.congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    exact hsplit
  · have e : ∫ u in a..b, ∑' x, 𝔉.rhsT s r g y u x = ∫ u in a..b, 𝔉.rhs s r g y u :=
      intervalIntegral.integral_congr_ae hsplit
    rw [← e, ← key]
    rfl

end Fam3

end OVNS.Quant.Metric

end
