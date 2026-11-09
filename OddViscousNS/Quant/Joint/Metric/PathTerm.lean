import OddViscousNS.Quant.Joint.Metric.Leaf

/-!
# One term of the energy identity on a path (step J5, node N13)

One block of a metric form along a path: `u ↦ ⟨G(u), H⁻¹ T_{ru}(v(u), w(u)) F(u)⟩`, where
`T` is the source of the block (`tR` for `X₂`, `zR` for `Z`), `H⁻¹ = outerInv`, and each of the four
vectors solves a mode equation `G' = −|l|² G + N_G`.  The result (`term_hasDeriv`) is the block form
of the homological identity:

`d/du ⟨G, O F⟩ = ⟨G, P_l T P_j F⟩ + ⟨N_G, O F⟩ + ⟨G, O N_F⟩ + ⟨G, O(N_v, w) F⟩ + ⟨G, O(v, N_w) F⟩`.

The four heats of the outer denominator come from the four vectors, the phase from the covariance of
`T`, and `(−Σ + i r δ)·(−Σ + i r δ)⁻¹ = 1` removes `O` from the first term.  So this one lemma is
"`(∂_t − Σ) X₂ = X₁𝓛 + 𝓛*X₁`" and "`(∂_t − Σ) Z = X₁(B)`" with moving amplitudes.

The time dependence is explicit: on an exterior channel `(c, e)` the block is `e^{iτδ}` times the
block at `τ = 0` (`hcov`), which is bilinear in the leaves.  No derivative of an operator-valued
function of `τ` is taken.
-/

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

section Term

variable {r H : ℝ} {l j : Mode}

/-- The outer inverse is a sum over the exterior channels, on any vectors. -/
lemma inner_outerInv (T : Blk) (G y : V3) :
    inner ℂ G (outerInv r H l j T y) = ∑ c : Sgn, ∑ e : Sgn,
      resolv (-1) H (r * outerPhi c e l j) * inner ℂ G (hel c l (T (hel e j y))) := by
  simp only [outerInv, sum_apply, smul_apply, ContinuousLinearMap.comp_apply, helL_apply,
    inner_sum, inner_smul_right]

/-- The projection is a sum of channels. -/
lemma inner_leray_leray (T : Blk) (G y : V3) :
    inner ℂ G (leray l (T (leray j y))) = ∑ c : Sgn, ∑ e : Sgn,
      inner ℂ G (hel c l (T (hel e j y))) := by
  rw [← hel_sum j y, ← hel_sum l, inner_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_sum, hel_sum_distrib, inner_sum]

/-- A block term. -/
def oTerm (r H : ℝ) (l j : Mode) (Sr : ℝ → V3 → V3 → Blk) (G F v w : V3) (τ : ℝ) : ℂ :=
  inner ℂ G (outerInv r H l j (Sr τ v w) F)

variable {Sr : ℝ → V3 → V3 → Blk} {Sr0 : V3 →L[ℂ] V3 →L[ℂ] Blk}

/-- The phase factor of a channel. -/
def chP (r u φ : ℝ) : ℂ := Complex.exp (Complex.I * ((r * u) * φ : ℝ))

/-- The channel core: the block at `τ = 0`. -/
def core (Sr0 : V3 →L[ℂ] V3 →L[ℂ] Blk) (l j : Mode) (c e : Sgn) (G F v w : V3) : ℂ :=
  inner ℂ G (hel c l (Sr0 v w (hel e j F)))

lemma oTerm_eq (hcov : ∀ τ v w c e y, hel c l (Sr τ v w (hel e j y)) =
      Complex.exp (Complex.I * (τ * outerPhi c e l j : ℝ)) • hel c l (Sr0 v w (hel e j y)))
    (G F v w : V3) (u : ℝ) :
    oTerm r H l j Sr G F v w (r * u) = ∑ c : Sgn, ∑ e : Sgn,
      resolv (-1) H (r * outerPhi c e l j) * (chP r u (outerPhi c e l j) *
        core Sr0 l j c e G F v w) := by
  rw [oTerm, inner_outerInv]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
  rw [hcov, inner_smul_right]
  rfl

lemma source_eq (hcov : ∀ τ v w c e y, hel c l (Sr τ v w (hel e j y)) =
      Complex.exp (Complex.I * (τ * outerPhi c e l j : ℝ)) • hel c l (Sr0 v w (hel e j y)))
    (G F v w : V3) (u : ℝ) :
    inner ℂ G (leray l (Sr (r * u) v w (leray j F))) = ∑ c : Sgn, ∑ e : Sgn,
      chP r u (outerPhi c e l j) * core Sr0 l j c e G F v w := by
  rw [inner_leray_leray]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
  rw [hcov, inner_smul_right]
  rfl

/-- The derivative of the channel core along a path. -/
lemma core_hasDeriv (Sr0 : V3 →L[ℂ] V3 →L[ℂ] Blk) (c e : Sgn) {G F v w : ℝ → V3}
    {G' F' v' w' : V3} {A : Set ℝ} {x : ℝ} (hG : HasDerivWithinAt G G' A x)
    (hF : HasDerivWithinAt F F' A x) (hv : HasDerivWithinAt v v' A x)
    (hw : HasDerivWithinAt w w' A x) :
    HasDerivWithinAt (fun u => core Sr0 l j c e (G u) (F u) (v u) (w u))
      (core Sr0 l j c e (G x) F' (v x) (w x) + core Sr0 l j c e G' (F x) (v x) (w x) +
        (core Sr0 l j c e (G x) (F x) v' (w x) + core Sr0 l j c e (G x) (F x) (v x) w')) A x := by
  have h1 : HasDerivWithinAt (fun u => Sr0 (v u) (w u)) (Sr0 v' (w x) + Sr0 (v x) w') A x :=
    hasDeriv_bil Sr0 hv hw
  have h2 : HasDerivWithinAt (fun u => helL e j (F u)) (helL e j F') A x := hasDeriv_clm _ hF
  have h3 := hasDeriv_bil (ContinuousLinearMap.id ℂ Blk) h1 h2
  have h4 := hasDeriv_clm (helL c l) h3
  have h5 := HasDerivWithinAt.inner ℂ hG h4
  refine (h5.congr_deriv ?_)
  simp only [ContinuousLinearMap.id_apply, add_apply, map_add, inner_add_right, helL_apply, core]
  ring

/-- The derivative of the phase of a channel. -/
lemma chP_hasDeriv (r φ : ℝ) {A : Set ℝ} (x : ℝ) :
    HasDerivWithinAt (fun u => chP r u φ) (Complex.I * ((r * φ : ℝ) : ℂ) * chP r x φ) A x := by
  have h1 : HasDerivAt (fun u : ℝ => Complex.I * (((r * u) * φ : ℝ) : ℂ))
      (Complex.I * ((r * φ : ℝ) : ℂ)) x := by
    have h2 : HasDerivAt (fun u : ℝ => ((r * u) * φ : ℝ)) (r * φ) x := by
      have := ((hasDerivAt_id x).const_mul r).mul_const φ
      simpa using this
    have h3 := (h2.ofReal_comp).const_mul Complex.I
    simpa using h3
  have h4 := h1.cexp
  refine h4.hasDerivWithinAt.congr_deriv ?_
  simp only [chP]
  ring

variable {L2 J2 Ha Hb : ℝ}

/-- **One term of the identity.**  With `G' = −L²G + N_G`, `F' = −J²F + N_F`, `v' = −A v + N_v`,
`w' = −B w + N_w`, `H = L² + J² + A + B`, the derivative is the source plus the four insertions. -/
theorem term_hasDeriv (hH : H = L2 + J2 + Ha + Hb) (hH0 : 0 < H)
    (hcov : ∀ τ v w c e y, hel c l (Sr τ v w (hel e j y)) =
      Complex.exp (Complex.I * (τ * outerPhi c e l j : ℝ)) • hel c l (Sr0 v w (hel e j y)))
    {G F v w : ℝ → V3} {NG NF Nv Nw : V3} {A : Set ℝ} {x : ℝ}
    (hG : HasDerivWithinAt G (((-L2 : ℝ) : ℂ) • G x + NG) A x)
    (hF : HasDerivWithinAt F (((-J2 : ℝ) : ℂ) • F x + NF) A x)
    (hv : HasDerivWithinAt v (((-Ha : ℝ) : ℂ) • v x + Nv) A x)
    (hw : HasDerivWithinAt w (((-Hb : ℝ) : ℂ) • w x + Nw) A x) :
    HasDerivWithinAt (fun u => oTerm r H l j Sr (G u) (F u) (v u) (w u) (r * u))
      (inner ℂ (G x) (leray l (Sr (r * x) (v x) (w x) (leray j (F x)))) +
        oTerm r H l j Sr NG (F x) (v x) (w x) (r * x) +
        oTerm r H l j Sr (G x) NF (v x) (w x) (r * x) +
        oTerm r H l j Sr (G x) (F x) Nv (w x) (r * x) +
        oTerm r H l j Sr (G x) (F x) (v x) Nw (r * x)) A x := by
  have hexp : (fun u => oTerm r H l j Sr (G u) (F u) (v u) (w u) (r * u)) = fun u =>
      ∑ c : Sgn, ∑ e : Sgn, resolv (-1) H (r * outerPhi c e l j) * (chP r u (outerPhi c e l j) *
        core Sr0 l j c e (G u) (F u) (v u) (w u)) :=
    funext fun u => oTerm_eq hcov _ _ _ _ u
  rw [hexp]
  have hterm : ∀ c e, HasDerivWithinAt (fun u => resolv (-1) H (r * outerPhi c e l j) *
      (chP r u (outerPhi c e l j) * core Sr0 l j c e (G u) (F u) (v u) (w u)))
      (chP r x (outerPhi c e l j) * core Sr0 l j c e (G x) (F x) (v x) (w x) +
        resolv (-1) H (r * outerPhi c e l j) * (chP r x (outerPhi c e l j) *
          (core Sr0 l j c e NG (F x) (v x) (w x) + core Sr0 l j c e (G x) NF (v x) (w x) +
            core Sr0 l j c e (G x) (F x) Nv (w x) + core Sr0 l j c e (G x) (F x) (v x) Nw))) A x :=
    fun c e => by
    have h1 := (chP_hasDeriv r (outerPhi c e l j) (A := A) x).mul
      (core_hasDeriv (l := l) (j := j) Sr0 c e hG hF hv hw)
    have h2 := h1.const_mul (resolv (-1) H (r * outerPhi c e l j))
    refine h2.congr_deriv ?_
    have hne := Quant.resolv_den_ne_zero (ε := -1) (Or.inr rfl) hH0.ne' (r * outerPhi c e l j)
    have e1 : resolv (-1) H (r * outerPhi c e l j) *
        (((-H : ℝ) : ℂ) + ((r * outerPhi c e l j : ℝ) : ℂ) * Complex.I) = 1 := by
      have e2 : (((-1 : ℝ) * H : ℝ) : ℂ) = ((-H : ℝ) : ℂ) := by push_cast; ring
      rw [e2] at hne
      rw [Quant.resolv, e2, one_div, inv_mul_cancel₀ hne]
    simp only [core, map_add, map_smul, add_apply, smul_apply, hel_add, hel_smul, inner_add_left,
      inner_add_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    simp only [hH] at e1 ⊢
    set R := resolv (-1) (L2 + J2 + Ha + Hb) (r * outerPhi c e l j)
    set P := chP r x (outerPhi c e l j)
    push_cast at e1 ⊢
    linear_combination (P * inner ℂ (G x) (hel c l (Sr0 (v x) (w x) (hel e j (F x))))) * e1
  have hs := HasDerivWithinAt.fun_sum (u := Finset.univ) fun c _ =>
    HasDerivWithinAt.fun_sum (u := Finset.univ) fun e _ => hterm c e
  refine hs.congr_deriv ?_
  rw [source_eq hcov, oTerm_eq hcov, oTerm_eq hcov, oTerm_eq hcov, oTerm_eq hcov]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
  ring

/-- The block term is continuous along continuous paths. -/
lemma oTerm_continuousOn (hcov : ∀ τ v w c e y, hel c l (Sr τ v w (hel e j y)) =
      Complex.exp (Complex.I * (τ * outerPhi c e l j : ℝ)) • hel c l (Sr0 v w (hel e j y)))
    {G F v w : ℝ → V3} {K : Set ℝ} (hG : ContinuousOn G K) (hF : ContinuousOn F K)
    (hv : ContinuousOn v K) (hw : ContinuousOn w K) :
    ContinuousOn (fun u => oTerm r H l j Sr (G u) (F u) (v u) (w u) (r * u)) K := by
  have hc : ∀ c e, ContinuousOn (fun u => core Sr0 l j c e (G u) (F u) (v u) (w u)) K := by
    intro c e
    have h1 : ContinuousOn (fun u => Sr0 (v u) (w u)) K :=
      (Sr0.continuous₂.comp_continuousOn (hv.prodMk hw))
    have h2 : ContinuousOn (fun u => helL e j (F u)) K := (helL e j).continuous.comp_continuousOn hF
    have h3 : ContinuousOn (fun u => Sr0 (v u) (w u) (helL e j (F u))) K := h1.clm_apply h2
    have h4 : ContinuousOn (fun u => helL c l (Sr0 (v u) (w u) (helL e j (F u)))) K :=
      (helL c l).continuous.comp_continuousOn h3
    exact hG.inner h4
  have hP : ∀ φ : ℝ, Continuous fun u : ℝ => chP r u φ := fun φ => by
    unfold chP
    fun_prop
  have hexp : (fun u => oTerm r H l j Sr (G u) (F u) (v u) (w u) (r * u)) = fun u =>
      ∑ c : Sgn, ∑ e : Sgn, resolv (-1) H (r * outerPhi c e l j) * (chP r u (outerPhi c e l j) *
        core Sr0 l j c e (G u) (F u) (v u) (w u)) :=
    funext fun u => oTerm_eq hcov _ _ _ _ u
  rw [hexp]
  exact continuousOn_finsetSum _ fun c _ => continuousOn_finsetSum _ fun e _ =>
    continuousOn_const.mul ((hP _).continuousOn.mul (hc c e))

/-- The source term is continuous along continuous paths. -/
lemma source_continuousOn (hcov : ∀ τ v w c e y, hel c l (Sr τ v w (hel e j y)) =
      Complex.exp (Complex.I * (τ * outerPhi c e l j : ℝ)) • hel c l (Sr0 v w (hel e j y)))
    {G F v w : ℝ → V3} {K : Set ℝ} (hG : ContinuousOn G K) (hF : ContinuousOn F K)
    (hv : ContinuousOn v K) (hw : ContinuousOn w K) :
    ContinuousOn (fun u => inner ℂ (G u) (leray l (Sr (r * u) (v u) (w u) (leray j (F u))))) K := by
  have hc : ∀ c e, ContinuousOn (fun u => core Sr0 l j c e (G u) (F u) (v u) (w u)) K := by
    intro c e
    have h1 : ContinuousOn (fun u => Sr0 (v u) (w u)) K :=
      (Sr0.continuous₂.comp_continuousOn (hv.prodMk hw))
    have h2 : ContinuousOn (fun u => helL e j (F u)) K := (helL e j).continuous.comp_continuousOn hF
    have h3 : ContinuousOn (fun u => Sr0 (v u) (w u) (helL e j (F u))) K := h1.clm_apply h2
    have h4 : ContinuousOn (fun u => helL c l (Sr0 (v u) (w u) (helL e j (F u)))) K :=
      (helL c l).continuous.comp_continuousOn h3
    exact hG.inner h4
  have hP : ∀ φ : ℝ, Continuous fun u : ℝ => chP r u φ := fun φ => by
    unfold chP
    fun_prop
  have hexp : (fun u => inner ℂ (G u) (leray l (Sr (r * u) (v u) (w u) (leray j (F u))))) = fun u =>
      ∑ c : Sgn, ∑ e : Sgn, chP r u (outerPhi c e l j) *
        core Sr0 l j c e (G u) (F u) (v u) (w u) :=
    funext fun u => source_eq hcov _ _ _ _ u
  rw [hexp]
  exact continuousOn_finsetSum _ fun c _ => continuousOn_finsetSum _ fun e _ =>
    (hP _).continuousOn.mul (hc c e)

end Term

end OVNS.Quant.Metric

end
