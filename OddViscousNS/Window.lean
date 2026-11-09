import OddViscousNS.NormalForm
import OddViscousNS.Corrector

/-! # Window transfer (`Proposition fg:prop:tr`) -/

open MeasureTheory Set intervalIntegral Filter
open scoped ENNReal Topology
noncomputable section
namespace OVNS

/-- The stability radius `θ = 1/(16 c₄)`. -/
def theta : ℝ := 1 / (16 * c4)

lemma theta_pos : 0 < theta := by
  have := c4_pos
  unfold theta
  positivity

/-- A crude lower bound for `c₄`, from the single term `k = (1,1,1)`. -/
private lemma one_third_le_c4 : 1 / 3 ≤ c4 := by
  have hs : Summable fun k : Mode => if k = 0 then (0 : ℝ) else (absSq k)⁻¹ ^ 2 := by
    by_contra h
    have h0 := c4_pos
    rw [c4, tsum_eq_zero_of_not_summable h] at h0
    simp at h0
  have hk : (fun _ => 1 : Mode) ≠ 0 := fun h => by simpa using congrFun h 0
  have h1 := hs.le_tsum (fun _ => 1) fun j _ => by
    split_ifs
    · exact le_rfl
    · exact sq_nonneg _
  rw [ite_eq_right hk] at h1
  have h3 : absSq (fun _ => 1 : Mode) = 3 := by
    simp [absSq]
  rw [h3] at h1
  refine Real.le_sqrt_of_sq_le ?_
  norm_num at h1 ⊢
  exact h1

lemma theta_lt_one : theta < 1 := by
  have h := one_third_le_c4
  unfold theta
  rw [div_lt_one (by linarith)]
  linarith

variable {g : Field} {T : ℝ≥0∞} {w y : ℝ → Field} {r t₀ : ℝ} {N : ℕ}

/-- The modified error `ẽ = y - w - ψ + R_N`. -/
def tildeE (r t₀ : ℝ) (N : ℕ) (g : Field) (w y : ℝ → Field) (t : ℝ) : Field :=
  y t - w t - psi r t₀ g t + RN r t₀ N w t

/-- The difference `z = y - w`. -/
def zdiff (w y : ℝ → Field) (t : ℝ) : Field := y t - w t

/-- The force `ℱ` of the modified error. -/
def errF (r t₀ : ℝ) (N : ℕ) (g : Field) (w y : ℝ → Field) (t : ℝ) : Field :=
  (-(Qphase (r * (t + t₀)) (zdiff w y t) (zdiff w y t))
    - (2 : ℂ) • Qphase (r * (t + t₀)) (w t) (zdiff w y t)
    - oscHigh (r * (t + t₀)) N (w t) + GN r t₀ N g w t)
    + (fun k => ((absSq k : ℝ) : ℂ) • RN r t₀ N w t k)

/-! ### The algebra of the modified error -/

/-- `A = |k|²` as a multiplier. -/
private def lapF (u : Field) : Field := fun k => ((absSq k : ℝ) : ℂ) • u k

private lemma lapF_term (u : Field) (k : Mode) :
    sobWeight 0 k * ‖lapF u k‖ ^ 2 = sobWeight 2 k * ‖u k‖ ^ 2 := by
  by_cases hk : k = 0
  · simp [sobWeight, hk]
  · have e : (2 * 2 : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
    simp only [sobWeight, hk, ite_false, lapF]
    rw [e, Real.rpow_natCast, norm_smul, Complex.norm_real, Real.norm_of_nonneg (absSq_nonneg k),
      ← absk_sq]
    simp only [mul_zero, Real.rpow_zero]
    ring

private lemma lapF_inH {u : Field} (hu : InH 2 u) : InH 0 (lapF u) := by
  unfold InH
  simp only [lapF_term]
  exact hu

private lemma hnorm_lapF (u : Field) : hnorm 0 (lapF u) = hnorm 2 u := by
  simp only [hnorm, lapF_term]

/-- On slow modes the filtered force is the original one. -/
private lemma PiS_filtG (hg : Adm 2 g) (t : ℝ) : PiS (filtG r t₀ g t) = PiS g := by
  funext k
  by_cases hk : k 2 = 0
  · simp only [PiS, hk, ↓reduceIte]
    change rot _ k (g k) = g k
    rw [rot_slow _ hk]
    by_cases h0 : k = 0
    · subst h0
      simp [leray, hg.mean]
    · exact leray_of_perp h0 (hg.sol k)
  · simp [PiS, hk]

/-- Binomial expansion of the filtered nonlinearity around `b`. -/
private lemma filtN_expand (t : ℝ) {a b : Field} (ha : MZ 2 a) (hb : MZ 2 b) :
    Qphase (r * (t + t₀)) a a = Qphase (r * (t + t₀)) (a - b) (a - b) +
      (2 : ℂ) • Qphase (r * (t + t₀)) b (a - b) + Qphase (r * (t + t₀)) b b := by
  have hN := majorized_filtN r t₀
  have hd : MZ 2 (a - b) := ⟨ha.inH.sub hb.inH, by simp [ha.mean, hb.mean]⟩
  have e1 : Qphase (r * (t + t₀)) (a - b) (a - b) = _ := hN.sub_left t a b (a - b) ha hb hd
  have e2 : Qphase (r * (t + t₀)) a (a - b) = _ := hN.sub_right t a a b ha ha hb
  have e3 : Qphase (r * (t + t₀)) b (a - b) = _ := hN.sub_right t b a b hb ha hb
  have e4 : Qphase (r * (t + t₀)) a b = Qphase (r * (t + t₀)) b a :=
    Qm_comm_of_symm (phaseM_symm _) ha hb
  simp only [filtN] at e1 e2 e3
  rw [e1, e2, e3, e4]
  module

/-- The force of the modified error, in terms of the right-hand sides of the equations. -/
private lemma errF_eq (hg : Adm 2 g) {t : ℝ} (hyt : MZ 2 (y t)) (hwt : MZ 2 (w t)) :
    errF r t₀ N g w y t = (filtG r t₀ g t - Qphase (r * (t + t₀)) (y t) (y t)) -
      (PiS g - Qres (w t) (w t)) - PiF (filtG r t₀ g t) +
      (oscLow (r * (t + t₀)) N (w t) + GN r t₀ N g w t) + lapF (RN r t₀ N w t) := by
  have h1 := filtN_expand (r := r) (t₀ := t₀) t hyt hwt
  have h2 := Qphase_split (r * (t + t₀)) N hwt
  have h3 : filtG r t₀ g t = PiS g + PiF (filtG r t₀ g t) := by
    conv_lhs => rw [← PiS_add_PiF (filtG r t₀ g t), PiS_filtG hg t]
  rw [h1, h2]
  change (-(Qphase (r * (t + t₀)) (y t - w t) (y t - w t))
    - (2 : ℂ) • Qphase (r * (t + t₀)) (w t) (y t - w t)
    - oscHigh (r * (t + t₀)) N (w t) + GN r t₀ N g w t) + lapF (RN r t₀ N w t) = _
  linear_combination (norm := module) (-1 : ℂ) • h3

/-- Continuity of the vertex. -/
private lemma continuous_hel (a : Sgn) (k : Mode) : Continuous (hel a k) :=
  LinearMap.continuous_of_finiteDimensional
    ({ toFun := hel a k, map_add' := hel_add a k, map_smul' := fun c v => hel_smul a k c v } :
      V3 →ₗ[ℂ] V3)

private lemma continuous_leray (k : Mode) : Continuous (leray k) :=
  LinearMap.continuous_of_finiteDimensional
    ({ toFun := leray k, map_add' := leray_add k, map_smul' := fun c v => leray_smul k c v } :
      V3 →ₗ[ℂ] V3)

private lemma continuous_dotM (k : Mode) : Continuous fun v : V3 => dotM v k := by
  change Continuous fun v : V3 => ∑ i, v i * (k i : ℂ)
  fun_prop

private lemma continuousOn_vert {S : Set ℝ} {A B : ℝ → V3} (p q : Mode) (hA : ContinuousOn A S)
    (hB : ContinuousOn B S) : ContinuousOn (fun t => vert p q (A t) (B t)) S := by
  have h1 : ContinuousOn (fun t => Complex.I * dotM (A t) q) S :=
    continuousOn_const.mul ((continuous_dotM q).comp_continuousOn hA)
  have h2 : ContinuousOn (fun t => Complex.I * dotM (B t) p) S :=
    continuousOn_const.mul ((continuous_dotM p).comp_continuousOn hB)
  have h3 : ContinuousOn (fun t => (Complex.I * dotM (A t) q) • B t) S := h1.smul hB
  have h4 : ContinuousOn (fun t => (Complex.I * dotM (B t) p) • A t) S := h2.smul hA
  have h5 : ContinuousOn
      (fun t => leray (p + q) ((Complex.I * dotM (A t) q) • B t + (Complex.I * dotM (B t) p) • A t))
      S := (continuous_leray _).comp_continuousOn (h3.add h4)
  exact (continuous_const_smul (1 / 2 : ℂ)).comp_continuousOn h5

/-- A `Qm` with a low-supported multiplier is a finite sum, so mode-wise continuous. -/
private lemma continuousOn_Qm_low {S : Set ℝ} {m : ℝ → Mult} {f h : ℝ → Field}
    (hm : ∀ t a b c p q, ¬ absk p ≤ N → m t a b c p q = 0)
    (hc : ∀ a b c p q, ContinuousOn (fun t => m t a b c p q) S)
    (hf : ∀ p, ContinuousOn (fun t => f t p) S) (hh : ∀ p, ContinuousOn (fun t => h t p) S)
    (k : Mode) : ContinuousOn (fun t => Qm (m t) (f t) (h t) k) S := by
  have e : (fun t => Qm (m t) (f t) (h t) k) = fun t => ∑ p ∈ (finite_ball N).toFinset,
      ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, m t a b c p (k - p) • hel c k
        (vert p (k - p) (hel a p (f t p)) (hel b (k - p) (h t (k - p)))) := by
    funext t
    refine tsum_eq_sum fun p hp => ?_
    have hp' : ¬ absk p ≤ N := by simpa using hp
    simp [hm t _ _ _ p _ hp']
  rw [e]
  refine continuousOn_finsetSum _ fun p _ => continuousOn_finsetSum _ fun a _ =>
    continuousOn_finsetSum _ fun b _ => continuousOn_finsetSum _ fun c _ => ?_
  exact (hc a b c p (k - p)).smul ((continuous_hel c k).comp_continuousOn (continuousOn_vert p _
    ((continuous_hel a p).comp_continuousOn (hf p))
    ((continuous_hel b _).comp_continuousOn (hh _))))

private lemma continuous_phaseM (a b c : Sgn) (p q : Mode) :
    Continuous fun t : ℝ => phaseM (r * (t + t₀)) a b c p q := by
  unfold phaseM
  fun_prop

private lemma nfM_low {τ : ℝ} {a b c : Sgn} {p q : Mode} (hp : ¬ absk p ≤ N) :
    nfM r τ N a b c p q = 0 :=
  ite_eq_right fun h => absurd h.1 hp

private lemma oscLowM_low {τ : ℝ} {a b c : Sgn} {p q : Mode} (hp : ¬ absk p ≤ N) :
    oscLowM τ N a b c p q = 0 :=
  ite_eq_right fun h => absurd h.1 hp

private lemma continuous_nfM (a b c : Sgn) (p q : Mode) :
    Continuous fun t : ℝ => nfM r (r * (t + t₀)) N a b c p q := by
  by_cases h : IsLow N a b c p q
  · simp only [nfM, h, ite_true]
    exact (continuous_phaseM a b c p q).div_const _
  · simp only [nfM, h, ite_false]
    exact continuous_const

private lemma continuous_oscLowM (a b c : Sgn) (p q : Mode) :
    Continuous fun t : ℝ => oscLowM (r * (t + t₀)) N a b c p q := by
  by_cases h : IsLow N a b c p q
  · simp only [oscLowM, h, ite_true]
    exact continuous_phaseM a b c p q
  · simp only [oscLowM, h, ite_false]
    exact continuous_const

/-- The norm of the force of the modified error, at a fixed time. -/
private lemma errF_bound {t : ℝ} (hz : MZ 2 (zdiff w y t)) (hw : MZ 2 (w t))
    (hO : InH 0 (oscHigh (r * (t + t₀)) N (w t))) (hG : InH 0 (GN r t₀ N g w t))
    (hR : InH 2 (RN r t₀ N w t)) :
    InH 0 (errF r t₀ N g w y t) ∧ hnorm 0 (errF r t₀ N g w y t) ≤
      2 * (hnorm 1 (zdiff w y t) * wiener (zdiff w y t)) +
      2 * (hnorm 1 (w t) * wiener (zdiff w y t) + wiener (w t) * hnorm 1 (zdiff w y t)) +
      hnorm 0 (oscHigh (r * (t + t₀)) N (w t)) + hnorm 0 (GN r t₀ N g w t) +
      hnorm 2 (RN r t₀ N w t) := by
  obtain ⟨h1i, h1⟩ := hnorm_Qm_zero_le (phaseM_bdd (r * (t + t₀))) hz hz
  obtain ⟨h2i, h2⟩ := hnorm_Qm_zero_le (phaseM_bdd (r * (t + t₀))) hw hz
  change InH 0 (Qphase (r * (t + t₀)) _ _) at h1i
  change InH 0 (Qphase (r * (t + t₀)) _ _) at h2i
  change hnorm 0 (Qphase (r * (t + t₀)) _ _) ≤ _ at h1
  change hnorm 0 (Qphase (r * (t + t₀)) _ _) ≤ _ at h2
  have hL := lapF_inH hR
  have i1 := h1i.neg
  have i2 := h2i.smul (2 : ℂ)
  have i3 := (i1.sub i2)
  have i4 := i3.sub hO
  have i5 := i4.add hG
  refine ⟨i5.add hL, ?_⟩
  change hnorm 0 (_ + lapF (RN r t₀ N w t)) ≤ _
  have b1 := hnorm_add_le i5 hL
  have b2 := hnorm_add_le i4 hG
  have b3 := hnorm_sub_le i3 hO
  have b4 := hnorm_sub_le i1 i2
  rw [hnorm_lapF] at b1
  rw [hnorm_neg] at b4
  rw [hnorm_smul] at b4
  have e2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [e2] at b4
  have e : wiener (zdiff w y t) * hnorm 1 (zdiff w y t) =
      hnorm 1 (zdiff w y t) * wiener (zdiff w y t) := mul_comm _ _
  nlinarith

/-- The norm along a `HeatPair` is bounded. -/
private lemma HeatPair.exists_bound {σ b : ℝ} {c F : ℝ → Field} (h : HeatPair σ 0 b c F)
    (hb : 0 ≤ b) : ∃ C : ℝ, ∀ t ∈ Icc 0 b, hnorm σ (c t) ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (h.continuousOn_hnorm_sq hb)
  refine ⟨1 + C, fun t ht => ?_⟩
  have h1 := (le_abs_self _).trans (hC t ht)
  nlinarith [sq_nonneg (hnorm σ (c t) - 1)]

/-- Crude `L²` bound of the force. -/
private lemma errF_l2 (hr : r ≠ 0) (hg : Adm 2 g) (hw : RefSol g ⊤ w) {Ty : ℝ≥0∞}
    (hy : IsHeatSol (filtN r t₀) (filtG r t₀ g) Ty y) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < Ty) :
    ∫⁻ t in Icc 0 b, hsE (1 - 1) (errF r t₀ N g w y t) < ∞ := by
  obtain ⟨Cy, hCy⟩ := (hy.heatPair (majorized_filtN r t₀) (goodForce_filtG r t₀ hg) hb
    hbT).exists_bound hb
  obtain ⟨Cw, hCw⟩ := (hw.heatPair majorized_res (goodForce_PiS hg) hb
    ENNReal.ofReal_lt_top).exists_bound hb
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = |Cy| + |Cw| := ⟨_, rfl⟩
  obtain ⟨K, -, hK⟩ := exists_normal_form_bound N (C ^ 2) (hnorm 1 g)
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have hc4 := c4_pos.le
  have hprod : ∀ {x x' u u' : ℝ}, 0 ≤ x → 0 ≤ u → x ≤ x' → u ≤ u' → x * u ≤ x' * u' :=
    fun hx hu h1 h2 => mul_le_mul h1 h2 hu (hx.trans h1)
  have hD : ∀ t ∈ Icc 0 b, InH 0 (errF r t₀ N g w y t) ∧ hnorm 0 (errF r t₀ N g w y t) ≤
      2 * (2 * C * (c4 * (2 * C))) + 2 * (C * (c4 * (2 * C)) + c4 * C * (2 * C)) +
      (C * (c4 * C) + c4 * C * C) + K / |r| + K / |r| := by
    intro t ht
    have htT : ENNReal.ofReal t < Ty := (ENNReal.ofReal_le_ofReal ht.2).trans_lt hbT
    have hyt := (hy.adm t ht.1 htT).mz
    have hwa := hw.adm t ht.1 ENNReal.ofReal_lt_top
    have hwt := hwa.mz
    have hzt : MZ 2 (zdiff w y t) := ⟨hyt.inH.sub hwt.inH, by simp [zdiff, hyt.mean, hwt.mean]⟩
    have hy2 : hnorm 2 (y t) ≤ C := by
      have := hCy t ht
      have := le_abs_self Cy
      have := abs_nonneg Cw
      linarith
    have hw2 : hnorm 2 (w t) ≤ C := by
      have := hCw t ht
      have := le_abs_self Cw
      have := abs_nonneg Cy
      linarith
    have hz2 : hnorm 2 (zdiff w y t) ≤ 2 * C := by
      have := hnorm_sub_le hyt.inH hwt.inH
      unfold zdiff
      linarith
    have hw1 : hnorm 1 (w t) ≤ C := (hnorm_mono (by norm_num) hwt.inH).trans hw2
    have hz1 : hnorm 1 (zdiff w y t) ≤ 2 * C := (hnorm_mono (by norm_num) hzt.inH).trans hz2
    have hw0 : hnorm 0 (w t) ^ 2 ≤ C ^ 2 :=
      pow_le_pow_left₀ (hnorm_nonneg _ _) ((hnorm_mono (by norm_num) hwt.inH).trans hw2) 2
    obtain ⟨hR, hRb, hG, hGb⟩ := hK r t₀ g w t hr hg le_rfl hwa hw0
    obtain ⟨hOi, hOb⟩ := hnorm_Qm_zero_le (oscHighM_bdd (r * (t + t₀)) N) hwt hwt
    have hAw : wiener (w t) ≤ c4 * C :=
      (wiener_le hwt).trans (mul_le_mul_of_nonneg_left hw2 hc4)
    have hAz : wiener (zdiff w y t) ≤ c4 * (2 * C) :=
      (wiener_le hzt).trans (mul_le_mul_of_nonneg_left hz2 hc4)
    have hR2 : InH 2 (RN r t₀ N w t) := hR.inH.mono (by norm_num)
    obtain ⟨hi, hb⟩ := errF_bound (g := g) hzt hwt hOi hG hR2
    refine ⟨hi, hb.trans ?_⟩
    have n1 := hnorm_nonneg 1 (zdiff w y t)
    have n2 := hnorm_nonneg 1 (w t)
    have n3 := wiener_nonneg (zdiff w y t)
    have n4 := wiener_nonneg (w t)
    have p1 := hprod n1 n3 hz1 hAz
    have p2 := hprod n2 n3 hw1 hAz
    have p3 := hprod n4 n1 hAw hz1
    have p4 := hprod n2 n4 hw1 hAw
    have p5 := hprod n4 n2 hAw hw1
    change hnorm 0 (oscHigh (r * (t + t₀)) N (w t)) ≤ _ at hOb
    linarith
  obtain ⟨D, hDdef⟩ : ∃ D, D = 2 * (2 * C * (c4 * (2 * C))) +
      2 * (C * (c4 * (2 * C)) + c4 * C * (2 * C)) + (C * (c4 * C) + c4 * C * C) +
      K / |r| + K / |r| := ⟨_, rfl⟩
  rw [← hDdef] at hD
  rw [show (1 : ℝ) - 1 = 0 by norm_num]
  calc ∫⁻ t in Icc 0 b, hsE 0 (errF r t₀ N g w y t)
      ≤ ∫⁻ _ in Icc 0 b, ENNReal.ofReal (D ^ 2) := by
        refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
        obtain ⟨hi, hn⟩ := hD t ht
        rw [hsE_eq_ofReal hi]
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hnorm_nonneg _ _) hn 2)
    _ < ∞ := by
        rw [setLIntegral_const, Real.volume_Icc]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- Each mode of the force of the modified error is continuous. -/
private lemma errF_cont (hg : Adm 2 g) (hw : RefSol g ⊤ w) {Ty : ℝ≥0∞}
    (hy : IsHeatSol (filtN r t₀) (filtG r t₀ g) Ty y) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < Ty) (k : Mode) :
    ContinuousOn (fun t => errF r t₀ N g w y t k) (Icc 0 b) := by
  have hpy := hy.heatPair (majorized_filtN r t₀) (goodForce_filtG r t₀ hg) hb hbT
  have hpw := hw.heatPair majorized_res (goodForce_PiS hg) hb ENNReal.ofReal_lt_top
  have hwm : ∀ p, ContinuousOn (fun t => w t p) (Icc 0 b) := fun p t ht =>
    (hpw.mode p t ht).continuousWithinAt
  have hWd : ∀ p, ContinuousOn (fun t => wdot g (w t) p) (Icc 0 b) := fun p => by
    have h : ContinuousOn (fun t => (-(absSq p : ℝ) : ℂ) • w t p + (PiS g - Qres (w t) (w t)) p)
        (Icc 0 b) := (ContinuousOn.smul (f := fun _ => (-(absSq p : ℝ) : ℂ)) continuousOn_const
      (hwm p)).add (hpw.force_cont p)
    refine h.congr fun t _ => ?_
    simp only [wdot, Pi.sub_apply]
    abel
  have c1 : ContinuousOn (fun t => (filtG r t₀ g t - Qphase (r * (t + t₀)) (y t) (y t)) k)
      (Icc 0 b) := hpy.force_cont k
  have c2 : ContinuousOn (fun t => (PiS g - Qres (w t) (w t)) k) (Icc 0 b) := hpw.force_cont k
  have c3 : ContinuousOn (fun t => PiF (filtG r t₀ g t) k) (Icc 0 b) := by
    by_cases hk : k 2 = 0
    · simp only [PiF, hk, ite_true]
      exact continuousOn_const
    · simp only [PiF, hk, ite_false]
      have hr' : Continuous fun τ : ℝ => rot τ k (g k) :=
        continuous_iff_continuousAt.2 fun τ => (hasDerivAt_rot k (g k) τ).continuousAt
      have hc : Continuous fun t : ℝ => -(r * (t + t₀)) := by fun_prop
      exact (hr'.comp hc).continuousOn
  have c4' : ContinuousOn (fun t => oscLow (r * (t + t₀)) N (w t) k) (Icc 0 b) :=
    continuousOn_Qm_low (fun _ _ _ _ _ _ hp => oscLowM_low hp)
      (fun a b c p q => (continuous_oscLowM a b c p q).continuousOn) hwm hwm k
  have c5 : ContinuousOn (fun t => GN r t₀ N g w t k) (Icc 0 b) :=
    (continuousOn_Qm_low (fun _ _ _ _ _ _ hp => nfM_low hp)
      (fun a b c p q => (continuous_nfM a b c p q).continuousOn) hWd hwm k).add
    (continuousOn_Qm_low (fun _ _ _ _ _ _ hp => nfM_low hp)
      (fun a b c p q => (continuous_nfM a b c p q).continuousOn) hwm hWd k)
  have c6 : ContinuousOn (fun t => lapF (RN r t₀ N w t) k) (Icc 0 b) :=
    ContinuousOn.smul (f := fun _ => ((absSq k : ℝ) : ℂ)) continuousOn_const
      (continuousOn_Qm_low (fun _ _ _ _ _ _ hp => nfM_low hp)
      (fun a b c p q => (continuous_nfM a b c p q).continuousOn) hwm hwm k)
  refine (((((c1.sub c2).sub c3).add (c4'.add c5))).add c6).congr fun t ht => ?_
  have htT : ENNReal.ofReal t < Ty := (ENNReal.ofReal_le_ofReal ht.2).trans_lt hbT
  rw [errF_eq (r := r) (N := N) hg (hy.adm t ht.1 htT).mz
    (hw.adm t ht.1 ENNReal.ofReal_lt_top).mz]
  rfl

/-- The modified error solves its mode equation. -/
private lemma tildeE_mode (hr : r ≠ 0) (hg : Adm 2 g) (hw : RefSol g ⊤ w) {Ty : ℝ≥0∞}
    (hy : IsHeatSol (filtN r t₀) (filtG r t₀ g) Ty y) {b : ℝ}
    (hbT : ENNReal.ofReal b < Ty) (k : Mode) (t : ℝ) (ht : t ∈ Icc 0 b) :
    HasDerivWithinAt (fun s => tildeE r t₀ N g w y s k)
      ((-(absSq k : ℝ) : ℂ) • tildeE r t₀ N g w y t k + errF r t₀ N g w y t k) (Icc 0 b) t := by
  have htT : ENNReal.ofReal t < Ty := (ENNReal.ofReal_le_ofReal ht.2).trans_lt hbT
  have hs : Icc (0 : ℝ) b ⊆ Ici 0 := Icc_subset_Ici_self
  have hyk := (hy.mode k t ht.1 htT).mono hs
  have hwk := (hw.mode k t ht.1 ENNReal.ofReal_lt_top).mono hs
  have hψ := (psi_mode (r := r) (t₀ := t₀) hg k t).hasDerivWithinAt (s := Icc 0 b)
  have hR := (RN_mode (N := N) (t₀ := t₀) hr hg hw k ht.1 ENNReal.ofReal_lt_top).mono hs
  refine HasDerivWithinAt.congr_deriv (((hyk.fun_sub hwk).fun_sub hψ).fun_add hR) ?_
  rw [errF_eq (r := r) (N := N) hg (hy.adm t ht.1 htT).mz
    (hw.adm t ht.1 ENNReal.ofReal_lt_top).mz]
  simp only [tildeE, lapF, filtN, Pi.add_apply, Pi.sub_apply]
  module

/-- The modified error solves a heat equation on every compact subinterval of the lifespan. -/
theorem heatPair_tildeE (hr : r ≠ 0) (hg : Adm 2 g) {Ty : ℝ≥0∞} (hw : RefSol g ⊤ w)
    (hy : IsHeatSol (filtN r t₀) (filtG r t₀ g) Ty y) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < Ty) (_h0 : y 0 = w 0) :
    HeatPair 1 0 b (tildeE r t₀ N g w y) (errF r t₀ N g w y) := by
  refine ⟨fun t ht => ?_, tildeE_mode hr hg hw hy hbT, errF_cont hg hw hy hb hbT,
    errF_l2 hr hg hw hy hb hbT⟩
  have htT : ENNReal.ofReal t < Ty := (ENNReal.ofReal_le_ofReal ht.2).trans_lt hbT
  obtain ⟨K, -, hK⟩ := exists_normal_form_bound N (hnorm 0 (w t) ^ 2) (hnorm 1 g)
  have hwa := hw.adm t ht.1 ENNReal.ofReal_lt_top
  obtain ⟨hR, -⟩ := hK r t₀ g w t hr hg le_rfl hwa le_rfl
  exact (((hy.adm t ht.1 htT).inH.sub hwa.inH).sub (psi_adm hg t ht.1).inH |>.add
    (hR.inH.mono (by norm_num))).mono (by norm_num)

/-! ### The energy estimate -/

/-- The linear coefficient of the force estimate. -/
private def coefA (cI X Y : ℝ) : ℝ := 4 * X ^ 2 * cI ^ 2 + 2 * c4 * Y

/-- What is known at a time of the window. -/
private structure Win (r t₀ : ℝ) (N : ℕ) (g : Field) (w y : ℝ → Field) (X Y ε D t : ℝ) :
    Prop where
  hy : MZ 2 (y t)
  hw : MZ 2 (w t)
  w1 : hnorm 1 (w t) ≤ X
  w2 : hnorm 2 (w t) ≤ Y
  rn : InH 2 (RN r t₀ N w t)
  ps : InH 2 (psi r t₀ g t)
  small : hnorm 2 (RN r t₀ N w t) + hnorm 2 (psi r t₀ g t) ≤ ε
  gn : InH 0 (GN r t₀ N g w t)
  gn' : hnorm 0 (GN r t₀ N g w t) ≤ ε
  os : InH 0 (oscHigh (r * (t + t₀)) N (w t))
  os' : hnorm 0 (oscHigh (r * (t + t₀)) N (w t)) ≤ D

variable {X Y ε D t : ℝ}

private lemma Win.mzZ (h : Win r t₀ N g w y X Y ε D t) : MZ 2 (zdiff w y t) :=
  ⟨h.hy.inH.sub h.hw.inH, by simp [zdiff, h.hy.mean, h.hw.mean]⟩

private lemma Win.inE (h : Win r t₀ N g w y X Y ε D t) : InH 2 (tildeE r t₀ N g w y t) :=
  ((h.hy.inH.sub h.hw.inH).sub h.ps).add h.rn

/-- `z = ẽ + ψ - R_N` costs at most `ε` in the norms below `2`. -/
private lemma Win.z_le (h : Win r t₀ N g w y X Y ε D t) {s : ℝ} (hs : s ≤ 2) :
    hnorm s (zdiff w y t) ≤ hnorm s (tildeE r t₀ N g w y t) + ε := by
  have e : zdiff w y t = tildeE r t₀ N g w y t + psi r t₀ g t - RN r t₀ N w t := by
    simp only [zdiff, tildeE]
    abel
  have hE := h.inE.mono hs
  have hψ := h.ps.mono hs
  have hR := h.rn.mono hs
  rw [e]
  have h1 := hnorm_sub_le (hE.add hψ) hR
  have h2 := hnorm_add_le hE hψ
  have h3 := hnorm_mono hs h.ps
  have h4 := hnorm_mono hs h.rn
  linarith [h.small]

/-- The real-variable core of the force estimate. -/
private lemma force_numerics {cI X Y Z₁ Z₂ Wz W₁ Ww : ℝ} (hX : 0 ≤ X) (hcI : 0 < cI)
    (hZ₁ : 0 ≤ Z₁) (hZ₂ : 0 ≤ Z₂) (hZ : Z₁ ≤ 2 * theta) (hWz0 : 0 ≤ Wz) (h1 : Wz ≤ c4 * Z₂)
    (h2 : Wz ≤ cI * Real.sqrt (Z₁ * Z₂)) (hW₁ : W₁ ≤ X) (hWw : Ww ≤ c4 * Y) :
    2 * (Z₁ * Wz) + 2 * (W₁ * Wz + Ww * Z₁) ≤ Z₂ / 2 + coefA cI X Y * Z₁ := by
  have hc := c4_pos
  have hθ : theta * c4 = 1 / 16 := by
    unfold theta
    field_simp
  have ha : Z₁ * Wz ≤ 2 * theta * (c4 * Z₂) := mul_le_mul hZ h1 hWz0 (hZ₁.trans hZ)
  have ha' : 2 * theta * (c4 * Z₂) = Z₂ / 8 := by
    calc 2 * theta * (c4 * Z₂) = 2 * (theta * c4) * Z₂ := by ring
      _ = Z₂ / 8 := by rw [hθ]; ring
  set s := Real.sqrt (Z₁ * Z₂) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = Z₁ * Z₂ := Real.sq_sqrt (mul_nonneg hZ₁ hZ₂)
  have hb : W₁ * Wz ≤ X * (cI * s) := mul_le_mul hW₁ h2 hWz0 hX
  have hb' : 2 * (X * (cI * s)) ≤ Z₂ / 4 + 4 * X ^ 2 * cI ^ 2 * Z₁ := by
    refine (sq_le_sq₀ (by positivity) (by positivity)).1 ?_
    have e : (2 * (X * (cI * s))) ^ 2 = 4 * (X ^ 2 * cI ^ 2 * (Z₁ * Z₂)) := by
      rw [← hs2]
      ring
    rw [e]
    nlinarith [sq_nonneg (Z₂ / 4 - 4 * X ^ 2 * cI ^ 2 * Z₁)]
  have hd : Ww * Z₁ ≤ c4 * Y * Z₁ := mul_le_mul_of_nonneg_right hWw hZ₁
  unfold coefA
  linarith

/-- The force estimate at a time where `‖z‖₁ ≤ 2θ`. -/
private lemma Win.force (h : Win r t₀ N g w y X Y ε D t) {cI : ℝ} (hcI : 0 < cI)
    (hI : ∀ u : Field, MZ 2 u → wiener u ≤ cI * Real.sqrt (hnorm 1 u * hnorm 2 u)) (hX : 0 ≤ X)
    (hz : hnorm 1 (zdiff w y t) ≤ 2 * theta) :
    InH 0 (errF r t₀ N g w y t) ∧ hnorm 0 (errF r t₀ N g w y t) ≤
      hnorm 2 (tildeE r t₀ N g w y t) / 2 + coefA cI X Y * hnorm 1 (tildeE r t₀ N g w y t) +
      ((5 / 2 + coefA cI X Y) * ε + D) := by
  obtain ⟨hi, hb⟩ := errF_bound (g := g) h.mzZ h.hw h.os h.gn h.rn
  refine ⟨hi, hb.trans ?_⟩
  have hY : 0 ≤ Y := (hnorm_nonneg _ _).trans h.w2
  have hA : 0 ≤ coefA cI X Y := by
    have := c4_pos
    unfold coefA
    positivity
  have hw2 : wiener (w t) ≤ c4 * Y :=
    (wiener_le h.hw).trans (mul_le_mul_of_nonneg_left h.w2 c4_pos.le)
  have hnum := force_numerics hX hcI (hnorm_nonneg 1 _) (hnorm_nonneg 2 _) hz
    (wiener_nonneg _) (wiener_le h.mzZ) (hI _ h.mzZ) h.w1 hw2
  have h1 := h.z_le (s := 1) (by norm_num)
  have h2 := h.z_le (s := 2) le_rfl
  have h3 := mul_le_mul_of_nonneg_left h1 hA
  have h4 : hnorm 2 (RN r t₀ N w t) ≤ ε := by
    have := hnorm_nonneg 2 (psi r t₀ g t)
    linarith [h.small]
  have h5 := h.gn'
  have h6 := h.os'
  linarith

/-- The pairing estimate at a time where `‖z‖₁ ≤ 2θ`. -/
private lemma Win.pair_le (h : Win r t₀ N g w y X Y ε D t) {cI : ℝ} (hcI : 0 < cI)
    (hI : ∀ u : Field, MZ 2 u → wiener u ≤ cI * Real.sqrt (hnorm 1 u * hnorm 2 u)) (hX : 0 ≤ X)
    (hz : hnorm 1 (zdiff w y t) ≤ 2 * theta) :
    2 * pair 1 (tildeE r t₀ N g w y t) (errF r t₀ N g w y t) ≤
      2 * hnorm 2 (tildeE r t₀ N g w y t) ^ 2 +
      (2 * coefA cI X Y ^ 2 * hnorm 1 (tildeE r t₀ N g w y t) ^ 2 +
        2 * ((5 / 2 + coefA cI X Y) * ε + D) ^ 2) := by
  obtain ⟨hi, hb⟩ := h.force hcI hI hX hz
  have e1 : (1 : ℝ) + 1 = 2 := by norm_num
  have e0 : (1 : ℝ) - 1 = 0 := by norm_num
  have hp := (OVNS.pair_le (σ := 1) (c := tildeE r t₀ N g w y t) (F := errF r t₀ N g w y t)
    (by rw [e1]; exact h.inE) (by rw [e0]; exact hi)).2
  rw [e1, e0] at hp
  have hp' := le_of_abs_le hp
  set a := hnorm 2 (tildeE r t₀ N g w y t) with ha
  set x := hnorm 1 (tildeE r t₀ N g w y t)
  set A := coefA cI X Y
  set L := (5 / 2 + A) * ε + D
  have ha0 : 0 ≤ a := hnorm_nonneg _ _
  have h1 := mul_le_mul_of_nonneg_left hb ha0
  nlinarith [sq_nonneg (a - (A * x + L)), sq_nonneg (A * x - L)]

/-- The Gronwall step on the window. -/
private lemma energy_bound (hr : r ≠ 0) (hg : Adm 2 g) (hw : RefSol g ⊤ w) {Ty : ℝ≥0∞}
    (hy : IsHeatSol (filtN r t₀) (filtG r t₀ g) Ty y) (h0 : y 0 = w 0) {κ β b : ℝ} (hκ : 0 ≤ κ)
    (hβ : 0 ≤ β) (hb : 0 ≤ b) (hbT : ENNReal.ofReal b < Ty)
    (hp : ∀ t ∈ Icc 0 b, 2 * pair 1 (tildeE r t₀ N g w y t) (errF r t₀ N g w y t) ≤
      2 * hnorm 2 (tildeE r t₀ N g w y t) ^ 2 +
      (κ * hnorm 1 (tildeE r t₀ N g w y t) ^ 2 + β)) :
    ∀ t ∈ Icc 0 b, hnorm 1 (tildeE r t₀ N g w y t) ^ 2 ≤
      (hnorm 1 (tildeE r t₀ N g w y 0) ^ 2 + b * β) * Real.exp (b * κ) := by
  have hP := heatPair_tildeE (N := N) hr hg hw hy hb hbT h0
  have hc := hP.continuousOn_hnorm_sq hb
  have key : ∀ s t, 0 ≤ s → s ≤ t → t ≤ b → hnorm 1 (tildeE r t₀ N g w y t) ^ 2 ≤
      hnorm 1 (tildeE r t₀ N g w y s) ^ 2 +
        ∫ u in s..t, ((fun _ => κ) u * hnorm 1 (tildeE r t₀ N g w y u) ^ 2 + (fun _ => β) u) := by
    intro s t hs hst ht
    have e : (1 : ℝ) + 1 = 2 := by norm_num
    have hq := hP.mono hs ht
    have hid := hq.energy_identity le_rfl hst le_rfl
    have hdiss := hq.intervalIntegrable_dissipation hst
    have hpair := hq.intervalIntegrable_pair hst
    rw [e] at hid hdiss
    have hG : IntervalIntegrable
        (fun u => κ * hnorm 1 (tildeE r t₀ N g w y u) ^ 2 + β) volume s t :=
      ContinuousOn.intervalIntegrable (by
        rw [uIcc_of_le hst]
        exact (continuousOn_const.mul (hc.mono (Icc_subset_Icc hs ht))).add continuousOn_const)
    have hle := intervalIntegral.integral_mono_on hst (hpair.const_mul 2)
      ((hdiss.const_mul 2).add hG) fun u hu => hp u ⟨hs.trans hu.1, hu.2.trans ht⟩
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hdiss.const_mul 2) hG,
      intervalIntegral.integral_const_mul] at hle
    beta_reduce
    linarith
  intro t ht
  have h := gronwall_simple (y := fun u => hnorm 1 (tildeE r t₀ N g w y u) ^ 2)
    (κ := fun _ => κ) (β := fun _ => β) hb hc intervalIntegrable_const (fun _ => hκ)
    intervalIntegrable_const (fun _ => hβ) key 0 t le_rfl ht.1 ht.2
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
  refine h.trans ?_
  have h1 : t * β ≤ b * β := mul_le_mul_of_nonneg_right ht.2 hβ
  have h2 : t * κ ≤ b * κ := mul_le_mul_of_nonneg_right ht.2 hκ
  have h3 := Real.exp_le_exp.2 h2
  exact mul_le_mul (by linarith) h3 (Real.exp_pos _).le
    (add_nonneg (sq_nonneg _) (mul_nonneg hb hβ))

/-- `‖z‖₁` is continuous on compact subintervals of the lifespan. -/
private lemma continuousOn_zdiff {G₁ G₂ : ℝ → Field} {N₁ N₂ : ℝ → Field → Field → Field}
    {Ty : ℝ≥0∞} (hy : IsHeatSol N₁ G₁ Ty y) (hw : IsHeatSol N₂ G₂ ⊤ w) {b : ℝ}
    (hbT : ENNReal.ofReal b < Ty) :
    ContinuousOn (fun t => hnorm 1 (zdiff w y t)) (Icc 0 b) := by
  intro τ hτ
  have hτT : ENNReal.ofReal τ < Ty := (ENNReal.ofReal_le_ofReal hτ.2).trans_lt hbT
  have hs : 𝓝[Icc 0 b] τ ≤ 𝓝[Ici 0] τ := nhdsWithin_mono τ Icc_subset_Ici_self
  have hcy := (hy.cont τ hτ.1 hτT).mono_left hs
  have hcw := (hw.cont τ hτ.1 ENNReal.ofReal_lt_top).mono_left hs
  have hsum := hcy.add hcw
  rw [add_zero] at hsum
  rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hsum
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htT : ENNReal.ofReal t < Ty := (ENNReal.ofReal_le_ofReal ht.2).trans_lt hbT
  have y1 := (hy.adm t ht.1 htT).inH
  have y0 := (hy.adm τ hτ.1 hτT).inH
  have w1 := (hw.adm t ht.1 ENNReal.ofReal_lt_top).inH
  have w0 := (hw.adm τ hτ.1 ENNReal.ofReal_lt_top).inH
  have iy := y1.sub y0
  have iw := w1.sub w0
  have hd := hnorm_sub_le iy iw
  have hd1 := hnorm_mono (s := 1) (by norm_num) (iy.sub iw)
  have ha : InH 1 (zdiff w y t) := (y1.sub w1).mono (by norm_num)
  have hb : InH 1 (zdiff w y τ) := (y0.sub w0).mono (by norm_num)
  have e1 : zdiff w y t = (y t - y τ - (w t - w τ)) + zdiff w y τ := by
    simp only [zdiff]
    abel
  have e2 : zdiff w y τ = -(y t - y τ - (w t - w τ)) + zdiff w y t := by
    simp only [zdiff]
    abel
  have i0 : InH 1 (y t - y τ - (w t - w τ)) := (iy.sub iw).mono (by norm_num)
  have h1 := hnorm_add_le i0 hb
  have h2 := hnorm_add_le i0.neg ha
  rw [← e1] at h1
  rw [← e2, hnorm_neg] at h2
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

/-- The first-exit argument: a bootstrap on initial segments closes. -/
private lemma first_exit {f : ℝ → ℝ} {θ b : ℝ} (hθ : 0 < θ) (hb : 0 ≤ b)
    (hf : ContinuousOn f (Icc 0 b)) (h0 : f 0 = 0)
    (hstep : ∀ c, 0 ≤ c → c ≤ b → (∀ u ∈ Icc 0 c, f u ≤ 2 * θ) → ∀ u ∈ Icc 0 c, f u ≤ θ) :
    ∀ u ∈ Icc 0 b, f u ≤ θ := by
  have hC : IsClosed (Icc 0 b ∩ f ⁻¹' Ici (3 * θ / 2)) :=
    hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hK : IsCompact (Icc 0 b ∩ f ⁻¹' Ici (3 * θ / 2)) :=
    isCompact_Icc.of_isClosed_subset hC inter_subset_left
  by_cases hne : (Icc 0 b ∩ f ⁻¹' Ici (3 * θ / 2)).Nonempty
  · obtain ⟨t, ⟨ht, hft⟩, hmin⟩ := hK.exists_isLeast hne
    have hft' : 3 * θ / 2 ≤ f t := hft
    have ht0 : 0 < t := by
      rcases ht.1.eq_or_lt with h | h
      · rw [← h, h0] at hft'
        linarith
      · exact h
    have hle : ∀ u ∈ Ico 0 t, f u ≤ θ := fun u hu => by
      refine hstep u hu.1 (hu.2.le.trans ht.2) (fun v hv => ?_) u ⟨hu.1, le_rfl⟩
      by_contra hv'
      have hvt : t ≤ v := hmin ⟨⟨hv.1, hv.2.trans (hu.2.le.trans ht.2)⟩, by
        change 3 * θ / 2 ≤ f v
        linarith⟩
      linarith [hv.2, hu.2]
    have hcl : closure (Ico 0 t) = Icc 0 t := closure_Ico ht0.ne
    have hsub : Icc 0 t ⊆ Icc 0 b := Icc_subset_Icc_right ht.2
    have := le_on_closure hle (by rw [hcl]; exact hf.mono hsub)
      (by rw [hcl]; exact continuousOn_const) (by rw [hcl]; exact ⟨ht.1, le_rfl⟩)
    linarith
  · refine hstep b hb le_rfl fun u hu => ?_
    by_contra hu'
    exact hne ⟨u, hu, by
      change 3 * θ / 2 ≤ f u
      linarith⟩

/-- The final numerics of the window estimate. -/
private lemma window_numerics {θ ε x T b A D : ℝ} (hθ : 0 < θ) (hε : 0 ≤ ε) (hx : 0 ≤ x)
    (hb : 0 ≤ b) (hbT : b ≤ T) (hA : 0 ≤ A)
    (hx2 : x ^ 2 ≤ (ε ^ 2 + b * (2 * ((5 / 2 + A) * ε + D) ^ 2)) *
      Real.exp (b * (2 * A ^ 2)))
    (hD : 4 * T * Real.exp (T * (2 * A ^ 2)) * D ^ 2 ≤ θ ^ 2 / 4)
    (hεP : ε * (1 + (1 + 4 * T * (5 / 2 + A) ^ 2) * Real.exp (T * (2 * A ^ 2))) ≤ θ / 4) :
    x + ε ≤ θ := by
  have hT : 0 ≤ T := hb.trans hbT
  obtain ⟨E, hE⟩ : ∃ E, E = Real.exp (T * (2 * A ^ 2)) := ⟨_, rfl⟩
  rw [← hE] at hD hεP
  have hE1 : 0 < E := hE ▸ Real.exp_pos _
  have hEb : Real.exp (b * (2 * A ^ 2)) ≤ E := by
    rw [hE]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hbT (by positivity))
  obtain ⟨P, hP⟩ : ∃ P, P = (1 + 4 * T * (5 / 2 + A) ^ 2) * E := ⟨_, rfl⟩
  rw [← hP] at hεP
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hL : ((5 / 2 + A) * ε + D) ^ 2 ≤ 2 * (5 / 2 + A) ^ 2 * ε ^ 2 + 2 * D ^ 2 := by
    nlinarith [sq_nonneg ((5 / 2 + A) * ε - D)]
  have h1 : (ε ^ 2 + b * (2 * ((5 / 2 + A) * ε + D) ^ 2)) *
      Real.exp (b * (2 * A ^ 2)) ≤ (ε ^ 2 + T * (2 * (2 * (5 / 2 + A) ^ 2 * ε ^ 2 + 2 * D ^ 2))) *
      E := by
    refine mul_le_mul ?_ hEb (Real.exp_pos _).le (by positivity)
    have : b * (2 * ((5 / 2 + A) * ε + D) ^ 2) ≤
        T * (2 * (2 * (5 / 2 + A) ^ 2 * ε ^ 2 + 2 * D ^ 2)) :=
      mul_le_mul hbT (by linarith) (by positivity) hT
    linarith
  have h2 : (ε ^ 2 + T * (2 * (2 * (5 / 2 + A) ^ 2 * ε ^ 2 + 2 * D ^ 2))) * E =
      ε ^ 2 * P + 4 * T * E * D ^ 2 := by
    rw [hP]
    ring
  have h3 : ε ^ 2 * P ≤ θ ^ 2 / 16 := by
    have h4 : (ε * (1 + P)) ^ 2 ≤ (θ / 4) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hεP 2
    have h5 : ε ^ 2 * P ≤ (ε * (1 + P)) ^ 2 := by
      have : P ≤ (1 + P) ^ 2 := by nlinarith
      have := mul_le_mul_of_nonneg_left this (sq_nonneg ε)
      nlinarith
    nlinarith
  have hx3 : x ≤ 3 * θ / 4 := by
    refine (sq_le_sq₀ hx (by positivity)).1 ?_
    nlinarith
  have hε2 : ε ≤ θ / 4 := by
    have : ε * 1 ≤ ε * (1 + P) := mul_le_mul_of_nonneg_left (by linarith) hε
    linarith
  linarith

/-- The pieces of `Win` from the bounds on the reference. -/
private lemma win_of_bounds {Cos K φ : ℝ} {Ty : ℝ≥0∞}
    (hCos : InH 0 (oscHigh (r * (t + t₀)) N (w t)) ∧
      hnorm 0 (oscHigh (r * (t + t₀)) N (w t)) ≤ Cos / Real.sqrt N * hnorm 2 (w t) ^ 2)
    (hCos0 : 0 ≤ Cos) (hr : r ≠ 0) (hg : Adm 2 g) (hg1 : hnorm 1 g ≤ φ) (hw : Adm 2 (w t))
    (hy : IsHeatSol (filtN r t₀) (filtG r t₀ g) Ty y) (ht0 : 0 ≤ t)
    (htT : ENNReal.ofReal t < Ty)
    (hK : Adm 3 (RN r t₀ N w t) ∧ hnorm 2 (RN r t₀ N w t) ≤ K / |r| ∧
      InH 0 (GN r t₀ N g w t) ∧ hnorm 0 (GN r t₀ N g w t) ≤ K / |r|)
    (hX : hnorm 1 (w t) ≤ X) (hY : hnorm 2 (w t) ≤ Y) (hφ : 0 ≤ φ) :
    Win r t₀ N g w y X Y ((K + 2 * φ) / |r|) (Cos / Real.sqrt N * Y ^ 2) t := by
  obtain ⟨hR, hRb, hG, hGb⟩ := hK
  obtain ⟨hψ, hψb⟩ := psi_bound (r := r) (t₀ := t₀) hr hg t ht0
  have hrp : 0 < |r| := abs_pos.2 hr
  have hψb' : hnorm 2 (psi r t₀ g t) ≤ 2 * φ / |r| :=
    hψb.trans (div_le_div_of_nonneg_right (by linarith) hrp.le)
  have e : (K + 2 * φ) / |r| = K / |r| + 2 * φ / |r| := add_div _ _ _
  have h2φ : 0 ≤ 2 * φ / |r| := by positivity
  refine ⟨(hy.adm t ht0 htT).mz, hw.mz, hX, hY, hR.inH.mono (by norm_num), hψ, ?_, hG, ?_,
    hCos.1, hCos.2.trans ?_⟩
  · rw [e]
    linarith
  · rw [e]
    linarith
  · have := pow_le_pow_left₀ (hnorm_nonneg 2 (w t)) hY 2
    exact mul_le_mul_of_nonneg_left this (by positivity)

/-- The window-transfer theorem: for `|r|` large, a filtered solution exists on the whole window
and stays `θ`-close in `H¹` to the reference with the same datum. -/
theorem window_transfer (φ T X E J Y : ℝ) (hφ : 0 ≤ φ) (hT : 0 < T) :
    ∃ Rw : ℝ, 0 ≤ Rw ∧ ∀ (r t₀ : ℝ) (g : Field) (w y : ℝ → Field) (Ty : ℝ≥0∞),
      Rw ≤ |r| → r ≠ 0 → Adm 2 g → hnorm 2 g ≤ φ → RefSol g ⊤ w →
      (∀ t ∈ Icc 0 T, hnorm 1 (w t) ≤ X ∧ hnorm 0 (w t) ^ 2 ≤ E ∧ hnorm 2 (w t) ≤ Y) →
      (∫ t in (0 : ℝ)..T, hnorm 2 (w t) ^ 2) ≤ J →
      IsHeatSol (filtN r t₀) (filtG r t₀ g) Ty y → y 0 = w 0 →
      (Ty ≠ ⊤ → ∀ C : ℝ, ¬ ∀ t, 0 ≤ t → ENNReal.ofReal t < Ty → hnorm 2 (y t) ≤ C) →
      ENNReal.ofReal T < Ty ∧ ∀ t ∈ Icc 0 T, hnorm 1 (y t - w t) ≤ theta := by
  obtain ⟨cI, hcI, hI⟩ := exists_wiener_interp
  obtain ⟨Cos, hCos0, hCos⟩ := exists_oscHigh_bound
  have hθ := theta_pos
  obtain ⟨A, hAdef⟩ : ∃ A, A = coefA cI |X| |Y| := ⟨_, rfl⟩
  have hA : 0 ≤ A := by
    have := c4_pos
    rw [hAdef]
    unfold coefA
    positivity
  obtain ⟨E₁, hE₁⟩ : ∃ E₁, E₁ = Real.exp (T * (2 * A ^ 2)) := ⟨_, rfl⟩
  have hE₁0 : 0 < E₁ := hE₁ ▸ Real.exp_pos _
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 16 * T * E₁ * (Cos * |Y| ^ 2) ^ 2 / theta ^ 2 := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌈M⌉₊ + 2 := ⟨_, rfl⟩
  have hN2 : 2 ≤ N := by omega
  have hNM : M ≤ N := by
    have := Nat.le_ceil M
    rw [hN]
    push_cast
    linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  obtain ⟨D, hDdef⟩ : ∃ D, D = Cos / Real.sqrt N * |Y| ^ 2 := ⟨_, rfl⟩
  have hD : 4 * T * E₁ * D ^ 2 ≤ theta ^ 2 / 4 := by
    have e : D ^ 2 = (Cos * |Y| ^ 2) ^ 2 / N := by
      rw [hDdef, mul_pow, div_pow, Real.sq_sqrt hNpos.le, mul_pow]
      ring
    have h1 : M * theta ^ 2 = 16 * T * E₁ * (Cos * |Y| ^ 2) ^ 2 := by
      rw [hM]
      field_simp
    have h2 : M * theta ^ 2 ≤ N * theta ^ 2 := mul_le_mul_of_nonneg_right hNM (sq_nonneg _)
    rw [e, ← mul_div_assoc, div_le_iff₀ hNpos]
    nlinarith
  obtain ⟨K, hK0, hK⟩ := exists_normal_form_bound N E φ
  obtain ⟨P, hP⟩ : ∃ P, P = (1 + 4 * T * (5 / 2 + A) ^ 2) * E₁ := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  refine ⟨(K + 2 * φ) * (4 * (1 + P)) / theta, by positivity, ?_⟩
  intro r t₀ g w y Ty hRw hr hg hgφ hw hbd _hJ hy h0 hblow
  have hrp : 0 < |r| := abs_pos.2 hr
  have hg1 : hnorm 1 g ≤ φ := (hnorm_mono (by norm_num) hg.inH).trans hgφ
  obtain ⟨ε, hεdef⟩ : ∃ ε, ε = (K + 2 * φ) / |r| := ⟨_, rfl⟩
  have hε0 : 0 ≤ ε := by rw [hεdef]; positivity
  have hεP : ε * (1 + P) ≤ theta / 4 := by
    rw [div_le_iff₀ hθ] at hRw
    rw [hεdef, div_mul_eq_mul_div, div_le_iff₀ hrp]
    nlinarith
  have hwin : ∀ t, t ∈ Icc 0 T → ENNReal.ofReal t < Ty → Win r t₀ N g w y |X| |Y| ε D t := by
    intro t ht htT
    have hwa := hw.adm t ht.1 ENNReal.ofReal_lt_top
    obtain ⟨b1, b2, b3⟩ := hbd t ht
    rw [hεdef, hDdef]
    exact win_of_bounds (hCos _ N (w t) hN2 hwa.mz) hCos0 hr hg hg1 hwa hy ht.1 htT
      (hK r t₀ g w t hr hg hg1 hwa b2) (b1.trans (le_abs_self _)) (b3.trans (le_abs_self _)) hφ
  have hstep : ∀ b, 0 ≤ b → b ≤ T → ENNReal.ofReal b < Ty →
      (∀ u ∈ Icc 0 b, hnorm 1 (zdiff w y u) ≤ 2 * theta) →
      ∀ u ∈ Icc 0 b, hnorm 1 (zdiff w y u) ≤ theta := by
    intro b hb hbT hbTy hz u hu
    have hsub : Icc 0 b ⊆ Icc 0 T := Icc_subset_Icc_right hbT
    have hlt : ∀ t ∈ Icc 0 b, ENNReal.ofReal t < Ty := fun t ht =>
      (ENNReal.ofReal_le_ofReal ht.2).trans_lt hbTy
    have hpair : ∀ t ∈ Icc 0 b, _ := fun t ht =>
      (hwin t (hsub ht) (hlt t ht)).pair_le hcI hI (abs_nonneg X) (hz t ht)
    rw [← hAdef] at hpair
    have hen := energy_bound (N := N) hr hg hw hy h0 (by positivity) (by positivity) hb hbTy
      hpair u hu
    have h00 : hnorm 1 (tildeE r t₀ N g w y 0) ^ 2 ≤ ε ^ 2 := by
      have hw0 := hwin 0 ⟨le_rfl, hT.le⟩ (hlt 0 ⟨le_rfl, hb⟩)
      have e : tildeE r t₀ N g w y 0 = RN r t₀ N w 0 := by
        simp only [tildeE, h0, psi_zero]
        simp
      rw [e]
      have h1 := hnorm_mono (s := 1) (by norm_num) hw0.rn
      have h2 := hw0.small
      have h3 := hnorm_nonneg 2 (psi r t₀ g 0)
      exact pow_le_pow_left₀ (hnorm_nonneg _ _) (by linarith) 2
    have hx2 := hen.trans (mul_le_mul_of_nonneg_right (add_le_add_left h00 _)
      (Real.exp_pos _).le)
    have hz1 := (hwin u (hsub hu) (hlt u hu)).z_le (s := 1) (by norm_num)
    have hfin := window_numerics hθ hε0 (hnorm_nonneg 1 _) hb hbT hA hx2 (by rw [← hE₁]; exact hD)
      (by rw [← hE₁, ← hP]; exact hεP)
    linarith
  have hclose : ∀ b, 0 ≤ b → b ≤ T → ENNReal.ofReal b < Ty →
      ∀ u ∈ Icc 0 b, hnorm 1 (zdiff w y u) ≤ theta := by
    intro b hb hbT hbTy
    refine first_exit hθ hb (continuousOn_zdiff hy hw hbTy) (by simp [zdiff, h0, hnorm_zero]) ?_
    intro c hc hcb hz
    exact hstep c hc (hcb.trans hbT) ((ENNReal.ofReal_le_ofReal hcb).trans_lt hbTy) hz
  have hlife : ENNReal.ofReal T < Ty := by
    by_contra hnot
    have hTy : Ty ≤ ENNReal.ofReal T := not_lt.1 hnot
    obtain ⟨C, hC⟩ := h1_bound_excludes_blowup (|X| + theta) (hnorm 1 g) T (hnorm 2 (y 0))
    refine hblow (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hTy) C (hC _ _ Ty y
      (majorized_filtN r t₀) (goodForce_filtG r t₀ hg) hy le_rfl hTy ?_)
    intro t ht htT
    have htle : t < T := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht).1 (htT.trans_le hTy)
    have hzt := hclose t ht htle.le htT t ⟨ht, le_rfl⟩
    have hwi := (hwin t ⟨ht, htle.le⟩ htT)
    have e : y t = zdiff w y t + w t := by simp [zdiff]
    rw [e]
    have h1 := hnorm_add_le (hwi.mzZ.inH.mono (s := 1) (by norm_num))
      (hwi.hw.inH.mono (s := 1) (by norm_num))
    have h2 := hwi.w1
    linarith
  exact ⟨hlife, hclose T hT.le le_rfl hlife⟩

end OVNS
