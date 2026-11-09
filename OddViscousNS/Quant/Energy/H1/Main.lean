import OddViscousNS.Quant.Energy.H1.Bounds
import OddViscousNS.Quant.Regimes.Continuation

/-!
# E5 — the corrected `H¹` energy: the interface

`h1Energy_of_threshold`: for every `Cs ≥ 0` with `ResH1 (281/1000) Cs`,
`H1EnergyInterface (281/1000) Cs μ φ 2 (h1Nbar μ φ) (h1Pi μ φ) h1K₁ (h1Threshold 2 μ φ) nearN`,
with the energy `E = h1Energy` and the constant sources `N_f = nfConst`, `f_f = ffConst`,
`m = mConst`; and `h1_degree`: the threshold `h1Threshold 2` has fixed-force degree `< d` at
`σ = 281/1000`, for slow exponents `eA ≤ 2`, `eB ≤ 3`, `eJ ≤ 4`, `eW ≤ 5/2` (the Fourier-side
`slowExpF`).  Everything rests on the six locked analytic inputs of `Bounds.lean`.

* **Coercivity** `ℓ₁ a_F² ≤ 2E ≤ u₁ a_F²` (`h1Energy_coercive`): the metric is `≤ 2⁻²⁰ a_F²`
  (`X1form_le`, role 28 operator), the cubic `≤ a_F²/128` (`cubicE_static_le`, role 13).
* **The integrated inequality** (`h1Energy_integrated`): `h1Energy_identity` on a subinterval,
  integrated against the pointwise `h1RHS_budget`; the integrands are continuous, `a_F, b_F` being
  continuous along the solution (`norms_continuous`, `Regimes/Continuation.lean`).
* **The budgets** (`nf_budget`, `ff_budget`, `m_budget`): the sources are constants on the piece,
  so their integrals are `(t − s)·const`, paid by the shares of `shares_of_threshold`.
* **`Cs`-independence**: `h1K₁`, `h1Threshold`, `h1Nbar`, `h1Pi` are defined without `Cs` (the
  resonant term stays on the right-hand side of the interface inequality), so
  `h1Energy_of_threshold` has exactly the quantifier order of the hypothesis `hE1` of
  `quantitative_fixed_force_of_energy'` (`K₁, q₁, Nbar, piTol` before `Cs`).
* **Degree** (`DegLe`: a small calculus of `f ≲ μ^a`, the constants hidden): with
  `β = 1719/719 ≤ 12/5`, `v = 2719/719 ≤ 19/5` and `δ ≤ 1/8`, every term of `h1Threshold 2` is
  `≲ μ^{27/2}` and `27/2 < 9876/719`.  Exact degrees are in `t12_h1_scaffold.md` §5; the worst is
  role 13, `100 v/29 ≈ 13.04`, then the mixed near partner, `(100/49)(eW + δ + v) ≈ 12.82 + 2δ`.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace OVNS.Quant

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-! ### A. Coercivity -/

lemma half_le_ell1 : (1 : ℝ) / 2 ≤ ell1 := by
  unfold ell1
  norm_num

lemma ell1_pos : 0 < ell1 := lt_of_lt_of_le (by norm_num) half_le_ell1

/-- The arithmetic of coercivity. -/
lemma coercive_core {a2 m c : ℝ} (hm : |m| ≤ 1 / 2 ^ 20 * a2) (hc : |2 * c| ≤ 1 / 128 * a2) :
    ell1 * a2 ≤ a2 + m + 2 * c ∧ a2 + m + 2 * c ≤ u1 * a2 := by
  have h1 := abs_le.mp hm
  have h2 := abs_le.mp hc
  unfold ell1 u1
  constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2]

/-- The metric share. -/
lemma metric_share {B' B q a : ℝ} (hq0 : 0 < q) (_hB' : 0 ≤ B') (hB : B' ≤ B)
    (hop : 2 ^ 8 * B / q ≤ 1 / 2 ^ 20) : 2 ^ 8 * B' * a ^ 2 / q ≤ 1 / 2 ^ 20 * a ^ 2 :=
  calc 2 ^ 8 * B' * a ^ 2 / q = (2 ^ 8 * B' / q) * a ^ 2 := by ring
    _ ≤ (2 ^ 8 * B / q) * a ^ 2 := by gcongr
    _ ≤ 1 / 2 ^ 20 * a ^ 2 := mul_le_mul_of_nonneg_right hop (sq_nonneg a)

/-- The static share. -/
lemma static_share {cS Pq a b Y : ℝ} (hcS : 0 ≤ cS) (hPq : 0 ≤ Pq) (hbY : b ≤ Y)
    (hst : 2 * cS * Y * Pq ≤ 1 / 128) : 2 * (cS * Pq * a ^ 2 * b) ≤ 1 / 128 * a ^ 2 :=
  calc 2 * (cS * Pq * a ^ 2 * b) = (2 * cS * b * Pq) * a ^ 2 := by ring
    _ ≤ (2 * cS * Y * Pq) * a ^ 2 := by gcongr
    _ ≤ 1 / 128 * a ^ 2 := mul_le_mul_of_nonneg_right hst (sq_nonneg a)

/-- **Coercivity of the corrected energy** (TeX after eq. quant-kinetic-floor):
`ℓ₁ a_F² ≤ 2E ≤ u₁ a_F²` on the piece. -/
theorem h1Energy_coercive (h : ActualSol μ φ r g y Ty) {Tp : ℝ} (hTp : 0 ≤ Tp) (hφ : 0 ≤ φ)
    {caps : Caps} {s t : ℝ} (hP : PieceHyp Tp (h1Threshold Tp μ φ) r g y Ty caps s t)
    (hK : h1K₁ * Real.sqrt caps.PF * caps.yF ^ (3 / 2 : ℝ) * nearN |r| ≤ 1)
    {u : ℝ} (hu : u ∈ Icc s t) :
    ell1 * fastNorm 1 r g y u ^ 2 ≤ 2 * h1Energy r g y u ∧
      2 * h1Energy r g y u ≤ u1 * fastNorm 1 r g y u ^ 2 := by
  obtain ⟨hr1, -, -, -, sstat, -, -, -, -, sop, -⟩ := shares_of_threshold hTp hφ hP.thr hK
  have hr0 : 0 < |r| := by linarith only [hr1]
  have hr : r ≠ 0 := abs_pos.mp hr0
  have hu0 : 0 ≤ u := hP.hs.trans hu.1
  have huT := lt_lifespan hu.2 hP.ht
  have hx := actual_adm h hu0 huT
  obtain ⟨-, cF2, -, cS2, -⟩ := hP.onPrefix.1 u hu
  have hF := hx.PiF
  have hS := hx.PiS
  have hF' : PiF (PiF (actual r g y u)) = PiF (actual r g y u) := by
    funext k; by_cases hk : k 2 = 0 <;> simp [PiF, hk]
  have hS' : PiS (PiS (actual r g y u)) = PiS (actual r g y u) := by
    funext k; by_cases hk : k 2 = 0 <;> simp [PiS, hk]
  have hm : |metricCorr r g y u| ≤ 1 / 2 ^ 20 * fastNorm 1 r g y u ^ 2 :=
    (X1form_le hr (r * u) hS.mz hS.real hS' hF.mz hF').trans
      (metric_share hr0 (hnorm_nonneg 2 _) (cS2.trans (le_cp _)) sop)
  have hc : |2 * cubicCorr r g y u| ≤ 1 / 128 * fastNorm 1 r g y u ^ 2 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h1 : |cubicE 1 (-1) r (r * u) (PiF (actual r g y u))| ≤
        cStat * nearP |r| * fastNorm 1 r g y u ^ 2 * fastNorm 2 r g y u :=
      cubicE_static_le hr1 (r * u) hF.mz hF'
    have h2 := static_share (a := fastNorm 1 r g y u) (b := fastNorm 2 r g y u)
      (by unfold cStat; positivity : (0 : ℝ) ≤ cStat) (nearP_nonneg (abs_nonneg r))
      (cF2.trans (le_cp _)) sstat
    exact (mul_le_mul_of_nonneg_left h1 (by norm_num)).trans h2
  have e : 2 * h1Energy r g y u = fastNorm 1 r g y u ^ 2 + metricCorr r g y u +
      2 * cubicCorr r g y u := by
    unfold h1Energy
    ring
  rw [e]
  exact coercive_core hm hc

/-! ### B. The integrated inequality -/

/-- The integrands are interval integrable inside the lifespan (`a_F, b_F` are continuous). -/
lemma h1_integrable (h : ActualSol μ φ r g y Ty) {σ : ℝ} (Cs nf ff m : ℝ) (hσ0 : 0 ≤ σ)
    (hσ3 : σ ≤ 3) {u₁ u₂ : ℝ} (hu₁ : 0 ≤ u₁) (hu : u₁ ≤ u₂) (ht : ENNReal.ofReal u₂ < Ty) :
    IntervalIntegrable (fun u => fastNorm 2 r g y u ^ 2) volume u₁ u₂ ∧
      IntervalIntegrable (fun u => Cs * fastNorm 1 r g y u ^ (3 - σ) * fastNorm 2 r g y u ^ σ +
        nf * fastNorm 2 r g y u + ff + m * fastNorm 1 r g y u ^ 2) volume u₁ u₂ := by
  obtain ⟨hA, hB, -⟩ := norms_continuous h (hu₁.trans hu) ht
  have hsub : uIcc u₁ u₂ ⊆ Icc 0 u₂ := by
    rw [uIcc_of_le hu]
    exact Icc_subset_Icc_left hu₁
  have hA' := hA.mono hsub
  have hB' := hB.mono hsub
  have c1 : ContinuousOn (fun u => fastNorm 1 r g y u ^ (3 - σ)) (uIcc u₁ u₂) :=
    hA'.rpow_const fun _ _ => Or.inr (by linarith only [hσ3])
  have c2 : ContinuousOn (fun u => fastNorm 2 r g y u ^ σ) (uIcc u₁ u₂) :=
    hB'.rpow_const fun _ _ => Or.inr hσ0
  refine ⟨(hB'.pow 2).intervalIntegrable, ?_⟩
  exact (((((continuousOn_const.mul c1).mul c2).add (continuousOn_const.mul hB')).add
    continuousOn_const).add (continuousOn_const.mul (hA'.pow 2))).intervalIntegrable

/-- **The integrated energy inequality** on every subinterval of the piece
(`h1Energy_identity` + `h1RHS_budget`): `E(u₂) − E(u₁) + ¾∫b_F² ≤ ∫(C_s a_F^{3−σ} b_F^σ + N_f b_F +
f_f + m a_F²)`. -/
theorem h1Energy_integrated (h : ActualSol μ φ r g y Ty) {Tp σ Cs : ℝ} (hσ0 : 0 ≤ σ) (hσ3 : σ ≤ 3)
    (hTp : 0 ≤ Tp) (hφ : 0 ≤ φ) (hres : ResH1 σ Cs) {caps : Caps} {s t : ℝ}
    (hP : PieceHyp Tp (h1Threshold Tp μ φ) r g y Ty caps s t)
    (hK : h1K₁ * Real.sqrt caps.PF * caps.yF ^ (3 / 2 : ℝ) * nearN |r| ≤ 1)
    {u₁ u₂ : ℝ} (h1 : s ≤ u₁) (h12 : u₁ ≤ u₂) (h2 : u₂ ≤ t) :
    h1Energy r g y u₂ - h1Energy r g y u₁ + 3 / 4 * (∫ u in u₁..u₂, fastNorm 2 r g y u ^ 2) ≤
      ∫ u in u₁..u₂, (Cs * fastNorm 1 r g y u ^ (3 - σ) * fastNorm 2 r g y u ^ σ +
        nfConst φ caps r * fastNorm 2 r g y u + ffConst φ caps r +
        mConst φ caps r * fastNorm 1 r g y u ^ 2) := by
  have hr1 : 1 ≤ |r| := (shares_of_threshold hTp hφ hP.thr hK).1
  have hr : r ≠ 0 := abs_pos.mp (by linarith only [hr1])
  have hu₁0 : 0 ≤ u₁ := hP.hs.trans h1
  have ht₂ : ENNReal.ofReal u₂ < Ty := lt_lifespan h2 hP.ht
  obtain ⟨hI, hid⟩ := h1Energy_identity h hr hu₁0 h12 ht₂
  obtain ⟨hb, hG⟩ := h1_integrable h Cs (nfConst φ caps r) (ffConst φ caps r) (mConst φ caps r)
    hσ0 hσ3 hu₁0 h12 ht₂
  have hmono := intervalIntegral.integral_mono_on h12 hI ((hb.const_mul (1 / 4)).add hG)
    fun u hu => by
      have := h1RHS_budget h hTp hφ hres hP hK (⟨h1.trans hu.1, hu.2.trans h2⟩ : u ∈ Icc s t)
      linarith only [this]
  rw [intervalIntegral.integral_add (hb.const_mul (1 / 4)) hG,
    intervalIntegral.integral_const_mul] at hmono
  linarith only [hmono, hid]

/-! ### C. The budgets -/

/-- `L nf² ≤ 1` for `0 ≤ L ≤ Tp` and `0 ≤ nf ≤ 1/(1+Tp)`. -/
lemma nf_budget {L Tp nf : ℝ} (hL0 : 0 ≤ L) (hL : L ≤ Tp) (hnf0 : 0 ≤ nf)
    (hnf : nf ≤ 1 / (1 + Tp)) : L * nf ^ 2 ≤ 1 ^ 2 := by
  have hT : 0 < 1 + Tp := by linarith only [hL0, hL]
  have h1 : nf * (1 + Tp) ≤ 1 := (le_div_iff₀ hT).1 hnf
  have h2 : L * nf ≤ 1 := by nlinarith only [h1, hnf0, hL]
  have h3 : nf ≤ 1 := by nlinarith only [h1, hnf0, hL, hL0]
  calc L * nf ^ 2 = (L * nf) * nf := by ring
    _ ≤ 1 * 1 := mul_le_mul h2 h3 hnf0 zero_le_one
    _ = 1 ^ 2 := by norm_num

/-- `L ffConst ≤ 1` for `L ≤ 2`, once `2⁸ B/q ≤ 2⁻²⁰` and `0 ≤ h1 ≤ 1`. -/
lemma ff_budget {L B h1 q : ℝ} (hL : L ≤ 2) (hq0 : 0 < q) (hB : 0 ≤ B) (hh0 : 0 ≤ h1)
    (hh1 : h1 ≤ 1) (hop : 2 ^ 8 * B / q ≤ 1 / 2 ^ 20) : L * (2 ^ 8 * B * h1 ^ 2 / q) ≤ 1 ^ 2 := by
  have h2 : h1 ^ 2 ≤ 1 := by nlinarith only [hh0, hh1]
  have h3 : 2 ^ 8 * B * h1 ^ 2 / q ≤ 1 / 2 ^ 20 * 1 :=
    calc 2 ^ 8 * B * h1 ^ 2 / q = (2 ^ 8 * B / q) * h1 ^ 2 := by ring
      _ ≤ 1 / 2 ^ 20 * 1 := mul_le_mul hop h2 (sq_nonneg _) (by norm_num)
  have h4 := mul_le_mul hL h3 (by positivity) (by norm_num : (0 : ℝ) ≤ 2)
  linarith only [h4]

/-- `(2/ℓ₁) L m ≤ 1` for `0 ≤ L ≤ Tp`, `0 ≤ m ≤ 1/(4(1+Tp))`. -/
lemma m_budget {L Tp m : ℝ} (hL0 : 0 ≤ L) (hL : L ≤ Tp) (hm0 : 0 ≤ m)
    (hm : m ≤ 1 / (4 * (1 + Tp))) : 2 / ell1 * (L * m) ≤ 1 := by
  have hT : 0 < 4 * (1 + Tp) := by linarith only [hL0, hL]
  have h1 : m * (4 * (1 + Tp)) ≤ 1 := (le_div_iff₀ hT).1 hm
  have h2 : L * m ≤ 1 / 4 := by nlinarith only [h1, hm0, hL, hL0]
  have h3 : 2 / ell1 ≤ 4 := by
    rw [div_le_iff₀ ell1_pos]
    linarith only [half_le_ell1]
  have h4 : 0 ≤ L * m := mul_nonneg hL0 hm0
  calc 2 / ell1 * (L * m) ≤ 4 * (1 / 4) := mul_le_mul h3 h2 h4 (by norm_num)
    _ = 1 := by norm_num

/-! ### D. The interface -/

/-- **E5, general form**: `H1EnergyInterface` on pieces of length `≤ Tp ≤ 2` with threshold
`h1Threshold Tp`, for any `σ ∈ [0, 3]` with `ResH1 σ Cs`. -/
theorem h1EnergyInterface_of_threshold {σ Cs Tp : ℝ} (hσ0 : 0 ≤ σ) (hσ3 : σ ≤ 3) (hTp : 0 ≤ Tp)
    (hTp2 : Tp ≤ 2) (hres : ResH1 σ Cs) {μ φ : ℝ} (hφ : 0 ≤ φ) :
    H1EnergyInterface σ Cs μ φ Tp (h1Nbar μ φ) (h1Pi μ φ) h1K₁ (h1Threshold Tp μ φ) nearN := by
  intro r g y Ty caps s t h hP hK
  obtain ⟨hr1, -, -, -, -, -, -, -, -, sop, sm, -, sh1, snf⟩ :=
    shares_of_threshold hTp hφ hP.thr hK
  have hr0 : 0 < |r| := by linarith only [hr1]
  have hst := hP.hst
  have hL0 : 0 ≤ t - s := sub_nonneg.2 hst
  have hL : t - s ≤ Tp := hP.len
  have hh0 := h1Const_nonneg hφ caps r
  refine ⟨h1Energy r g y, fun _ => nfConst φ caps r, fun _ => ffConst φ caps r,
    fun _ => mConst φ caps r, fun u hu => h1Energy_coercive h hTp hφ hP hK hu,
    fun u₁ u₂ h1 h12 h2 => h1Energy_integrated h hσ0 hσ3 hTp hφ hres hP hK h1 h12 h2,
    fun _ _ => ⟨ffConst_nonneg hφ caps r, mConst_nonneg hφ caps r⟩,
    continuous_const.intervalIntegrable _ _, continuous_const.intervalIntegrable _ _,
    continuous_const.intervalIntegrable _ _, ?_, ?_, ?_⟩
  · rw [intervalIntegral.integral_const, smul_eq_mul]
    exact nf_budget hL0 hL (nfConst_nonneg hφ caps r) snf
  · rw [intervalIntegral.integral_const, smul_eq_mul]
    exact ff_budget (hL.trans hTp2) hr0 (cp_nonneg _) hh0 (h1Const_le_one sh1) sop
  · rw [intervalIntegral.integral_const, smul_eq_mul]
    exact m_budget hL0 hL (mConst_nonneg hφ caps r) sm

/-- **E5** (the consumable form, with `Tp = 2`): for every valid resonant constant `Cs`, the
`H¹` energy interface holds with `K₁ = h1K₁`, `q₁ = h1Threshold 2`, `N̄ = h1Nbar`, `π = h1Pi`,
none of which depends on `Cs`.  This is exactly the shape of the hypothesis `hE1` of
`quantitative_fixed_force_of_energy'`. -/
theorem h1Energy_of_threshold : ∀ Cs : ℝ, 0 ≤ Cs → ResH1 ((281 : ℝ) / 1000) Cs →
    ∀ μ φ : ℝ, 0 ≤ μ → 0 ≤ φ →
      H1EnergyInterface ((281 : ℝ) / 1000) Cs μ φ 2 (h1Nbar μ φ) (h1Pi μ φ) h1K₁
        (h1Threshold 2 μ φ) nearN :=
  fun _ _ hres _ _ _ hφ =>
    h1EnergyInterface_of_threshold (by norm_num) (by norm_num) (by norm_num) le_rfl hres hφ

/-! ### E. The degree of the threshold -/

/-- `DegLe Sc f a`: `0 ≤ f μ caps ≲ μ^a` uniformly on the class `Sc` of pairs `(μ, caps)`,
`μ ≥ 1` (the constant is hidden, which is all that `DegreeBelow` asks). -/
def DegLe (Sc : ℝ → Caps → Prop) (f : ℝ → Caps → ℝ) (a : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ μ caps, 1 ≤ μ → Sc μ caps → 0 ≤ f μ caps ∧ f μ caps ≤ C * μ ^ a

namespace DegLe

variable {Sc : ℝ → Caps → Prop} {f f' : ℝ → Caps → ℝ} {a b : ℝ}

lemma congr (h : DegLe Sc f a) (e : ∀ μ caps, f μ caps = f' μ caps) : DegLe Sc f' a := by
  simpa only [funext fun μ => funext fun caps => e μ caps] using h

lemma const {c : ℝ} (hc : 0 ≤ c) : DegLe Sc (fun _ _ => c) 0 :=
  ⟨c, hc, fun μ _ _ _ => ⟨hc, by rw [Real.rpow_zero, mul_one]⟩⟩

lemma mono (h : DegLe Sc f a) (hab : a ≤ b) : DegLe Sc f b := by
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun μ caps hμ hc => ⟨(hC μ caps hμ hc).1, (hC μ caps hμ hc).2.trans ?_⟩⟩
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hμ hab) hC0

lemma add (hf : DegLe Sc f a) (hg : DegLe Sc f' a) :
    DegLe Sc (fun μ caps => f μ caps + f' μ caps) a := by
  obtain ⟨C, hC0, hC⟩ := hf
  obtain ⟨D, hD0, hD⟩ := hg
  refine ⟨C + D, add_nonneg hC0 hD0, fun μ caps hμ hc => ?_⟩
  obtain ⟨h1, h2⟩ := hC μ caps hμ hc
  obtain ⟨h3, h4⟩ := hD μ caps hμ hc
  rw [add_mul]
  exact ⟨add_nonneg h1 h3, add_le_add h2 h4⟩

lemma mul (hf : DegLe Sc f a) (hg : DegLe Sc f' b) :
    DegLe Sc (fun μ caps => f μ caps * f' μ caps) (a + b) := by
  obtain ⟨C, hC0, hC⟩ := hf
  obtain ⟨D, hD0, hD⟩ := hg
  refine ⟨C * D, mul_nonneg hC0 hD0, fun μ caps hμ hc => ?_⟩
  obtain ⟨h1, h2⟩ := hC μ caps hμ hc
  obtain ⟨h3, h4⟩ := hD μ caps hμ hc
  have hμ0 : 0 < μ := by linarith only [hμ]
  refine ⟨mul_nonneg h1 h3, (mul_le_mul h2 h4 h3 (by positivity)).trans_eq ?_⟩
  rw [Real.rpow_add hμ0]
  ring

lemma sq (hf : DegLe Sc f a) : DegLe Sc (fun μ caps => f μ caps ^ 2) (a + a) := by
  simpa only [pow_two] using hf.mul hf

lemma rpow (hf : DegLe Sc f a) {p : ℝ} (hp : 0 ≤ p) :
    DegLe Sc (fun μ caps => f μ caps ^ p) (a * p) := by
  obtain ⟨C, hC0, hC⟩ := hf
  refine ⟨C ^ p, Real.rpow_nonneg hC0 p, fun μ caps hμ hc => ?_⟩
  obtain ⟨h1, h2⟩ := hC μ caps hμ hc
  have hμ0 : 0 < μ := by linarith only [hμ]
  refine ⟨Real.rpow_nonneg h1 p, (Real.rpow_le_rpow h1 h2 hp).trans_eq ?_⟩
  rw [Real.mul_rpow hC0 (Real.rpow_nonneg hμ0.le a), ← Real.rpow_mul hμ0.le]

lemma sqrt (hf : DegLe Sc f a) : DegLe Sc (fun μ caps => Real.sqrt (f μ caps)) (a * (1 / 2)) := by
  have h := hf.rpow (p := 1 / 2) (by norm_num)
  simpa only [Real.sqrt_eq_rpow] using h

/-- An atom: the nonnegative part of a cap bounded by `K μ^a`. -/
lemma atom {c : Caps → ℝ} {K : ℝ} (hK : 0 ≤ K) (h : ∀ μ caps, 1 ≤ μ → Sc μ caps → c caps ≤ K * μ ^ a) :
    DegLe Sc (fun _ caps => cp (c caps)) a :=
  ⟨K, hK, fun μ caps hμ hc =>
    ⟨cp_nonneg _, cp_le (mul_nonneg hK (Real.rpow_nonneg (by linarith only [hμ]) _))
      (h μ caps hμ hc)⟩⟩

end DegLe

/-- **R1 duty of the `H¹` roles** (Table quant-fixed): `h1Threshold 2` has fixed-force degree
`< d = 9876/719` at `σ = 281/1000`, for slow exponents `eA ≤ 2`, `eB ≤ 3`, `eJ ≤ 4`, `eW ≤ 5/2`
(the Fourier-side `slowExpF = ⟨2, 3, 4, 5/2⟩`) and polylog exponents `δ ≤ 1/8`.  The proof shows
every term `≲ μ^{27/2}`.  The worst terms are the profile terms: role 13, `100 v/29`, and the
mixed near partner, `(100/49)(eW + δ + v)`; see `t12_h1_scaffold.md` §5. -/
theorem h1_degree (e : SlowExp) (heA : e.eA ≤ 2) (heB : e.eB ≤ 3) (_heJ : e.eJ ≤ 4)
    (heW : e.eW ≤ 5 / 2) :
    DegreeBelow ((281 : ℝ) / 1000) ((9876 : ℝ) / 719) e (fun μ φ => h1Threshold 2 μ φ) := by
  intro φ hφ
  refine ⟨1 / 8, by norm_num, fun δ K hδ hδ' hK => ?_⟩
  have hβ : betaOf ((281 : ℝ) / 1000) = 1719 / 719 := by unfold betaOf; norm_num
  have hv : vOf ((281 : ℝ) / 1000) = 2719 / 719 := by unfold vOf; rw [hβ]; norm_num
  have hK0 : 0 ≤ K := by linarith only [hK]
  set Sc : ℝ → Caps → Prop := fun μ caps => CapsScaled ((281 : ℝ) / 1000) δ K μ e caps with hSc
  have hpow : ∀ {μ a b : ℝ}, 1 ≤ μ → a ≤ b → K * μ ^ a ≤ K * μ ^ b := fun hμ hab =>
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hμ hab) hK0
  -- the atoms
  have hP : DegLe Sc (fun _ caps => cp caps.PF) (12 / 5) := DegLe.atom hK0 fun μ caps hμ hc =>
    hc.1.2.trans (hpow hμ (by rw [hβ]; norm_num))
  have hY : DegLe Sc (fun _ caps => cp caps.yF) (19 / 5) := DegLe.atom hK0 fun μ caps hμ hc =>
    hc.2.1.2.trans (hpow hμ (by rw [hv]; norm_num))
  have hA : DegLe Sc (fun _ caps => cp caps.AS) (17 / 8) := DegLe.atom hK0 fun μ caps hμ hc =>
    hc.2.2.2.1.trans (hpow hμ (by linarith only [heA, hδ']))
  have hB : DegLe Sc (fun _ caps => cp caps.BS) (25 / 8) := DegLe.atom hK0 fun μ caps hμ hc =>
    hc.2.2.2.2.1.trans (hpow hμ (by linarith only [heB, hδ']))
  have hW : DegLe Sc (fun _ caps => cp caps.WS) (21 / 8) := DegLe.atom hK0 fun μ caps hμ hc =>
    hc.2.2.2.2.2.2.1.trans (hpow hμ (by linarith only [heW, hδ']))
  have hc4 := c4_pos
  have hcI := cI_pos
  have hcQ := cQ1_pos
  have hpC := profC_pos
  have hC0 := nearC₀_pos
  -- a constant multiple keeps the degree
  have hconst : ∀ {f : ℝ → Caps → ℝ} {a c : ℝ}, 0 ≤ c → DegLe Sc f a →
      DegLe Sc (fun μ caps => c * f μ caps) a := fun hc hf => by
    simpa only [zero_add] using (DegLe.const hc).mul hf
  have hone : ∀ {a : ℝ}, 0 ≤ a → DegLe Sc (fun _ _ => (1 : ℝ)) a := fun ha =>
    (DegLe.const zero_le_one).mono ha
  -- `mixNear`, `ffCoef`, `srcAll`, `hSrc`, `mCoef`
  have hBW : DegLe Sc (fun _ caps => cp caps.BS * cp caps.WS + cI * cp caps.BS ^ 2)
      (13 / 2) := ((hB.mul hW).mono (by norm_num)).add
      ((hconst hcI.le hB.sq).mono (by norm_num))
  have hmix : DegLe Sc (fun _ caps => mixNear caps) (13 / 2) :=
    ((hW.mul hY).mono (by norm_num)).add
      (((hconst hcI.le hB).mul (hP.mul hY).sqrt).mono (by norm_num))
  have hff : DegLe Sc (fun _ caps => ffCoef caps) (7 : ℝ) :=
    ((((hconst hcQ.le hP.sqrt).mul (hY.rpow (p := 3 / 2) (by norm_num)))).mono (by norm_num))
  have hsrc : DegLe Sc (fun _ caps => srcAll caps) (7 : ℝ) :=
    (hff.add ((hconst (by norm_num) hmix).mono (by norm_num))).add (hone (by norm_num))
  have hS1 : DegLe Sc (fun _ caps => cp caps.WS + c4 * cp caps.yF + c4) (19 / 5) :=
    ((hW.mono (by norm_num)).add (hconst hc4.le hY)).add
      ((DegLe.const hc4.le).mono (by norm_num))
  have hS2 : DegLe Sc (fun _ caps => cp caps.BS + cp caps.yF + 1) (19 / 5) :=
    ((hB.mono (by norm_num)).add hY).add (hone (by norm_num))
  have hS : DegLe Sc (fun _ caps => hSrc φ caps) (8 : ℝ) := by
    have h1 := (hconst (c := 8) (by norm_num) (hS1.mul hS2)).mono (b := 8) (by norm_num)
    have h2 : DegLe Sc (fun _ _ => φ) (8 : ℝ) := (DegLe.const hφ).mono (by norm_num)
    refine (h1.add h2).congr fun _ caps => ?_
    unfold hSrc
    ring
  have hm : DegLe Sc (fun _ caps => mCoef φ caps) (8 : ℝ) :=
    ((hconst (by norm_num) hS).add ((hconst (by norm_num) hBW).mono (by norm_num))).add
      ((hconst (by norm_num) hB).mono (by norm_num))
  have hC' : 0 ≤ cStat ∧ 0 ≤ cHeat := by
    unfold cStat cHeat
    constructor <;> positivity
  -- the role terms
  have r8 : DegLe Sc (fun _ _ => role8) (27 / 2) := hone (by norm_num)
  have r9 : DegLe Sc (fun _ caps => role9 caps) (27 / 2) :=
    (hconst (by norm_num) hsrc).mono (by norm_num)
  have r13 : DegLe Sc (fun _ caps => role13 caps) (27 / 2) :=
    ((hconst (c := 2 ^ 8 * cStat * profC) (mul_nonneg (mul_nonneg (by norm_num) hC'.1) hpC.le)
      hY).rpow (p := 100 / 29) (by norm_num)).mono (by norm_num)
  have r14 : DegLe Sc (fun _ caps => role14 caps) (27 / 2) :=
    ((hconst (c := 2 ^ 6 * cHeat * profC) (mul_nonneg (mul_nonneg (by norm_num) hC'.2) hpC.le)
      hY).rpow (p := 100 / 29) (by norm_num)).mono (by norm_num)
  have r15 : DegLe Sc (fun _ caps => role15mix caps) (27 / 2) :=
    ((hconst (c := 2 ^ 9 * nearC₀ * profC) (mul_nonneg (mul_nonneg (by norm_num) hC0.le) hpC.le)
      hmix).rpow (p := 100 / 49) (by norm_num)).mono (by norm_num)
  have r28o : DegLe Sc (fun _ caps => role28op caps) (27 / 2) :=
    (hconst (by norm_num) hB).mono (by norm_num)
  have r28Q : DegLe Sc (fun _ caps => role28Q caps) (27 / 2) :=
    ((hconst (c := 2 ^ 15 * cQ1) (mul_nonneg (by norm_num) hcQ.le) hB).mul hP).mono (by norm_num)
  have r28SF : DegLe Sc (fun _ caps => role28SF caps) (27 / 2) :=
    (hconst (by norm_num) hBW).mono (by norm_num)
  have r28s : DegLe Sc (fun _ caps => role28src φ caps) (27 / 2) :=
    (hconst (by norm_num) hS).mono (by norm_num)
  have r28t : DegLe Sc (fun _ caps => role28timed 2 φ caps) (27 / 2) :=
    (hconst (by norm_num) hm).mono (by norm_num)
  have rF : DegLe Sc (fun _ caps => roleForce 2 φ caps) (27 / 2) :=
    (hconst (c := 2 ^ 22 * (1 + nearC₀) * (1 + c4) * (1 + φ) * (1 + 2)) (by positivity)
      ((((((hB.mono (by norm_num)).add hY).add (hW.mono (by norm_num))).add
        (hA.mono (by norm_num))).add (hP.mono (by norm_num))).add (hone (by norm_num)))).mono
      (by norm_num)
  have hz : DegLe Sc (fun μ _ => 0 * μ) (27 / 2) :=
    ⟨0, le_rfl, fun μ _ _ _ => by simp⟩
  obtain ⟨C, -, hC⟩ : DegLe Sc (fun μ caps => h1Threshold 2 μ φ caps) (27 / 2) :=
    ((((((((((r8.add r9).add r13).add r14).add r15).add r28o).add r28Q).add r28SF).add
      r28s).add r28t).add rF).add hz
  exact ⟨C, 27 / 2, by norm_num, fun μ hμ caps hc => (hC μ caps hμ hc).2⟩

end OVNS.Quant

end
