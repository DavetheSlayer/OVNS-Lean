import OddViscousNS.Flux
import OddViscousNS.LocalTheory

/-! # Reference system: the sector equations

`w' = -A w - Q_res(w,w) + Π_S g` splits into fast, horizontal slow and vertical slow parts
(`Lemma fg:lem:split`).  We record each as a `HeatPair` so the master energy identity applies. -/

open MeasureTheory Set Filter intervalIntegral
open scoped ENNReal Topology
noncomputable section
namespace OVNS

variable {g : Field} {T : ℝ≥0∞} {w : ℝ → Field}

/-- `P` acts on each mode through the contraction `p k`. -/
private structure ModeProj (P : Field → Field) (p : Mode → V3 →L[ℂ] V3) : Prop where
  apply : ∀ u k, P u k = p k (u k)
  le : ∀ k v, ‖p k v‖ ≤ ‖v‖

/-- Keeping the first two components, as a continuous linear map. -/
private def horizL : V3 →L[ℂ] V3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 ![v 0, v 1, 0]
      map_add' := fun u v => by
        ext i
        fin_cases i <;> simp
      map_smul' := fun c v => by
        ext i
        fin_cases i <;> simp }

/-- Keeping the third component, as a continuous linear map. -/
private def vertL : V3 →L[ℂ] V3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 ![0, 0, v 2]
      map_add' := fun u v => by
        ext i
        fin_cases i <;> simp
      map_smul' := fun c v => by
        ext i
        fin_cases i <;> simp }

/-- `horizL` is a contraction. -/
private lemma norm_horizL_le (v : V3) : ‖horizL v‖ ≤ ‖v‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  simp only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp only [horizL, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  nlinarith [sq_nonneg ‖v 2‖]

/-- `vertL` is a contraction. -/
private lemma norm_vertL_le (v : V3) : ‖vertL v‖ ≤ ‖v‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  simp only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp only [vertL, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]
  nlinarith [sq_nonneg ‖v 0‖, sq_nonneg ‖v 1‖]

/-- The identity is a mode-wise projection. -/
private lemma modeProj_id :
    ModeProj id (fun _ => ContinuousLinearMap.id ℂ V3) :=
  ⟨fun _ _ => rfl, fun _ _ => le_rfl⟩

/-- `Π_F` is a mode-wise projection. -/
private lemma modeProj_PiF :
    ModeProj PiF (fun k => if k 2 = 0 then 0 else ContinuousLinearMap.id ℂ V3) := by
  refine ⟨fun u k => ?_, fun k v => ?_⟩ <;> by_cases h : k 2 = 0 <;> simp [PiF, h]

/-- `Π_H` is a mode-wise projection. -/
private lemma modeProj_PiH : ModeProj PiH (fun k => if k 2 = 0 then horizL else 0) := by
  refine ⟨fun u k => ?_, fun k v => ?_⟩ <;> by_cases h : k 2 = 0
  · simp [PiH, h, horizL]
  · simp [PiH, h]
  · simpa [h] using norm_horizL_le v
  · simp [h]

/-- `Π_V` is a mode-wise projection. -/
private lemma modeProj_PiV : ModeProj PiV (fun k => if k 2 = 0 then vertL else 0) := by
  refine ⟨fun u k => ?_, fun k v => ?_⟩ <;> by_cases h : k 2 = 0
  · simp [PiV, h, vertL]
  · simp [PiV, h]
  · simpa [h] using norm_vertL_le v
  · simp [h]

/-- Mode-wise projections respect differences. -/
private lemma ModeProj.sub {P : Field → Field} {p : Mode → V3 →L[ℂ] V3} (hP : ModeProj P p)
    (u v : Field) : P (u - v) = P u - P v := by
  ext1 k
  simp [hP.apply]

/-- Mode-wise projections decrease each weighted term. -/
private lemma ModeProj.term_le {P : Field → Field} {p : Mode → V3 →L[ℂ] V3}
    (hP : ModeProj P p) (s : ℝ) (u : Field) (k : Mode) :
    sobWeight s k * ‖P u k‖ ^ 2 ≤ sobWeight s k * ‖u k‖ ^ 2 := by
  rw [hP.apply]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hP.le k _) 2)
    (sobWeight_nonneg s k)

/-- Mode-wise projections preserve `H^s`. -/
private lemma ModeProj.inH {P : Field → Field} {p : Mode → V3 →L[ℂ] V3} (hP : ModeProj P p)
    {s : ℝ} {u : Field} (hu : InH s u) : InH s (P u) :=
  Summable.of_nonneg_of_le
    (fun k => mul_nonneg (sobWeight_nonneg s k) (sq_nonneg _)) (hP.term_le s u) hu

/-- Mode-wise projections decrease the `H^s` norm. -/
private lemma ModeProj.hnorm_le {P : Field → Field} {p : Mode → V3 →L[ℂ] V3}
    (hP : ModeProj P p) {s : ℝ} {u : Field} (hu : InH s u) : hnorm s (P u) ≤ hnorm s u :=
  Real.sqrt_le_sqrt <| (hP.inH hu).tsum_le_tsum (hP.term_le s u) hu

/-- Mode-wise projections decrease the extended `H^s` norm. -/
private lemma ModeProj.hsE_le {P : Field → Field} {p : Mode → V3 →L[ℂ] V3}
    (hP : ModeProj P p) (s : ℝ) (u : Field) : hsE s (P u) ≤ hsE s u :=
  tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal (hP.term_le s u k)

/-- A mode-wise projection of a `HeatPair` is a `HeatPair`. -/
private lemma HeatPair.proj {P : Field → Field} {p : Mode → V3 →L[ℂ] V3} (hP : ModeProj P p)
    {σ b : ℝ} {c F F' : ℝ → Field} (h : HeatPair σ 0 b c F)
    (hF : ∀ t ∈ Icc 0 b, P (F t) = F' t) : HeatPair σ 0 b (fun t => P (c t)) F' := by
  refine ⟨fun t ht => hP.inH (h.inH t ht), fun k t ht => ?_, fun k => ?_, ?_⟩
  · have hd : HasDerivWithinAt (fun s => p k (c s k))
        (p k ((-(absSq k : ℝ) : ℂ) • c t k + F t k)) (Icc 0 b) t :=
      ((p k).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t (h.mode k t ht)
    rw [map_add, map_smul, ← hP.apply, ← hP.apply, hF t ht] at hd
    simpa only [hP.apply] using hd
  · refine (ContinuousOn.congr ?_ fun t ht => congrFun (hF t ht).symm k)
    simp only [hP.apply]
    exact (p k).continuous.comp_continuousOn (h.force_cont k)
  · refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Icc fun t ht => ?_) h.force_l2
    rw [← hF t ht]
    exact hP.hsE_le _ _

/-- Time-continuity of a mode-wise projection in `H^σ`, `σ ≤ 2`. -/
private lemma IsHeatSol.continuousOn_proj {P : Field → Field} {p : Mode → V3 →L[ℂ] V3}
    (hP : ModeProj P p) {N : ℝ → Field → Field → Field} {G : ℝ → Field} {y : ℝ → Field}
    (hy : IsHeatSol N G T y) {σ b : ℝ} (hσ : σ ≤ 2) (hbT : ENNReal.ofReal b < T) :
    ContinuousOn (fun t => hnorm σ (P (y t))) (Icc 0 b) := by
  have hlt : ∀ t ∈ Icc 0 b, ENNReal.ofReal t < T := fun t ht =>
    (ENNReal.ofReal_le_ofReal ht.2).trans_lt hbT
  have hi : ∀ t ∈ Icc 0 b, InH 2 (y t) := fun t ht => (hy.adm t ht.1 (hlt t ht)).inH
  intro t₀ ht₀
  have hc : Tendsto (fun t => hnorm 2 (y t - y t₀)) (𝓝[Icc 0 b] t₀) (𝓝 0) :=
    (hy.cont t₀ ht₀.1 (hlt t₀ ht₀)).mono_left (nhdsWithin_mono t₀ Icc_subset_Ici_self)
  rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hc
  filter_upwards [self_mem_nhdsWithin] with t ht
  have it := hP.inH ((hi t ht).mono hσ)
  have it₀ := hP.inH ((hi t₀ ht₀).mono hσ)
  have hd : hnorm σ (P (y t) - P (y t₀)) ≤ hnorm 2 (y t - y t₀) := by
    rw [← hP.sub]
    exact (hP.hnorm_le (((hi t ht).sub (hi t₀ ht₀)).mono hσ)).trans
      (hnorm_mono hσ ((hi t ht).sub (hi t₀ ht₀)))
  have h1 : hnorm σ (P (y t)) ≤ hnorm σ (P (y t) - P (y t₀)) + hnorm σ (P (y t₀)) := by
    simpa using hnorm_add_le (it.sub it₀) it₀
  have h2 : hnorm σ (P (y t₀)) ≤ hnorm σ (P (y t₀) - P (y t)) + hnorm σ (P (y t)) := by
    simpa using hnorm_add_le (it₀.sub it) it
  rw [hnorm_sub_comm (f := P (y t₀)) (g := P (y t))] at h2
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

/-- `Π_H` factors through `Π_S`. -/
private lemma PiH_PiS (u : Field) : PiH (PiS u) = PiH u := by
  ext1 k
  by_cases h : k 2 = 0 <;> simp [PiH, PiS, h]

/-- `Π_V` factors through `Π_S`. -/
private lemma PiV_PiS (u : Field) : PiV (PiS u) = PiV u := by
  ext1 k
  by_cases h : k 2 = 0 <;> simp [PiV, PiS, h]

/-- A reference solution is admissible at each time of `[0,b]`. -/
private lemma adm_of_mem (hw : RefSol g T w) {t b : ℝ} (ht : t ∈ Icc 0 b)
    (hbT : ENNReal.ofReal b < T) : Adm 2 (w t) :=
  hw.adm t ht.1 ((ENNReal.ofReal_le_ofReal ht.2).trans_lt hbT)

/-- The fast part solves a heat equation with force `-Π_F Q_res(w,w)`. -/
theorem RefSol.heatPair_fast (hg : Adm 2 g) (hw : RefSol g T w) {σ b : ℝ} (hσ : σ = 0 ∨ σ = 1)
    (hb : 0 ≤ b) (hbT : ENNReal.ofReal b < T) :
    HeatPair σ 0 b (fun t => PiF (w t)) (fun t => -PiF (Qres (w t) (w t))) := by
  refine (hw.heatPair_low majorized_res (goodForce_PiS hg) hσ hb hbT).proj modeProj_PiF
    fun t _ => ?_
  ext1 k
  by_cases h : k 2 = 0 <;> simp [PiF, PiS, h]

/-- The horizontal slow part solves a heat equation. -/
theorem RefSol.heatPair_horiz (hg : Adm 2 g) (hw : RefSol g T w) {σ b : ℝ} (hσ : σ = 0 ∨ σ = 1)
    (hb : 0 ≤ b) (hbT : ENNReal.ofReal b < T) :
    HeatPair σ 0 b (fun t => PiH (w t))
      (fun t => PiH g - PiH (Bsym (PiS (w t)) (PiS (w t)))) := by
  refine (hw.heatPair_low majorized_res (goodForce_PiS hg) hσ hb hbT).proj modeProj_PiH
    fun t ht => ?_
  rw [← PiS_Qres (adm_of_mem hw ht hbT), modeProj_PiH.sub, PiH_PiS, PiH_PiS]

/-- The vertical slow part solves a heat equation. -/
theorem RefSol.heatPair_vert (hg : Adm 2 g) (hw : RefSol g T w) {σ b : ℝ} (hσ : σ = 0 ∨ σ = 1)
    (hb : 0 ≤ b) (hbT : ENNReal.ofReal b < T) :
    HeatPair σ 0 b (fun t => PiV (w t))
      (fun t => PiV g - PiV (Bsym (PiS (w t)) (PiS (w t)))) := by
  refine (hw.heatPair_low majorized_res (goodForce_PiS hg) hσ hb hbT).proj modeProj_PiV
    fun t ht => ?_
  rw [← PiS_Qres (adm_of_mem hw ht hbT), modeProj_PiV.sub, PiV_PiS, PiV_PiS]

/-- Time translation of a reference solution (the equation is autonomous). -/
theorem RefSol.shift (hw : RefSol g T w) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (hlt : ENNReal.ofReal t₀ < T) :
    RefSol g (T - ENNReal.ofReal t₀) (fun t => w (t + t₀)) :=
  IsHeatSol.shift hw ht₀ hlt

/-- All four norms of `w` at level `σ` are continuous in time on the lifespan. -/
theorem RefSol.continuousOn_hnorm (_hg : Adm 2 g) (hw : RefSol g T w) {σ b : ℝ}
    (hσ : σ = 0 ∨ σ = 1 ∨ σ = 2) (_hb : 0 ≤ b) (hbT : ENNReal.ofReal b < T) :
    ContinuousOn (fun t => hnorm σ (w t)) (Icc 0 b) ∧
    ContinuousOn (fun t => hnorm σ (PiF (w t))) (Icc 0 b) ∧
    ContinuousOn (fun t => hnorm σ (PiH (w t))) (Icc 0 b) ∧
    ContinuousOn (fun t => hnorm σ (PiV (w t))) (Icc 0 b) := by
  have h2 : σ ≤ 2 := by
    rcases hσ with rfl | rfl | rfl <;> norm_num
  exact ⟨IsHeatSol.continuousOn_proj modeProj_id hw h2 hbT,
    IsHeatSol.continuousOn_proj modeProj_PiF hw h2 hbT,
    IsHeatSol.continuousOn_proj modeProj_PiH hw h2 hbT,
    IsHeatSol.continuousOn_proj modeProj_PiV hw h2 hbT⟩

/-- `w` at time `t` splits orthogonally into the three sectors. -/
theorem hnorm_sq_three {s : ℝ} {u : Field} (hu : InH s u) :
    hnorm s u ^ 2 = hnorm s (PiH u) ^ 2 + hnorm s (PiV u) ^ 2 + hnorm s (PiF u) ^ 2 := by
  rw [hnorm_sq_split hu, hnorm_sq_split_slow hu]

end OVNS
