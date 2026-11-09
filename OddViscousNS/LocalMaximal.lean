import OddViscousNS.LocalExist
import OddViscousNS.LocalUniq

/-! # The maximal solution and blow-up alternative -/

open scoped ENNReal Topology
open MeasureTheory Set Filter
noncomputable section
namespace OVNS

variable {N : ℝ → Field → Field → Field} {G : ℝ → Field} {Γ : ℝ}

/-- The solution property at a single time. -/
private structure SolAt (N : ℝ → Field → Field → Field) (G : ℝ → Field) (y : ℝ → Field)
    (t : ℝ) : Prop where
  /-- Admissibility at time `t`. -/
  adm : Adm 2 (y t)
  /-- `H²` continuity at time `t`. -/
  cont : Tendsto (fun s => hnorm 2 (y s - y t)) (𝓝[Ici 0] t) (𝓝 0)
  /-- The mode equations at time `t`. -/
  mode : ∀ k, HasDerivWithinAt (fun s => y s k)
    ((-(absSq k : ℝ) : ℂ) • y t k - N t (y t) (y t) k + G t k) (Ici 0) t

/-- A solution has the solution property at each time of its lifespan. -/
private lemma IsHeatSol.solAt {T : ℝ≥0∞} {y : ℝ → Field} (hy : IsHeatSol N G T y) {t : ℝ}
    (ht : 0 ≤ t) (h : ENNReal.ofReal t < T) : SolAt N G y t :=
  ⟨hy.adm t ht h, hy.cont t ht h, fun k => hy.mode k t ht h⟩

/-- The solution property at each time of the lifespan gives a solution. -/
private lemma IsHeatSol.of_solAt {T : ℝ≥0∞} {y : ℝ → Field}
    (h : ∀ t, 0 ≤ t → ENNReal.ofReal t < T → SolAt N G y t) : IsHeatSol N G T y :=
  ⟨fun t ht h' => (h t ht h').adm, fun t ht h' => (h t ht h').cont,
    fun k t ht h' => (h t ht h').mode k⟩

/-- The solution property at a time only depends on the germ of the curve there. -/
private lemma SolAt.congr {y z : ℝ → Field} {t : ℝ} (hz : SolAt N G z t) (ht : 0 ≤ t)
    (h : y =ᶠ[𝓝[Ici 0] t] z) : SolAt N G y t := by
  have e : y t = z t := h.eq_of_nhdsWithin ht
  refine ⟨e ▸ hz.adm, ?_, fun k => ?_⟩
  · rw [e]
    refine hz.cont.congr' ?_
    filter_upwards [h] with s hs
    rw [hs]
  · rw [e]
    exact (hz.mode k).congr_of_eventuallyEq (h.mono fun s hs => congrFun hs k) (congrFun e k)

/-- Translating a solution of the shifted system back, at times where the shift is interior. -/
private lemma SolAt.unshift {z : ℝ → Field} {t t₁ : ℝ}
    (hz : SolAt (fun s => N (s + t₁)) (fun s => G (s + t₁)) z t) (ht : 0 < t) :
    SolAt N G (fun s => z (s - t₁)) (t + t₁) := by
  have e : t + t₁ - t₁ = t := add_sub_cancel_right t t₁
  have hm : Tendsto (fun s => s - t₁) (𝓝 (t + t₁)) (𝓝[Ici 0] t) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h : ContinuousAt (fun s : ℝ => s - t₁) (t + t₁) := by fun_prop
      simpa only [ContinuousAt, e] using h
    · filter_upwards [lt_mem_nhds (show t₁ < t + t₁ by linarith)] with s hs
      exact (sub_pos.2 hs).le
  refine ⟨?_, ?_, fun k => ?_⟩
  · simpa only [e] using hz.adm
  · simp only [e]
    exact (hz.cont.comp hm).mono_left nhdsWithin_le_nhds
  · have hd : HasDerivAt (fun s => z s k)
        ((-(absSq k : ℝ) : ℂ) • z t k - N (t + t₁) (z t) (z t) k + G (t + t₁) k)
        (t + t₁ - t₁) := by
      rw [e]
      exact (hz.mode k).hasDerivAt (Ici_mem_nhds ht)
    have hs : HasDerivAt (fun s : ℝ => s - t₁) 1 (t + t₁) := (hasDerivAt_id _).sub_const t₁
    have h' := HasDerivAt.scomp (h := fun s : ℝ => s - t₁) (t + t₁) hd hs
    rw [one_smul] at h'
    simp only [e]
    exact h'.hasDerivWithinAt

/-- Restriction of a solution to a shorter lifespan. -/
private lemma IsHeatSol.mono {T T' : ℝ≥0∞} {y : ℝ → Field} (hy : IsHeatSol N G T y)
    (h : T' ≤ T) : IsHeatSol N G T' y :=
  IsHeatSol.of_solAt fun _ ht h' => hy.solAt ht (h'.trans_le h)

/-- Two solutions with the same data agree on the common lifespan. -/
private lemma IsHeatSol.eq_of_lt (hN : Majorized N) (hG : GoodForce G Γ) {T T' : ℝ≥0∞}
    {y z : ℝ → Field} (hy : IsHeatSol N G T y) (hz : IsHeatSol N G T' z) (h0 : y 0 = z 0) {t : ℝ}
    (ht : 0 ≤ t) (h : ENNReal.ofReal t < T) (h' : ENNReal.ofReal t < T') : y t = z t :=
  heatSol_unique hN hG (hy.mono (min_le_left _ _)) (hz.mono (min_le_right _ _)) h0 t ht
    (lt_min h h')

/-- Being inside the lifespan is an open condition. -/
private lemma eventually_ofReal_lt {T : ℝ≥0∞} {t : ℝ} (h : ENNReal.ofReal t < T) :
    ∀ᶠ s in 𝓝 t, ENNReal.ofReal s < T :=
  (ENNReal.continuous_ofReal.tendsto t).eventually_lt_const h

/-- There is a longest solution, obtained by gluing all solutions. -/
private lemma exists_longest (hN : Majorized N) (hG : GoodForce G Γ) {y₀ : Field}
    (hy₀ : Adm 2 y₀) : ∃ (T : ℝ≥0∞) (y : ℝ → Field), 0 < T ∧ IsHeatSol N G T y ∧ y 0 = y₀ ∧
      ∀ (T' : ℝ≥0∞) (y' : ℝ → Field), IsHeatSol N G T' y' → y' 0 = y₀ → T' ≤ T := by
  classical
  let S : Set ℝ≥0∞ := {T | ∃ y, IsHeatSol N G T y ∧ y 0 = y₀}
  choose! sol hsol hsol0 using (show ∀ T ∈ S, ∃ y, IsHeatSol N G T y ∧ y 0 = y₀ from fun _ h => h)
  let y : ℝ → Field := fun t =>
    if h : ∃ T ∈ S, ENNReal.ofReal t < T then sol h.choose t else 0
  have hyT : ∀ T ∈ S, ∀ t, 0 ≤ t → ENNReal.ofReal t < T → y t = sol T t := by
    intro T hT t ht h
    have h' : ∃ T ∈ S, ENNReal.ofReal t < T := ⟨T, hT, h⟩
    obtain ⟨hm, hl⟩ := h'.choose_spec
    simp only [y, dite_eq_left h']
    exact (hsol _ hm).eq_of_lt hN hG (hsol T hT) ((hsol0 _ hm).trans (hsol0 T hT).symm) ht hl h
  obtain ⟨τ, hτ, hex⟩ := local_existence (hnorm 2 y₀) Γ
  obtain ⟨z, hz, hz0⟩ := hex N G y₀ hN hG hy₀ le_rfl
  have hτS : ENNReal.ofReal τ ∈ S := ⟨z, hz, hz0⟩
  have hpos : 0 < ENNReal.ofReal τ := ENNReal.ofReal_pos.2 hτ
  refine ⟨sSup S, y, hpos.trans_le (le_sSup hτS), ?_, ?_, fun T' y' h h0 => le_sSup ⟨y', h, h0⟩⟩
  · refine IsHeatSol.of_solAt fun t ht h => ?_
    obtain ⟨T, hT, hl⟩ := lt_sSup_iff.1 h
    refine ((hsol T hT).solAt ht hl).congr ht ?_
    filter_upwards [nhdsWithin_le_nhds (eventually_ofReal_lt hl), self_mem_nhdsWithin] with s hs h0
    exact hyT T hT s h0 hs
  · rw [hyT _ hτS 0 le_rfl (by simpa using hτ), hsol0 _ hτS]

/-- A solution bounded in `H²` on a finite lifespan can be continued past its end. -/
private lemma exists_extension (hN : Majorized N) (hG : GoodForce G Γ) {b C : ℝ} (hb : 0 < b)
    {y : ℝ → Field} (hy : IsHeatSol N G (ENNReal.ofReal b) y)
    (hC : ∀ t, 0 ≤ t → ENNReal.ofReal t < ENNReal.ofReal b → hnorm 2 (y t) ≤ C) :
    ∃ (T : ℝ≥0∞) (w : ℝ → Field), ENNReal.ofReal b < T ∧ IsHeatSol N G T w ∧ w 0 = y 0 := by
  classical
  obtain ⟨τ, hτ, hex⟩ := local_existence C Γ
  set t₁ : ℝ := max 0 (b - τ / 2) with ht₁
  have h0t : 0 ≤ t₁ := le_max_left _ _
  have hlb : t₁ < b := max_lt hb (by linarith)
  have hub : b < t₁ + τ := by linarith [le_max_right 0 (b - τ / 2)]
  have ht₁b : ENNReal.ofReal t₁ < ENNReal.ofReal b := (ENNReal.ofReal_lt_ofReal_iff hb).2 hlb
  obtain ⟨z, hz, hz0⟩ := hex (fun t => N (t + t₁)) (fun t => G (t + t₁)) (y t₁) (hN.shift t₁)
    (hG.shift t₁) (hy.adm t₁ h0t ht₁b) (hC t₁ h0t ht₁b)
  have hshift := hy.shift h0t ht₁b
  rw [← ENNReal.ofReal_sub b h0t] at hshift
  have hyz : ∀ t, t₁ ≤ t → t < b → y t = z (t - t₁) := by
    intro t h1 h2
    have h3 := hshift.eq_of_lt (hN.shift t₁) (hG.shift t₁) hz (by simp [hz0]) (sub_nonneg.2 h1)
      ((ENNReal.ofReal_lt_ofReal_iff (sub_pos.2 hlb)).2 (sub_lt_sub_right h2 t₁))
      ((ENNReal.ofReal_lt_ofReal_iff hτ).2 (by linarith))
    simpa using h3
  let w : ℝ → Field := fun t => if t < t₁ then y t else z (t - t₁)
  have hwy : ∀ t, t < b → w t = y t := by
    intro t ht
    by_cases h : t < t₁
    · simp only [w, ite_eq_left h]
    · simp only [w, ite_eq_right h]
      exact (hyz t (not_lt.1 h) ht).symm
  have hsol : IsHeatSol N G (ENNReal.ofReal (t₁ + τ)) w := by
    refine IsHeatSol.of_solAt fun t ht h => ?_
    have htτ : t < t₁ + τ := (ENNReal.ofReal_lt_ofReal_iff (by linarith)).1 h
    by_cases htb : t < b
    · refine (hy.solAt ht ((ENNReal.ofReal_lt_ofReal_iff hb).2 htb)).congr ht ?_
      filter_upwards [nhdsWithin_le_nhds (gt_mem_nhds htb)] with s hs
      exact hwy s hs
    · have hpos : 0 < t - t₁ := by linarith
      have hzs := (hz.solAt hpos.le ((ENNReal.ofReal_lt_ofReal_iff hτ).2
        (by linarith))).unshift hpos
      rw [sub_add_cancel] at hzs
      refine hzs.congr ht ?_
      filter_upwards [nhdsWithin_le_nhds (lt_mem_nhds (show t₁ < t by linarith))] with s hs
      exact ite_eq_right (not_lt.2 hs.le)
  exact ⟨_, w, (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hub, hsol, hwy 0 hb⟩

/-- The maximal solution, with the `H²` blow-up alternative. -/
theorem exists_maximal (hN : Majorized N) (hG : GoodForce G Γ) {y₀ : Field} (hy₀ : Adm 2 y₀) :
    ∃ (T : ℝ≥0∞) (y : ℝ → Field), 0 < T ∧ IsHeatSol N G T y ∧ y 0 = y₀ ∧
      (T ≠ ⊤ → ∀ C : ℝ, ¬ ∀ t, 0 ≤ t → ENNReal.ofReal t < T → hnorm 2 (y t) ≤ C) := by
  obtain ⟨T, y, hT, hy, hy0, hmax⟩ := exists_longest hN hG hy₀
  refine ⟨T, y, hT, hy, hy0, fun hfin C hC => ?_⟩
  obtain ⟨b, rfl⟩ : ∃ b : ℝ, T = ENNReal.ofReal b := ⟨T.toReal, (ENNReal.ofReal_toReal hfin).symm⟩
  obtain ⟨T', w, hlt, hw, hw0⟩ := exists_extension hN hG (ENNReal.ofReal_pos.1 hT) hy hC
  exact absurd (hmax T' w hw (hw0.trans hy0)) (not_le.2 hlt)

end OVNS
