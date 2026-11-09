import OddViscousNS.Closed.Barrier

/-!
# Piecewise-affine graph regions and their invariance (forced branch)

The graph of a slope list `m₀, …, m_{N−1} ≥ 0` over the cells `[B_l, B_{l+1}]`, `B_l = 1 + l/1000`:
`G(Y) = 1 − Δ ∑_{l<N} m_l · clamp((Y − B_l)/Δ)`, so `G ≡ 1` on `Y ≤ 1`, `G = ℓ_l` on cell `l` with
`ℓ_l(Y) = E_l − m_l(Y − B_l)`, `E_l = 1 − Δ ∑_{i<l} m_i`, and `G` is continuous and antitone.

`graph_invariant` is the first-exit argument: if `(X,Y)` is continuous, starts in the region
`{Y ≤ Y*, X ≤ G(Y)}` (`Y* = B_N`), `X ≤ 1` throughout, and at every boundary point the active
constraints do not increase for a short time (non-strict), then the region is invariant.
-/

open Set Filter Topology

noncomputable section

namespace OVNS

namespace Forced

/-- Clamp to `[0,1]`. -/
def clamp01 (x : ℝ) : ℝ := max 0 (min 1 x)

/-- The knots `B_l = 1 + l/1000`. -/
def knotB (l : ℕ) : ℝ := 1 + (l : ℝ) / 1000

/-- The levels `E_l = 1 − ∑_{i<l} m_i/1000`. -/
def levelE (m : ℕ → ℝ) (l : ℕ) : ℝ := 1 - ∑ i ∈ Finset.range l, m i / 1000

/-- The affine piece `ℓ_l(Y) = E_l − m_l (Y − B_l)`. -/
def piece (m : ℕ → ℝ) (l : ℕ) (Y : ℝ) : ℝ := levelE m l - m l * (Y - knotB l)

/-- The graph function. -/
def graphFun (m : ℕ → ℝ) (N : ℕ) (Y : ℝ) : ℝ :=
  1 - ∑ l ∈ Finset.range N, m l / 1000 * clamp01 ((Y - knotB l) * 1000)

/-- `clamp01` vanishes on nonpositive arguments. -/
private theorem clamp01_of_nonpos {x : ℝ} (hx : x ≤ 0) : clamp01 x = 0 := by
  unfold clamp01
  exact max_eq_left (le_trans (min_le_right _ _) hx)

/-- `clamp01` is `1` on arguments `≥ 1`. -/
private theorem clamp01_of_one_le {x : ℝ} (hx : 1 ≤ x) : clamp01 x = 1 := by
  unfold clamp01
  rw [min_eq_left hx]
  norm_num

/-- `clamp01` is the identity on `[0,1]`. -/
private theorem clamp01_of_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : clamp01 x = x := by
  unfold clamp01
  rw [min_eq_right h1, max_eq_right h0]

/-- `clamp01` is nonnegative. -/
private theorem clamp01_nonneg (x : ℝ) : 0 ≤ clamp01 x := le_max_left _ _

/-- `clamp01` is monotone. -/
private theorem clamp01_mono : Monotone clamp01 := fun _ _ h ↦
  max_le_max le_rfl (min_le_min le_rfl h)

/-- Every `Y ∈ (1, B_N]` lies in some cell `l < N`. -/
private theorem exists_cell {N : ℕ} {Y : ℝ} (h1 : 1 < Y) (hN : Y ≤ knotB N) :
    ∃ l < N, Y ∈ Icc (knotB l) (knotB (l + 1)) := by
  induction N with
  | zero =>
    unfold knotB at hN
    simp at hN
    linarith
  | succ n ih =>
    by_cases h : Y ≤ knotB n
    · obtain ⟨l, hl, hc⟩ := ih h
      exact ⟨l, by omega, hc⟩
    · exact ⟨n, by omega, (lt_of_not_ge h).le, hN⟩

theorem continuous_clamp01 : Continuous clamp01 := by
  exact continuous_const.max (continuous_const.min continuous_id)

theorem continuous_graphFun (m : ℕ → ℝ) (N : ℕ) : Continuous (graphFun m N) := by
  have hS : Continuous fun Y : ℝ ↦
      ∑ l ∈ Finset.range N, m l / 1000 * clamp01 ((Y - knotB l) * 1000) :=
    continuous_finsetSum _ fun l _ ↦ by
      have h1 : Continuous fun Y : ℝ ↦ (Y - knotB l) * 1000 :=
        (continuous_id.sub continuous_const).mul continuous_const
      exact continuous_const.mul (continuous_clamp01.comp h1)
  exact continuous_const.sub hS

theorem graphFun_eq_one (m : ℕ → ℝ) (N : ℕ) {Y : ℝ} (hY : Y ≤ 1) : graphFun m N Y = 1 := by
  unfold graphFun
  rw [Finset.sum_eq_zero fun l _ => ?_, sub_zero]
  have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  rw [clamp01_of_nonpos, mul_zero]
  unfold knotB
  nlinarith

theorem graphFun_eq_piece (m : ℕ → ℝ) {N l : ℕ} (hl : l < N) {Y : ℝ}
    (hY : Y ∈ Icc (knotB l) (knotB (l + 1))) : graphFun m N Y = piece m l Y := by
  obtain ⟨h1, h2⟩ := hY
  have hk : knotB (l + 1) = knotB l + 1 / 1000 := by unfold knotB; push_cast; ring
  unfold graphFun piece levelE
  rw [← Finset.sum_range_add_sum_Ico _ hl.le, Finset.sum_eq_sum_Ico_succ_bot hl]
  have hA : ∀ i ∈ Finset.range l,
      m i / 1000 * clamp01 ((Y - knotB i) * 1000) = m i / 1000 := by
    intro i hi
    have hi' : (i : ℝ) + 1 ≤ l := by exact_mod_cast Finset.mem_range.mp hi
    rw [clamp01_of_one_le, mul_one]
    unfold knotB at h1 ⊢
    linarith
  have hB : ∀ i ∈ Finset.Ico (l + 1) N,
      m i / 1000 * clamp01 ((Y - knotB i) * 1000) = 0 := by
    intro i hi
    have hi' : (l : ℝ) + 1 ≤ i := by exact_mod_cast (Finset.mem_Ico.mp hi).1
    rw [clamp01_of_nonpos, mul_zero]
    unfold knotB at h2 ⊢
    push_cast at h2
    linarith
  have hC : clamp01 ((Y - knotB l) * 1000) = (Y - knotB l) * 1000 :=
    clamp01_of_mem (by linarith) (by linarith)
  rw [Finset.sum_congr rfl hA, Finset.sum_congr rfl hB, hC, Finset.sum_const_zero]
  ring

theorem graphFun_le_one {m : ℕ → ℝ} (hm : ∀ l, 0 ≤ m l) (N : ℕ) (Y : ℝ) : graphFun m N Y ≤ 1 := by
  unfold graphFun
  have : 0 ≤ ∑ l ∈ Finset.range N, m l / 1000 * clamp01 ((Y - knotB l) * 1000) :=
    Finset.sum_nonneg fun l _ => mul_nonneg (div_nonneg (hm l) (by norm_num)) (clamp01_nonneg _)
  linarith

theorem graphFun_antitone {m : ℕ → ℝ} (hm : ∀ l, 0 ≤ m l) (N : ℕ) : Antitone (graphFun m N) := by
  intro a b hab
  unfold graphFun
  refine sub_le_sub_left (Finset.sum_le_sum fun l _ => ?_) _
  refine mul_le_mul_of_nonneg_left (clamp01_mono ?_) (div_nonneg (hm l) (by norm_num))
  nlinarith

theorem knotB_succ (l : ℕ) : knotB (l + 1) = knotB l + 1 / 1000 := by
  unfold knotB
  push_cast
  ring

theorem levelE_succ (m : ℕ → ℝ) (l : ℕ) : levelE m (l + 1) = levelE m l - m l / 1000 := by
  unfold levelE
  rw [Finset.sum_range_succ]
  ring

/-- The terminal value `G(B_N) = E_N`. -/
theorem graphFun_knotN (m : ℕ → ℝ) (N : ℕ) : graphFun m N (knotB N) = levelE m N := by
  unfold graphFun levelE
  congr 1
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' : (l : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.mp hl
  rw [clamp01_of_one_le, mul_one]
  unfold knotB
  linarith

/-- Non-strict first-exit lemma on `[0, T)`. -/
theorem barrier_of_local' {T : ℝ} {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Ico 0 T)) (h0 : φ 0 ≤ 0)
    (hloc : ∀ τ₀ ∈ Ico 0 T, φ τ₀ = 0 →
      ∃ δ > 0, ∀ τ ∈ Ioo τ₀ (τ₀ + δ), τ < T → φ τ ≤ 0) :
    ∀ τ ∈ Ico 0 T, φ τ ≤ 0 := by
  intro τ₁ hτ₁
  by_contra hpos
  push Not at hpos
  set S : Set ℝ := Icc 0 τ₁ ∩ φ ⁻¹' Iic 0 with hS
  have hsub : Icc 0 τ₁ ⊆ Ico 0 T := fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hτ₁.2⟩
  have hcl : IsClosed S := (hφ.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hne : S.Nonempty := ⟨0, ⟨le_rfl, hτ₁.1⟩, h0⟩
  have hbdd : BddAbove S := ⟨τ₁, fun x hx => hx.1.2⟩
  have hmem : sSup S ∈ S := hcl.csSup_mem hne hbdd
  set τ₀ := sSup S with hτ₀
  have hτ₀le : φ τ₀ ≤ 0 := hmem.2
  have hlt : τ₀ < τ₁ := by
    rcases lt_or_eq_of_le hmem.1.2 with h | h
    · exact h
    · exfalso
      have := hmem.2
      simp only [mem_preimage, mem_Iic] at this
      rw [h] at this
      linarith
  have hgt : ∀ u ∈ Ioc τ₀ τ₁, 0 < φ u := by
    intro u hu
    by_contra hu'
    push Not at hu'
    have : u ≤ τ₀ := le_csSup hbdd ⟨⟨le_trans hmem.1.1 hu.1.le, hu.2⟩, hu'⟩
    linarith [hu.1]
  have hpt : ∀ δ > 0, ∃ x ∈ Ioc τ₀ τ₁, x < τ₀ + δ := by
    intro δ hδ
    refine ⟨min (τ₀ + δ / 2) τ₁, ⟨lt_min (by linarith) hlt, min_le_right _ _⟩, ?_⟩
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hτ₀mem : τ₀ ∈ Ico 0 T := hsub hmem.1
  have hzero : φ τ₀ = 0 := by
    refine le_antisymm hτ₀le ?_
    by_contra hneg
    push Not at hneg
    obtain ⟨δ, hδ, hball⟩ :=
      Metric.continuousWithinAt_iff.mp (hφ τ₀ hτ₀mem) (-φ τ₀) (by linarith)
    obtain ⟨x, hx, hxδ⟩ := hpt δ hδ
    have hd : dist x τ₀ < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1]
    have := hball (hsub ⟨le_trans hmem.1.1 hx.1.le, hx.2⟩) hd
    rw [Real.dist_eq, abs_lt] at this
    linarith [hgt x hx, this.2]
  obtain ⟨δ, hδ, hneg⟩ := hloc τ₀ hτ₀mem hzero
  obtain ⟨x, hx, hxδ⟩ := hpt δ hδ
  have h1 := hneg x ⟨hx.1, hxδ⟩ (lt_of_le_of_lt hx.2 hτ₁.2)
  linarith [hgt x hx]

/-- Invariance of the graph region `{Y ≤ B_N, X ≤ G(Y)}` under non-strict local decrease of the
active constraints: the terminal face (`Y` does not increase), and each face `l` (`X + m_l Y`
does not increase from a point of the closed face `l`); the plateau is covered by `X ≤ 1`. -/
theorem graph_invariant {T : ℝ} {X Y : ℝ → ℝ} {m : ℕ → ℝ} {N : ℕ} (hm : ∀ l, 0 ≤ m l)
    (hN : 0 < N) (hX : ContinuousOn X (Ico 0 T)) (hY : ContinuousOn Y (Ico 0 T))
    (hX0 : X 0 ≤ graphFun m N (Y 0)) (hY0 : Y 0 ≤ knotB N) (hXle : ∀ τ ∈ Ico 0 T, X τ ≤ 1)
    (hterm : ∀ τ₀ ∈ Ico 0 T, Y τ₀ = knotB N → X τ₀ ≤ levelE m N →
      ∃ δ > 0, ∀ τ ∈ Ioo τ₀ (τ₀ + δ), τ < T → Y τ ≤ knotB N)
    (hface : ∀ l < N, ∀ τ₀ ∈ Ico 0 T, Y τ₀ ∈ Icc (knotB l) (knotB (l + 1)) →
      X τ₀ = piece m l (Y τ₀) →
      ∃ δ > 0, ∀ τ ∈ Ioo τ₀ (τ₀ + δ), τ < T → X τ + m l * Y τ ≤ X τ₀ + m l * Y τ₀) :
    ∀ τ ∈ Ico 0 T, Y τ ≤ knotB N ∧ X τ ≤ graphFun m N (Y τ) := by
  -- `hm` and `hN` are not needed for the invariance argument itself.
  have _hm := hm
  have _hN := hN
  have hG := continuous_graphFun m N
  have key := barrier_of_local'
    (φ := fun τ ↦ max (Y τ - knotB N) (X τ - graphFun m N (Y τ)))
    (continuous_max.comp_continuousOn
      ((hY.sub continuousOn_const).prodMk (hX.sub (hG.comp_continuousOn hY))))
    (by simp only [max_le_iff, sub_nonpos]; exact ⟨hY0, hX0⟩) ?_
  · intro τ hτ
    have := key τ hτ
    simp only [max_le_iff, sub_nonpos] at this
    exact this
  intro τ₀ hτ₀ hΦ
  have hle : Y τ₀ ≤ knotB N ∧ X τ₀ ≤ graphFun m N (Y τ₀) := by
    have := hΦ.le
    simp only [max_le_iff, sub_nonpos] at this
    exact this
  have hin : ∀ᶠ τ in 𝓝[>] τ₀, τ ∈ Ico 0 T := by
    filter_upwards [Ioo_mem_nhdsGT hτ₀.2] with τ hτ using ⟨hτ₀.1.trans hτ.1.le, hτ.2⟩
  have hYc : Tendsto Y (𝓝[>] τ₀) (𝓝 (Y τ₀)) := (hY τ₀ hτ₀).mono_of_mem_nhdsWithin hin
  have hXc : Tendsto X (𝓝[>] τ₀) (𝓝 (X τ₀)) := (hX τ₀ hτ₀).mono_of_mem_nhdsWithin hin
  have hev : ∀ {P : ℝ → Prop}, (∃ δ > 0, ∀ τ ∈ Ioo τ₀ (τ₀ + δ), τ < T → P τ) →
      ∀ᶠ τ in 𝓝[>] τ₀, P τ := by
    rintro P ⟨δ, hδ, h⟩
    filter_upwards [Ioo_mem_nhdsGT (by linarith : τ₀ < τ₀ + δ), Ioo_mem_nhdsGT hτ₀.2]
      with τ h1 h2 using h τ h1 h2.2
  have hP1 : ∀ᶠ τ in 𝓝[>] τ₀, Y τ ≤ knotB N := by
    rcases hle.1.lt_or_eq with h | h
    · filter_upwards [hYc.eventually_lt_const h] with τ hτ using hτ.le
    · have h2 := hle.2
      rw [h, graphFun_knotN] at h2
      exact hev (hterm τ₀ hτ₀ h h2)
  have hP2 : ∀ᶠ τ in 𝓝[>] τ₀, Y τ ≤ knotB N → X τ ≤ graphFun m N (Y τ) := by
    rcases hle.2.lt_or_eq with h | h
    · have ht : Tendsto (fun τ ↦ X τ - graphFun m N (Y τ)) (𝓝[>] τ₀)
          (𝓝 (X τ₀ - graphFun m N (Y τ₀))) := hXc.sub ((hG.tendsto _).comp hYc)
      filter_upwards [ht.eventually_lt_const (sub_neg.mpr h)] with τ hτ _
      exact (sub_neg.mp hτ).le
    · have hcell : ∀ j ∈ Finset.range N, ∀ᶠ τ in 𝓝[>] τ₀,
          Y τ ∈ Icc (knotB j) (knotB (j + 1)) → X τ ≤ graphFun m N (Y τ) := by
        intro j hj
        have hj' := Finset.mem_range.mp hj
        by_cases hmem : Y τ₀ ∈ Icc (knotB j) (knotB (j + 1))
        · have hX₀ : X τ₀ = piece m j (Y τ₀) := by rw [h, graphFun_eq_piece m hj' hmem]
          filter_upwards [hev (hface j hj' τ₀ hτ₀ hmem hX₀)] with τ hτ hYτ
          rw [graphFun_eq_piece m hj' hYτ]
          rw [hX₀] at hτ
          unfold piece at hτ ⊢
          linarith
        · filter_upwards [hYc.eventually (isClosed_Icc.isOpen_compl.mem_nhds hmem)]
            with τ hτ hYτ
          exact absurd hYτ hτ
      have hall := (Filter.eventually_all_finset (Finset.range N)).mpr hcell
      filter_upwards [hall, hin] with τ hτ hτin hYN
      by_cases h1 : Y τ ≤ 1
      · rw [graphFun_eq_one m N h1]
        exact hXle τ hτin
      · obtain ⟨j, hj, hjc⟩ := exists_cell (lt_of_not_ge h1) hYN
        exact hτ j (Finset.mem_range.mpr hj) hjc
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hP1.and hP2)
  refine ⟨u - τ₀, by rw [mem_Ioi] at hu; linarith, fun τ hτ _ ↦ ?_⟩
  have hτu : τ ∈ Ioo τ₀ u := ⟨hτ.1, by linarith [hτ.2]⟩
  obtain ⟨h1, h2⟩ := hsub hτu
  show max (Y τ - knotB N) (X τ - graphFun m N (Y τ)) ≤ 0
  simp only [max_le_iff, sub_nonpos]
  exact ⟨h1, h2 h1⟩

end Forced

end OVNS

end
