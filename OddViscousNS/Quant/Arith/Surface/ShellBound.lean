import OddViscousNS.Quant.Arith.Surface.Direct

/-!
# `shell_surface_bound'`

The bound on an intermediate shell, with no hypothesis of surface type: `shell_large` for `N ≥ N₀`
(the choice of the parameters), `shell_small` for `N < N₀` (the box), and the assembly.
-/

open MvPolynomial Finset

namespace OVNS.Quant.Surf

open private shell_facts from OddViscousNS.Quant.Arith.Weighted.SurfaceCover

/-- The choice of the parameters. -/
theorem shell_large : ∀ ε : ℝ, 0 < ε → ∃ C N₀ : ℝ, 0 ≤ C ∧
    ∀ (n : Mode) (Δ z : ℕ) (s2 s3 : ℤ) (g T : ℕ), ShellHyp n Δ z g T → N₀ ≤ absk n →
      ((shellPts n Δ z s2 s3 g T).card : ℝ) ≤ C * absk n ^ (pStar + ε) := by
  intro ε hε
  set η := min ((1 : ℝ) / 10) (ε / 2) with hη
  set δ := min ((1 : ℝ) / 100) (ε / 10) with hδ
  have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 / 10 := min_le_left _ _
  have hη2 : η ≤ ε / 2 := min_le_right _ _
  have hδ1 : δ ≤ 1 / 100 := min_le_left _ _
  have hδ2 : δ ≤ ε / 10 := min_le_right _ _
  obtain ⟨ϑ₀, C₃, hϑ₀, hC₃, htree⟩ := tree_cover η hη0 (by linarith)
  set K₀ : ℕ := ⌈21 / δ⌉₊ + 5 with hK₀
  set L₀ : ℕ := ⌈1 / δ⌉₊ with hL₀
  set Dg : ℕ := ⌈312 * ϑ₀⌉₊ + 24 with hDg
  obtain ⟨C₂, hC₂, hPF⟩ := plane_factor_count PlaneCount.planeCurveCount quadraticNormCount
    fewPointsNotAbsIrred Dg (ε / 4) (by positivity)
  set A₀ := Real.exp C₃ * 2 ^ (K₀ + 1) * Real.exp (4 * (1 + η)) with hA
  have hA₀0 : 0 ≤ A₀ := by rw [hA]; positivity
  have hev : ∀ᶠ N : ℝ in Filter.atTop, 2 ≤ N ∧ 20 * Real.log N ≤ N ^ δ ∧
      72 * (((K₀ : ℝ) + 1) * Real.log 2) ≤ Real.log N ∧ A₀ ≤ N ^ ((1 : ℝ) / 2) := by
    have h1 : ∀ᶠ N : ℝ in Filter.atTop, 2 ≤ N := Filter.eventually_ge_atTop 2
    have h2 : ∀ᶠ N : ℝ in Filter.atTop, 20 * Real.log N ≤ N ^ δ := by
      have hb := (isLittleO_log_rpow_atTop hδ0).bound (by norm_num : (0 : ℝ) < 1 / 20)
      filter_upwards [hb, Filter.eventually_ge_atTop 2] with N hN hN2
      have hpos : 0 ≤ N ^ δ := by positivity
      rw [Real.norm_of_nonneg (Real.log_nonneg (by linarith)), Real.norm_of_nonneg hpos] at hN
      linarith
    have h3 : ∀ᶠ N : ℝ in Filter.atTop, 72 * (((K₀ : ℝ) + 1) * Real.log 2) ≤ Real.log N :=
      Real.tendsto_log_atTop.eventually_ge_atTop _
    have h4 : ∀ᶠ N : ℝ in Filter.atTop, A₀ ≤ N ^ ((1 : ℝ) / 2) :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually_ge_atTop _
    filter_upwards [h1, h2, h3, h4] with N a b c d using ⟨a, b, c, d⟩
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hev
  have hC : 0 ≤ coreC C₂ ϑ₀ A₀ K₀ L₀ := by
    unfold coreC
    positivity
  refine ⟨coreC C₂ ϑ₀ A₀ K₀ L₀, N₀, hC, ?_⟩
  intro n Δ z s2 s3 g T hH hN
  have hN1 : (1 : ℝ) ≤ absk n := by
    obtain ⟨-, -, -, h, -⟩ := shell_facts hH
    linarith
  rcases (shellPts n Δ z s2 s3 g T).eq_empty_or_nonempty with h0 | ⟨k, hk⟩
  · rw [h0, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg hC (Real.rpow_nonneg (by linarith) _)
  have hkA : k ∈ activePts n s2 s3 := by
    classical
    unfold shellPts at hk
    exact (Finset.mem_filter.1 (Finset.mem_filter.1 hk).1).1
  obtain ⟨c, -, -, -, hc3, -⟩ := tOf_eq_coords_t hkA hH.1 hH.2.1
  have hn3 := c.hn3
  have hs3 : s3 = 1 ∨ s3 = -1 := hc3 ▸ c.hs3
  have hnh := active_nh hkA
  obtain ⟨i, j, hij, hnj⟩ : ∃ i j : Fin 3, ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) ∧ n j ≠ 0 := by
    by_cases h1 : n 1 = 0
    · refine ⟨1, 0, Or.inr ⟨rfl, rfl⟩, fun h0 => hnh ?_⟩
      rw [h0, h1]; ring
    · exact ⟨0, 1, Or.inl ⟨rfl, rfl⟩, h1⟩
  obtain ⟨h1, h2, h3, h4⟩ := hN₀ _ hN
  have hP : Params (absk n) δ η ε K₀ A₀ :=
    { hN2 := h1, h20 := h2, h72 := h3, hA₀ := h4, hδ0 := hδ0, hδ1 := hδ1, hδ2 := hδ2, hη0 := hη0,
      hη1 := hη1, hη2 := hη2,
      hK₀ := by
        have := Nat.le_ceil (21 / δ)
        rw [hK₀]
        push_cast
        linarith
      hK₅ := by omega }
  have hD1 : 312 * ϑ₀ ≤ (Dg : ℝ) := by
    rw [hDg]
    push_cast
    have := Nat.le_ceil (312 * ϑ₀)
    linarith
  exact shell_core htree hϑ₀ hC₂ hD1 (by omega) hPF hA (Nat.le_ceil _) hH hij hn3 hnj hs3 hP

/-- The box: the trivial bound for bounded `N`. -/
theorem shell_small {N₀ : ℝ} {n : Mode} {Δ z : ℕ} {s2 s3 : ℤ} {g T : ℕ} (hN : absk n < N₀) :
    ((shellPts n Δ z s2 s3 g T).card : ℝ) ≤ (2 * N₀ + 1) ^ 3 := by
  classical
  set R := Nat.sqrt (nsqZ n).toNat with hR
  have hsub : shellPts n Δ z s2 s3 g T ⊆ modeBox R := by
    intro k hk
    unfold shellPts at hk
    have h1 := (Finset.mem_filter.1 (Finset.mem_filter.1 hk).1).1
    unfold activePts at h1
    exact (Finset.mem_filter.1 h1).1
  have hcard : (modeBox R).card = (2 * R + 1) ^ 3 := by
    simp only [modeBox, Fintype.card_piFinset, Finset.prod_const, Int.card_Icc, Finset.card_univ,
      Fintype.card_fin]
    have : ((R : ℤ) + 1 - (-(R : ℤ))).toNat = 2 * R + 1 := by omega
    rw [this]
  have hN0 : 0 ≤ absk n := Real.sqrt_nonneg _
  have hRN : (R : ℝ) ≤ absk n := by
    have h1 : ((R ^ 2 : ℕ) : ℤ) ≤ nsqZ n := by
      have h0 : 0 ≤ nsqZ n := Finset.sum_nonneg fun i _ => sq_nonneg _
      have h2 : R ^ 2 ≤ (nsqZ n).toNat := by
        have := Nat.sqrt_le' (nsqZ n).toNat
        rwa [← hR] at this
      calc ((R ^ 2 : ℕ) : ℤ) ≤ ((nsqZ n).toNat : ℤ) := by exact_mod_cast h2
        _ = nsqZ n := Int.toNat_of_nonneg h0
    have h3 : ((R : ℝ)) ^ 2 ≤ absk n ^ 2 := by
      rw [absk_sq]
      exact_mod_cast h1
    exact abs_le_of_sq_le_sq' h3 hN0 |>.2
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have h1 : ((shellPts n Δ z s2 s3 g T).card : ℝ) ≤ ((2 * R + 1) ^ 3 : ℕ) := by
    rw [← hcard]
    exact_mod_cast Finset.card_le_card hsub
  refine h1.trans ?_
  push_cast
  exact pow_le_pow_left₀ (by positivity) (by linarith) 3

end OVNS.Quant.Surf

namespace OVNS.Quant

open OVNS.Quant.Surf

open private shell_facts from OddViscousNS.Quant.Arith.Weighted.SurfaceCover

/-- **The shell bound with no hypothesis of surface type.** -/
theorem shell_surface_bound' : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (n : Mode) (Δ z : ℕ) (s2 s3 : ℤ) (g T : ℕ), Squarefree Δ → nsqZ n = Δ * z ^ 2 →
      g ∣ (n 2).natAbs → 1 ≤ T → T ≤ 2 * z → absk n ^ (pStar - 1 / 4) < g →
      absk n ^ pStar < (T : ℝ) / g →
      ((((activePts n s2 s3).filter fun k =>
          Nat.gcd (n 2).natAbs (tOf Δ s2 n k).natAbs = g).filter fun k =>
        (T : ℤ) ≤ tOf Δ s2 n k ∧ tOf Δ s2 n k < 2 * T ∧
          caOf Δ z (n 2) (tOf Δ s2 n k) ≠ 0).card : ℝ) ≤ C * absk n ^ (pStar + ε) := by
  intro ε hε
  obtain ⟨C, N₀, hC, hL⟩ := shell_large ε hε
  refine ⟨C + (2 * max N₀ 0 + 1) ^ 3, by positivity, ?_⟩
  intro n Δ z s2 s3 g T hsq hn hg hT1 hT2 hgN hTg
  have hH : ShellHyp n Δ z g T := ⟨hsq, hn, hg, hT1, hT2, hgN, hTg⟩
  change ((shellPts n Δ z s2 s3 g T).card : ℝ) ≤ _
  have hN1 : (1 : ℝ) ≤ absk n := by
    obtain ⟨-, -, -, h, -⟩ := shell_facts hH
    linarith
  have hX1 : 1 ≤ absk n ^ (pStar + ε) :=
    Real.one_le_rpow hN1 (by have := pStar_bounds.1; linarith)
  have hm0 : 0 ≤ max N₀ 0 := le_max_right _ _
  rcases le_or_gt N₀ (absk n) with h | h
  · refine (hL n Δ z s2 s3 g T hH h).trans ?_
    have : 0 ≤ (2 * max N₀ 0 + 1) ^ 3 * absk n ^ (pStar + ε) := by positivity
    nlinarith
  · have h1 : ((shellPts n Δ z s2 s3 g T).card : ℝ) ≤ (2 * max N₀ 0 + 1) ^ 3 :=
      shell_small (lt_of_lt_of_le h (le_max_left _ _))
    have h2 : (2 * max N₀ 0 + 1) ^ 3 ≤ (2 * max N₀ 0 + 1) ^ 3 * absk n ^ (pStar + ε) :=
      le_mul_of_one_le_right (by positivity) hX1
    have h3 : 0 ≤ C * absk n ^ (pStar + ε) := by positivity
    nlinarith

end OVNS.Quant
