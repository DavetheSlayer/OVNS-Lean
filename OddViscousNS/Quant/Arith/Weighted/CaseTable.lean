import OddViscousNS.Quant.Arith.Weighted.SurfacePoints

/-!
# The covered-curve case table (Section D6)

Setting (all rows): `ShellHyp n Δ z g T` (so `N = |n| ≥ 1`, `g > N^{p*−1/4}`, `T/g > N^{p*}`,
`T ≤ 2z ≤ 2N`) and `H ∈ ℤ[X₁,X₂]`.  We count the shell points `k ∈ shellPts` whose projection
`(X₁, X₂) = (t/g, gw/n₃)` (`projPt`) is a zero of `H`.  The projected points lie in the box
`|X₁| ≤ B₀ = 2T/g`, `|X₂| ≤ B₁ = 4gN/T` (`surface_points`), with `B₀B₁ = 8N`,
`2N^{p*} < B₀ < 4N^{5/4−p*}`, `B₁ < 4N^{1−p*}`, and each projected point has at most two shell
points above it (`proj_two_to_one`).  `PlaneCurveCount` is applied after swapping coordinates so
that the shorter side comes first; its exponent is `log B_min log B_max / log 𝔗(H)`.

Rows:
* `row_notAbsIrred` (`ℚ`-irreducible, not absolutely irreducible): `≤ deg²` points
  (`FewPointsNotAbsIrred`).
* `row_degree_ge3` (abs. irr., `d ≥ 3`): `𝔗 ≥ B_min^d`, exponent `≤ log B_max/3
  ≤ ((5/4−p*)λ + log 4)/3`, and `(5/4−p*)/3 < 1/4`.
* `row_conic_general` (abs. irr., `d = 2`, `X₁²` or `X₁X₂` occurs): `𝔗 ≥ B₀²` gives
  `≤ log B₁/2` with `(1−p*)/2 < 1/4`; `𝔗 ≥ B₀B₁ = 8N` gives `≤ log(8N)/4`.
* `row_conic_X2sq` (`ℚ`-irr., `d = 2`, no `X₁²`, no `X₁X₂`): degree-10 lift.
* `row_line_sloped` (`d = 1`, both `X₁, X₂` occur): sextic lift.
* `row_const_t` (`d = 1`, no `X₂`): `X₁ = c`, fixed non-parabolic `t = gc`: `fixed_t_count`.
* `row_const_w` (`d = 1`, no `X₁`): `X₂ = c`, fixed height `w = n₃c/g`: `fixed_w_count`.

Lifts (TeX: "the remaining conic is a quadratic graph … degree-ten plane lift … a sloping
projected line similarly gives a sextic lift").  Along a rational parametrization
`(X₁, X₂) = (q(s), s)` (conic `αX₂² + βX₁ + γX₂ + δ`, `β ≠ 0`; if `β = 0` the `ℚ`-irreducible
quadratic in `X₂` has no rational zero, so there are no points) or `(s, λs + μ)` (sloped line), the
surface `F` restricts to `Φ(s, X₃)` (denominators cleared) of degree `10` resp. `6`, with
`s¹⁰` resp. `s⁶` coefficient a nonzero multiple of `Δ²g⁴` (`X₁⁴X₂²` is the only degree-6 monomial
of `F`).  In the J-form `|n_h|²Φ = 4g²[(|n_h|²X₃ − n_iL(s))² − n_j²P(s)]`, `P` has negative
leading coefficient (`−(lead L)²`); by `sq_or_absIrred` and the triangular change of variables,
either `Φ` is absolutely irreducible — then `PlaneCurveCount` in the square box `max(2, 4N)` with
`𝔗 ≥ (4N)^{10}` resp. `(4N)^6` gives `≤ C N^{1/10+ε}` resp. `C N^{1/6+ε}` points `(s, X₃)` — or
`P = cR²` with `c < 0`, forcing `R(s) = 0`: at most `5` resp. `3` values of `s`.  Each `(s, X₃)`
determines the surface point, which has at most two shell points above it.
-/

open MvPolynomial

noncomputable section

namespace OVNS.Quant

/-- The number of shell points whose projection is a zero of `H`. -/
def curveCount (n : Mode) (Δ z : ℕ) (s2 s3 : ℤ) (g T : ℕ) (H : MvPolynomial (Fin 2) ℤ) : ℕ := by
  classical
  exact ((shellPts n Δ z s2 s3 g T).filter fun k => eval (projPt Δ s2 g n k) H = 0).card

/-- The monomial `X₁^p X₂^q`. -/
private abbrev e2 (p q : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 p + Finsupp.single 1 q

private lemma e2_eq (m : Fin 2 →₀ ℕ) : m = e2 (m 0) (m 1) := by
  ext i; fin_cases i <;> simp [e2]

private lemma e2_deg (p q : ℕ) : ((e2 p q).sum fun _ e => e) = p + q := by
  simp [e2, Finsupp.sum_add_index', Finsupp.sum_single_index]

private lemma coeff_e2_zero {H : MvPolynomial (Fin 2) ℤ} {p q : ℕ} (h : H.totalDegree < p + q) :
    H.coeff (e2 p q) = 0 := by
  by_contra h'
  have := le_totalDegree (mem_support_iff.mpr h')
  rw [e2_deg] at this; omega

/-- Evaluation of a polynomial of degree `≤ D` as a double sum over its coefficients. -/
private lemma eval_eq_sum (H : MvPolynomial (Fin 2) ℤ) (D : ℕ) (hH : H.totalDegree ≤ D)
    (x : Fin 2 → ℤ) : eval x H = ∑ p ∈ Finset.range (D + 1), ∑ q ∈ Finset.range (D + 1),
      H.coeff (e2 p q) * (x 0 ^ p * x 1 ^ q) := by
  classical
  rw [eval_eq', ← Finset.sum_product']
  have hinj : Set.InjOn (fun pq : ℕ × ℕ => e2 pq.1 pq.2)
      ↑(Finset.range (D + 1) ×ˢ Finset.range (D + 1)) := by
    intro a _ b _ hab
    have h0 := congrArg (fun m => m 0) hab
    have h1 := congrArg (fun m => m 1) hab
    simp [e2] at h0 h1
    exact Prod.ext h0 h1
  have hr : ∀ pq ∈ Finset.range (D + 1) ×ˢ Finset.range (D + 1),
      H.coeff (e2 pq.1 pq.2) * (x 0 ^ pq.1 * x 1 ^ pq.2) =
        (fun m => H.coeff m * ∏ i, x i ^ m i) (e2 pq.1 pq.2) := by
    intro pq _
    simp [e2, Fin.prod_univ_two]
  rw [Finset.sum_congr rfl hr, ← Finset.sum_image (f := fun m => H.coeff m * ∏ i, x i ^ m i) hinj]
  apply Finset.sum_subset
  · intro m hm
    have := le_totalDegree hm
    rw [e2_eq m, e2_deg] at this
    rw [Finset.mem_image]
    refine ⟨(m 0, m 1), ?_, (e2_eq m).symm⟩
    simp only [Finset.mem_product, Finset.mem_range]; omega
  · intro m _ hm
    rw [notMem_support_iff.mp hm, zero_mul]

private lemma eval_deg2 (H : MvPolynomial (Fin 2) ℤ) (hH : H.totalDegree ≤ 2) (x : Fin 2 → ℤ) :
    eval x H = H.coeff (e2 0 0) + H.coeff (e2 1 0) * x 0 + H.coeff (e2 0 1) * x 1 +
      H.coeff (e2 2 0) * x 0 ^ 2 + H.coeff (e2 1 1) * (x 0 * x 1) +
      H.coeff (e2 0 2) * x 1 ^ 2 := by
  rw [eval_eq_sum H 2 hH x]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [coeff_e2_zero (p := 2) (q := 1) (by omega), coeff_e2_zero (p := 1) (q := 2) (by omega),
    coeff_e2_zero (p := 2) (q := 2) (by omega)]
  ring

private lemma eval_deg1 (H : MvPolynomial (Fin 2) ℤ) (hH : H.totalDegree ≤ 1) (x : Fin 2 → ℤ) :
    eval x H = H.coeff (e2 0 0) + H.coeff (e2 1 0) * x 0 + H.coeff (e2 0 1) * x 1 := by
  rw [eval_eq_sum H 1 hH x]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [coeff_e2_zero (p := 1) (q := 1) (by omega)]
  ring

private lemma e2_20 : e2 2 0 = Finsupp.single 0 2 := by simp [e2]
private lemma e2_02 : e2 0 2 = Finsupp.single 1 2 := by simp [e2]
private lemma e2_10 : e2 1 0 = Finsupp.single 0 1 := by simp [e2]
private lemma e2_01 : e2 0 1 = Finsupp.single 1 1 := by simp [e2]

/-- A polynomial of degree `d ≥ 1` has a nonzero coefficient of degree `d`. -/
private lemma exists_top (H : MvPolynomial (Fin 2) ℤ) {d : ℕ} (hd : H.totalDegree = d)
    (hd1 : 1 ≤ d) : ∃ p q : ℕ, p + q = d ∧ H.coeff (e2 p q) ≠ 0 := by
  have hne : H.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h
    have : H = 0 := by rw [← support_eq_empty]; exact h
    subst this; simp at hd; omega
  obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_sup H.support hne (fun s => s.sum fun _ e => e)
  refine ⟨m 0, m 1, ?_, ?_⟩
  · have : H.totalDegree = m.sum fun _ e => e := hmax
    rw [e2_eq m, e2_deg] at this; omega
  · rw [← e2_eq m]; exact mem_support_iff.mp hm

private lemma log4 : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num

private lemma log8 : Real.log 8 = 3 * Real.log 2 := by
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num

/-- The numerical facts about the shell box `(B₀, B₁) = (2T/g, 4gN/T)`. -/
private lemma shell_facts {n : Mode} {Δ z g T : ℕ} (hH : ShellHyp n Δ z g T) :
    1 ≤ absk n ∧ (z : ℝ) ≤ absk n ∧ 1 ≤ (g : ℝ) ∧ 1 ≤ (T : ℝ) ∧
    2 ≤ 2 * (T : ℝ) / g ∧ 2 ≤ 4 * (g : ℝ) * absk n / T ∧
    2 * (T : ℝ) / g ≤ 4 * absk n ∧ 4 * (g : ℝ) * absk n / T ≤ 4 * absk n ∧
    Real.log (2 * T / g) ≤ Real.log 4 + (5 / 4 - pStar) * Real.log (absk n) ∧
    Real.log (4 * g * absk n / T) ≤ Real.log 4 + (1 - pStar) * Real.log (absk n) ∧
    Real.log (2 * T / g) + Real.log (4 * g * absk n / T) = Real.log 8 + Real.log (absk n) := by
  obtain ⟨hsq, hn, -, hT1, hTz, hg, hTg⟩ := hH
  set N := absk n with hNdef
  have hΔ1 : (1 : ℝ) ≤ Δ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hsq.ne_zero
  have hz1 : (1 : ℝ) ≤ z := by exact_mod_cast (show 1 ≤ z by omega)
  have hT1' : (1 : ℝ) ≤ T := by exact_mod_cast hT1
  have hTz' : (T : ℝ) ≤ 2 * z := by exact_mod_cast hTz
  have hNsq : N = Real.sqrt ((Δ : ℝ) * (z : ℝ) ^ 2) := by
    rw [hNdef, absk_eq_sqrt_nsqZ, hn]; push_cast; rfl
  have hzN : (z : ℝ) ≤ N := by
    rw [hNsq]; apply Real.le_sqrt_of_sq_le; nlinarith
  have hN1 : 1 ≤ N := le_trans hz1 hzN
  have hN0 : 0 < N := by linarith
  have hp := pStar_bounds
  have hg0 : (0 : ℝ) < g := lt_of_le_of_lt (Real.rpow_nonneg hN0.le _) hg
  have hg1 : (1 : ℝ) ≤ g := by
    have : 0 < g := by exact_mod_cast hg0
    exact_mod_cast this
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hlg : (pStar - 1 / 4) * Real.log N < Real.log g := by
    have := Real.log_lt_log (Real.rpow_pos_of_pos hN0 _) hg
    rwa [Real.log_rpow hN0] at this
  have hlTg : pStar * Real.log N < Real.log T - Real.log g := by
    have := Real.log_lt_log (Real.rpow_pos_of_pos hN0 _) hTg
    rwa [Real.log_rpow hN0, Real.log_div hT0.ne' hg0.ne'] at this
  have hlT : Real.log T ≤ Real.log 2 + Real.log N := by
    rw [← Real.log_mul (by norm_num) hN0.ne']
    exact Real.log_le_log hT0 (by linarith)
  have hB0 : Real.log (2 * T / g) = Real.log 2 + Real.log T - Real.log g := by
    rw [Real.log_div (by positivity) hg0.ne', Real.log_mul (by norm_num) hT0.ne']
  have hprod : (2 * (T : ℝ) / g) * (4 * g * N / T) = 8 * N := by
    field_simp; ring
  have hsum : Real.log (2 * T / g) + Real.log (4 * g * N / T) = Real.log 8 + Real.log N := by
    rw [← Real.log_mul (by positivity) (by positivity), hprod,
      Real.log_mul (by norm_num) hN0.ne']
  have h1Tg : 1 ≤ (T : ℝ) / g := le_trans (Real.one_le_rpow hN1 (by linarith)) hTg.le
  refine ⟨hN1, hzN, hg1, hT1', ?_, ?_, ?_, ?_, ?_, ?_, hsum⟩
  · rw [mul_div_assoc]; linarith
  · rw [le_div_iff₀ hT0]; nlinarith
  · rw [div_le_iff₀ hg0]; nlinarith
  · have hgT : (g : ℝ) ≤ T := by rw [le_div_iff₀ hg0, one_mul] at h1Tg; exact h1Tg
    rw [div_le_iff₀ hT0]; nlinarith
  · rw [hB0, log4]; nlinarith
  · have : Real.log (4 * g * N / T) = Real.log 8 + Real.log N - Real.log (2 * T / g) := by
      linarith
    rw [this, hB0, log8, log4]; nlinarith

/-- The shell box of the projected points. -/
private def projBox (n : Mode) (g T : ℕ) : Fin 2 → ℝ := ![2 * T / g, 4 * g * absk n / T]

/-- Bookkeeping: every counted shell point projects into the box, at most two per point. -/
private lemma count_le_proj (n : Mode) (Δ z : ℕ) (s2 s3 : ℤ) (g T : ℕ)
    (H : MvPolynomial (Fin 2) ℤ) (hH : ShellHyp n Δ z g T) :
    curveCount n Δ z s2 s3 g T H ≤ 2 * (boxZeros H (projBox n g T)).card := by
  classical
  unfold curveCount
  refine Finset.card_le_mul_card_image_of_maps_to (f := projPt Δ s2 g n) ?_ 2 ?_
  · intro k hk
    rw [Finset.mem_filter] at hk
    have hs := surface_points hH hk.1 0 1 (Or.inl ⟨rfl, rfl⟩)
    simp only [boxZeros, boxPts, Finset.mem_filter, Fintype.mem_piFinset] at hs ⊢
    refine ⟨fun i => ?_, hk.2⟩
    fin_cases i
    · simpa [surfPt, projPt, shellBox, projBox] using hs.1 0
    · simpa [surfPt, projPt, shellBox, projBox] using hs.1 1
  · intro X _
    refine le_trans (Finset.card_le_card ?_) (proj_two_to_one n Δ z s2 s3 g T hH X)
    intro k hk
    simp only [Finset.mem_filter] at hk ⊢
    exact ⟨hk.1.1, hk.2⟩

/-- A monomial of `F` bounds the box size from below. -/
private lemma boxSize_ge (F : MvPolynomial (Fin 2) ℤ) (B : Fin 2 → ℝ) {m : Fin 2 →₀ ℕ}
    (hm : m ∈ F.support) : B 0 ^ m 0 * B 1 ^ m 1 ≤ boxSize F B := by
  unfold boxSize
  refine le_csSup ((Set.Finite.image _ (Finset.finite_toSet _)).bddAbove) ⟨m, hm, ?_⟩
  simp [Fin.prod_univ_two]

/-- `PlaneCurveCount` for an unsorted box, with the exponent bounded through one monomial. -/
private lemma plane_count (hP : PlaneCurveCount) (d : ℕ) (η : ℝ) (hd : 1 ≤ d) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : MvPolynomial (Fin 2) ℤ, F.totalDegree = d → AbsIrred F →
      ∀ B : Fin 2 → ℝ, 2 ≤ B 0 → 2 ≤ B 1 → ∀ m ∈ F.support, m ≠ 0 →
        ((boxZeros F B).card : ℝ) ≤ C * max (B 0) (B 1) ^ η *
          Real.exp (Real.log (B 0) * Real.log (B 1) /
            (m 0 * Real.log (B 0) + m 1 * Real.log (B 1))) := by
  obtain ⟨C, hC⟩ := hP d η hd hη
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  have key : ∀ F : MvPolynomial (Fin 2) ℤ, F.totalDegree = d → AbsIrred F →
      ∀ B : Fin 2 → ℝ, 2 ≤ B 0 → B 0 ≤ B 1 → ∀ m ∈ F.support, m ≠ 0 →
        ((boxZeros F B).card : ℝ) ≤ max C 0 * B 1 ^ η *
          Real.exp (Real.log (B 0) * Real.log (B 1) /
            (m 0 * Real.log (B 0) + m 1 * Real.log (B 1))) := by
    intro F hF hA B hB0 hB01 m hm hm0
    have h := hC F hF hA B hB0 hB01
    have hl0 : 0 < Real.log (B 0) := Real.log_pos (by linarith)
    have hl1 : 0 < Real.log (B 1) := Real.log_pos (by linarith)
    have hm01 : 1 ≤ m 0 + m 1 := by
      by_contra h'
      apply hm0; ext i; fin_cases i <;> simp <;> omega
    have hden : 0 < (m 0 : ℝ) * Real.log (B 0) + m 1 * Real.log (B 1) := by
      rcases Nat.eq_zero_or_pos (m 0) with h0 | h0
      · have : 0 < m 1 := by omega
        have : (0 : ℝ) < m 1 := by exact_mod_cast this
        rw [h0, Nat.cast_zero, zero_mul, zero_add]; exact mul_pos this hl1
      · have : (0 : ℝ) < m 0 := by exact_mod_cast h0
        have := mul_pos this hl0
        have := mul_nonneg (Nat.cast_nonneg (α := ℝ) (m 1)) hl1.le
        linarith
    have hT := boxSize_ge F B hm
    have hlogT : (m 0 : ℝ) * Real.log (B 0) + m 1 * Real.log (B 1) ≤
        Real.log (boxSize F B) := by
      have hb0 : 0 < B 0 := by linarith
      have hb1 : 0 < B 1 := by linarith
      have hpos : 0 < B 0 ^ m 0 * B 1 ^ m 1 := by positivity
      have := Real.log_le_log hpos hT
      rwa [Real.log_mul (pow_pos hb0 _).ne' (pow_pos hb1 _).ne', Real.log_pow,
        Real.log_pow] at this
    have hexp : Real.exp (Real.log (B 0) * Real.log (B 1) / Real.log (boxSize F B)) ≤
        Real.exp (Real.log (B 0) * Real.log (B 1) /
          (m 0 * Real.log (B 0) + m 1 * Real.log (B 1))) := by
      apply Real.exp_le_exp.mpr
      exact div_le_div_of_nonneg_left (mul_pos hl0 hl1).le hden hlogT
    have hBη : 0 ≤ B 1 ^ η := Real.rpow_nonneg (by linarith) _
    calc ((boxZeros F B).card : ℝ) ≤ C * B 1 ^ η *
          Real.exp (Real.log (B 0) * Real.log (B 1) / Real.log (boxSize F B)) := h
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) hBη) hexp
          (Real.exp_pos _).le (mul_nonneg (le_max_right _ _) hBη)
  intro F hF hA B hB0 hB1 m hm hm0
  rcases le_total (B 0) (B 1) with h01 | h10
  · rw [max_eq_right h01]; exact key F hF hA B hB0 h01 m hm hm0
  · rw [max_eq_left h10]
    set e : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
    set F' := rename e F
    set B' : Fin 2 → ℝ := fun i => B (e i)
    set m' := Finsupp.mapDomain e m
    have he0 : e 0 = 1 := Equiv.swap_apply_left _ _
    have he1 : e 1 = 0 := Equiv.swap_apply_right _ _
    have hm'0 : m' 0 = m 1 := by
      rw [← he1]; exact Finsupp.mapDomain_apply_of_injective e.injective m 1
    have hm'1 : m' 1 = m 0 := by
      rw [← he0]; exact Finsupp.mapDomain_apply_of_injective e.injective m 0
    have hF' : F'.totalDegree = d := by
      rw [← hF]; exact totalDegree_renameEquiv e F
    have hA' : AbsIrred F' := by
      unfold AbsIrred at hA ⊢
      rw [map_rename]
      exact (MulEquiv.irreducible_iff (renameEquiv (AlgebraicClosure ℚ) e).toMulEquiv).mpr hA
    have hmem : m' ∈ F'.support := by
      rw [mem_support_iff, coeff_rename_mapDomain e e.injective]; exact mem_support_iff.mp hm
    have hm'ne : m' ≠ 0 := by
      intro h'
      apply hm0; ext i; fin_cases i
      · simp [← hm'1, h']
      · simp [← hm'0, h']
    have hk := key F' hF' hA' B' (by simp [B', he0]; exact hB1) (by simp [B', he0, he1]; exact h10)
      m' hmem hm'ne
    simp only [B', he0, he1, hm'0, hm'1] at hk
    have hcard : (boxZeros F B).card ≤ (boxZeros F' B').card := by
      classical
      refine Finset.card_le_card_of_injOn (fun x => x ∘ e) ?_ ?_
      · intro x hx
        simp only [boxZeros, boxPts, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_coe]
          at hx ⊢
        refine ⟨fun i => hx.1 (e i), ?_⟩
        rw [eval_rename]
        have hxe : (x ∘ e) ∘ e = x := by funext i; simp [e]
        rw [hxe]; exact hx.2
      · intro x _ y _ hxy
        funext i
        have := congrFun hxy (e i)
        simpa [e] using this
    calc ((boxZeros F B).card : ℝ) ≤ (boxZeros F' B').card := by exact_mod_cast hcard
      _ ≤ _ := hk
      _ = _ := by rw [mul_comm (Real.log (B 1)), add_comm ((m 1 : ℝ) * _)]

/-- Turning `C₀ M^η e^E` with `M ≤ 4N`, `E ≤ c + log N / 4` into `C N^{1/4+η}`. -/
private lemma finish_bound {N C₀ η c M E x : ℝ} (hN : 1 ≤ N) (hC₀ : 0 ≤ C₀) (hη : 0 < η)
    (hM0 : 0 ≤ M) (hM : M ≤ 4 * N) (hE : E ≤ c + Real.log N / 4)
    (hx : x ≤ C₀ * M ^ η * Real.exp E) :
    x ≤ C₀ * 4 ^ η * Real.exp c * N ^ ((1 : ℝ) / 4 + η) := by
  have hN0 : 0 < N := by linarith
  have h1 : M ^ η ≤ 4 ^ η * N ^ η := by
    rw [← Real.mul_rpow (by norm_num) hN0.le]
    exact Real.rpow_le_rpow hM0 hM hη.le
  have h2 : Real.exp E ≤ Real.exp c * N ^ ((1 : ℝ) / 4) := by
    rw [Real.rpow_def_of_pos hN0, ← Real.exp_add]
    apply Real.exp_le_exp.mpr; linarith
  have h3 : N ^ ((1 : ℝ) / 4 + η) = N ^ ((1 : ℝ) / 4) * N ^ η := Real.rpow_add hN0 _ _
  calc x ≤ C₀ * M ^ η * Real.exp E := hx
    _ ≤ C₀ * (4 ^ η * N ^ η) * (Real.exp c * N ^ ((1 : ℝ) / 4)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h1 hC₀) h2 (Real.exp_pos _).le
        exact mul_nonneg hC₀ (by positivity)
    _ = _ := by rw [h3]; ring

/-- Final assembly of a planar row: a box bound for `H` with a good exponent. -/
private lemma shell_row {n : Mode} {Δ z : ℕ} {s2 s3 : ℤ} {g T : ℕ} {H : MvPolynomial (Fin 2) ℤ}
    (hH : ShellHyp n Δ z g T) {C₀ c E ε : ℝ} (hC₀ : 0 ≤ C₀) (hε : 0 < ε)
    (hbox : ((boxZeros H (projBox n g T)).card : ℝ) ≤
      C₀ * max (2 * (T : ℝ) / g) (4 * g * absk n / T) ^ ε * Real.exp E)
    (hE : E ≤ c + Real.log (absk n) / 4) :
    (curveCount n Δ z s2 s3 g T H : ℝ) ≤
      2 * C₀ * 4 ^ ε * Real.exp c * absk n ^ ((1 : ℝ) / 4 + ε) := by
  obtain ⟨hN1, -, -, -, hB0, -, hB0N, hB1N, -⟩ := shell_facts hH
  have h2 : (curveCount n Δ z s2 s3 g T H : ℝ) ≤ 2 * (boxZeros H (projBox n g T)).card := by
    exact_mod_cast count_le_proj n Δ z s2 s3 g T H hH
  refine finish_bound hN1 (by positivity) hε (le_trans (by norm_num) (le_max_of_le_left hB0))
    (max_le hB0N hB1N) hE ?_
  calc (curveCount n Δ z s2 s3 g T H : ℝ) ≤ 2 * (boxZeros H (projBox n g T)).card := h2
    _ ≤ 2 * (C₀ * max (2 * (T : ℝ) / g) (4 * g * absk n / T) ^ ε * Real.exp E) := by
        linarith
    _ = _ := by ring

/-- The counted points lie in `shellPts`. -/
private lemma mem_curve {n : Mode} {Δ z : ℕ} {s2 s3 : ℤ} {g T : ℕ} {H : MvPolynomial (Fin 2) ℤ}
    {k : Mode} (hk : k ∈ (shellPts n Δ z s2 s3 g T).filter
      (fun k => eval (projPt Δ s2 g n k) H = 0)) :
    k ∈ shellPts n Δ z s2 s3 g T ∧ eval (projPt Δ s2 g n k) H = 0 :=
  Finset.mem_filter.mp hk

private lemma shellPts_sub {n : Mode} {Δ z : ℕ} {s2 s3 : ℤ} {g T : ℕ} {k : Mode}
    (hk : k ∈ shellPts n Δ z s2 s3 g T) :
    k ∈ activePts n s2 s3 ∧ caOf Δ z (n 2) (tOf Δ s2 n k) ≠ 0 := by
  classical
  simp only [shellPts, Finset.mem_filter] at hk
  exact ⟨hk.1.1, hk.2.2.2⟩

private lemma projPt_spec {n : Mode} {s2 s3 : ℤ} {Δ z g T : ℕ} (hH : ShellHyp n Δ z g T)
    {k : Mode} (hk : k ∈ shellPts n Δ z s2 s3 g T) :
    (g : ℤ) * projPt Δ s2 g n k 0 = tOf Δ s2 n k ∧ n 2 * projPt Δ s2 g n k 1 = g * k 2 := by
  have h := surfPt_spec hH hk 0
  exact ⟨h.1, h.2.1⟩

private lemma totalDegree_mapQ (H : MvPolynomial (Fin 2) ℤ) :
    (MvPolynomial.map (Int.castRingHom ℚ) H).totalDegree = H.totalDegree := by
  rw [totalDegree, totalDegree,
    support_map_of_injective H (RingHom.injective_int (Int.castRingHom ℚ))]

private lemma one_le_totalDegree (H : MvPolynomial (Fin 2) ℤ)
    (hirr : Irreducible (MvPolynomial.map (Int.castRingHom ℚ) H)) : 1 ≤ H.totalDegree := by
  by_contra h
  have h0 : (MvPolynomial.map (Int.castRingHom ℚ) H).totalDegree = 0 := by
    rw [totalDegree_mapQ]; omega
  have hc := totalDegree_eq_zero_iff_eq_C.mp h0
  set c := (MvPolynomial.map (Int.castRingHom ℚ) H).coeff 0
  rw [hc] at hirr
  by_cases hc0 : c = 0
  · rw [hc0, map_zero] at hirr; exact not_irreducible_zero hirr
  · exact hirr.not_isUnit ((Ne.isUnit hc0).map C)

/-- `U = u(X₁)` in `ℤ[s, Y]` (`s = X 0`). -/
private def liftU (u : Polynomial ℤ) : MvPolynomial (Fin 2) ℤ := Polynomial.eval₂ C (X 0) u

/-- `a² · 2gL` along the parametrized curve `a X₁ = u(s)`, `X₂ = s`. -/
private def liftTg (Δ z n3 s3 g a : ℤ) (u : Polynomial ℤ) : MvPolynomial (Fin 2) ℤ :=
  -C (2 * Δ * g ^ 2) * liftU u ^ 2 * X 0 - C (Δ * g ^ 3) * liftU u ^ 2
    - C (2 * Δ * g ^ 2 * s3 * z * a) * liftU u - C (a ^ 2 * Δ * g * z ^ 2)
    - C (2 * a ^ 2 * n3 ^ 2) * X 0

/-- `a · x` along the curve. -/
private def liftXx (z s3 g a : ℤ) (u : Polynomial ℤ) : MvPolynomial (Fin 2) ℤ :=
  C g * liftU u + C (a * s3 * z) + liftU u * X 0

/-- The lifted plane curve `Φ(s, X₃) = a⁴ F(u(s)/a, s, X₃)`. -/
private def liftPoly (Δ z n3 ni nj s3 g a : ℤ) (u : Polynomial ℤ) : MvPolynomial (Fin 2) ℤ :=
  C (4 * g ^ 2 * nj ^ 2 * a ^ 4) * X 1 ^ 2 +
    (liftTg Δ z n3 s3 g a u - C (2 * g * ni * a ^ 2) * X 1) ^ 2
    + C (4 * nj ^ 2 * n3 ^ 2 * a ^ 4) * X 0 ^ 2
    - C (4 * g ^ 2 * nj ^ 2 * Δ * a ^ 2) * liftXx z s3 g a u ^ 2

/-- `a² · 2gL` as a polynomial in `s`. -/
private def tgP (Δ z n3 s3 g a : ℤ) (u : Polynomial ℤ) : Polynomial ℤ :=
  -Polynomial.C (2 * Δ * g ^ 2) * u ^ 2 * Polynomial.X - Polynomial.C (Δ * g ^ 3) * u ^ 2
    - Polynomial.C (2 * Δ * g ^ 2 * s3 * z * a) * u - Polynomial.C (a ^ 2 * Δ * g * z ^ 2)
    - Polynomial.C (2 * a ^ 2 * n3 ^ 2) * Polynomial.X

/-- `a · x` as a polynomial in `s`. -/
private def xxP (z s3 g a : ℤ) (u : Polynomial ℤ) : Polynomial ℤ :=
  Polynomial.C g * u + Polynomial.C (a * s3 * z) + u * Polynomial.X

/-- The radicand: `|n_h|² Φ = (2g|n_h|²a² Y − n_i tg)² − n_j² PP`. -/
private def PP (Δ z n3 ni nj s3 g a : ℤ) (u : Polynomial ℤ) : Polynomial ℤ :=
  -(tgP Δ z n3 s3 g a u) ^ 2
    - Polynomial.C (4 * (ni ^ 2 + nj ^ 2) * n3 ^ 2 * a ^ 4) * Polynomial.X ^ 2
    + Polynomial.C (4 * (ni ^ 2 + nj ^ 2) * g ^ 2 * Δ * a ^ 2) * (xxP z s3 g a u) ^ 2

private lemma eval_liftU (u : Polynomial ℤ) (y : Fin 2 → ℤ) : eval y (liftU u) = u.eval (y 0) := by
  unfold liftU
  rw [Polynomial.hom_eval₂, RingHom.ext_int ((eval y).comp C) (RingHom.id ℤ), eval_X]
  rfl

private lemma eval_tg (Δ z n3 s3 g a : ℤ) (u : Polynomial ℤ) (y : Fin 2 → ℤ) :
    eval y (liftTg Δ z n3 s3 g a u) = (tgP Δ z n3 s3 g a u).eval (y 0) := by
  simp only [liftTg, tgP, map_sub, map_mul, map_neg, map_pow, eval_C, eval_X,
    eval_liftU, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_neg, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]

private lemma eval_xx (z s3 g a : ℤ) (u : Polynomial ℤ) (y : Fin 2 → ℤ) :
    eval y (liftXx z s3 g a u) = (xxP z s3 g a u).eval (y 0) := by
  simp only [liftXx, xxP, map_add, map_mul, eval_C, eval_X, eval_liftU, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

/-- The lift is `a⁴ F` on the curve. -/
private lemma eval_lift_surface (Δ z n3 ni nj s3 g a : ℤ) (u : Polynomial ℤ) (x : Fin 3 → ℤ)
    (hx : a * x 0 = u.eval (x 1)) :
    eval ![x 1, x 2] (liftPoly Δ z n3 ni nj s3 g a u) =
      a ^ 4 * eval x (surfacePoly Δ z n3 ni nj s3 g) := by
  simp only [liftPoly, liftTg, liftXx, surfacePoly, map_add, map_sub, map_mul, map_neg, map_pow,
    eval_C, eval_X, eval_liftU, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← hx]
  ring

/-- The J-form of the lift. -/
private lemma eval_lift_J (Δ z n3 ni nj s3 g a : ℤ) (u : Polynomial ℤ) (y : Fin 2 → ℤ) :
    (ni ^ 2 + nj ^ 2) * eval y (liftPoly Δ z n3 ni nj s3 g a u) =
      (2 * g * (ni ^ 2 + nj ^ 2) * a ^ 2 * y 1 - ni * (tgP Δ z n3 s3 g a u).eval (y 0)) ^ 2 -
        nj ^ 2 * (PP Δ z n3 ni nj s3 g a u).eval (y 0) := by
  have h1 := eval_tg Δ z n3 s3 g a u y
  have h2 := eval_xx z s3 g a u y
  simp only [liftPoly, map_add, map_sub, map_mul, map_pow, eval_C, eval_X, h1, h2, PP,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_neg,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  ring

section Deg
open Polynomial

private lemma nd_add {p q : ℤ[X]} {n : ℕ} (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    (p + q).natDegree ≤ n := (natDegree_add_le _ _).trans (max_le hp hq)

private lemma nd_sub {p q : ℤ[X]} {n : ℕ} (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    (p - q).natDegree ≤ n := (natDegree_sub_le _ _).trans (max_le hp hq)

private lemma nd_Cmul {p : ℤ[X]} {n : ℕ} (c : ℤ) (hp : p.natDegree ≤ n) :
    (Polynomial.C c * p).natDegree ≤ n := (natDegree_C_mul_le _ _).trans hp

private lemma nd_mul {p q : ℤ[X]} {a b n : ℕ} (hp : p.natDegree ≤ a) (hq : q.natDegree ≤ b)
    (h : a + b ≤ n) : (p * q).natDegree ≤ n := (natDegree_mul_le).trans (by omega)

private lemma nd_C (c : ℤ) (n : ℕ) : (Polynomial.C c).natDegree ≤ n := by rw [natDegree_C]; omega

private lemma nd_X {n : ℕ} (h : 1 ≤ n) : (Polynomial.X : ℤ[X]).natDegree ≤ n :=
  natDegree_X_le.trans h

private lemma nd_pow {p : ℤ[X]} {a n : ℕ} (k : ℕ) (hp : p.natDegree ≤ a) (h : k * a ≤ n) :
    (p ^ k).natDegree ≤ n := natDegree_pow_le.trans ((Nat.mul_le_mul_left k hp).trans h)

private lemma xxP_deg (z s3 g a : ℤ) (u : ℤ[X]) : (xxP z s3 g a u).natDegree ≤ u.natDegree + 1 :=
  nd_add (nd_add (nd_Cmul _ (by omega)) (nd_C _ _)) (nd_mul le_rfl natDegree_X_le le_rfl)

private lemma tgP_deg (Δ z n3 s3 g a : ℤ) (u : ℤ[X]) (hΔ : Δ ≠ 0) (hg : g ≠ 0)
    (hm : 1 ≤ u.natDegree) :
    (tgP Δ z n3 s3 g a u).natDegree = 2 * u.natDegree + 1 ∧
      (tgP Δ z n3 s3 g a u).leadingCoeff = -(2 * Δ * g ^ 2) * u.leadingCoeff ^ 2 := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hm
  set m := u.natDegree
  set A : ℤ[X] := -(Polynomial.C (2 * Δ * g ^ 2) * (u ^ 2 * Polynomial.X))
  set R : ℤ[X] := -Polynomial.C (Δ * g ^ 3) * u ^ 2 -
    Polynomial.C (2 * Δ * g ^ 2 * s3 * z * a) * u -
    Polynomial.C (a ^ 2 * Δ * g * z ^ 2) - Polynomial.C (2 * a ^ 2 * n3 ^ 2) * Polynomial.X
  have he : tgP Δ z n3 s3 g a u = R + A := by simp only [tgP, R, A]; ring
  have hc : (2 * Δ * g ^ 2) ≠ 0 := by positivity
  have hA : A.natDegree = 2 * m + 1 := by
    simp only [A, natDegree_neg]
    rw [natDegree_C_mul hc, natDegree_mul (pow_ne_zero 2 hu0) X_ne_zero, natDegree_pow,
      natDegree_X]
  have hAl : A.leadingCoeff = -(2 * Δ * g ^ 2) * u.leadingCoeff ^ 2 := by
    simp only [A, leadingCoeff_neg, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_pow,
      leadingCoeff_X, mul_one, neg_mul]
  have hR : R.natDegree ≤ 2 * m := by
    have h2 : (u ^ 2).natDegree ≤ 2 * m := nd_pow 2 le_rfl le_rfl
    refine nd_sub (nd_sub (nd_sub ?_ (nd_Cmul _ (by omega))) (nd_C _ _))
      (nd_Cmul _ (nd_X (by omega)))
    rw [← map_neg]; exact nd_Cmul _ h2
  have hlt : R.natDegree < A.natDegree := by omega
  rw [he]
  refine ⟨by rw [natDegree_add_eq_right_of_natDegree_lt hlt, hA], ?_⟩
  rw [leadingCoeff_add_of_degree_lt (degree_lt_degree hlt), hAl]

private lemma PP_deg (Δ z n3 ni nj s3 g a : ℤ) (u : ℤ[X]) (hΔ : Δ ≠ 0) (hg : g ≠ 0)
    (hm : 1 ≤ u.natDegree) :
    (PP Δ z n3 ni nj s3 g a u).natDegree = 4 * u.natDegree + 2 ∧
      (PP Δ z n3 ni nj s3 g a u).leadingCoeff = -((2 * Δ * g ^ 2) * u.leadingCoeff ^ 2) ^ 2 := by
  obtain ⟨hd, hl⟩ := tgP_deg Δ z n3 s3 g a u hΔ hg hm
  set t := tgP Δ z n3 s3 g a u
  set m := u.natDegree
  have ht0 : t ≠ 0 := by intro h; rw [h] at hd; simp at hd
  set A : ℤ[X] := -(t ^ 2)
  set R : ℤ[X] := -Polynomial.C (4 * (ni ^ 2 + nj ^ 2) * n3 ^ 2 * a ^ 4) * Polynomial.X ^ 2 +
    Polynomial.C (4 * (ni ^ 2 + nj ^ 2) * g ^ 2 * Δ * a ^ 2) * (xxP z s3 g a u) ^ 2
  have he : PP Δ z n3 ni nj s3 g a u = R + A := by simp only [PP, R, A, t]; ring
  have hA : A.natDegree = 4 * m + 2 := by
    simp only [A, natDegree_neg, natDegree_pow, hd]; ring
  have hR : R.natDegree ≤ 2 * m + 2 := by
    refine nd_add ?_ (nd_Cmul _ (nd_pow 2 (xxP_deg z s3 g a u) (by omega)))
    rw [← map_neg]; exact nd_Cmul _ (nd_pow 2 natDegree_X_le (by omega))
  have hlt : R.natDegree < A.natDegree := by omega
  rw [he]
  refine ⟨by rw [natDegree_add_eq_right_of_natDegree_lt hlt, hA], ?_⟩
  rw [leadingCoeff_add_of_degree_lt (degree_lt_degree hlt)]
  simp only [A, leadingCoeff_neg, leadingCoeff_pow, hl]
  ring

end Deg

/-- Keep the pure-`s` part of a polynomial in `ℤ[s, Y]`. -/
private def sPart : MvPolynomial (Fin 2) ℤ →ₐ[ℤ] Polynomial ℤ :=
  aeval fun i => if i = 0 then Polynomial.X else 0

private lemma coeff_sPart (p : MvPolynomial (Fin 2) ℤ) (a : ℕ) :
    (sPart p).coeff a = p.coeff (Finsupp.single 0 a) := by
  induction p using MvPolynomial.induction_on' with
  | monomial m r =>
    simp only [sPart, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Fin.prod_univ_two, coeff_monomial]
    simp only [Fin.isValue, ↓reduceIte, one_ne_zero]
    by_cases h : m = Finsupp.single 0 a
    · subst h; simp
    · rw [ite_eq_right_iff.mpr (fun h' => absurd h' h)]
      have hm : ¬ (m 0 = a ∧ m 1 = 0) := by
        rintro ⟨h0, h1⟩
        apply h
        ext i
        fin_cases i <;> simp [h0, h1]
      by_cases h1 : m 1 = 0
      · rw [h1]
        rw [Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          Polynomial.coeff_C_mul, pow_zero, mul_one, Polynomial.coeff_X_pow]
        simp [show a ≠ m 0 from fun h' => hm ⟨h'.symm, h1⟩]
      · rw [zero_pow h1]; simp
  | add p q hp hq => simp [hp, hq]

private lemma sPart_C (c : ℤ) : sPart (C c) = Polynomial.C c := by
  simp [sPart]

private lemma sPart_X0 : sPart (X 0) = Polynomial.X := by simp [sPart]

private lemma sPart_X1 : sPart (X 1) = 0 := by simp [sPart]

private lemma sPart_liftU (u : Polynomial ℤ) : sPart (liftU u) = u := by
  unfold liftU
  have := Polynomial.hom_eval₂ u C (sPart : MvPolynomial (Fin 2) ℤ →+* Polynomial ℤ) (X 0)
  simp only [RingHom.coe_coe] at this
  rw [this, RingHom.ext_int ((sPart : MvPolynomial (Fin 2) ℤ →+* Polynomial ℤ).comp C)
    Polynomial.C, sPart_X0, Polynomial.eval₂_C_X]

private lemma sPart_lift (Δ z n3 ni nj s3 g a : ℤ) (u : Polynomial ℤ) :
    sPart (liftPoly Δ z n3 ni nj s3 g a u) = (tgP Δ z n3 s3 g a u) ^ 2 +
      Polynomial.C (4 * nj ^ 2 * n3 ^ 2 * a ^ 4) * Polynomial.X ^ 2 -
      Polynomial.C (4 * g ^ 2 * nj ^ 2 * Δ * a ^ 2) * (xxP z s3 g a u) ^ 2 := by
  simp only [liftPoly, liftTg, liftXx, tgP, xxP, map_add, map_sub, map_mul, map_neg, map_pow,
    sPart_C, sPart_X0, sPart_X1, sPart_liftU]
  ring

private lemma lift_coeff_top (Δ z n3 ni nj s3 g a : ℤ) (u : Polynomial ℤ) (hΔ : Δ ≠ 0)
    (hg : g ≠ 0) (hm : 1 ≤ u.natDegree) :
    (liftPoly Δ z n3 ni nj s3 g a u).coeff (Finsupp.single 0 (4 * u.natDegree + 2)) =
      ((2 * Δ * g ^ 2) * u.leadingCoeff ^ 2) ^ 2 := by
  rw [← coeff_sPart, sPart_lift]
  obtain ⟨hd, hl⟩ := tgP_deg Δ z n3 s3 g a u hΔ hg hm
  set t := tgP Δ z n3 s3 g a u
  have hR : (Polynomial.C (4 * nj ^ 2 * n3 ^ 2 * a ^ 4) * Polynomial.X ^ 2 -
      Polynomial.C (4 * g ^ 2 * nj ^ 2 * Δ * a ^ 2) * (xxP z s3 g a u) ^ 2).natDegree <
        4 * u.natDegree + 2 := by
    have : (Polynomial.C (4 * nj ^ 2 * n3 ^ 2 * a ^ 4) * Polynomial.X ^ 2 -
      Polynomial.C (4 * g ^ 2 * nj ^ 2 * Δ * a ^ 2) * (xxP z s3 g a u) ^ 2).natDegree ≤
        2 * u.natDegree + 2 :=
      nd_sub (nd_Cmul _ (nd_pow 2 Polynomial.natDegree_X_le (by omega)))
        (nd_Cmul _ (nd_pow 2 (xxP_deg z s3 g a u) (by omega)))
    omega
  rw [add_sub_assoc, Polynomial.coeff_add, Polynomial.coeff_eq_zero_of_natDegree_lt hR,
    add_zero]
  have ht2 : (t ^ 2).natDegree = 4 * u.natDegree + 2 := by
    rw [Polynomial.natDegree_pow, hd]; ring
  rw [← ht2, Polynomial.coeff_natDegree, Polynomial.leadingCoeff_pow, hl]
  ring

private lemma td_add {p q : MvPolynomial (Fin 2) ℤ} {n : ℕ} (hp : p.totalDegree ≤ n)
    (hq : q.totalDegree ≤ n) : (p + q).totalDegree ≤ n :=
  (totalDegree_add p q).trans (max_le hp hq)

private lemma td_sub {p q : MvPolynomial (Fin 2) ℤ} {n : ℕ} (hp : p.totalDegree ≤ n)
    (hq : q.totalDegree ≤ n) : (p - q).totalDegree ≤ n :=
  (totalDegree_sub p q).trans (max_le hp hq)

private lemma td_mul {p q : MvPolynomial (Fin 2) ℤ} {a b n : ℕ} (hp : p.totalDegree ≤ a)
    (hq : q.totalDegree ≤ b) (h : a + b ≤ n) : (p * q).totalDegree ≤ n :=
  (totalDegree_mul p q).trans (by omega)

private lemma td_pow {p : MvPolynomial (Fin 2) ℤ} {a n : ℕ} (k : ℕ) (hp : p.totalDegree ≤ a)
    (h : k * a ≤ n) : (p ^ k).totalDegree ≤ n :=
  (totalDegree_pow p k).trans ((Nat.mul_le_mul_left k hp).trans h)

private lemma td_C (c : ℤ) (n : ℕ) : (C c : MvPolynomial (Fin 2) ℤ).totalDegree ≤ n := by
  rw [totalDegree_C]; omega

private lemma td_Cmul {p : MvPolynomial (Fin 2) ℤ} {n : ℕ} (c : ℤ) (hp : p.totalDegree ≤ n) :
    (C c * p).totalDegree ≤ n := td_mul (td_C c 0) hp (by omega)

private lemma td_X (i : Fin 2) {n : ℕ} (h : 1 ≤ n) :
    (X i : MvPolynomial (Fin 2) ℤ).totalDegree ≤ n :=
  (totalDegree_X i).le.trans h

private lemma td_liftU (u : Polynomial ℤ) : (liftU u).totalDegree ≤ u.natDegree := by
  unfold liftU
  rw [Polynomial.eval₂_eq_sum_range]
  refine totalDegree_finsetSum_le fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  refine td_Cmul _ ?_
  rw [totalDegree_X_pow]; omega

private lemma td_lift (Δ z n3 ni nj s3 g a : ℤ) (u : Polynomial ℤ) (hm : 1 ≤ u.natDegree) :
    (liftPoly Δ z n3 ni nj s3 g a u).totalDegree ≤ 4 * u.natDegree + 2 := by
  have hU := td_liftU u
  set m := u.natDegree
  have hU2 : (liftU u ^ 2).totalDegree ≤ 2 * m := td_pow 2 hU le_rfl
  have htg : (liftTg Δ z n3 s3 g a u).totalDegree ≤ 2 * m + 1 := by
    unfold liftTg
    refine td_sub (td_sub (td_sub (td_sub ?_ ?_) (td_Cmul _ (hU.trans (by omega))))
      (td_C _ _)) (td_Cmul _ (td_X 0 (by omega)))
    · rw [← map_neg]; exact td_mul (td_Cmul _ hU2) (td_X 0 le_rfl) le_rfl
    · exact td_Cmul _ (hU2.trans (by omega))
  have hxx : (liftXx z s3 g a u).totalDegree ≤ m + 1 := by
    unfold liftXx
    exact td_add (td_add (td_Cmul _ (hU.trans (by omega))) (td_C _ _))
      (td_mul hU (td_X 0 le_rfl) le_rfl)
  unfold liftPoly
  refine td_sub (td_add (td_add ?_ ?_) ?_) ?_
  · exact td_Cmul _ (td_pow 2 (td_X 1 le_rfl) (by omega))
  · exact td_pow 2 (td_sub htg (td_Cmul _ (td_X 1 (by omega)))) (by omega)
  · exact td_Cmul _ (td_pow 2 (td_X 0 le_rfl) (by omega))
  · exact td_Cmul _ (td_pow 2 hxx (by omega))

private lemma lift_deg (Δ z n3 ni nj s3 g a : ℤ) (u : Polynomial ℤ) (hΔ : Δ ≠ 0)
    (hg : g ≠ 0) (hm : 1 ≤ u.natDegree) :
    (liftPoly Δ z n3 ni nj s3 g a u).totalDegree = 4 * u.natDegree + 2 ∧
      Finsupp.single 0 (4 * u.natDegree + 2) ∈ (liftPoly Δ z n3 ni nj s3 g a u).support := by
  have hu0 : u.leadingCoeff ≠ 0 := by
    rw [Polynomial.leadingCoeff_ne_zero]; rintro rfl; simp at hm
  have hmem : Finsupp.single 0 (4 * u.natDegree + 2) ∈
      (liftPoly Δ z n3 ni nj s3 g a u).support := by
    rw [mem_support_iff, lift_coeff_top Δ z n3 ni nj s3 g a u hΔ hg hm]
    have : (2 * Δ * g ^ 2) ≠ 0 := by positivity
    positivity
  refine ⟨le_antisymm (td_lift Δ z n3 ni nj s3 g a u hm) ?_, hmem⟩
  have := le_totalDegree hmem
  rwa [Finsupp.sum_single_index rfl] at this

open Polynomial in
/-- Irreducibility transfers along the triangular change `k ↦ α(Y + φ(t))`. -/
private theorem irred_of_shear {K : Type*} [_root_.Field K] (α : K) (hα : α ≠ 0) (φ : K[X])
    (G : MvPolynomial (Fin 2) K)
    (h : Irreducible (MvPolynomial.eval₂Hom (Polynomial.C.comp Polynomial.C)
      (![Polynomial.C Polynomial.X, Polynomial.C (Polynomial.C α) *
        (Polynomial.X + Polynomial.C φ)]) G)) :
    Irreducible G := by
  set Φ : MvPolynomial (Fin 2) K →+* K[X][X] :=
    MvPolynomial.eval₂Hom (Polynomial.C.comp Polynomial.C) (![Polynomial.C Polynomial.X,
      Polynomial.C (Polynomial.C α) * (Polynomial.X + Polynomial.C φ)]) with hΦ
  set ψ0 : K[X] →+* MvPolynomial (Fin 2) K :=
    Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0) with hψ0
  set Ψ : K[X][X] →+* MvPolynomial (Fin 2) K :=
    Polynomial.eval₂RingHom ψ0 (MvPolynomial.C α⁻¹ * MvPolynomial.X 1 - ψ0 φ) with hΨ
  have hΦψ0 : ∀ p : K[X], Φ (ψ0 p) = Polynomial.C p := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
    | monomial n a => simp [ψ0, Φ, ← Polynomial.C_mul_X_pow_eq_monomial]
  have h1 : Φ.comp Ψ = RingHom.id _ := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext
      · intro a; simp [Ψ, Φ, ψ0]
      · simp [Ψ, Φ, ψ0]
    · simp only [RingHom.comp_apply, Ψ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, map_sub,
        map_mul, hΦψ0,
        RingHom.id_apply]
      simp only [Φ, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X,
        RingHom.comp_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [← mul_assoc, ← map_mul, ← map_mul, inv_mul_cancel₀ hα, map_one, map_one, one_mul]
      ring
  have h2 : Ψ.comp Φ = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [Ψ, Φ, ψ0]
    · intro i
      fin_cases i
      · simp [Ψ, Φ, ψ0]
      · simp only [RingHom.comp_apply, Φ, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
        simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, map_mul,
          map_add, RingHom.id_apply, Ψ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
          Polynomial.eval₂_X]
        have : ψ0 (Polynomial.C α) = MvPolynomial.C α := by simp [ψ0]
        rw [this, sub_add_cancel, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hα, map_one, one_mul]
  exact (MulEquiv.irreducible_iff (RingEquiv.ofRingHom Φ Ψ h1 h2)).mp h

/-- The radicand `n_j² PP`. -/
private def radP (Δ z n3 ni nj s3 g a : ℤ) (u : Polynomial ℤ) : Polynomial ℤ :=
  Polynomial.C (nj ^ 2) * PP Δ z n3 ni nj s3 g a u

private lemma map_liftU {K : Type*} [CommRing K] (ι : ℤ →+* K)
    (Φ : MvPolynomial (Fin 2) K →+* Polynomial (Polynomial K))
    (hΦ0 : Φ (MvPolynomial.X 0) = Polynomial.C Polynomial.X) (u : Polynomial ℤ) :
    Φ (MvPolynomial.map ι (liftU u)) = Polynomial.C (u.map ι) := by
  unfold liftU
  have h := Polynomial.hom_eval₂ u MvPolynomial.C (Φ.comp (MvPolynomial.map ι)) (MvPolynomial.X 0)
  rw [RingHom.comp_apply] at h
  rw [h, RingHom.ext_int ((Φ.comp (MvPolynomial.map ι)).comp MvPolynomial.C)
    (Polynomial.C.comp (Polynomial.C.comp ι)), RingHom.comp_apply, MvPolynomial.map_X, hΦ0,
    ← Polynomial.hom_eval₂]
  rfl

open Polynomial in
private theorem lift_absIrred (Δ z n3 ni nj s3 g a : ℤ) (u : Polynomial ℤ) (hg : g ≠ 0)
    (ha : a ≠ 0) (hnj : nj ≠ 0)
    (h : Irreducible ((Polynomial.X : (AlgebraicClosure ℚ)[X][X]) ^ 2 - Polynomial.C
      (((radP Δ z n3 ni nj s3 g a u).map (Int.castRingHom ℚ)).map
        (algebraMap ℚ (AlgebraicClosure ℚ))))) :
    AbsIrred (liftPoly Δ z n3 ni nj s3 g a u) := by
  set K := AlgebraicClosure ℚ
  set ι := Int.castRingHom K
  have hmap : ((radP Δ z n3 ni nj s3 g a u).map (Int.castRingHom ℚ)).map (algebraMap ℚ K) =
      (radP Δ z n3 ni nj s3 g a u).map ι := by
    rw [Polynomial.map_map]; congr 1
  rw [hmap] at h
  have hh : ((ni ^ 2 + nj ^ 2 : ℤ) : K) ≠ 0 := by
    have : ni ^ 2 + nj ^ 2 ≠ 0 := by positivity
    exact_mod_cast this
  have hc1 : ((2 * g * (ni ^ 2 + nj ^ 2) * a ^ 2 : ℤ) : K) ≠ 0 := by
    have : 2 * g * (ni ^ 2 + nj ^ 2) * a ^ 2 ≠ 0 := by positivity
    exact_mod_cast this
  set α : K := ((2 * g * (ni ^ 2 + nj ^ 2) * a ^ 2 : ℤ) : K)⁻¹
  set τ : K[X] := (tgP Δ z n3 s3 g a u).map ι
  set ξ : K[X] := (xxP z s3 g a u).map ι
  set υ : K[X] := u.map ι
  set Φ : MvPolynomial (Fin 2) K →+* K[X][X] :=
    MvPolynomial.eval₂Hom (Polynomial.C.comp Polynomial.C)
      (![Polynomial.C Polynomial.X, Polynomial.C (Polynomial.C α) *
        (Polynomial.X + Polynomial.C (Polynomial.C (ι ni) * τ))])
  have hΦ0 : Φ (MvPolynomial.X 0) = Polynomial.C Polynomial.X := by
    simp [Φ]
  have hΦC : ∀ c : ℤ, Φ (MvPolynomial.map ι (MvPolynomial.C c)) =
      Polynomial.C (Polynomial.C (ι c)) := by
    intro c; simp [Φ]
  have hU := map_liftU ι Φ hΦ0 u
  have hT : Φ (MvPolynomial.map ι (liftTg Δ z n3 s3 g a u)) = Polynomial.C τ := by
    simp only [liftTg, map_sub, map_mul, map_neg, map_pow, hU, hΦC, MvPolynomial.map_X,
      hΦ0, τ, tgP, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_neg, Polynomial.map_pow,
      Polynomial.map_C, Polynomial.map_X]
  have hX' : Φ (MvPolynomial.map ι (liftXx z s3 g a u)) = Polynomial.C ξ := by
    simp only [liftXx, map_add, map_mul, hU, hΦC, MvPolynomial.map_X, hΦ0, ξ, xxP,
      Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
  have hΦ1 : Φ (MvPolynomial.X 1) = Polynomial.C (Polynomial.C α) *
      (Polynomial.X + Polynomial.C (Polynomial.C (ι ni) * τ)) := by
    simp [Φ]
  have hA : Polynomial.C (Polynomial.C α) *
      Polynomial.C (Polynomial.C (ι (2 * g * (ni ^ 2 + nj ^ 2) * a ^ 2))) = (1 : K[X][X]) := by
    rw [← map_mul, ← map_mul, eq_intCast, inv_mul_cancel₀ hc1, map_one, map_one]
  have key : Φ (MvPolynomial.map ι (liftPoly Δ z n3 ni nj s3 g a u)) *
      Polynomial.C (Polynomial.C (ι (ni ^ 2 + nj ^ 2))) =
        Polynomial.X ^ 2 - Polynomial.C ((radP Δ z n3 ni nj s3 g a u).map ι) := by
    simp only [liftPoly, map_add, map_sub, map_mul, map_pow, hT, hX', hΦC, MvPolynomial.map_X,
      hΦ0, hΦ1, radP, PP, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub,
      Polynomial.map_neg, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]
    rw [show (tgP Δ z n3 s3 g a u).map ι = τ from rfl, show (xxP z s3 g a u).map ι = ξ from rfl]
    simp only [map_mul, map_add, map_pow, map_ofNat, map_neg] at hA ⊢
    linear_combination (Polynomial.X + Polynomial.C (Polynomial.C (ι ni)) * Polynomial.C τ) *
      (Polynomial.C (Polynomial.C α) * (2 * Polynomial.C (Polynomial.C (ι g)) *
        (Polynomial.C (Polynomial.C (ι ni)) ^ 2 + Polynomial.C (Polynomial.C (ι nj)) ^ 2) *
          Polynomial.C (Polynomial.C (ι a)) ^ 2) *
        (Polynomial.X + Polynomial.C (Polynomial.C (ι ni)) * Polynomial.C τ) -
        Polynomial.C (Polynomial.C (ι ni)) * Polynomial.C τ + Polynomial.X) * hA
  have hu : IsUnit (Polynomial.C (Polynomial.C (ι (ni ^ 2 + nj ^ 2))) : K[X][X]) :=
    Polynomial.isUnit_C.mpr (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by simpa using hh)))
  rw [← key] at h
  exact irred_of_shear α (inv_ne_zero hc1) (Polynomial.C (ι ni) * τ) _
    ((irreducible_mul_isUnit hu).mp h)

private lemma radP_deg (Δ z n3 ni nj s3 g a : ℤ) (u : Polynomial ℤ) (hΔ : Δ ≠ 0) (hg : g ≠ 0)
    (hnj : nj ≠ 0) (hm : 1 ≤ u.natDegree) :
    (radP Δ z n3 ni nj s3 g a u).natDegree = 4 * u.natDegree + 2 ∧
      (radP Δ z n3 ni nj s3 g a u).leadingCoeff < 0 := by
  obtain ⟨hd, hl⟩ := PP_deg Δ z n3 ni nj s3 g a u hΔ hg hm
  have hnj2 : nj ^ 2 ≠ 0 := pow_ne_zero 2 hnj
  unfold radP
  refine ⟨by rw [Polynomial.natDegree_C_mul hnj2, hd], ?_⟩
  rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hl]
  have hu0 : u.leadingCoeff ≠ 0 := by
    rw [Polynomial.leadingCoeff_ne_zero]; rintro rfl; simp at hm
  have h1 : 0 < nj ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hnj2)
  have h2 : 0 < ((2 * Δ * g ^ 2) * u.leadingCoeff ^ 2) ^ 2 := by
    have : (2 * Δ * g ^ 2) * u.leadingCoeff ^ 2 ≠ 0 := by positivity
    positivity
  nlinarith

open Polynomial in
private lemma lift_sq_count (Δ z n3 ni nj s3 g a : ℤ) (u : Polynomial ℤ) (hΔ : Δ ≠ 0)
    (hg : g ≠ 0) (ha : a ≠ 0) (hnj : nj ≠ 0) (hm : 1 ≤ u.natDegree) (c : ℚ) (R : ℚ[X])
    (hcR : (radP Δ z n3 ni nj s3 g a u).map (Int.castRingHom ℚ) = Polynomial.C c * R ^ 2)
    (B : Fin 2 → ℝ) :
    (boxZeros (liftPoly Δ z n3 ni nj s3 g a u) B).card ≤ 2 * u.natDegree + 1 := by
  classical
  obtain ⟨hdeg, hcoef⟩ := radP_deg Δ z n3 ni nj s3 g a u hΔ hg hnj hm
  set Pz := radP Δ z n3 ni nj s3 g a u with hPz
  set Pq := Pz.map (Int.castRingHom ℚ) with hPq
  have hdegq : Pq.natDegree = 4 * u.natDegree + 2 := by
    rw [hPq, natDegree_map_eq_of_injective (RingHom.injective_int _), hdeg]
  have hcoefq : Pq.leadingCoeff < 0 := by
    rw [hPq, leadingCoeff_map_of_injective (RingHom.injective_int _), eq_intCast]
    exact_mod_cast hcoef
  have hc0 : c ≠ 0 := by rintro rfl; rw [hcR] at hdegq; simp at hdegq
  have hR0 : R ≠ 0 := by rintro rfl; rw [hcR] at hdegq; simp at hdegq
  have hRdeg : R.natDegree = 2 * u.natDegree + 1 := by
    rw [hcR, natDegree_C_mul hc0, natDegree_pow] at hdegq; omega
  have hc : c < 0 := by
    rw [hcR, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_pow] at hcoefq
    have : 0 < R.leadingCoeff ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (leadingCoeff_ne_zero.mpr hR0)))
    nlinarith
  have hpt : ∀ x ∈ boxZeros (liftPoly Δ z n3 ni nj s3 g a u) B,
      2 * g * (ni ^ 2 + nj ^ 2) * a ^ 2 * x 1 - ni * (tgP Δ z n3 s3 g a u).eval (x 0) = 0 ∧
        R.eval ((x 0 : ℤ) : ℚ) = 0 := by
    intro x hx
    simp only [boxZeros, Finset.mem_filter] at hx
    have h1 := eval_lift_J Δ z n3 ni nj s3 g a u x
    rw [hx.2, mul_zero] at h1
    set Y := 2 * g * (ni ^ 2 + nj ^ 2) * a ^ 2 * x 1 - ni * (tgP Δ z n3 s3 g a u).eval (x 0)
    have hPe : Pz.eval (x 0) = nj ^ 2 * (PP Δ z n3 ni nj s3 g a u).eval (x 0) := by
      simp [hPz, radP]
    have h2 : ((Y : ℤ) : ℚ) ^ 2 = c * (R.eval ((x 0 : ℤ) : ℚ)) ^ 2 := by
      have h3 : ((Y ^ 2 : ℤ) : ℚ) = ((Pz.eval (x 0) : ℤ) : ℚ) := by
        congr 1; rw [hPe]; linarith
      have h4 := eval_intCast_map (Int.castRingHom ℚ) Pz (x 0)
      simp only [eq_intCast, Int.cast_id] at h4
      rw [← h4, ← hPq, hcR] at h3
      simpa [Polynomial.eval_mul, Polynomial.eval_pow] using h3
    have hY : ((Y : ℤ) : ℚ) ^ 2 = 0 := by
      nlinarith [sq_nonneg ((Y : ℤ) : ℚ), sq_nonneg (R.eval ((x 0 : ℤ) : ℚ))]
    have hR : c * (R.eval ((x 0 : ℤ) : ℚ)) ^ 2 = 0 := by rw [← h2, hY]
    have hY0 : ((Y : ℤ) : ℚ) = 0 := (pow_eq_zero_iff two_ne_zero).mp hY
    refine ⟨by exact_mod_cast hY0, ?_⟩
    rcases mul_eq_zero.mp hR with h | h
    · exact absurd h hc0
    · exact (pow_eq_zero_iff two_ne_zero).mp h
  have hmaps : ∀ x ∈ boxZeros (liftPoly Δ z n3 ni nj s3 g a u) B,
      ((x 0 : ℤ) : ℚ) ∈ R.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, mem_roots hR0]
    exact (hpt x hx).2
  have hinj : Set.InjOn (fun x : Fin 2 → ℤ => ((x 0 : ℤ) : ℚ))
      (boxZeros (liftPoly Δ z n3 ni nj s3 g a u) B) := by
    intro x hx y hy hxy
    have h0 : x 0 = y 0 := by simpa using hxy
    have hx1 := (hpt x hx).1
    have hy1 := (hpt y hy).1
    rw [h0] at hx1
    have hne : 2 * g * (ni ^ 2 + nj ^ 2) * a ^ 2 ≠ 0 := by
      have : ni ^ 2 + nj ^ 2 ≠ 0 := by positivity
      positivity
    have h1 : x 1 = y 1 := by
      have : 2 * g * (ni ^ 2 + nj ^ 2) * a ^ 2 * (x 1 - y 1) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hne
      · linarith
    funext i; fin_cases i
    · exact h0
    · exact h1
  calc (boxZeros (liftPoly Δ z n3 ni nj s3 g a u) B).card ≤ R.roots.toFinset.card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ ≤ Multiset.card R.roots := Multiset.toFinset_card_le _
    _ ≤ R.natDegree := card_roots' R
    _ = _ := hRdeg

/-- The lifted curves have few points in any box with sides `≥ 2`. -/
private lemma lift_count (hP : PlaneCurveCount) (m : ℕ) (hm : 1 ≤ m) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Δ z n3 ni nj s3 g a : ℤ) (u : Polynomial ℤ), Δ ≠ 0 → g ≠ 0 → a ≠ 0 →
      nj ≠ 0 → u.natDegree = m → ∀ B : Fin 2 → ℝ, 2 ≤ B 0 → 2 ≤ B 1 →
        ((boxZeros (liftPoly Δ z n3 ni nj s3 g a u) B).card : ℝ) ≤
          C * max (B 0) (B 1) ^ η * Real.exp (Real.log (B 0) * Real.log (B 1) /
            ((4 * m + 2 : ℕ) * Real.log (B 0))) + (2 * m + 1 : ℕ) := by
  obtain ⟨C, hC0, hC⟩ := plane_count hP (4 * m + 2) η (by omega) hη
  refine ⟨C, hC0, ?_⟩
  intro Δ z n3 ni nj s3 g a u hΔ hg ha hnj hu B hB0 hB1
  have hm' : 1 ≤ u.natDegree := hu ▸ hm
  have hpos : 0 ≤ C * max (B 0) (B 1) ^ η * Real.exp (Real.log (B 0) * Real.log (B 1) /
      ((4 * m + 2 : ℕ) * Real.log (B 0))) :=
    mul_nonneg (mul_nonneg hC0 (Real.rpow_nonneg (le_trans (by norm_num) (le_max_of_le_left hB0))
      _)) (Real.exp_pos _).le
  obtain ⟨hdeg, -⟩ := radP_deg Δ z n3 ni nj s3 g a u hΔ hg hnj hm'
  have hdq : 0 < ((radP Δ z n3 ni nj s3 g a u).map (Int.castRingHom ℚ)).natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int _), hdeg]; omega
  rcases sq_or_absIrred _ hdq with hirr | ⟨c, R, hcR⟩
  · have habs := lift_absIrred Δ z n3 ni nj s3 g a u hg ha hnj hirr
    obtain ⟨htd, hmem⟩ := lift_deg Δ z n3 ni nj s3 g a u hΔ hg hm'
    rw [hu] at htd hmem
    have h := hC _ htd habs B hB0 hB1 _ hmem (by simp)
    simp only [Finsupp.single_eq_same, Finsupp.single_apply, Fin.isValue,
      zero_ne_one, ↓reduceIte, Nat.cast_zero, zero_mul, add_zero] at h
    have : (0 : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  · have h := lift_sq_count Δ z n3 ni nj s3 g a u hΔ hg ha hnj hm' c R hcR B
    rw [hu] at h
    have : ((boxZeros (liftPoly Δ z n3 ni nj s3 g a u) B).card : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := by
      exact_mod_cast h
    linarith

/-- The box of the lifted points `(X₂, X₃)`. -/
private def liftBox (n : Mode) (g T : ℕ) : Fin 2 → ℝ := ![4 * g * absk n / T, max 2 (absk n)]

/-- Bookkeeping for a parametrized curve `a X₁ = u(X₂)`: count via the lifted points. -/
private lemma count_le_lift (n : Mode) (Δ z : ℕ) (s2 s3 : ℤ) (g T : ℕ)
    (H : MvPolynomial (Fin 2) ℤ) (hH : ShellHyp n Δ z g T) (a : ℤ) (u : Polynomial ℤ)
    (ha : a ≠ 0) (hcurve : ∀ x : Fin 2 → ℤ, eval x H = 0 → a * x 0 = u.eval (x 1))
    (i j : Fin 3) (hij : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) :
    curveCount n Δ z s2 s3 g T H ≤
      2 * (boxZeros (liftPoly Δ z (n 2) (n i) (n j) s3 g a u) (liftBox n g T)).card := by
  classical
  unfold curveCount
  have hi : i = 0 ∨ i = 1 := by rcases hij with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  have hspec : ∀ k ∈ (shellPts n Δ z s2 s3 g T).filter
      (fun k => eval (projPt Δ s2 g n k) H = 0),
      a * surfPt Δ s2 g i n k 0 = u.eval (surfPt Δ s2 g i n k 1) := by
    intro k hk
    have := hcurve _ (Finset.mem_filter.mp hk).2
    simpa [surfPt, projPt] using this
  refine Finset.card_le_mul_card_image_of_maps_to
    (f := fun k => ![surfPt Δ s2 g i n k 1, surfPt Δ s2 g i n k 2]) ?_ 2 ?_
  · intro k hk
    have hs := surface_points hH (Finset.mem_filter.mp hk).1 i j hij
    simp only [boxZeros, boxPts, Finset.mem_filter, Fintype.mem_piFinset] at hs ⊢
    refine ⟨fun l => ?_, ?_⟩
    · fin_cases l
      · simpa [shellBox, liftBox] using hs.1 1
      · simpa [shellBox, liftBox] using hs.1 2
    · rw [eval_lift_surface _ _ _ _ _ _ _ _ u _ (hspec k hk), hs.2, mul_zero]
  · intro b _
    refine le_trans (Finset.card_le_card ?_)
      (surface_points_two_to_one n Δ z s2 s3 g T hH i hi ![u.eval (b 0) / a, b 0, b 1])
    intro k hk
    simp only [Finset.mem_filter] at hk ⊢
    obtain ⟨hk1, hkb⟩ := hk
    refine ⟨hk1.1, ?_⟩
    have h1 : surfPt Δ s2 g i n k 1 = b 0 := by rw [← hkb]; simp
    have h2 : surfPt Δ s2 g i n k 2 = b 1 := by rw [← hkb]; simp
    have h0 : surfPt Δ s2 g i n k 0 = u.eval (b 0) / a := by
      rw [← h1, ← hspec k (Finset.mem_filter.mpr hk1), Int.mul_ediv_cancel_left _ ha]
    funext l; fin_cases l
    · simpa using h0
    · simpa using h1
    · simpa using h2

/-- A parametrized curve `a X₁ = u(X₂)` with `deg u = m ≥ 1` costs `C N^{1/4+ε}`. -/
private lemma lift_row (hP : PlaneCurveCount) (m : ℕ) (hm : 1 ≤ m) : ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : Mode) (Δ z : ℕ) (s2 s3 : ℤ) (g T : ℕ) (H : MvPolynomial (Fin 2) ℤ)
      (a : ℤ) (u : Polynomial ℤ), ShellHyp n Δ z g T → a ≠ 0 → u.natDegree = m →
      (∀ x : Fin 2 → ℤ, eval x H = 0 → a * x 0 = u.eval (x 1)) →
      (curveCount n Δ z s2 s3 g T H : ℝ) ≤ C * absk n ^ ((1 : ℝ) / 4 + ε) := by
  intro ε hε
  obtain ⟨C₁, hC₁0, hC₁⟩ := lift_count hP m hm ε hε
  refine ⟨2 * (C₁ * 4 ^ ε * Real.exp (Real.log 2) + (2 * m + 1 : ℕ)), by positivity, ?_⟩
  intro n Δ z s2 s3 g T H a u hH ha hu hcurve
  classical
  obtain ⟨hN1, -, hg1, -, -, hB1, -, hB1N, -⟩ := shell_facts hH
  have hNp : 1 ≤ absk n ^ ((1 : ℝ) / 4 + ε) := Real.one_le_rpow hN1 (by positivity)
  have hC0 : 0 ≤ 2 * (C₁ * 4 ^ ε * Real.exp (Real.log 2) + (2 * m + 1 : ℕ)) := by positivity
  rcases Nat.eq_zero_or_pos (curveCount n Δ z s2 s3 g T H) with h0 | hpos
  · rw [h0, Nat.cast_zero]; positivity
  obtain ⟨k₀, hk₀⟩ : ((shellPts n Δ z s2 s3 g T).filter
      fun k => eval (projPt Δ s2 g n k) H = 0).Nonempty := by
    rw [← Finset.card_pos]; unfold curveCount at hpos; convert hpos
  have hnh := active_nh (shellPts_sub (mem_curve hk₀).1).1
  obtain ⟨i, j, hij, hnj⟩ : ∃ i j : Fin 3, ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) ∧ n j ≠ 0 := by
    by_cases h1 : n 1 = 0
    · refine ⟨1, 0, Or.inr ⟨rfl, rfl⟩, ?_⟩
      intro h0; apply hnh; rw [h0, h1]; ring
    · exact ⟨0, 1, Or.inl ⟨rfl, rfl⟩, h1⟩
  have hΔ : (Δ : ℤ) ≠ 0 := by exact_mod_cast hH.1.ne_zero
  have hg : (g : ℤ) ≠ 0 := by
    have : (0 : ℝ) < g := by linarith
    exact_mod_cast this.ne'
  have hcount := count_le_lift n Δ z s2 s3 g T H hH a u ha hcurve i j hij
  have hL0 : (2 : ℝ) ≤ liftBox n g T 0 := by simpa [liftBox] using hB1
  have hL1 : (2 : ℝ) ≤ liftBox n g T 1 := by simp [liftBox]
  have hbox := hC₁ Δ z (n 2) (n i) (n j) s3 g a u hΔ hg ha hnj hu _ hL0 hL1
  set Z := ((boxZeros (liftPoly Δ z (n 2) (n i) (n j) s3 g a u) (liftBox n g T)).card : ℝ)
  set b0 := liftBox n g T 0
  set b1 := liftBox n g T 1
  have hl0 : 0 < Real.log b0 := Real.log_pos (by linarith)
  have hb1 : b1 = max 2 (absk n) := by simp [b1, liftBox]
  have hb1le : b1 ≤ 2 * absk n := by rw [hb1]; exact max_le (by linarith) (by linarith)
  have hlog1 : Real.log b1 ≤ Real.log 2 + Real.log (absk n) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by linarith) hb1le
  have hl1 : 0 < Real.log b1 := Real.log_pos (by linarith)
  have hE : Real.log b0 * Real.log b1 / ((4 * m + 2 : ℕ) * Real.log b0) ≤
      Real.log 2 + Real.log (absk n) / 4 := by
    have hm6 : (6 : ℝ) ≤ ((4 * m + 2 : ℕ) : ℝ) := by
      exact_mod_cast (show 6 ≤ 4 * m + 2 by omega)
    rw [div_le_iff₀ (by positivity)]
    have hlN : 0 ≤ Real.log (absk n) := Real.log_nonneg hN1
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have : Real.log b1 ≤ ((4 * m + 2 : ℕ) : ℝ) * (Real.log 2 + Real.log (absk n) / 4) := by
      nlinarith
    nlinarith
  have hmax : max b0 b1 ≤ 4 * absk n := max_le (by simpa [b0, liftBox] using hB1N) (by linarith)
  have hx := finish_bound hN1 hC₁0 hε (le_trans (by norm_num) (le_max_of_le_left hL0)) hmax hE
    (x := Z - (2 * m + 1 : ℕ)) (by linarith)
  have h2 : (curveCount n Δ z s2 s3 g T H : ℝ) ≤ 2 * Z := by
    simp only [Z]; exact_mod_cast hcount
  have hm0 : (0 : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- A `ℚ`-irreducible quadratic in `X₂` alone has no integer zero. -/
private lemma no_root_X2 (H : MvPolynomial (Fin 2) ℤ)
    (hirr : Irreducible (MvPolynomial.map (Int.castRingHom ℚ) H)) (hd : H.totalDegree = 2)
    (h20 : H.coeff (e2 2 0) = 0) (h11 : H.coeff (e2 1 1) = 0) (h10 : H.coeff (e2 1 0) = 0)
    (hα : H.coeff (e2 0 2) ≠ 0) (x : Fin 2 → ℤ) : eval x H ≠ 0 := by
  intro hx
  set c0 := H.coeff (e2 0 0)
  set c1 := H.coeff (e2 0 1)
  set α := H.coeff (e2 0 2)
  set r := x 1
  have hev : ∀ y : Fin 2 → ℤ, eval y H = c0 + c1 * y 1 + α * y 1 ^ 2 := by
    intro y; rw [eval_deg2 H hd.le y, h20, h11, h10]; ring
  have hH : H = C c0 + C c1 * X 1 + C α * X 1 ^ 2 := by
    apply MvPolynomial.funext; intro y; rw [hev]; simp
  have hr : c0 = -(c1 * r + α * r ^ 2) := by rw [hev] at hx; linarith
  set ι := Int.castRingHom ℚ
  have hfac : MvPolynomial.map ι H =
      (X 1 - C (ι r)) * (C (ι α) * X 1 + C (ι α * ι r + ι c1)) := by
    rw [hH]
    simp only [map_add, map_mul, map_pow, MvPolynomial.map_C, MvPolynomial.map_X]
    rw [hr]
    simp only [map_neg, map_add, map_mul, map_pow]
    ring
  rw [hfac] at hirr
  rcases hirr.isUnit_or_isUnit rfl with h | h
  · obtain ⟨c, -, hc⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).mp h
    have e0 := congrArg (eval ![0, 0]) hc
    have e1 := congrArg (eval ![0, 1]) hc
    simp only [map_sub, eval_X, eval_C, Matrix.cons_val_one, Matrix.cons_val_zero] at e0 e1
    linarith
  · obtain ⟨c, -, hc⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).mp h
    have e0 := congrArg (eval ![0, 0]) hc
    have e1 := congrArg (eval ![0, 1]) hc
    simp only [map_add, map_mul, eval_X, eval_C, Matrix.cons_val_one, Matrix.cons_val_zero]
      at e0 e1
    have : ι α = 0 := by linarith
    exact hα (by simpa [ι] using this)

/-- Row: `ℚ`-irreducible but not absolutely irreducible (`FewPointsNotAbsIrred` with the box
containing the projections, times two lifts). -/
theorem row_notAbsIrred (hF : FewPointsNotAbsIrred) (n : Mode) (Δ z : ℕ) (s2 s3 : ℤ) (g T : ℕ)
    (H : MvPolynomial (Fin 2) ℤ) (hH : ShellHyp n Δ z g T)
    (hirr : Irreducible (MvPolynomial.map (Int.castRingHom ℚ) H)) (hna : ¬ AbsIrred H) :
    (curveCount n Δ z s2 s3 g T H : ℝ) ≤ 2 * (H.totalDegree : ℝ) ^ 2 := by
  have h1 : (curveCount n Δ z s2 s3 g T H : ℝ) ≤ 2 * (boxZeros H (projBox n g T)).card := by
    exact_mod_cast count_le_proj n Δ z s2 s3 g T H hH
  have h2 := hF H hirr hna (projBox n g T)
  linarith

/-- Row: absolutely irreducible of degree `3 ≤ d ≤ D` (`𝔗 ≥ min(B₀,B₁)^d`). -/
theorem row_degree_ge3 (hP : PlaneCurveCount) (D : ℕ) : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (n : Mode) (Δ z : ℕ) (s2 s3 : ℤ) (g T : ℕ) (H : MvPolynomial (Fin 2) ℤ),
      ShellHyp n Δ z g T → AbsIrred H → 3 ≤ H.totalDegree → H.totalDegree ≤ D →
      (curveCount n Δ z s2 s3 g T H : ℝ) ≤ C * absk n ^ ((1 : ℝ) / 4 + ε) := by
  intro ε hε
  have hC : ∀ d : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (1 ≤ d → ∀ F : MvPolynomial (Fin 2) ℤ,
      F.totalDegree = d → AbsIrred F → ∀ B : Fin 2 → ℝ, 2 ≤ B 0 → 2 ≤ B 1 →
        ∀ m ∈ F.support, m ≠ 0 → ((boxZeros F B).card : ℝ) ≤ C * max (B 0) (B 1) ^ ε *
          Real.exp (Real.log (B 0) * Real.log (B 1) /
            (m 0 * Real.log (B 0) + m 1 * Real.log (B 1)))) := by
    intro d
    by_cases hd : 1 ≤ d
    · obtain ⟨C, hC0, hC⟩ := plane_count hP d ε hd hε
      exact ⟨C, hC0, fun _ => hC⟩
    · exact ⟨0, le_rfl, fun h => absurd h hd⟩
  choose Cf hCf0 hCf using hC
  set S := ∑ d ∈ Finset.range (D + 1), Cf d with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun d _ => hCf0 d
  refine ⟨2 * S * 4 ^ ε * Real.exp (Real.log 4), by positivity, ?_⟩
  intro n Δ z s2 s3 g T H hH habs hd3 hdD
  obtain ⟨hN1, -, -, -, hB0, hB1, hB0N, hB1N, hl0, hl1, -⟩ := shell_facts hH
  have hp := pStar_bounds
  set d := H.totalDegree with hd
  obtain ⟨p, q, hpq, hc⟩ := exists_top H hd.symm (by omega)
  have hm : e2 p q ∈ H.support := mem_support_iff.mpr hc
  have hm0 : e2 p q ≠ 0 := by
    intro h; have := congrArg (fun m => m 0 + m 1) h; simp [e2] at this; omega
  have hcount := count_le_proj n Δ z s2 s3 g T H hH
  have hbox := hCf d (by omega) H rfl habs (projBox n g T) (by simpa [projBox] using hB0)
    (by simpa [projBox] using hB1) _ hm hm0
  simp only [projBox, Matrix.cons_val_zero, Matrix.cons_val_one, e2,
    Finsupp.add_apply, Finsupp.single_apply] at hbox
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero, zero_ne_one, add_zero, zero_add] at hbox
  set a := Real.log (2 * T / g)
  set b := Real.log (4 * g * absk n / T)
  set lam := Real.log (absk n)
  have hlam : 0 ≤ lam := Real.log_nonneg hN1
  have ha : Real.log 2 ≤ a := Real.log_le_log (by norm_num) hB0
  have hb : Real.log 2 ≤ b := Real.log_le_log (by norm_num) hB1
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl4 : Real.log 4 = 2 * Real.log 2 := log4
  have hpq' : (3 : ℝ) ≤ p + q := by exact_mod_cast (show 3 ≤ p + q by omega)
  have hE : a * b / (p * a + q * b) ≤ Real.log 4 + lam / 4 := by
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    have hden : 0 < (p : ℝ) * a + q * b := by nlinarith
    rw [div_le_iff₀ hden]
    obtain ⟨U, hUdef⟩ : ∃ U, U = Real.log 4 + (5 / 4 - pStar) * lam := ⟨_, rfl⟩
    have hU : U / 3 ≤ Real.log 4 + lam / 4 := by rw [hUdef]; nlinarith
    have haU : a ≤ U := hUdef ▸ hl0
    have hbU : b ≤ U := by rw [hUdef]; nlinarith
    rcases le_total a b with hab | hab
    · have h1 : 3 * a ≤ p * a + q * b := by nlinarith
      nlinarith
    · have h1 : 3 * b ≤ p * a + q * b := by nlinarith
      nlinarith
  have hmax : max (2 * (T : ℝ) / g) (4 * g * absk n / T) ≤ 4 * absk n := max_le hB0N hB1N
  have hCd : Cf d ≤ S := Finset.single_le_sum (fun d _ => hCf0 d)
    (Finset.mem_range.mpr (by omega))
  have hx : (curveCount n Δ z s2 s3 g T H : ℝ) ≤ (2 * S) *
      max (2 * (T : ℝ) / g) (4 * g * absk n / T) ^ ε * Real.exp (a * b / (p * a + q * b)) := by
    have h2 : (curveCount n Δ z s2 s3 g T H : ℝ) ≤ 2 * (boxZeros H (projBox n g T)).card := by
      exact_mod_cast hcount
    have hpos : 0 ≤ max (2 * (T : ℝ) / g) (4 * g * absk n / T) ^ ε *
        Real.exp (a * b / (p * a + q * b)) :=
      mul_nonneg (Real.rpow_nonneg (le_trans (by norm_num) (le_max_of_le_left hB0)) _)
        (Real.exp_pos _).le
    calc (curveCount n Δ z s2 s3 g T H : ℝ) ≤ 2 * (boxZeros H (projBox n g T)).card := h2
      _ ≤ 2 * (Cf d * max (2 * (T : ℝ) / g) (4 * g * absk n / T) ^ ε *
          Real.exp (a * b / (p * a + q * b))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num); exact hbox
      _ ≤ 2 * (S * max (2 * (T : ℝ) / g) (4 * g * absk n / T) ^ ε *
          Real.exp (a * b / (p * a + q * b))) := by
          rw [mul_assoc (Cf d), mul_assoc S]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCd hpos) (by norm_num)
      _ = _ := by ring
  exact finish_bound hN1 (by positivity) hε (le_trans (by norm_num) (le_max_of_le_left hB0))
    hmax hE hx

/-- Row: absolutely irreducible conic in which `X₁²` or `X₁X₂` occurs. -/
theorem row_conic_general (hP : PlaneCurveCount) : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (n : Mode) (Δ z : ℕ) (s2 s3 : ℤ) (g T : ℕ) (H : MvPolynomial (Fin 2) ℤ),
      ShellHyp n Δ z g T → AbsIrred H → H.totalDegree = 2 →
      (H.coeff (Finsupp.single 0 2) ≠ 0 ∨
        H.coeff (Finsupp.single 0 1 + Finsupp.single 1 1) ≠ 0) →
      (curveCount n Δ z s2 s3 g T H : ℝ) ≤ C * absk n ^ ((1 : ℝ) / 4 + ε) := by
  intro ε hε
  obtain ⟨C₂, hC₂0, hC₂⟩ := plane_count hP 2 ε (by norm_num) hε
  refine ⟨2 * C₂ * 4 ^ ε * Real.exp (Real.log 8), by positivity, ?_⟩
  intro n Δ z s2 s3 g T H hH habs hd hcases
  obtain ⟨hN1, -, -, -, hB0, hB1, -, -, -, hl1, hsum⟩ := shell_facts hH
  have hp := pStar_bounds
  set a := Real.log (2 * T / g)
  set b := Real.log (4 * g * absk n / T)
  set lam := Real.log (absk n)
  have hlam : 0 ≤ lam := Real.log_nonneg hN1
  have ha : Real.log 2 ≤ a := Real.log_le_log (by norm_num) hB0
  have hb : Real.log 2 ≤ b := Real.log_le_log (by norm_num) hB1
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl4 : Real.log 4 = 2 * Real.log 2 := log4
  have hl8 : Real.log 8 = 3 * Real.log 2 := log8
  have hb0 : (2 : ℝ) ≤ projBox n g T 0 := by simpa [projBox] using hB0
  have hb1 : (2 : ℝ) ≤ projBox n g T 1 := by simpa [projBox] using hB1
  rcases hcases with h20 | h11
  · have hm : Finsupp.single (0 : Fin 2) 2 ∈ H.support := mem_support_iff.mpr h20
    have hbox := hC₂ H hd habs _ hb0 hb1 _ hm (by simp)
    have e0 : (Finsupp.single (0 : Fin 2) 2) 0 = 2 := by simp
    have e1 : (Finsupp.single (0 : Fin 2) 2) 1 = 0 := by simp
    simp only [projBox, Matrix.cons_val_zero, Matrix.cons_val_one, e0, e1, Nat.cast_ofNat,
      Nat.cast_zero, zero_mul, add_zero] at hbox
    refine shell_row hH hC₂0 hε hbox ?_
    have ha0 : a ≠ 0 := by linarith
    have : a * b / (2 * a) = b / 2 := by field_simp
    rw [this]; nlinarith
  · have hm : Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1 ∈ H.support :=
      mem_support_iff.mpr h11
    have hbox := hC₂ H hd habs _ hb0 hb1 _ hm (by
      intro h; have := congrArg (fun m => m 0) h; simp at this)
    simp only [projBox, Matrix.cons_val_zero, Matrix.cons_val_one, Finsupp.add_apply,
      Finsupp.single_apply] at hbox
    simp only [Fin.isValue, ↓reduceIte, one_ne_zero, zero_ne_one, Nat.cast_one,
      one_mul, add_zero, zero_add] at hbox
    refine shell_row hH hC₂0 hε hbox ?_
    have hden : 0 < a + b := by linarith
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg (a - b)]

/-- Row: the quadratic graph `αX₂² + βX₁ + γX₂ + δ` (degree-10 lift, `sq_or_absIrred`). -/
theorem row_conic_X2sq (hP : PlaneCurveCount) : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (n : Mode) (Δ z : ℕ) (s2 s3 : ℤ) (g T : ℕ) (H : MvPolynomial (Fin 2) ℤ),
      ShellHyp n Δ z g T → Irreducible (MvPolynomial.map (Int.castRingHom ℚ) H) →
      H.totalDegree = 2 → H.coeff (Finsupp.single 0 2) = 0 →
      H.coeff (Finsupp.single 0 1 + Finsupp.single 1 1) = 0 →
      (curveCount n Δ z s2 s3 g T H : ℝ) ≤ C * absk n ^ ((1 : ℝ) / 4 + ε) := by
  intro ε hε
  obtain ⟨C, hC0, hC⟩ := lift_row hP 2 (by norm_num) ε hε
  refine ⟨C, hC0, ?_⟩
  intro n Δ z s2 s3 g T H hH hirr hd h20 h11
  rw [← e2_20] at h20
  have h11' : H.coeff (e2 1 1) = 0 := h11
  have hα : H.coeff (e2 0 2) ≠ 0 := by
    obtain ⟨p, q, hpq, hc⟩ := exists_top H hd (by norm_num)
    rcases (show (p = 2 ∧ q = 0) ∨ (p = 1 ∧ q = 1) ∨ (p = 0 ∧ q = 2) by omega) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd h20 hc
    · exact absurd h11' hc
    · exact hc
  by_cases hβ : H.coeff (e2 1 0) = 0
  · have h0 : curveCount n Δ z s2 s3 g T H = 0 := by
      classical
      unfold curveCount
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k _
      convert no_root_X2 H hirr hd h20 h11' hβ hα (projPt Δ s2 g n k)
    rw [h0, Nat.cast_zero]
    obtain ⟨hN1, -⟩ := shell_facts hH
    exact mul_nonneg hC0 (Real.rpow_nonneg (by linarith) _)
  · set u : Polynomial ℤ := -(Polynomial.C (H.coeff (e2 0 2)) * Polynomial.X ^ 2 +
      Polynomial.C (H.coeff (e2 0 1)) * Polynomial.X + Polynomial.C (H.coeff (e2 0 0)))
    have hu : u.natDegree = 2 := by
      rw [Polynomial.natDegree_neg, Polynomial.natDegree_quadratic hα]
    refine hC n Δ z s2 s3 g T H _ u hH hβ hu fun x hx => ?_
    rw [eval_deg2 H hd.le x, h20, h11'] at hx
    simp only [u, Polynomial.eval_neg, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
    linear_combination hx

/-- Row: the sloped line `aX₁ + bX₂ + c`, `a ≠ 0 ≠ b` (sextic lift, `sq_or_absIrred`). -/
theorem row_line_sloped (hP : PlaneCurveCount) : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (n : Mode) (Δ z : ℕ) (s2 s3 : ℤ) (g T : ℕ) (H : MvPolynomial (Fin 2) ℤ),
      ShellHyp n Δ z g T → H.totalDegree = 1 → H.coeff (Finsupp.single 0 1) ≠ 0 →
      H.coeff (Finsupp.single 1 1) ≠ 0 →
      (curveCount n Δ z s2 s3 g T H : ℝ) ≤ C * absk n ^ ((1 : ℝ) / 4 + ε) := by
  intro ε hε
  obtain ⟨C, hC0, hC⟩ := lift_row hP 1 le_rfl ε hε
  refine ⟨C, hC0, ?_⟩
  intro n Δ z s2 s3 g T H hH hd ha hb
  set u : Polynomial ℤ := -(Polynomial.C (H.coeff (Finsupp.single 1 1)) * Polynomial.X +
    Polynomial.C (H.coeff (e2 0 0)))
  have hu : u.natDegree = 1 := by
    rw [Polynomial.natDegree_neg, Polynomial.natDegree_linear hb]
  refine hC n Δ z s2 s3 g T H _ u hH ha hu fun x hx => ?_
  rw [eval_deg1 H hd.le x, e2_10, e2_01] at hx
  simp only [u, Polynomial.eval_neg, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  linear_combination hx

/-- Row: constant `X₁` (fixed non-parabolic `t`; `fixed_t_count`). -/
theorem row_const_t (hQ : QuadraticNormCount) : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (n : Mode) (Δ z : ℕ) (s2 s3 : ℤ) (g T : ℕ) (H : MvPolynomial (Fin 2) ℤ),
      ShellHyp n Δ z g T → H.totalDegree = 1 → H.coeff (Finsupp.single 1 1) = 0 →
      (curveCount n Δ z s2 s3 g T H : ℝ) ≤ C * absk n ^ ((1 : ℝ) / 4 + ε) := by
  intro ε hε
  obtain ⟨K, hK0, hK⟩ := fixed_t_count hQ (ε / 2) (by positivity)
  refine ⟨K, hK0, ?_⟩
  intro n Δ z s2 s3 g T H hH hd h01
  classical
  obtain ⟨hN1, -, hg1, -⟩ := shell_facts hH
  have hev : ∀ x : Fin 2 → ℤ, eval x H = H.coeff (e2 0 0) + H.coeff (e2 1 0) * x 0 := by
    intro x; rw [eval_deg1 H hd.le x, e2_01, h01]; ring
  have hpos : 0 ≤ K * absk n ^ ((1 : ℝ) / 4 + ε) :=
    mul_nonneg hK0 (Real.rpow_nonneg (by linarith) _)
  unfold curveCount
  set S := (shellPts n Δ z s2 s3 g T).filter fun k => eval (projPt Δ s2 g n k) H = 0
  rcases S.eq_empty_or_nonempty with hS | ⟨k₀, hk₀⟩
  · rw [hS, Finset.card_empty, Nat.cast_zero]; exact hpos
  obtain ⟨hk₀s, hk₀H⟩ := mem_curve hk₀
  obtain ⟨hact₀, hca⟩ := shellPts_sub hk₀s
  have ha : H.coeff (e2 1 0) ≠ 0 := by
    obtain ⟨p, q, hpq, hc⟩ := exists_top H hd le_rfl
    rcases (show (p = 1 ∧ q = 0) ∨ (p = 0 ∧ q = 1) by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hc
    · rw [e2_01] at hc; exact absurd h01 hc
  have hsub : S ⊆ (activePts n s2 s3).filter fun k => tOf Δ s2 n k = tOf Δ s2 n k₀ := by
    intro k hk
    obtain ⟨hks, hkH⟩ := mem_curve hk
    refine Finset.mem_filter.mpr ⟨(shellPts_sub hks).1, ?_⟩
    rw [← (projPt_spec hH hks).1, ← (projPt_spec hH hk₀s).1]
    rw [hev] at hkH hk₀H
    have : H.coeff (e2 1 0) * (projPt Δ s2 g n k 0 - projPt Δ s2 g n k₀ 0) = 0 := by
      linear_combination hkH - hk₀H
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h ha
    · rw [sub_eq_zero.mp h]
  have hb := hK n Δ z (tOf Δ s2 n k₀) s2 s3 hH.1 hH.2.1 hca
  have hN0 : 0 < absk n := by linarith
  have hnsq : (nsqZ n : ℝ) ^ (ε / 2) = absk n ^ ε := by
    rw [show (nsqZ n : ℝ) = absk n ^ (2 : ℝ) by
      rw [absk_eq_sqrt_nsqZ, Real.rpow_two, Real.sq_sqrt]
      exact_mod_cast (Finset.sum_nonneg fun i _ => sq_nonneg (n i))]
    rw [← Real.rpow_mul hN0.le]; ring_nf
  have hmono : absk n ^ ε ≤ absk n ^ ((1 : ℝ) / 4 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  calc (S.card : ℝ) ≤ (((activePts n s2 s3).filter
        fun k => tOf Δ s2 n k = tOf Δ s2 n k₀).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ K * (nsqZ n : ℝ) ^ (ε / 2) := hb
    _ ≤ K * absk n ^ ((1 : ℝ) / 4 + ε) := by
        rw [hnsq]; exact mul_le_mul_of_nonneg_left hmono hK0

/-- Row: constant `X₂` (fixed height `w`; `fixed_w_count`). -/
theorem row_const_w (hP : PlaneCurveCount) : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (n : Mode) (Δ z : ℕ) (s2 s3 : ℤ) (g T : ℕ) (H : MvPolynomial (Fin 2) ℤ),
      ShellHyp n Δ z g T → H.totalDegree = 1 → H.coeff (Finsupp.single 0 1) = 0 →
      (curveCount n Δ z s2 s3 g T H : ℝ) ≤ C * absk n ^ ((1 : ℝ) / 4 + ε) := by
  intro ε hε
  obtain ⟨K, hK0, hK⟩ := fixed_w_count hP ε hε
  refine ⟨K * 2 ^ ((1 : ℝ) / 4 + ε) + 2, by positivity, ?_⟩
  intro n Δ z s2 s3 g T H hH hd h10
  classical
  obtain ⟨hN1, -, hg1, -⟩ := shell_facts hH
  have hev : ∀ x : Fin 2 → ℤ, eval x H = H.coeff (e2 0 0) + H.coeff (e2 0 1) * x 1 := by
    intro x; rw [eval_deg1 H hd.le x, e2_10, h10]; ring
  have hN0 : 0 < absk n := by linarith
  have hNp : 1 ≤ absk n ^ ((1 : ℝ) / 4 + ε) := Real.one_le_rpow hN1 (by positivity)
  unfold curveCount
  set S := (shellPts n Δ z s2 s3 g T).filter fun k => eval (projPt Δ s2 g n k) H = 0
  rcases S.eq_empty_or_nonempty with hS | ⟨k₀, hk₀⟩
  · rw [hS, Finset.card_empty, Nat.cast_zero]; positivity
  obtain ⟨hk₀s, hk₀H⟩ := mem_curve hk₀
  have hb : H.coeff (e2 0 1) ≠ 0 := by
    obtain ⟨p, q, hpq, hc⟩ := exists_top H hd le_rfl
    rcases (show (p = 1 ∧ q = 0) ∨ (p = 0 ∧ q = 1) by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [e2_10] at hc; exact absurd h10 hc
    · exact hc
  have hg0 : (g : ℤ) ≠ 0 := by
    have : (0 : ℝ) < g := by linarith
    exact_mod_cast this.ne'
  have hsub : S ⊆ (activePts n s2 s3).filter fun k => k 2 = k₀ 2 := by
    intro k hk
    obtain ⟨hks, hkH⟩ := mem_curve hk
    refine Finset.mem_filter.mpr ⟨(shellPts_sub hks).1, ?_⟩
    rw [hev] at hkH hk₀H
    have h1 : H.coeff (e2 0 1) * (projPt Δ s2 g n k 1 - projPt Δ s2 g n k₀ 1) = 0 := by
      linear_combination hkH - hk₀H
    have h2 : projPt Δ s2 g n k 1 = projPt Δ s2 g n k₀ 1 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h hb
      · exact sub_eq_zero.mp h
    have h3 : (g : ℤ) * (k 2 - k₀ 2) = 0 := by
      have e1 := (projPt_spec hH hks).2
      have e2' := (projPt_spec hH hk₀s).2
      rw [h2] at e1
      linear_combination e2' - e1
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h hg0
    · exact sub_eq_zero.mp h
  have hbound := hK n (k₀ 2) s2 s3
  have hmax : max 2 (2 * absk n) = 2 * absk n := max_eq_right (by linarith)
  rw [hmax, Real.mul_rpow (by norm_num) hN0.le] at hbound
  calc (S.card : ℝ) ≤ (((activePts n s2 s3).filter fun k => k 2 = k₀ 2).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ K * (2 ^ ((1 : ℝ) / 4 + ε) * absk n ^ ((1 : ℝ) / 4 + ε)) + 2 := hbound
    _ ≤ _ := by nlinarith

/-- Every `ℚ`-irreducible `H` falls into one of the rows (it is nonconstant). -/
theorem row_classification (H : MvPolynomial (Fin 2) ℤ)
    (hirr : Irreducible (MvPolynomial.map (Int.castRingHom ℚ) H)) :
    ¬ AbsIrred H ∨ (AbsIrred H ∧ 3 ≤ H.totalDegree) ∨
      (AbsIrred H ∧ H.totalDegree = 2 ∧ (H.coeff (Finsupp.single 0 2) ≠ 0 ∨
        H.coeff (Finsupp.single 0 1 + Finsupp.single 1 1) ≠ 0)) ∨
      (H.totalDegree = 2 ∧ H.coeff (Finsupp.single 0 2) = 0 ∧
        H.coeff (Finsupp.single 0 1 + Finsupp.single 1 1) = 0) ∨
      (H.totalDegree = 1 ∧ H.coeff (Finsupp.single 0 1) ≠ 0 ∧
        H.coeff (Finsupp.single 1 1) ≠ 0) ∨
      (H.totalDegree = 1 ∧ H.coeff (Finsupp.single 1 1) = 0) ∨
      (H.totalDegree = 1 ∧ H.coeff (Finsupp.single 0 1) = 0) := by
  have h1 := one_le_totalDegree H hirr
  by_cases hA : AbsIrred H
  · right
    rcases (show 3 ≤ H.totalDegree ∨ H.totalDegree = 2 ∨ H.totalDegree = 1 by omega)
      with h3 | h2 | h1'
    · exact Or.inl ⟨hA, h3⟩
    · right
      by_cases hc : H.coeff (Finsupp.single 0 2) ≠ 0 ∨
          H.coeff (Finsupp.single 0 1 + Finsupp.single 1 1) ≠ 0
      · exact Or.inl ⟨hA, h2, hc⟩
      · push Not at hc; exact Or.inr (Or.inl ⟨h2, hc.1, hc.2⟩)
    · right; right; right
      by_cases ha : H.coeff (Finsupp.single 0 1) = 0
      · exact Or.inr (Or.inr ⟨h1', ha⟩)
      · by_cases hb : H.coeff (Finsupp.single 1 1) = 0
        · exact Or.inr (Or.inl ⟨h1', hb⟩)
        · exact Or.inl ⟨h1', ha, hb⟩
  · exact Or.inl hA

/-- D6: every `ℚ`-irreducible covered curve of degree `≤ D` costs `C N^{1/4+ε}`. -/
theorem plane_factor_count (hP : PlaneCurveCount) (hQ : QuadraticNormCount)
    (hF : FewPointsNotAbsIrred) (D : ℕ) : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (n : Mode) (Δ z : ℕ) (s2 s3 : ℤ) (g T : ℕ) (H : MvPolynomial (Fin 2) ℤ),
      ShellHyp n Δ z g T → Irreducible (MvPolynomial.map (Int.castRingHom ℚ) H) →
      H.totalDegree ≤ D →
      (curveCount n Δ z s2 s3 g T H : ℝ) ≤ C * absk n ^ ((1 : ℝ) / 4 + ε) := by
  intro ε hε
  obtain ⟨C1, h1, hC1⟩ := row_degree_ge3 hP D ε hε
  obtain ⟨C2, h2, hC2⟩ := row_conic_general hP ε hε
  obtain ⟨C3, h3, hC3⟩ := row_conic_X2sq hP ε hε
  obtain ⟨C4, h4, hC4⟩ := row_line_sloped hP ε hε
  obtain ⟨C5, h5, hC5⟩ := row_const_t hQ ε hε
  obtain ⟨C6, h6, hC6⟩ := row_const_w hP ε hε
  refine ⟨2 * (D : ℝ) ^ 2 + C1 + C2 + C3 + C4 + C5 + C6, by positivity, ?_⟩
  intro n Δ z s2 s3 g T H hH hirr hD
  obtain ⟨hN1, -⟩ := shell_facts hH
  set p := absk n ^ ((1 : ℝ) / 4 + ε)
  have hp : 1 ≤ p := Real.one_le_rpow hN1 (by positivity)
  have hD2 : 0 ≤ 2 * (D : ℝ) ^ 2 * p := by positivity
  have hC : ∀ c : ℝ, 0 ≤ c → 0 ≤ c * p := fun c hc => mul_nonneg hc (by linarith)
  have e : (2 * (D : ℝ) ^ 2 + C1 + C2 + C3 + C4 + C5 + C6) * p =
      2 * (D : ℝ) ^ 2 * p + C1 * p + C2 * p + C3 * p + C4 * p + C5 * p + C6 * p := by ring
  rw [e]
  have := hC C1 h1; have := hC C2 h2; have := hC C3 h3; have := hC C4 h4; have := hC C5 h5
  have := hC C6 h6
  rcases row_classification H hirr with hna | ⟨ha, hd⟩ | ⟨ha, hd, hc⟩ | ⟨hd, h20, h11⟩ |
      ⟨hd, ha, hb⟩ | ⟨hd, hb⟩ | ⟨hd, ha⟩
  · have h := row_notAbsIrred hF n Δ z s2 s3 g T H hH hirr hna
    have hDD : (H.totalDegree : ℝ) ^ 2 ≤ (D : ℝ) ^ 2 := by
      have : (H.totalDegree : ℝ) ≤ D := by exact_mod_cast hD
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) this 2
    nlinarith
  · have := hC1 n Δ z s2 s3 g T H hH ha hd hD; linarith
  · have := hC2 n Δ z s2 s3 g T H hH ha hd hc; linarith
  · have := hC3 n Δ z s2 s3 g T H hH hirr hd h20 h11; linarith
  · have := hC4 n Δ z s2 s3 g T H hH hd ha hb; linarith
  · have := hC5 n Δ z s2 s3 g T H hH hd hb; linarith
  · have := hC6 n Δ z s2 s3 g T H hH hd ha; linarith

end OVNS.Quant

end
