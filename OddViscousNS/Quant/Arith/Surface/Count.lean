import OddViscousNS.Quant.Arith.Surface.ShellData
import OddViscousNS.Quant.Arith.Weighted.CaseTable
import OddViscousNS.Quant.Arith.Weighted.Factor

/-!
# Counting the shell points on curves

Transfer from the points of the surface to the shell points:
* `card_le_of_curves`: shell points on finitely many integer curves;
* `split_part`: a set of shell points splits into points on the low curves (`plane_factor_count`)
  and exceptional projected points, the projection being at most two-to-one (`proj_two_to_one`);
* `zero_part`: the shell points with `m = 0` lie on at most `24` curves of degree `≤ 24`.
-/

open MvPolynomial Finset

namespace OVNS.Quant.Surf

open private clear_denom from OddViscousNS.Quant.Arith.Weighted.Factor

/-- A `ℚ`-irreducible polynomial has an integer multiple with the same zeros. -/
lemma exists_int_factor (H : MvPolynomial (Fin 2) ℚ) (hH : Irreducible H) :
    ∃ H' : MvPolynomial (Fin 2) ℤ, Irreducible (MvPolynomial.map (Int.castRingHom ℚ) H') ∧
      H'.totalDegree = H.totalDegree ∧
      ∀ x : Fin 3 → ℤ, eval (proj2 x) H = 0 → eval (fun i : Fin 2 => x i.castSucc) H' = 0 := by
  obtain ⟨H', d, hd, hH'⟩ := clear_denom H
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have hCd : C (d : ℚ) ≠ (0 : MvPolynomial (Fin 2) ℚ) := by simpa using hdq
  refine ⟨H', ?_, ?_, fun x hx => ?_⟩
  · rw [hH', irreducible_isUnit_mul ((Ne.isUnit hdq).map C)]
    exact hH
  · rw [← totalDegree_mapQ, hH', totalDegree_mul_of_isDomain hCd hH.ne_zero, totalDegree_C,
      zero_add]
  · have h := eval_proj2 x H'
    rw [hH', map_mul, hx, mul_zero] at h
    exact_mod_cast h.symm

lemma surfPt_cast (Δ : ℕ) (s2 : ℤ) (g : ℕ) (i : Fin 3) (n k : Mode) :
    (fun l : Fin 2 => surfPt Δ s2 g i n k (Fin.castSucc l)) = projPt Δ s2 g n k := by
  funext l
  fin_cases l <;> rfl

/-- The derivative of the surface in `X₃`. -/
noncomputable def sG0 (c : ℤ) (F1 : MvPolynomial (Fin 2) ℤ) : MvPolynomial (Fin 3) ℤ :=
  C (2 * c) * X 2 + rename Fin.castSucc F1

lemma eval_sG0 (c : ℤ) (F1 : MvPolynomial (Fin 2) ℤ) (x : Fin 3 → ℤ) :
    eval x (sG0 c F1) = mVal c F1 x := by
  simp [sG0, mVal, eval_rename, Function.comp_def]

lemma td_sL (Δ z n3 s3 g : ℤ) : (sL Δ z n3 s3 g).totalDegree ≤ 3 := by
  have hX : ∀ i : Fin 2, (X i : MvPolynomial (Fin 2) ℤ).totalDegree ≤ 1 := fun i => by
    rw [totalDegree_X]
  have hsq : ((X 0 : MvPolynomial (Fin 2) ℤ) ^ 2).totalDegree ≤ 2 :=
    (totalDegree_pow _ _).trans (by have := hX 0; omega)
  have hCX : ∀ (r : ℤ) (p : MvPolynomial (Fin 2) ℤ) (d : ℕ), p.totalDegree ≤ d → d ≤ 3 →
      (C r * p).totalDegree ≤ 3 := fun r p d hp hd =>
    (totalDegree_mul _ _).trans (by rw [totalDegree_C]; omega)
  unfold sL
  refine (totalDegree_sub _ _).trans (max_le ((totalDegree_sub _ _).trans (max_le
    ((totalDegree_sub _ _).trans (max_le ((totalDegree_sub _ _).trans (max_le ?_ ?_)) ?_)) ?_)) ?_)
  · refine (totalDegree_mul _ _).trans ?_
    have h1 : (-C (2 * Δ * g ^ 2) * X 0 ^ 2 : MvPolynomial (Fin 2) ℤ).totalDegree ≤ 2 := by
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_neg, totalDegree_C]
      omega
    have := hX 1
    omega
  · exact hCX _ _ 2 hsq (by norm_num)
  · exact hCX _ _ 1 (hX 0) (by norm_num)
  · rw [totalDegree_C]
    norm_num
  · exact hCX _ _ 1 (hX 1) (by norm_num)

lemma td_sF1 (Δ z n3 ni s3 g : ℤ) : (sF1 Δ z n3 ni s3 g).totalDegree ≤ 3 := by
  unfold sF1
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_neg, totalDegree_C]
  have := td_sL Δ z n3 s3 g
  omega

section
variable {n : Mode} {Δ z : ℕ} {s2 s3 : ℤ} {g T : ℕ}

/-- Shell points on finitely many integer curves. -/
lemma card_le_of_curves {A : Finset Mode} (hA : A ⊆ shellPts n Δ z s2 s3 g T)
    (L : Finset (MvPolynomial (Fin 2) ℤ))
    (hcov : ∀ k ∈ A, ∃ H ∈ L, eval (projPt Δ s2 g n k) H = 0) {M : ℝ}
    (hM : ∀ H ∈ L, (curveCount n Δ z s2 s3 g T H : ℝ) ≤ M) :
    (A.card : ℝ) ≤ L.card * M := by
  classical
  have hsub : A ⊆ L.biUnion fun H =>
      (shellPts n Δ z s2 s3 g T).filter fun k => eval (projPt Δ s2 g n k) H = 0 := by
    intro k hk
    obtain ⟨H, hH, h0⟩ := hcov k hk
    exact mem_biUnion.2 ⟨H, hH, mem_filter.2 ⟨hA hk, h0⟩⟩
  have h1 := (card_le_card hsub).trans card_biUnion_le
  have h2 : (A.card : ℝ) ≤ ∑ H ∈ L, (curveCount n Δ z s2 s3 g T H : ℝ) := by
    exact_mod_cast h1
  refine h2.trans ((sum_le_sum hM).trans ?_)
  rw [Finset.sum_const, nsmul_eq_mul]

/-- The splitting of a set of shell points along a finite set of curves over `ℚ`. -/
lemma split_part (hH : ShellHyp n Δ z g T) {A : Finset Mode}
    (hA : A ⊆ shellPts n Δ z s2 s3 g T) (i : Fin 3)
    (low : Finset (MvPolynomial (Fin 2) ℚ)) {D' M : ℝ} (hM0 : 0 ≤ M)
    (hlow : ∀ H ∈ low, Irreducible H ∧ (H.totalDegree : ℝ) ≤ D')
    (hM : ∀ H : MvPolynomial (Fin 2) ℤ, Irreducible (MvPolynomial.map (Int.castRingHom ℚ) H) →
      (H.totalDegree : ℝ) ≤ D' → (curveCount n Δ z s2 s3 g T H : ℝ) ≤ M) :
    (A.card : ℝ) ≤ low.card * M + 2 * (((A.image fun k => proj2 (surfPt Δ s2 g i n k)).filter
      fun y => ∀ H ∈ low, eval y H ≠ 0).card : ℝ) := by
  classical
  set x : Mode → Fin 3 → ℤ := surfPt Δ s2 g i n with hx
  have hch : ∀ H ∈ low, ∃ H' : MvPolynomial (Fin 2) ℤ,
      Irreducible (MvPolynomial.map (Int.castRingHom ℚ) H') ∧ H'.totalDegree = H.totalDegree ∧
      ∀ x : Fin 3 → ℤ, eval (proj2 x) H = 0 → eval (fun i : Fin 2 => x i.castSucc) H' = 0 :=
    fun H hH => exists_int_factor H (hlow H hH).1
  choose! φ hφ1 hφ2 hφ3 using hch
  set A₁ := A.filter fun k => ¬ ∀ H ∈ low, eval (proj2 (x k)) H ≠ 0 with hA₁
  set A₂ := A.filter fun k => ∀ H ∈ low, eval (proj2 (x k)) H ≠ 0 with hA₂
  have hsplit : (A.card : ℝ) = A₂.card + A₁.card := by
    exact_mod_cast (card_filter_add_card_filter_not (s := A)
      (fun k => ∀ H ∈ low, eval (proj2 (x k)) H ≠ 0)).symm
  have h1 : (A₁.card : ℝ) ≤ low.card * M := by
    have hc := card_le_of_curves (A := A₁) (M := M) ((filter_subset _ _).trans hA) (low.image φ)
      (fun k hk => ?_) (fun H hH => ?_)
    · refine hc.trans (mul_le_mul_of_nonneg_right ?_ hM0)
      exact_mod_cast card_image_le
    · have := (mem_filter.1 hk).2
      push Not at this
      obtain ⟨H, hH, h0⟩ := this
      refine ⟨φ H, mem_image_of_mem _ hH, ?_⟩
      have := hφ3 H hH (x k) h0
      rwa [hx, surfPt_cast] at this
    · obtain ⟨H', hH', rfl⟩ := mem_image.1 hH
      refine hM _ (hφ1 H' hH') ?_
      rw [hφ2 H' hH']
      exact (hlow H' hH').2
  have h2 : (A₂.card : ℝ) ≤ 2 * (((A.image fun k => proj2 (x k)).filter
      fun y => ∀ H ∈ low, eval y H ≠ 0).card : ℝ) := by
    have hle := card_le_mul_card_image_of_maps_to (s := A₂) (f := fun k => proj2 (x k))
      (t := (A.image fun k => proj2 (x k)).filter fun y => ∀ H ∈ low, eval y H ≠ 0)
      (fun k hk => ?_) 2 (fun y _ => ?_)
    · exact_mod_cast hle
    · obtain ⟨hk1, hk2⟩ := mem_filter.1 hk
      exact mem_filter.2 ⟨mem_image_of_mem _ hk1, hk2⟩
    · rcases (A₂.filter fun k => proj2 (x k) = y).eq_empty_or_nonempty with h0 | ⟨k₀, hk₀⟩
      · rw [h0, card_empty]
        omega
      refine (card_le_card fun k hk => ?_).trans
        (proj_two_to_one n Δ z s2 s3 g T hH (projPt Δ s2 g n k₀))
      obtain ⟨hk1, hk2⟩ := mem_filter.1 hk
      obtain ⟨hk3, hk4⟩ := mem_filter.1 hk₀
      refine mem_filter.2 ⟨hA (mem_filter.1 hk1).1, ?_⟩
      have e : proj2 (x k) = proj2 (x k₀) := hk2.trans hk4.symm
      rw [← surfPt_cast Δ s2 g i n k, ← surfPt_cast Δ s2 g i n k₀]
      funext l
      have := congrFun e l
      simp only [proj2] at this
      exact_mod_cast this
  rw [hsplit]
  linarith

/-- The shell points with `m = 0`. -/
theorem zero_part (D : SurfData)
    (hD1 : D.F1.totalDegree ≤ 3) {A : Finset Mode} (hA : A ⊆ shellPts n Δ z s2 s3 g T) (x : Mode → Fin 3 → ℤ)
    (hx : ∀ k ∈ A, eval (x k) D.F = 0 ∧ mVal D.c D.F1 (x k) = 0 ∧
      (fun l : Fin 2 => x k (Fin.castSucc l)) = projPt Δ s2 g n k) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ H : MvPolynomial (Fin 2) ℤ, Irreducible (MvPolynomial.map (Int.castRingHom ℚ) H) →
      H.totalDegree ≤ 24 → (curveCount n Δ z s2 s3 g T H : ℝ) ≤ M) :
    (A.card : ℝ) ≤ 24 * M := by
  classical
  set G := sG0 D.c D.F1 with hG
  have hGd : G.totalDegree ≤ 3 := by
    refine (totalDegree_add _ _).trans (max_le ?_ ((totalDegree_rename_le _ _).trans hD1))
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, totalDegree_X]
    norm_num
  have hG0 : G ≠ 0 := by
    intro h0
    have e : (fun i : Fin 2 => (![0, 0, 1] : Fin 3 → ℤ) i.castSucc) =
        fun i => (![0, 0, 0] : Fin 3 → ℤ) i.castSucc := by
      funext i
      fin_cases i <;> rfl
    have h1 : eval ![0, 0, 1] G = 0 := by rw [h0, map_zero]
    have h2 : eval ![0, 0, 0] G = 0 := by rw [h0, map_zero]
    rw [hG, eval_sG0, mVal, e] at h1
    rw [hG, eval_sG0, mVal] at h2
    have h3 : 2 * D.c = 0 := by
      simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, mul_one, mul_zero,
        zero_add] at h1 h2
      linarith
    exact D.hc (by linarith)
  have hnot : ¬ MvPolynomial.map (Int.castRingHom ℚ) D.F ∣ MvPolynomial.map (Int.castRingHom ℚ) G := by
    refine not_dvd_of_support _ _ _ _ _ _ _ D.hΔ D.hg G hG0 fun d hd => Or.inl ?_
    have h1 := le_totalDegree hd
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_three] at h1
    omega
  obtain ⟨R, hR0, hRd, hRz⟩ := resultant_projection_lin D.F G D.c D.hc D.F1 D.F0 D.hF
    (surface_totalDegree _ _ _ _ _ _ _ D.hΔ D.hg).le D.hirr hnot
  have hRd' : R.totalDegree ≤ 24 := by omega
  obtain ⟨L, hL1, hL2, hL3⟩ := resultant_factor_cover R hR0
  have hc := card_le_of_curves (A := A) hA L.toFinset (M := M) (fun k hk => ?_) (fun H hH => ?_)
  · refine hc.trans (mul_le_mul_of_nonneg_right ?_ hM0)
    have : L.toFinset.card ≤ 24 := (List.toFinset_card_le _).trans (hL1.trans hRd')
    exact_mod_cast this
  · obtain ⟨h1, h2, h3⟩ := hx k hk
    have hz := hRz (x k) h1 (by rw [hG, eval_sG0]; exact h2)
    rw [h3] at hz
    obtain ⟨H, hH, h0⟩ := hL3 _ hz
    exact ⟨H, List.mem_toFinset.2 hH, h0⟩
  · obtain ⟨h1, h2⟩ := hL2 H (List.mem_toFinset.1 hH)
    exact hM H h1 (h2.trans hRd')

end

end OVNS.Quant.Surf
