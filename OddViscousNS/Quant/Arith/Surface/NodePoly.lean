import OddViscousNS.Quant.Arith.Surface.Node
import OddViscousNS.Quant.Arith.Surface.Lead

/-!
# The auxiliary polynomial at a node (route L10)

From the vanishing of all minors to an integer polynomial `G` supported on the exponent set:
`exists_kernel`, `exists_int_kernel`, `polyOf`, then `node_poly`, and the choice of the scale
`theta_ok`: with `K' = e^{C₃} P₀ e^{(1+η)κ̂}`, the scale `ϑ = max(ϑ₀, K'/q^a)` is admissible,
provided `log P₀ ≤ κ̂`.
-/

open Finset MvPolynomial

namespace OVNS.Quant.Surf

section Kernel

variable {ι : Type*} [Fintype ι]

/-- The row of a point. -/
noncomputable def rowQ (es : ι → Fin 3 → ℕ) (ξ : Fin 3 → ℤ) : ι → ℚ :=
  fun j => ∏ l, (ξ l : ℚ) ^ es j l

theorem exists_kernel [DecidableEq ι] (es : ι → Fin 3 → ℕ) (A : Finset (Fin 3 → ℤ))
    (hdet : ∀ pts : ι → Fin 3 → ℤ, (∀ j, pts j ∈ A) → (monoMat pts es).det = 0) :
    ∃ c : ι → ℚ, c ≠ 0 ∧ ∀ ξ ∈ A, ∑ j, c j * rowQ es ξ j = 0 := by
  classical
  set T : Set (ι → ℚ) := rowQ es '' (A : Set (Fin 3 → ℤ)) with hT
  set W := Submodule.span ℚ T with hW
  by_cases htop : W = ⊤
  · exfalso
    obtain ⟨b, hbT, hbspan, hbli⟩ := exists_linearIndependent ℚ T
    have hb_top : Submodule.span ℚ b = ⊤ := hbspan.trans htop
    let _ : Fintype b := by
      have : Finite b := hbli.finite
      exact Fintype.ofFinite _
    have hcard : Fintype.card b = Fintype.card ι := by
      have h1 := finrank_span_eq_card hbli
      have h2 : Submodule.span ℚ (Set.range ((↑) : b → (ι → ℚ))) = ⊤ := by
        simpa using hb_top
      rw [h2, finrank_top, Module.finrank_fintype_fun_eq_card] at h1
      exact h1.symm
    let e : ι ≃ b := (Fintype.equivOfCardEq hcard).symm
    have hch : ∀ i : ι, ∃ ξ ∈ A, rowQ es ξ = (e i : ι → ℚ) := by
      intro i
      obtain ⟨ξ, hξ, h⟩ := hbT (e i).2
      exact ⟨ξ, hξ, h⟩
    choose ξ hξA hξ using hch
    have hd := hdet ξ hξA
    set Mq : Matrix ι ι ℚ := Matrix.of fun i => (e i : ι → ℚ) with hMq
    have hcast : (Int.castRingHom ℚ).mapMatrix (monoMat ξ es) = Mq := by
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hMq, Matrix.of_apply, monoMat]
      rw [← hξ i]
      simp [rowQ]
    have hdetq : Mq.det = 0 := by
      rw [← hcast, ← RingHom.map_det, hd]
      simp
    have hli : LinearIndependent ℚ Mq.row := by
      have : LinearIndependent ℚ (fun i : ι => (e i : ι → ℚ)) :=
        hbli.comp _ e.injective
      exact this
    have hunit := Matrix.linearIndependent_row_iff_isUnit.mp hli
    have := (Matrix.isUnit_iff_isUnit_det Mq).mp hunit
    rw [hdetq] at this
    exact not_isUnit_zero this
  · obtain ⟨f, hf0, hfW⟩ := Submodule.exists_le_ker_of_lt_top W (lt_top_iff_ne_top.mpr htop)
    refine ⟨fun j => f (Pi.single j 1), ?_, ?_⟩
    · intro h
      apply hf0
      ext j
      have := congrFun h j
      simpa using this
    · intro ξ hξ
      have hmem : rowQ es ξ ∈ W := Submodule.subset_span ⟨ξ, hξ, rfl⟩
      have h0 : f (rowQ es ξ) = 0 := hfW hmem
      rw [← h0]
      have : rowQ es ξ = ∑ j, rowQ es ξ j • (Pi.single j 1 : ι → ℚ) := by
        funext k
        simp [Finset.sum_apply, Pi.single_apply]
      conv_rhs => rw [this]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]

/-- The kernel vector with integer coordinates. -/
theorem exists_int_kernel [DecidableEq ι] (es : ι → Fin 3 → ℕ) (A : Finset (Fin 3 → ℤ))
    (hdet : ∀ pts : ι → Fin 3 → ℤ, (∀ j, pts j ∈ A) → (monoMat pts es).det = 0) :
    ∃ z : ι → ℤ, z ≠ 0 ∧ ∀ ξ ∈ A, ∑ j, z j * ∏ l, ξ l ^ es j l = 0 := by
  obtain ⟨c, hc0, hc⟩ := exists_kernel es A hdet
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ) (univ : Finset ι) c
  have hb0 : ((b : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast nonZeroDivisors.ne_zero b.2
  have hz : ∀ j, ∃ z : ℤ, (z : ℚ) = ((b : ℤ) : ℚ) * c j := by
    intro j
    obtain ⟨z, hz⟩ := hb j (mem_univ j)
    refine ⟨z, ?_⟩
    have : (z : ℚ) = (b : ℤ) • c j := by simpa using hz
    rw [this]
    simp
  choose z hz using hz
  refine ⟨z, ?_, fun ξ hξ => ?_⟩
  · intro h0
    apply hc0
    funext j
    have := hz j
    rw [h0] at this
    simp only [Pi.zero_apply, Int.cast_zero] at this
    exact (mul_eq_zero.1 this.symm).resolve_left hb0
  · have h := hc ξ hξ
    have e : ((∑ j, z j * ∏ l, ξ l ^ es j l : ℤ) : ℚ) =
        ((b : ℤ) : ℚ) * ∑ j, c j * rowQ es ξ j := by
      push_cast
      rw [Finset.mul_sum]
      refine sum_congr rfl fun j _ => ?_
      rw [hz j, ← mul_assoc]
      rfl
    rw [h, mul_zero] at e
    exact_mod_cast e

/-- The polynomial with exponents `es` and coefficients `z`. -/
noncomputable def polyOf (es : ι → Fin 3 → ℕ) (z : ι → ℤ) : MvPolynomial (Fin 3) ℤ :=
  ∑ j, monomial (Finsupp.equivFunOnFinite.symm (es j)) (z j)

lemma eval_polyOf (es : ι → Fin 3 → ℕ) (z : ι → ℤ) (x : Fin 3 → ℤ) :
    eval x (polyOf es z) = ∑ j, z j * ∏ l, x l ^ es j l := by
  simp only [polyOf, map_sum, eval_monomial]
  refine sum_congr rfl fun j _ => ?_
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rfl

lemma mem_support_polyOf {es : ι → Fin 3 → ℕ} {z : ι → ℤ} {d : Fin 3 →₀ ℕ}
    (hd : d ∈ (polyOf es z).support) : ∃ j, ∀ i, d i = es j i := by
  classical
  have h := support_sum hd
  obtain ⟨j, -, hj⟩ := mem_biUnion.1 h
  have := support_monomial_subset hj
  rw [mem_singleton] at this
  exact ⟨j, fun i => by rw [this]; rfl⟩

lemma polyOf_ne_zero {es : ι → Fin 3 → ℕ} (hes : Function.Injective es) {z : ι → ℤ} (hz : z ≠ 0) :
    polyOf es z ≠ 0 := by
  classical
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.1 hz
  intro h0
  have h : (polyOf es z).coeff (Finsupp.equivFunOnFinite.symm (es j₀)) = 0 := by
    rw [h0]; simp
  rw [polyOf, coeff_sum, Finset.sum_eq_single j₀] at h
  · simp only [coeff_monomial, ite_true] at h
    exact hj₀ h
  · intro j _ hj
    have hne : Finsupp.equivFunOnFinite.symm (es j) ≠ Finsupp.equivFunOnFinite.symm (es j₀) :=
      fun he => hj (hes (Finsupp.equivFunOnFinite.symm.injective he))
    simp only [coeff_monomial, hne, ite_false]
  · exact fun h => (h (mem_univ _)).elim

lemma totalDegree_polyOf_le {es : ι → Fin 3 → ℕ} {z : ι → ℤ} {X : ℝ} (hX : 0 ≤ X)
    (h : ∀ j, (∑ i, (es j i : ℝ)) ≤ X) : ((polyOf es z).totalDegree : ℝ) ≤ X := by
  have hle : (polyOf es z).totalDegree ≤ ⌊X⌋₊ := by
    refine Finset.sup_le fun d hd => ?_
    obtain ⟨j, hj⟩ := mem_support_polyOf hd
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    refine Nat.le_floor ?_
    push_cast
    simp only [hj]
    exact h j
  exact (Nat.cast_le.2 hle).trans (Nat.floor_le hX)

end Kernel

/-- **The node polynomial.** -/
theorem node_poly : ∃ C₅ : ℝ, 0 ≤ C₅ ∧ ∀ (Δ z n3 ni nj s3 g c : ℤ)
    (F1 F0 : MvPolynomial (Fin 2) ℤ) (Bad : ℤ) (B l : Fin 3 → ℝ) (L Mb ϑ : ℝ) (P₀ q a : ℕ)
    (T : Finset (Fin 3 → ℤ)),
    Δ ≠ 0 → g ≠ 0 →
    surfacePoly Δ z n3 ni nj s3 g =
      C c * X 2 ^ 2 + rename Fin.castSucc F1 * X 2 + rename Fin.castSucc F0 →
    PointCount (surfacePoly Δ z n3 ni nj s3 g) Bad → Bad ≠ 0 → |(Bad : ℝ)| ≤ Mb →
    (∀ i, 1 < B i) → (∀ i, l i = Real.log (B i)) → (∀ i, l i ≤ L) → (∀ i, L ≤ 6 * l i) →
    Real.log Mb ≤ P₀ → 18 ≤ P₀ →
    NodeHyp (surfacePoly Δ z n3 ni nj s3 g) c F1 B Mb P₀ q a T → 77 ≤ ϑ →
    Real.log P₀ + C₅ + (1 + 1199 / ϑ) * kappaHat l <
      Real.log ϑ + (a : ℝ) * Real.log q * (1 - 3 / ϑ) →
    ∃ G : MvPolynomial (Fin 3) ℤ,
      ¬ MvPolynomial.map (Int.castRingHom ℚ) (surfacePoly Δ z n3 ni nj s3 g) ∣
        MvPolynomial.map (Int.castRingHom ℚ) G ∧
      (G.totalDegree : ℝ) ≤ 30 + 9 * ϑ ∧ ∀ x ∈ T, eval x G = 0 := by
  classical
  obtain ⟨C₅, hC₅, hcore⟩ := det_eq_zero_core
  refine ⟨C₅, hC₅, ?_⟩
  intro Δ z n3 ni nj s3 g c F1 F0 Bad B l L Mb ϑ P₀ q a T hΔ hg hF hPC hBad hBadMb hB hlB hL hL6
    hMb hP₀ hN hϑ hnum
  have hl : ∀ i, 0 < l i := fun i => by rw [hlB]; exact Real.log_pos (hB i)
  obtain ⟨hE, hS⟩ := weight_bound hl hL hL6 hϑ
  have hdet := hcore c F1 F0 _ Bad B l (kappaHat l) Mb ϑ P₀ q a T _ hF hPC hBad hBadMb
    (fun i => (hB i).le) hlB (Real.sqrt_nonneg _) hMb hP₀ hN hϑ hE hS hnum
  obtain ⟨w, hw0, hw⟩ := exists_int_kernel (Subtype.val : ↥(expSet l (scaleY l L ϑ)) → Fin 3 → ℕ) T
    hdet
  have hϑ0 : 0 ≤ ϑ := by linarith
  set G := polyOf (Subtype.val : ↥(expSet l (scaleY l L ϑ)) → Fin 3 → ℕ) w with hG
  have hG0 : G ≠ 0 := polyOf_ne_zero Subtype.val_injective hw0
  refine ⟨G, ?_, ?_, ?_⟩
  · refine not_dvd_of_support Δ z n3 ni nj s3 g hΔ hg G hG0 fun d hd => ?_
    obtain ⟨j, hj⟩ := mem_support_polyOf hd
    rw [hj, hj]
    exact ((mem_expSet hl).1 j.2).1
  · exact totalDegree_polyOf_le (by positivity) fun j => deg_of_mem_expSet hl hL hL6 hϑ0 j.2
  · intro x hx
    rw [hG, eval_polyOf]
    exact hw x hx

/-- The choice of the scale. -/
lemma theta_ok {η ϑ₀ C₅ C₃ κ lP lK t ϑ : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hϑ₀ : 1208 / η ≤ ϑ₀)
    (hC₃ : 2 * C₅ + 2 ≤ C₃) (hC₅ : 0 ≤ C₅) (hκ : 0 ≤ κ) (hlP : lP ≤ κ)
    (hlK : lK = C₃ + lP + (1 + η) * κ) (hϑ : ϑ = max ϑ₀ (Real.exp (lK - t))) :
    lP + C₅ + (1 + 1199 / ϑ) * κ < Real.log ϑ + t * (1 - 3 / ϑ) := by
  have h1208 : (1208 : ℝ) ≤ 1208 / η := by
    rw [le_div_iff₀ hη]
    nlinarith
  have hϑ₀' : 1208 ≤ ϑ₀ := by linarith
  have hϑ1 : ϑ₀ ≤ ϑ := by rw [hϑ]; exact le_max_left _ _
  have hϑ2 : Real.exp (lK - t) ≤ ϑ := by rw [hϑ]; exact le_max_right _ _
  have hϑ0 : 0 < ϑ := by linarith
  have hlogϑ : 0 ≤ Real.log ϑ := Real.log_nonneg (by linarith)
  have hC₃0 : 0 ≤ C₃ := by linarith
  have hbig : 1208 * κ ≤ η * ϑ * κ := by
    have : 1208 ≤ η * ϑ := by
      have : 1208 / η ≤ ϑ := by linarith
      rw [div_le_iff₀ hη] at this
      linarith
    exact mul_le_mul_of_nonneg_right this hκ
  have e1 : 1199 / ϑ * κ * ϑ = 1199 * κ := by field_simp
  have hmul : (Real.log ϑ + t * (1 - 3 / ϑ) - (lP + C₅ + (1 + 1199 / ϑ) * κ)) * ϑ =
      (Real.log ϑ + t - lP - C₅ - κ) * ϑ - 3 * t - 1199 * κ := by
    field_simp
    ring
  have key : 0 < (Real.log ϑ + t * (1 - 3 / ϑ) - (lP + C₅ + (1 + 1199 / ϑ) * κ)) * ϑ := by
    rw [hmul]
    rcases eq_or_lt_of_le hϑ2 with hEq | hlt
    · -- `ϑ = exp (lK - t)`
      have hlog : Real.log ϑ = lK - t := by rw [← hEq, Real.log_exp]
      have h3 : t ≤ lK := by linarith
      have h4 : lK ≤ C₃ + 3 * κ := by
        rw [hlK]
        nlinarith
      have h5 : 1 ≤ ϑ / 6 := by
        rw [le_div_iff₀ (by norm_num)]
        linarith
      rw [hlog, hlK]
      have h6 : 3 * t ≤ 3 * C₃ + 9 * κ := by linarith
      have h7 : 3 * C₃ ≤ C₃ * (ϑ / 2) := by nlinarith
      have h8 : (2 * C₅ + 2) * (ϑ / 2) ≤ C₃ * (ϑ / 2) :=
        mul_le_mul_of_nonneg_right hC₃ (by linarith)
      have h9 : 0 < ϑ := hϑ0
      nlinarith
    · -- `ϑ = ϑ₀`
      have hϑe : ϑ = ϑ₀ := by
        rw [hϑ]
        exact max_eq_left (by
          rw [hϑ] at hlt
          by_contra hc
          push Not at hc
          rw [max_eq_right hc.le] at hlt
          exact lt_irrefl _ hlt)
      have hexp : Real.exp (lK - t) ≤ ϑ := hϑ2
      have hlog : lK - t ≤ Real.log ϑ := by
        rw [← Real.log_exp (lK - t)]
        exact Real.log_le_log (Real.exp_pos _) hexp
      have h3 : lK ≤ Real.log ϑ + t := by linarith
      rw [hlK] at h3
      -- `(log ϑ + t) ϑ - 3 t ≥ (C₃ + lP + (1+η) κ) (ϑ - 3)`
      have h4 : (C₃ + lP + (1 + η) * κ) * (ϑ - 3) ≤ (Real.log ϑ + t) * (ϑ - 3) :=
        mul_le_mul_of_nonneg_right h3 (by linarith)
      have h5 : 0 ≤ 3 * Real.log ϑ := by positivity
      have h6 : 3 * lP ≤ 3 * κ := by linarith
      have h7 : (2 * C₅ + 2) * (ϑ / 2) ≤ C₃ * (ϑ / 2) :=
        mul_le_mul_of_nonneg_right hC₃ (by linarith)
      have h8 : 3 * C₃ ≤ C₃ * (ϑ / 2) := by nlinarith
      nlinarith
  have := (mul_pos_iff_of_pos_right hϑ0).1 key
  linarith

end OVNS.Quant.Surf
