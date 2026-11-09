import OddViscousNS.Quant.Arith.Surface.NodePoly
import OddViscousNS.Quant.Arith.Surface.ResultantLin
import OddViscousNS.Quant.Arith.Surface.Chain

/-!
# The prime-power tree (route L12, L13)

For a prime `q` the points of `S₀` (zeros of the surface in a box, `m ≠ 0`, `q ∤ m`) are organised in the
tree of classes `(x₁ mod q^a, x₂ mod q^a, x₃ mod q)`.  At every class `node_poly` and
`resultant_projection_lin` give a plane polynomial of degree `≤ 312 max(ϑ₀, K/q^a)`, and `chain_cover`
gives `tree_cover`: at most `312 ϑ₀ K` low curves of degree `≤ 312 ϑ₀`, and off them at most
`L₀ (312 ϑ₀)² q³ K²` plane points.
-/

open MvPolynomial Finset

namespace OVNS.Quant.Surf

/-- The data of a surface over a box, with the bookkeeping hypotheses of `node_poly`. -/
structure SurfData where
  (Δ z n3 ni nj s3 g c Bad : ℤ)
  (F1 F0 : MvPolynomial (Fin 2) ℤ)
  (B l : Fin 3 → ℝ)
  (L Mb : ℝ)
  (P₀ : ℕ)
  hΔ : Δ ≠ 0
  hg : g ≠ 0
  hc : c ≠ 0
  hF : surfacePoly Δ z n3 ni nj s3 g =
    C c * X 2 ^ 2 + rename Fin.castSucc F1 * X 2 + rename Fin.castSucc F0
  hirr : Irreducible (MvPolynomial.map (Int.castRingHom ℚ) (surfacePoly Δ z n3 ni nj s3 g))
  hPC : PointCount (surfacePoly Δ z n3 ni nj s3 g) Bad
  hBad : Bad ≠ 0
  hBadMb : |(Bad : ℝ)| ≤ Mb
  hB : ∀ i, 1 < B i
  hlB : ∀ i, l i = Real.log (B i)
  hL : ∀ i, l i ≤ L
  hL6 : ∀ i, L ≤ 6 * l i
  hMb : Real.log Mb ≤ P₀
  hP₀ : 18 ≤ P₀
  hκ : Real.log P₀ ≤ kappaHat l

/-- The surface of the data. -/
noncomputable abbrev SurfData.F (D : SurfData) : MvPolynomial (Fin 3) ℤ :=
  surfacePoly D.Δ D.z D.n3 D.ni D.nj D.s3 D.g

/-- The projection to the plane, over `ℚ`. -/
def proj2 (x : Fin 3 → ℤ) : Fin 2 → ℚ := fun i => (x i.castSucc : ℚ)

/-- The class of a point at level `a`. -/
def clT (q : ℤ) : ℕ → (Fin 3 → ℤ) → ℤ × ℤ × ℤ
  | 0, _ => (0, 0, 0)
  | a + 1, x => (x 0 % q ^ (a + 1), x 1 % q ^ (a + 1), x 2 % q)

/-- The parent of a class. -/
def parT (q : ℤ) : ℕ → ℤ × ℤ × ℤ → ℤ × ℤ × ℤ
  | 0, _ => (0, 0, 0)
  | a + 1, c => (c.1 % q ^ (a + 1), c.2.1 % q ^ (a + 1), c.2.2 % q)

/-- The classes at level `a`. -/
def ClT (q : ℤ) : ℕ → Finset (ℤ × ℤ × ℤ)
  | 0 => {(0, 0, 0)}
  | a + 1 => Ico 0 (q ^ (a + 1)) ×ˢ (Ico 0 (q ^ (a + 1)) ×ˢ Ico 0 q)

lemma parT_clT (q : ℤ) (a : ℕ) (x : Fin 3 → ℤ) : parT q a (clT q (a + 1) x) = clT q a x := by
  cases a with
  | zero => rfl
  | succ a =>
    simp only [parT, clT]
    have h : q ^ (a + 1) ∣ q ^ (a + 1 + 1) := pow_dvd_pow _ (by omega)
    rw [Int.emod_emod_of_dvd _ h, Int.emod_emod_of_dvd _ h, Int.emod_emod_of_dvd _ dvd_rfl]

lemma clT_mem {q : ℤ} (hq : 0 < q) (a : ℕ) (x : Fin 3 → ℤ) : clT q a x ∈ ClT q a := by
  cases a with
  | zero => simp [clT, ClT]
  | succ a =>
    simp only [clT, ClT, mem_product, mem_Ico]
    have h : 0 < q ^ (a + 1) := by positivity
    exact ⟨⟨Int.emod_nonneg _ h.ne', Int.emod_lt_of_pos _ h⟩,
      ⟨Int.emod_nonneg _ h.ne', Int.emod_lt_of_pos _ h⟩,
      ⟨Int.emod_nonneg _ hq.ne', Int.emod_lt_of_pos _ hq⟩⟩

lemma card_ClT_succ (q : ℕ) (a : ℕ) : (ClT (q : ℤ) (a + 1)).card = q ^ (2 * a + 3) := by
  simp only [ClT, card_product, Int.card_Ico, sub_zero]
  have e : ((q : ℤ) ^ (a + 1)).toNat = q ^ (a + 1) := by
    rw [← Nat.cast_pow, Int.toNat_natCast]
  rw [e, Int.toNat_natCast]
  ring

lemma dvd_of_clT_eq {q : ℤ} {a : ℕ} (ha : 1 ≤ a) {x x' : Fin 3 → ℤ}
    (h : clT q a x = clT q a x') :
    (q ^ a ∣ x 0 - x' 0) ∧ (q ^ a ∣ x 1 - x' 1) ∧ (q ∣ x 2 - x' 2) := by
  cases a with
  | zero => omega
  | succ a =>
    simp only [clT, Prod.mk.injEq] at h
    obtain ⟨h0, h1, h2⟩ := h
    exact ⟨Int.ModEq.dvd (Int.ModEq.symm h0), Int.ModEq.dvd (Int.ModEq.symm h1),
      Int.ModEq.dvd (Int.ModEq.symm h2)⟩

lemma totalDegree_mapQ (p : MvPolynomial (Fin 2) ℤ) :
    (MvPolynomial.map (Int.castRingHom ℚ) p).totalDegree = p.totalDegree := by
  simp only [totalDegree, support_map_of_injective _ (f := Int.castRingHom ℚ) Int.cast_injective]

lemma eval_proj2 (x : Fin 3 → ℤ) (P : MvPolynomial (Fin 2) ℤ) :
    eval (proj2 x) (MvPolynomial.map (Int.castRingHom ℚ) P) =
      ((eval (fun i : Fin 2 => x i.castSucc) P : ℤ) : ℚ) := by
  unfold proj2
  induction P using MvPolynomial.induction_on <;> simp_all

/-- A divisor of a nonzero polynomial has smaller degree. -/
lemma totalDegree_le_of_dvd {H R : MvPolynomial (Fin 2) ℚ} (hR : R ≠ 0) (h : H ∣ R) :
    H.totalDegree ≤ R.totalDegree := by
  obtain ⟨W, rfl⟩ := h
  have hH : H ≠ 0 := left_ne_zero_of_mul hR
  have hW : W ≠ 0 := right_ne_zero_of_mul hR
  rw [totalDegree_mul_of_isDomain hH hW]
  omega

/-- A node gives a plane polynomial of degree `≤ 312 ϑ`. -/
theorem node_resultant : ∃ C₅ : ℝ, 0 ≤ C₅ ∧ ∀ (D : SurfData) (ϑ : ℝ) (q a : ℕ)
    (T : Finset (Fin 3 → ℤ)), NodeHyp D.F D.c D.F1 D.B D.Mb D.P₀ q a T → 77 ≤ ϑ →
    Real.log D.P₀ + C₅ + (1 + 1199 / ϑ) * kappaHat D.l <
      Real.log ϑ + (a : ℝ) * Real.log q * (1 - 3 / ϑ) →
    ∃ R : MvPolynomial (Fin 2) ℤ, R ≠ 0 ∧ (R.totalDegree : ℝ) ≤ 312 * ϑ ∧
      ∀ x ∈ T, eval (fun i : Fin 2 => x i.castSucc) R = 0 := by
  obtain ⟨C₅, hC₅, hnode⟩ := node_poly
  refine ⟨C₅, hC₅, fun D ϑ q a T hN hϑ hnum => ?_⟩
  obtain ⟨G, hG1, hG2, hG3⟩ := hnode D.Δ D.z D.n3 D.ni D.nj D.s3 D.g D.c D.F1 D.F0 D.Bad D.B D.l
    D.L D.Mb ϑ D.P₀ q a T D.hΔ D.hg D.hF D.hPC D.hBad D.hBadMb D.hB D.hlB D.hL D.hL6 D.hMb D.hP₀ hN
    hϑ hnum
  have hF6 : (surfacePoly D.Δ D.z D.n3 D.ni D.nj D.s3 D.g).totalDegree ≤ 6 :=
    (surface_totalDegree _ _ _ _ _ _ _ D.hΔ D.hg).le
  obtain ⟨R, hR0, hRd, hRz⟩ := resultant_projection_lin _ G D.c D.hc D.F1 D.F0 D.hF hF6 D.hirr hG1
  refine ⟨R, hR0, ?_, fun x hx => hRz x (hN.hT x hx).2.1 (hG3 x hx)⟩
  have h1 : (R.totalDegree : ℝ) ≤ 8 * G.totalDegree := by exact_mod_cast hRd
  linarith

/-- One step of the Bézout sum. -/
lemma step_le {ϑ₀ K θ θ' Q q' : ℝ} (hϑ₀ : 1 ≤ ϑ₀) (hQ : 1 ≤ Q) (hK : Q < K) (hq : 1 ≤ q')
    (hθ : θ = max ϑ₀ (K / Q)) (hθ' : θ' = max ϑ₀ (K / (Q * q'))) :
    Q ^ 2 * (312 * θ * (312 * θ')) ≤ (312 * ϑ₀) ^ 2 * K ^ 2 := by
  have hQ0 : 0 < Q := by linarith
  have hK0 : 0 < K := by linarith
  set y := K / Q with hy
  have hy1 : 1 ≤ y := (one_le_div hQ0).2 hK.le
  have h1 : θ ≤ ϑ₀ * y := by
    rw [hθ]
    exact max_le (by nlinarith) (by nlinarith)
  have h2 : θ' ≤ ϑ₀ * y := by
    rw [hθ']
    refine max_le (by nlinarith) ?_
    have : K / (Q * q') ≤ y := by
      rw [hy]
      refine div_le_div_of_nonneg_left hK0.le hQ0 ?_
      nlinarith
    nlinarith
  have hθ0 : 0 ≤ θ := by rw [hθ]; exact le_trans (by linarith) (le_max_left _ _)
  have hθ'0 : 0 ≤ θ' := by rw [hθ']; exact le_trans (by linarith) (le_max_left _ _)
  have h3 : θ * θ' ≤ (ϑ₀ * y) * (ϑ₀ * y) := mul_le_mul h1 h2 hθ'0 (by positivity)
  have h4 : Q ^ 2 * y ^ 2 = K ^ 2 := by
    rw [hy]
    field_simp
  calc Q ^ 2 * (312 * θ * (312 * θ')) = Q ^ 2 * 312 ^ 2 * (θ * θ') := by ring
    _ ≤ Q ^ 2 * 312 ^ 2 * ((ϑ₀ * y) * (ϑ₀ * y)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (312 * ϑ₀) ^ 2 * (Q ^ 2 * y ^ 2) := by ring
    _ = _ := by rw [h4]

/-- The conclusion of the tree for one prime. -/
def TreeProp (η ϑ₀ C₃ : ℝ) : Prop :=
  ∀ (D : SurfData) (q L₀ : ℕ) (S₀ : Finset (Fin 3 → ℤ)) (K : ℝ),
    K = Real.exp C₃ * D.P₀ * Real.exp ((1 + η) * kappaHat D.l) →
    q.Prime → q ≤ D.P₀ → K ≤ (q : ℝ) ^ L₀ →
    (∀ x ∈ S₀, (∀ i, |(x i : ℝ)| ≤ D.B i) ∧ eval x D.F = 0 ∧ mVal D.c D.F1 x ≠ 0 ∧
      |(mVal D.c D.F1 x : ℝ)| ≤ D.Mb ∧ ¬ (q : ℤ) ∣ mVal D.c D.F1 x) →
    ∃ low : Finset (MvPolynomial (Fin 2) ℚ),
      (low.card : ℝ) ≤ 312 * ϑ₀ * K ∧
      (∀ H ∈ low, Irreducible H ∧ (H.totalDegree : ℝ) ≤ 312 * ϑ₀) ∧
      (((S₀.image proj2).filter fun y => ∀ H ∈ low, eval y H ≠ 0).card : ℝ) ≤
        L₀ * (312 * ϑ₀) ^ 2 * (q : ℝ) ^ 3 * K ^ 2

/-- **The tree for one prime.** -/
theorem tree_cover (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) : ∃ ϑ₀ C₃ : ℝ, 1 ≤ ϑ₀ ∧ 0 ≤ C₃ ∧
    TreeProp η ϑ₀ C₃ := by
  classical
  obtain ⟨C₅, hC₅, hnode⟩ := node_resultant
  set ϑ₀ := 1208 / η with hϑ₀
  have hϑ₀1 : 1208 ≤ ϑ₀ := by
    rw [hϑ₀, le_div_iff₀ hη]
    nlinarith
  refine ⟨ϑ₀, 2 * C₅ + 2, by linarith, by positivity, ?_⟩
  intro D q L₀ S₀ K hK hq hqP hKL hS
  have hκ0 : 0 ≤ kappaHat D.l := Real.sqrt_nonneg _
  have hP : (18 : ℝ) ≤ D.P₀ := by exact_mod_cast D.hP₀
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.one_le
  have hq0 : (0 : ℤ) < q := by exact_mod_cast hq.pos
  have hlK : Real.log K = 2 * C₅ + 2 + Real.log D.P₀ + (1 + η) * kappaHat D.l := by
    rw [hK, Real.log_mul (by positivity) (Real.exp_pos _).ne',
      Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp, Real.log_exp]
  have hK1 : 1 ≤ K := by
    have h1 : 1 ≤ Real.exp (2 * C₅ + 2) := Real.one_le_exp (by positivity)
    have h2 : 1 ≤ Real.exp ((1 + η) * kappaHat D.l) := Real.one_le_exp (by positivity)
    rw [hK]
    have h3 : (1 : ℝ) ≤ D.P₀ := by linarith
    have h4 : 1 * 1 ≤ Real.exp (2 * C₅ + 2) * D.P₀ := mul_le_mul h1 h3 (by norm_num) (by positivity)
    have h5 := mul_le_mul (by linarith : 1 ≤ Real.exp (2 * C₅ + 2) * D.P₀) h2 (by norm_num)
      (by positivity)
    linarith
  have hK0 : 0 < K := by linarith
  set ϑ : ℕ → ℝ := fun a => max ϑ₀ (K / (q : ℝ) ^ a) with hϑ
  have hϑ1 : ∀ a, ϑ₀ ≤ ϑ a := fun a => le_max_left _ _
  have hnum : ∀ a : ℕ, Real.log D.P₀ + C₅ + (1 + 1199 / ϑ a) * kappaHat D.l <
      Real.log (ϑ a) + (a : ℝ) * Real.log q * (1 - 3 / ϑ a) := by
    intro a
    refine theta_ok (ϑ₀ := ϑ₀) (C₃ := 2 * C₅ + 2) (lK := Real.log K) hη hη1 le_rfl le_rfl hC₅ hκ0
      D.hκ hlK ?_
    have e : Real.exp (Real.log K - (a : ℝ) * Real.log q) = K / (q : ℝ) ^ a := by
      rw [Real.exp_sub, Real.exp_log hK0, Real.exp_nat_mul, Real.exp_log (by linarith)]
    rw [e]
  set T : ℕ → ℤ × ℤ × ℤ → Finset (Fin 3 → ℤ) := fun a c => S₀.filter fun x => clT q a x = c
    with hT
  have hex : ∀ a c, ∃ R : MvPolynomial (Fin 2) ℤ, R ≠ 0 ∧ (R.totalDegree : ℝ) ≤ 312 * ϑ a ∧
      ∀ x ∈ T a c, eval (fun i : Fin 2 => x i.castSucc) R = 0 := by
    intro a c
    refine hnode D (ϑ a) q a (T a c) ⟨?_, hqP, Or.inr hq, ?_⟩ (by linarith [hϑ1 a]) (hnum a)
    · intro x hx
      obtain ⟨h1, h2, h3, h4, -⟩ := hS x (mem_filter.1 hx).1
      exact ⟨h1, h2, h3, h4⟩
    · intro ha x hx
      obtain ⟨hx1, hx2⟩ := mem_filter.1 hx
      refine ⟨(hS x hx1).2.2.2.2, fun x' hx' => ?_⟩
      exact dvd_of_clT_eq ha (hx2.trans (mem_filter.1 hx').2.symm)
  choose R' hR0 hRd hRz using hex
  set R : ℕ → ℤ × ℤ × ℤ → MvPolynomial (Fin 2) ℚ := fun a c =>
    MvPolynomial.map (Int.castRingHom ℚ) (R' a c) with hR
  have hRne : ∀ a c, R a c ≠ 0 := by
    intro a c h0
    refine hR0 a c (MvPolynomial.map_injective _ (RingHom.injective_int (Int.castRingHom ℚ)) ?_)
    rw [map_zero]
    exact h0
  have hdeg : ∀ a c, ((R a c).totalDegree : ℝ) ≤ 312 * ϑ a := by
    intro a c
    rw [hR, totalDegree_mapQ]
    exact hRd a c
  have hvan : ∀ x ∈ S₀, ∀ a, eval (proj2 x) (R a (clT q a x)) = 0 := by
    intro x hx a
    rw [hR, eval_proj2, hRz a _ x (mem_filter.2 ⟨hx, rfl⟩), Int.cast_zero]
  have hexL : ∃ L', K ≤ (q : ℝ) ^ L' := ⟨L₀, hKL⟩
  have hL'spec : K ≤ (q : ℝ) ^ (Nat.find hexL) := Nat.find_spec hexL
  have hL'min : ∀ a < Nat.find hexL, (q : ℝ) ^ a < K := fun a ha =>
    not_le.1 (Nat.find_min hexL ha)
  have hL'le : Nat.find hexL ≤ L₀ := Nat.find_min' hexL hKL
  set L' := Nat.find hexL with hL'
  obtain ⟨low, h1, h2, h3⟩ := chain_cover S₀ proj2 L' (clT (q : ℤ)) (parT (q : ℤ)) (ClT (q : ℤ))
    (0, 0, 0) R (parT_clT _) (fun x _ a => clT_mem hq0 a x) (fun _ => rfl) hRne
    (fun x hx a _ => hvan x hx a)
  refine ⟨low, ?_, ?_, ?_⟩
  · have h4 : (low.card : ℝ) ≤ ((R 0 (0, 0, 0)).totalDegree : ℝ) := by exact_mod_cast h1
    refine h4.trans ((hdeg 0 _).trans ?_)
    have : ϑ 0 ≤ ϑ₀ * K := by
      refine max_le (by nlinarith) ?_
      simp only [pow_zero, div_one]
      nlinarith
    linarith
  · intro H hH
    obtain ⟨hirr, c, -, hdvd⟩ := h2 H hH
    refine ⟨hirr, ?_⟩
    have h4 : (H.totalDegree : ℝ) ≤ ((R L' c).totalDegree : ℝ) := by
      exact_mod_cast totalDegree_le_of_dvd (hRne L' c) hdvd
    refine h4.trans ((hdeg L' c).trans ?_)
    have : ϑ L' ≤ ϑ₀ := by
      refine max_le le_rfl ?_
      have hqL : 0 < (q : ℝ) ^ L' := by positivity
      exact ((div_le_one hqL).2 hL'spec).trans (by linarith)
    linarith
  · have h4 : (((S₀.image proj2).filter fun y => ∀ H ∈ low, eval y H ≠ 0).card : ℝ) ≤
        ∑ a ∈ range L', ∑ c ∈ ClT (q : ℤ) (a + 1),
          ((R a (parT (q : ℤ) a c)).totalDegree : ℝ) * ((R (a + 1) c).totalDegree : ℝ) := by
      exact_mod_cast h3
    refine h4.trans ?_
    have hstep : ∀ a ∈ range L', ∑ c ∈ ClT (q : ℤ) (a + 1),
        ((R a (parT (q : ℤ) a c)).totalDegree : ℝ) * ((R (a + 1) c).totalDegree : ℝ) ≤
        (312 * ϑ₀) ^ 2 * (q : ℝ) ^ 3 * K ^ 2 := by
      intro a ha
      have haL := mem_range.1 ha
      have hterm : ∀ c ∈ ClT (q : ℤ) (a + 1),
          ((R a (parT (q : ℤ) a c)).totalDegree : ℝ) * ((R (a + 1) c).totalDegree : ℝ) ≤
            312 * ϑ a * (312 * ϑ (a + 1)) := fun c _ =>
        mul_le_mul (hdeg _ _) (hdeg _ _) (Nat.cast_nonneg _)
          (by have := hϑ1 a; linarith)
      refine (sum_le_sum hterm).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul, card_ClT_succ]
      have hs := step_le (ϑ₀ := ϑ₀) (K := K) (Q := (q : ℝ) ^ a) (q' := (q : ℝ))
        (θ := ϑ a) (θ' := ϑ (a + 1)) (by linarith) (one_le_pow₀ hq1) (hL'min a haL) hq1 rfl
        (by simp only [hϑ, pow_succ])
      push_cast
      calc (q : ℝ) ^ (2 * a + 3) * (312 * ϑ a * (312 * ϑ (a + 1)))
          = (q : ℝ) ^ 3 * (((q : ℝ) ^ a) ^ 2 * (312 * ϑ a * (312 * ϑ (a + 1)))) := by ring
        _ ≤ (q : ℝ) ^ 3 * ((312 * ϑ₀) ^ 2 * K ^ 2) :=
            mul_le_mul_of_nonneg_left hs (by positivity)
        _ = _ := by ring
    refine (sum_le_sum hstep).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, card_range, mul_assoc (L₀ : ℝ), mul_assoc (L₀ : ℝ)]
    have h5 : (L' : ℝ) ≤ L₀ := by exact_mod_cast hL'le
    rw [show (312 * ϑ₀) ^ 2 * (q : ℝ) ^ 3 * K ^ 2 = (312 * ϑ₀) ^ 2 * ((q : ℝ) ^ 3 * K ^ 2) by ring]
    exact mul_le_mul_of_nonneg_right h5 (by positivity)

end OVNS.Quant.Surf
