import OddViscousNS.Quant.Arith.Surface.Count
import OddViscousNS.Quant.Arith.Plane.PlaneCount
import OddViscousNS.Quant.Arith.NormCount
import OddViscousNS.Quant.Arith.Algebra.FewPoints

/-!
# The shell bound without the general surface covering (route L13)

`shell_core`: on a shell with `N` large, for fixed parameters: every shell point has `m = 0` (at most
`24` curves) or `q ∤ m` for one of `K₀` primes `q ≈ N^δ`; the tree of each prime gives `≲ K` low curves and
`≲ q³K²` further points, `K ≲ N^{δ + (1+η)p*/2}`.
-/

open MvPolynomial Finset

namespace OVNS.Quant.Surf

/-- The parameters of the assembly, as real inequalities in `N`. -/
structure Params (N δ η ε : ℝ) (K₀ : ℕ) (A₀ : ℝ) : Prop where
  hN2 : 2 ≤ N
  h20 : 20 * Real.log N ≤ N ^ δ
  h72 : 72 * (((K₀ : ℝ) + 1) * Real.log 2) ≤ Real.log N
  hA₀ : A₀ ≤ N ^ ((1 : ℝ) / 2)
  hδ0 : 0 < δ
  hδ1 : δ ≤ 1 / 100
  hδ2 : δ ≤ ε / 10
  hη0 : 0 < η
  hη1 : η ≤ 1 / 10
  hη2 : η ≤ ε / 2
  hK₀ : 21 / δ ≤ K₀
  hK₅ : 5 ≤ K₀

section

variable {N δ η ε A₀ : ℝ} {K₀ : ℕ}

lemma Params.N_pos (h : Params N δ η ε K₀ A₀) : 0 < N := by linarith [h.hN2]
lemma Params.N_one (h : Params N δ η ε K₀ A₀) : 1 ≤ N := by linarith [h.hN2]

/-- The size of `Q`. -/
lemma Params.Q_bounds (h : Params N δ η ε K₀ A₀) :
    N ^ δ ≤ (⌈N ^ δ⌉₊ : ℝ) ∧ (⌈N ^ δ⌉₊ : ℝ) ≤ 2 * N ^ δ ∧ 1 ≤ N ^ δ := by
  have h1 : 1 ≤ N ^ δ := Real.one_le_rpow h.N_one h.hδ0.le
  refine ⟨Nat.le_ceil _, ?_, h1⟩
  have := Nat.ceil_lt_add_one (by linarith : 0 ≤ N ^ δ)
  linarith

/-- The size of `P₀ = 2^{K₀} Q`. -/
lemma Params.P_bounds (h : Params N δ η ε K₀ A₀) :
    20 * Real.log N ≤ ((2 ^ K₀ * ⌈N ^ δ⌉₊ : ℕ) : ℝ) ∧ 18 ≤ 2 ^ K₀ * ⌈N ^ δ⌉₊ ∧
      Real.log ((2 ^ K₀ * ⌈N ^ δ⌉₊ : ℕ) : ℝ) ≤ Real.log N / 36 ∧
      ((2 ^ K₀ * ⌈N ^ δ⌉₊ : ℕ) : ℝ) ≤ 2 ^ (K₀ + 1) * N ^ δ := by
  obtain ⟨hQ1, hQ2, hN1⟩ := h.Q_bounds
  set Q := ⌈N ^ δ⌉₊ with hQ
  have hQ0 : 1 ≤ Q := by
    have : (1 : ℝ) ≤ Q := by linarith
    exact_mod_cast this
  have h2K : (1 : ℝ) ≤ 2 ^ K₀ := one_le_pow₀ (by norm_num)
  have e : ((2 ^ K₀ * Q : ℕ) : ℝ) = 2 ^ K₀ * (Q : ℝ) := by push_cast; ring
  have hle : ((2 ^ K₀ * Q : ℕ) : ℝ) ≤ 2 ^ (K₀ + 1) * N ^ δ := by
    rw [e, pow_succ, mul_assoc]
    exact mul_le_mul_of_nonneg_left hQ2 (by positivity)
  have hNlog : 0 ≤ Real.log N := Real.log_nonneg h.N_one
  refine ⟨?_, ?_, ?_, hle⟩
  · rw [e]
    have h3 := h.h20
    have : (Q : ℝ) ≤ 2 ^ K₀ * (Q : ℝ) := le_mul_of_one_le_left (by positivity) h2K
    linarith
  · have h5 : 2 ^ 5 ≤ 2 ^ K₀ := Nat.pow_le_pow_right (by norm_num) h.hK₅
    have : 32 * 1 ≤ 2 ^ K₀ * Q := Nat.mul_le_mul (by simpa using h5) hQ0
    omega
  · have hpos : 0 < ((2 ^ K₀ * Q : ℕ) : ℝ) := by
      rw [e]
      have : (0 : ℝ) < Q := by linarith
      positivity
    refine (Real.log_le_log hpos hle).trans ?_
    rw [Real.log_mul (by positivity) (by have := h.N_pos; positivity), Real.log_pow,
      Real.log_rpow h.N_pos]
    push_cast
    have h3 := h.h72
    have h4 : δ * Real.log N ≤ 1 / 100 * Real.log N :=
      mul_le_mul_of_nonneg_right h.hδ1 hNlog
    linarith

/-- The exponent `e₁ = δ + (1+η)p*/2`. -/
noncomputable def e1 (δ η : ℝ) : ℝ := δ + (1 + η) * pStar / 2

lemma Params.exps (h : Params N δ η ε K₀ A₀) :
    (1 : ℝ) / 4 + ε / 4 ≤ pStar + ε ∧ e1 δ η + ((1 : ℝ) / 4 + ε / 4) ≤ pStar + ε ∧
      3 * δ + 2 * e1 δ η ≤ pStar + ε ∧ (1 : ℝ) / 2 + e1 δ η ≤ 1 := by
  obtain ⟨hp1, hp2, -⟩ := pStar_bounds
  have hε : 0 < ε := by linarith [h.hδ0, h.hδ2]
  have hδ1 := h.hδ1
  have hδ2 := h.hδ2
  have hη0 := h.hη0
  have hη1 := h.hη1
  have hη2 := h.hη2
  have hpη : η * pStar ≤ η * 1 := mul_le_mul_of_nonneg_left (by linarith) hη0.le
  have hpη2 : η * pStar ≤ (1 / 10) * pStar := mul_le_mul_of_nonneg_right hη1 (by linarith)
  unfold e1
  refine ⟨by linarith, ?_, ?_, ?_⟩ <;> nlinarith

end

section

variable {N δ η ε A₀ : ℝ} {K₀ : ℕ}

/-- Bound for the scale `K`. -/
lemma K_bounds (h : Params N δ η ε K₀ A₀) {C₃ κ K P₀ : ℝ}
    (hP : P₀ ≤ 2 ^ (K₀ + 1) * N ^ δ)
    (hκ : κ ≤ pStar / 2 * Real.log N + 4)
    (hK : K = Real.exp C₃ * P₀ * Real.exp ((1 + η) * κ))
    (hA : A₀ = Real.exp C₃ * 2 ^ (K₀ + 1) * Real.exp (4 * (1 + η))) :
    K ≤ A₀ * N ^ e1 δ η ∧ K ≤ N := by
  have hN := h.N_pos
  have hη := h.hη0
  have hexp : Real.exp ((1 + η) * κ) ≤ Real.exp (4 * (1 + η)) * N ^ ((1 + η) * pStar / 2) := by
    rw [Real.rpow_def_of_pos hN, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have : (1 + η) * κ ≤ (1 + η) * (pStar / 2 * Real.log N + 4) :=
      mul_le_mul_of_nonneg_left hκ (by linarith)
    nlinarith
  have hK1 : K ≤ A₀ * N ^ e1 δ η := by
    have e : A₀ * N ^ e1 δ η = Real.exp C₃ * (2 ^ (K₀ + 1) * N ^ δ) *
        (Real.exp (4 * (1 + η)) * N ^ ((1 + η) * pStar / 2)) := by
      rw [hA, e1, Real.rpow_add hN]
      ring
    rw [hK, e]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hP (Real.exp_pos _).le) hexp (by positivity)
      (by positivity)
  refine ⟨hK1, hK1.trans ?_⟩
  have h1 := (h.exps).2.2.2
  calc A₀ * N ^ e1 δ η ≤ N ^ ((1 : ℝ) / 2) * N ^ e1 δ η :=
        mul_le_mul_of_nonneg_right h.hA₀ (by positivity)
    _ = N ^ ((1 : ℝ) / 2 + e1 δ η) := (Real.rpow_add hN _ _).symm
    _ ≤ N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h.N_one h1
    _ = N := Real.rpow_one N

/-- `K ≤ q^{L₀}` for `q ≥ N^δ`. -/
lemma K_le_pow (h : Params N δ η ε K₀ A₀) {K : ℝ} (hK : K ≤ N) {q : ℕ}
    (hq : N ^ δ ≤ (q : ℝ)) (L₀ : ℕ) (hL₀ : 1 / δ ≤ L₀) : K ≤ (q : ℝ) ^ L₀ := by
  have hN := h.N_pos
  refine hK.trans ?_
  have h1 : (N ^ δ) ^ L₀ ≤ (q : ℝ) ^ L₀ := pow_le_pow_left₀ (by positivity) hq _
  refine le_trans ?_ h1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
  have h2 : 1 ≤ δ * L₀ := by
    have := mul_le_mul_of_nonneg_left hL₀ h.hδ0.le
    rwa [mul_one_div_cancel h.hδ0.ne'] at this
  calc N = N ^ (1 : ℝ) := (Real.rpow_one N).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le h.N_one h2

/-- `|m| < Q^{K₀}`. -/
lemma natAbs_lt (h : Params N δ η ε K₀ A₀) {m : ℤ} (hm : |(m : ℝ)| ≤ N ^ 20) :
    m.natAbs < ⌈N ^ δ⌉₊ ^ K₀ := by
  have hN := h.N_pos
  obtain ⟨hQ1, -, -⟩ := h.Q_bounds
  have h1 : (N ^ δ) ^ K₀ ≤ (⌈N ^ δ⌉₊ : ℝ) ^ K₀ := pow_le_pow_left₀ (by positivity) hQ1 _
  have h2 : N ^ (21 : ℝ) ≤ (N ^ δ) ^ K₀ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    refine Real.rpow_le_rpow_of_exponent_le h.N_one ?_
    have := mul_le_mul_of_nonneg_left h.hK₀ h.hδ0.le
    rwa [mul_div_cancel₀ _ h.hδ0.ne'] at this
  have h3 : N ^ 20 < N ^ (21 : ℝ) := by
    have e : N ^ (21 : ℝ) = N ^ (21 : ℕ) := by
      rw [← Real.rpow_natCast]
      norm_num
    rw [e]
    exact pow_lt_pow_right₀ (by linarith [h.hN2]) (by norm_num)
  have h4 : (m.natAbs : ℝ) < ((⌈N ^ δ⌉₊ ^ K₀ : ℕ) : ℝ) := by
    push_cast
    rw [Nat.cast_natAbs]
    push_cast
    linarith
  exact_mod_cast h4

end

/-- The constant of `shell_core`. -/
noncomputable def coreC (C₂ ϑ₀ A₀ : ℝ) (K₀ L₀ : ℕ) : ℝ :=
  24 * C₂ + K₀ * (312 * ϑ₀ * A₀ * C₂ + 2 * L₀ * (312 * ϑ₀) ^ 2 * ((2 : ℝ) ^ (K₀ + 1)) ^ 3 * A₀ ^ 2)

set_option maxHeartbeats 1000000 in
/-- **The shell bound for large `N`**, at fixed parameters. -/
theorem shell_core {ε δ η ϑ₀ C₃ C₂ A₀ : ℝ} {K₀ L₀ Dg : ℕ} (htree : TreeProp η ϑ₀ C₃)
    (hϑ₀ : 1 ≤ ϑ₀) (hC₂ : 0 ≤ C₂) (hDg1 : 312 * ϑ₀ ≤ Dg) (hDg2 : 24 ≤ Dg)
    (hPF : ∀ (n : Mode) (Δ z : ℕ) (s2 s3 : ℤ) (g T : ℕ) (H : MvPolynomial (Fin 2) ℤ),
      ShellHyp n Δ z g T → Irreducible (MvPolynomial.map (Int.castRingHom ℚ) H) →
      H.totalDegree ≤ Dg → (curveCount n Δ z s2 s3 g T H : ℝ) ≤
        C₂ * absk n ^ ((1 : ℝ) / 4 + ε / 4))
    (hA : A₀ = Real.exp C₃ * 2 ^ (K₀ + 1) * Real.exp (4 * (1 + η))) (hL₀ : 1 / δ ≤ L₀)
    {n : Mode} {Δ z : ℕ} {s2 s3 : ℤ} {g T : ℕ} (hH : ShellHyp n Δ z g T) {i j : Fin 3}
    (hij : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) (hn3 : n 2 ≠ 0) (hnj : n j ≠ 0)
    (hs3 : s3 = 1 ∨ s3 = -1) (hP : Params (absk n) δ η ε K₀ A₀) :
    ((shellPts n Δ z s2 s3 g T).card : ℝ) ≤ coreC C₂ ϑ₀ A₀ K₀ L₀ * absk n ^ (pStar + ε) := by
  classical
  set N := absk n with hNdef
  have hN0 := hP.N_pos
  obtain ⟨hP1, hP2, hP3, hP4⟩ := hP.P_bounds
  have hQ1 := hP.Q_bounds.1
  have hN1 := hP.Q_bounds.2.2
  have hQ0 : ⌈N ^ δ⌉₊ ≠ 0 := by
    intro h0
    rw [h0] at hQ1
    norm_num at hQ1
    linarith
  obtain ⟨ps, hps, hpsp⟩ := PlaneCount.exists_primes K₀ ⌈N ^ δ⌉₊ hQ0
  have hA₀0 : 0 ≤ A₀ := by rw [hA]; positivity
  set D := shellD n Δ z s3 g T i j (2 ^ K₀ * ⌈N ^ δ⌉₊) hH hij hn3 hnj hs3 hP.hN2 hP1 hP2 hP3 with hD
  have hDP : D.P₀ = 2 ^ K₀ * ⌈N ^ δ⌉₊ := rfl
  have hκ : kappaHat D.l ≤ pStar / 2 * Real.log N + 4 := shell_kappaHat_le hH hP.hN2
  set K := Real.exp C₃ * (D.P₀ : ℝ) * Real.exp ((1 + η) * kappaHat D.l) with hK
  obtain ⟨hK1, hK2⟩ := K_bounds hP hP4 hκ hK hA
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  set x : Mode → Fin 3 → ℤ := surfPt Δ s2 g i n with hx
  set M := C₂ * N ^ ((1 : ℝ) / 4 + ε / 4) with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hxF : ∀ k ∈ shellPts n Δ z s2 s3 g T, (∀ l, |(x k l : ℝ)| ≤ D.B l) ∧ eval (x k) D.F = 0 := by
    intro k hk
    have h := surface_points hH hk i j hij
    rw [boxZeros, mem_filter] at h
    exact ⟨fun l => abs_le_of_mem_box h.1 l, h.2⟩
  have hmb : ∀ k ∈ shellPts n Δ z s2 s3 g T, |(mVal D.c D.F1 (x k) : ℝ)| ≤ D.Mb := fun k hk =>
    shell_m_le hH hn3 hP.hN2 hij hs3 (hxF k hk).1
  -- the points with `m = 0`
  set Z := (shellPts n Δ z s2 s3 g T).filter fun k => mVal D.c D.F1 (x k) = 0 with hZdef
  have hZ : (Z.card : ℝ) ≤ 24 * M :=
    zero_part D (td_sF1 _ _ _ _ _ _) (filter_subset _ _) x
      (fun k hk => ⟨(hxF k (mem_filter.1 hk).1).2, (mem_filter.1 hk).2, surfPt_cast _ _ _ _ _ _⟩)
      hM0 (fun H h1 h2 => hPF n Δ z s2 s3 g T H hH h1 (h2.trans hDg2))
  -- the points with `q ∤ m`
  set Aq : ℕ → Finset Mode := fun q => (shellPts n Δ z s2 s3 g T).filter fun k =>
    mVal D.c D.F1 (x k) ≠ 0 ∧ ¬ (q : ℤ) ∣ mVal D.c D.F1 (x k) with hAqdef
  have hAq : ∀ q ∈ ps, ((Aq q).card : ℝ) ≤
      312 * ϑ₀ * K * M + 2 * (L₀ * (312 * ϑ₀) ^ 2 * (q : ℝ) ^ 3 * K ^ 2) := by
    intro q hq
    obtain ⟨hqp, hqQ, hqP⟩ := hpsp q hq
    have hq1 : N ^ δ ≤ (q : ℝ) := hQ1.trans (by exact_mod_cast hqQ.le)
    have hKq := K_le_pow hP hK2 hq1 L₀ hL₀
    obtain ⟨low, h1, h2, h3⟩ := htree D q L₀ ((Aq q).image x) K hK hqp hqP hKq (fun y hy => by
      obtain ⟨k, hk, rfl⟩ := mem_image.1 hy
      obtain ⟨hk1, hk2, hk3⟩ := mem_filter.1 hk
      exact ⟨(hxF k hk1).1, (hxF k hk1).2, hk2, hmb k hk1, hk3⟩)
    have hs := split_part (s2 := s2) (s3 := s3) hH (A := Aq q) (filter_subset _ _) i low hM0 h2
      (fun H h1' h2' => hPF n Δ z s2 s3 g T H hH h1' (by
        have : (H.totalDegree : ℝ) ≤ Dg := h2'.trans hDg1
        exact_mod_cast this))
    have himg : ((Aq q).image x).image proj2 = (Aq q).image fun k => proj2 (surfPt Δ s2 g i n k) := by
      rw [image_image]
      rfl
    rw [himg] at h3
    have h4 : (low.card : ℝ) * M ≤ 312 * ϑ₀ * K * M := mul_le_mul_of_nonneg_right h1 hM0
    linarith
  -- the cover
  have hcover : shellPts n Δ z s2 s3 g T ⊆ Z ∪ ps.biUnion Aq := by
    intro k hk
    by_cases h0 : mVal D.c D.F1 (x k) = 0
    · exact mem_union_left _ (mem_filter.2 ⟨hk, h0⟩)
    · obtain ⟨q, hq, hnd⟩ := PlaneCount.exists_prime_not_dvd ps (fun p hp => (hpsp p hp).1)
        ⌈N ^ δ⌉₊ (fun p hp => (hpsp p hp).2.1.le) (mVal D.c D.F1 (x k)) h0
        (by rw [hps]; exact natAbs_lt hP (hmb k hk))
      exact mem_union_right _ (mem_biUnion.2 ⟨q, hq, mem_filter.2 ⟨hk, h0, hnd⟩⟩)
  have hcard : ((shellPts n Δ z s2 s3 g T).card : ℝ) ≤ Z.card + ∑ q ∈ ps, ((Aq q).card : ℝ) := by
    have h1 := (card_le_card hcover).trans ((card_union_le _ _).trans
      (Nat.add_le_add_left card_biUnion_le _))
    exact_mod_cast h1
  -- the final estimate
  obtain ⟨he1, he2, he3, -⟩ := hP.exps
  set X := N ^ (pStar + ε) with hX
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hN1' : 1 ≤ N := hP.N_one
  have hMX : M ≤ C₂ * X :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1' he1) hC₂
  have hKM : K * M ≤ A₀ * C₂ * X := by
    have h1 : K * M ≤ A₀ * N ^ e1 δ η * M := mul_le_mul_of_nonneg_right hK1 hM0
    refine h1.trans ?_
    have e : A₀ * N ^ e1 δ η * M = A₀ * C₂ * N ^ (e1 δ η + ((1 : ℝ) / 4 + ε / 4)) := by
      rw [hM, Real.rpow_add hN0 (e1 δ η) ((1 : ℝ) / 4 + ε / 4)]
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1' he2) (by positivity)
  have hqK : ∀ q ∈ ps, (q : ℝ) ^ 3 * K ^ 2 ≤ ((2 : ℝ) ^ (K₀ + 1)) ^ 3 * A₀ ^ 2 * X := by
    intro q hq
    have hqP : (q : ℝ) ≤ 2 ^ (K₀ + 1) * N ^ δ := by
      refine le_trans ?_ hP4
      exact_mod_cast (hpsp q hq).2.2
    have h1 : (q : ℝ) ^ 3 ≤ (2 ^ (K₀ + 1) * N ^ δ) ^ 3 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hqP 3
    have h2 : K ^ 2 ≤ (A₀ * N ^ e1 δ η) ^ 2 := pow_le_pow_left₀ hK0 hK1 2
    have e : (2 ^ (K₀ + 1) * N ^ δ) ^ 3 * (A₀ * N ^ e1 δ η) ^ 2 =
        ((2 : ℝ) ^ (K₀ + 1)) ^ 3 * A₀ ^ 2 * N ^ (3 * δ + 2 * e1 δ η) := by
      rw [Real.rpow_add hN0, mul_pow, mul_pow]
      have e1' : (N ^ δ) ^ 3 = N ^ (3 * δ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
        norm_num
        ring_nf
      have e2' : (N ^ e1 δ η) ^ 2 = N ^ (2 * e1 δ η) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
        norm_num
        ring_nf
      rw [e1', e2']
      ring
    calc (q : ℝ) ^ 3 * K ^ 2 ≤ (2 ^ (K₀ + 1) * N ^ δ) ^ 3 * (A₀ * N ^ e1 δ η) ^ 2 :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = _ := e
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1' he3)
          (by positivity)
  have hAq2 : ∀ q ∈ ps, ((Aq q).card : ℝ) ≤
      (312 * ϑ₀ * A₀ * C₂ + 2 * L₀ * (312 * ϑ₀) ^ 2 * ((2 : ℝ) ^ (K₀ + 1)) ^ 3 * A₀ ^ 2) * X := by
    intro q hq
    refine (hAq q hq).trans ?_
    have h1 : 312 * ϑ₀ * K * M ≤ 312 * ϑ₀ * (A₀ * C₂ * X) := by
      have : 312 * ϑ₀ * K * M = 312 * ϑ₀ * (K * M) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hKM (by positivity)
    have h2 : 2 * ((L₀ : ℝ) * (312 * ϑ₀) ^ 2 * (q : ℝ) ^ 3 * K ^ 2) ≤
        2 * ((L₀ : ℝ) * (312 * ϑ₀) ^ 2 * (((2 : ℝ) ^ (K₀ + 1)) ^ 3 * A₀ ^ 2 * X)) := by
      have : (L₀ : ℝ) * (312 * ϑ₀) ^ 2 * (q : ℝ) ^ 3 * K ^ 2 =
          (L₀ : ℝ) * (312 * ϑ₀) ^ 2 * ((q : ℝ) ^ 3 * K ^ 2) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hqK q hq) (by positivity))
        (by norm_num)
    calc _ ≤ 312 * ϑ₀ * (A₀ * C₂ * X) + 2 * ((L₀ : ℝ) * (312 * ϑ₀) ^ 2 *
          (((2 : ℝ) ^ (K₀ + 1)) ^ 3 * A₀ ^ 2 * X)) := add_le_add h1 h2
      _ = _ := by ring
  have hsum : ∑ q ∈ ps, ((Aq q).card : ℝ) ≤ (K₀ : ℝ) *
      ((312 * ϑ₀ * A₀ * C₂ + 2 * L₀ * (312 * ϑ₀) ^ 2 * ((2 : ℝ) ^ (K₀ + 1)) ^ 3 * A₀ ^ 2) * X) := by
    refine (sum_le_sum hAq2).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, hps]
  calc _ ≤ (Z.card : ℝ) + ∑ q ∈ ps, ((Aq q).card : ℝ) := hcard
    _ ≤ 24 * (C₂ * X) + (K₀ : ℝ) *
      ((312 * ϑ₀ * A₀ * C₂ + 2 * L₀ * (312 * ϑ₀) ^ 2 * ((2 : ℝ) ^ (K₀ + 1)) ^ 3 * A₀ ^ 2) * X) := by
        have : 24 * M ≤ 24 * (C₂ * X) := by linarith
        linarith
    _ = _ := by
        rw [coreC]
        ring

end OVNS.Quant.Surf
