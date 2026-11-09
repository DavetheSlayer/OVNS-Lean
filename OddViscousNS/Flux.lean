import OddViscousNS.Trilinear
import OddViscousNS.Counting
import OddViscousNS.RestrictedConv

/-! # The half-derivative gain for `Q_FFF` (`Proposition prop:flux`)

For real fast `f`, the pairing `⟨Q_res(f,f), Δf⟩` is a triad sum, whose advective half `xSum`
is odd under `(q,b) ↔ (r,c)`.  Writing `-|r|² = r·p + r·q`, the `r·q` part cancels, and the `r·p`
part is bounded by `2^{3/2} ∑_T u_p u_q u_r` with `u_k = |k| ‖f_k‖` on the resonant triads `T`,
which `restricted_conv` and `card_resonant_vertical` control. -/

open scoped ENNReal

noncomputable section
namespace OVNS

/-- The universal constant of `Proposition prop:flux`. -/
def CF : ℝ := 6 * Real.sqrt 2400

lemma CF_pos : 0 < CF := by
  unfold CF
  positivity

/-! ### The real dot product of wave vectors -/

/-- The real dot product of two wave vectors. -/
private def rdot (p q : Mode) : ℝ := ∑ i, (p i : ℝ) * (q i : ℝ)

private lemma rdot_comm (p q : Mode) : rdot p q = rdot q p := by
  simp only [rdot, mul_comm]

private lemma abs_rdot_le (p q : Mode) : |rdot p q| ≤ absk p * absk q := by
  rw [absk, absk, ← Real.sqrt_mul (absSq_nonneg p)]
  apply Real.abs_le_sqrt
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

private lemma absSq_split (p q : Mode) :
    absSq (p + q) = -rdot (-(p + q)) p - rdot (-(p + q)) q := by
  simp only [absSq, rdot, Fin.sum_univ_three, Pi.add_apply, Pi.neg_apply, Int.cast_add,
    Int.cast_neg]
  ring

/-! ### The advective half of the triad -/

/-- One helicity term of the advective half: `i (A·q)(B·C)`. -/
private def xTerm (f : Field) (a b c : Sgn) (p q : Mode) : ℂ :=
  Complex.I * dotM (hel a p (f p)) q * bd (hel b q (f q)) (hel c (-(p + q)) (f (-(p + q))))

/-- The advective half of the resonant triad. -/
private def xSum (f : Field) (p q : Mode) : ℂ :=
  ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, resM a b c p q * xTerm f a b c p q

private lemma resM_comm (a b c : Sgn) (p q : Mode) : resM a b c q p = resM b a c p q := by
  simp only [resM, Phi, add_comm q p, add_comm (lam a q)]
  congr

/-- The vertex is the symmetrization of its advective half. -/
private lemma tripT_eq_half (f : Field) (p q : Mode) :
    tripT resM f f f p q = (1 / 2) * (xSum f p q + xSum f q p) := by
  simp only [tripT, xSum, xTerm, tau, add_comm q p, resM_comm _ _ _ p q, Fintype.sum_bool]
  ring

/-- The advective half is odd under `q ↔ r`. -/
private lemma xSum_anti (f : Field) (p q : Mode) : xSum f p (-(p + q)) = -xSum f p q := by
  set r := -(p + q) with hr
  have h1 : -(p + r) = q := by rw [hr]; abel
  have hd : ∀ a, dotM (hel a p (f p)) r = -dotM (hel a p (f p)) q := fun a => by
    rw [hr, dotM_neg_mode, dotM_add_mode, dotM_hel, zero_add]
  have e : xSum f p r = ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, resM a c b p r * xTerm f a c b p r := by
    exact sum3_swap fun a b c => resM a b c p r * xTerm f a b c p r
  rw [e, xSum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← resM_swap, xTerm, xTerm, h1, ← hr, hd, bd_comm]
  ring

/-! ### The resonant triads -/

/-- Fast zero-sum triads carrying a resonant helicity pattern. -/
private def Tr (k m n : Mode) : Prop :=
  k + m + n = 0 ∧ k 2 ≠ 0 ∧ m 2 ≠ 0 ∧ n 2 ≠ 0 ∧
    ∃ σ₁ σ₂ σ₃ : Sgn, lam σ₁ k + lam σ₂ m + lam σ₃ n = 0

private lemma ne_zero_of_third {k : Mode} (h : k 2 ≠ 0) : k ≠ 0 := by
  rintro rfl
  exact h rfl

private lemma Tr.swap₁ {k m n : Mode} (h : Tr k m n) : Tr m k n := by
  obtain ⟨h0, hk, hm, hn, σ₁, σ₂, σ₃, hl⟩ := h
  exact ⟨by rw [add_comm m k]; exact h0, hm, hk, hn, σ₂, σ₁, σ₃, by linarith⟩

private lemma Tr.swap₂ {k m n : Mode} (h : Tr k m n) : Tr k n m := by
  obtain ⟨h0, hk, hm, hn, σ₁, σ₂, σ₃, hl⟩ := h
  exact ⟨by rw [add_right_comm]; exact h0, hk, hn, hm, σ₁, σ₃, σ₂, by linarith⟩

/-- The advective half is supported on the resonant triads. -/
private lemma xSum_zero {f : Field} (hf : PiF f = f) {p q : Mode}
    (h : ¬Tr p q (-(p + q))) : xSum f p q = 0 := by
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
    Finset.sum_eq_zero fun c _ => ?_
  by_cases hp : p 2 = 0
  · simp [xTerm, fast_zero hf hp, hel_zero_right, dotM_zero_left]
  by_cases hq : q 2 = 0
  · simp [xTerm, fast_zero hf hq, hel_zero_right, bd_zero_left]
  by_cases hr : (-(p + q)) 2 = 0
  · simp only [xTerm, fast_zero hf hr, hel_zero_right, bd_zero_right, mul_zero]
  by_cases hΦ : Phi a b c p q = 0
  · refine absurd ?_ h
    refine ⟨by abel, hp, hq, hr, a, b, c, ?_⟩
    rw [lam_neg]
    simpa only [Phi, sub_eq_add_neg] using hΦ
  · simp [resM, hΦ]

/-! ### Helicity sums -/

private lemma sum_norm_hel_le (k : Mode) (v : V3) :
    ∑ a : Sgn, ‖hel a k v‖ ≤ Real.sqrt 2 * ‖v‖ := by
  have h1 := norm_sq_hel_sum k v
  have h2 : ‖leray k v‖ ^ 2 ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_leray_le k v) 2
  rw [Fintype.sum_bool] at h1 ⊢
  rw [← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul (by norm_num)]
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg (‖hel true k v‖ - ‖hel false k v‖)]

private lemma sqrt_two_cube : Real.sqrt 2 * Real.sqrt 2 * Real.sqrt 2 = Real.sqrt 8 := by
  rw [← Real.sqrt_mul (by norm_num), ← Real.sqrt_mul (by norm_num)]
  norm_num

private lemma norm_xSum_le (f : Field) (p q : Mode) :
    ‖xSum f p q‖ ≤ Real.sqrt 8 * (absk q * ‖f p‖ * ‖f q‖ * ‖f (-(p + q))‖) := by
  set r := -(p + q) with hr
  have hq := absk_nonneg q
  have hterm : ∀ a b c, ‖resM a b c p q * xTerm f a b c p q‖ ≤
      absk q * ‖hel a p (f p)‖ * ‖hel b q (f q)‖ * ‖hel c r (f r)‖ := by
    intro a b c
    have h1 := norm_dotM_le (hel a p (f p)) q
    have h2 := norm_bd_le (hel b q (f q)) (hel c r (f r))
    have hres : ‖resM a b c p q‖ ≤ 1 := resM_bdd a b c p q
    rw [norm_mul, xTerm, ← hr, norm_mul, norm_mul, Complex.norm_I, one_mul]
    calc _ ≤ 1 * (‖dotM (hel a p (f p)) q‖ * ‖bd (hel b q (f q)) (hel c r (f r))‖) := by gcongr
      _ ≤ 1 * ((‖hel a p (f p)‖ * absk q) * (‖hel b q (f q)‖ * ‖hel c r (f r)‖)) := by gcongr
      _ = _ := by ring
  have hbd : ‖xSum f p q‖ ≤ ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn,
      absk q * ‖hel a p (f p)‖ * ‖hel b q (f q)‖ * ‖hel c r (f r)‖ :=
    norm_sum_le_of_le _ fun a _ => norm_sum_le_of_le _ fun b _ =>
      norm_sum_le_of_le _ fun c _ => hterm a b c
  have hprod : ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn,
      absk q * ‖hel a p (f p)‖ * ‖hel b q (f q)‖ * ‖hel c r (f r)‖ =
      absk q * ((∑ a : Sgn, ‖hel a p (f p)‖) * (∑ a : Sgn, ‖hel a q (f q)‖) *
        (∑ a : Sgn, ‖hel a r (f r)‖)) := by
    simp only [Fintype.sum_bool]
    ring
  have h1 := sum_norm_hel_le p (f p)
  have h2 := sum_norm_hel_le q (f q)
  have h3 := sum_norm_hel_le r (f r)
  have hs : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  refine hbd.trans ?_
  rw [hprod, ← sqrt_two_cube]
  calc _ ≤ absk q * ((Real.sqrt 2 * ‖f p‖) * (Real.sqrt 2 * ‖f q‖) * (Real.sqrt 2 * ‖f r‖)) := by
        have h10 : 0 ≤ ∑ a : Sgn, ‖hel a p (f p)‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
        have h20 : 0 ≤ ∑ a : Sgn, ‖hel a q (f q)‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
        have h30 : 0 ≤ ∑ a : Sgn, ‖hel a r (f r)‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
        gcongr
    _ = _ := by ring

/-! ### Fibres -/

private lemma mk3_eta (k : Mode) : mk3 (k 0) (k 1) (k 2) = k := by
  ext i
  fin_cases i <;> rfl

private lemma abs_coord_le (k : Mode) (i : Fin 3) : |(k i : ℝ)| ≤ absk k := by
  apply Real.abs_le_sqrt
  unfold absSq
  exact Finset.single_le_sum (f := fun i => (k i : ℝ) ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ i)

/-- The vertical components carrying a resonance. -/
private def Rset (n : Mode) (a b : ℤ) : Set ℤ :=
  {x : ℤ | ∃ σ₁ σ₂ σ₃ : Sgn,
      sg σ₁ * (x : ℝ) * absk (mk3 a b x) + sg σ₂ * ((-mk3 a b x - n) 2 : ℤ) * absk (-mk3 a b x - n)
        + sg σ₃ * (n 2 : ℝ) * absk n = 0}

private lemma coord_mem {i : ℕ} {k : Mode} (h : absk k < 2 ^ (i + 1)) (j : Fin 3) :
    k j ∈ Finset.Icc (-(2 ^ (i + 1) : ℤ)) (2 ^ (i + 1)) := by
  have h1 := (abs_coord_le k j).trans_lt h
  have h2 : |k j| < (2 ^ (i + 1) : ℤ) := by exact_mod_cast h1
  exact Finset.mem_Icc.2 ⟨(abs_lt.1 h2).1.le, (abs_lt.1 h2).2.le⟩

private lemma fib_encard (n : Mode) (i : ℕ) :
    ({k | (2 : ℝ) ^ i ≤ absk k ∧ absk k < 2 ^ (i + 1) ∧ Tr k (-k - n) n}.encard : ℝ≥0∞) ≤
      ENNReal.ofReal (150 * 4 ^ i) := by
  classical
  by_cases hn : n 2 = 0
  · have : {k | (2 : ℝ) ^ i ≤ absk k ∧ absk k < 2 ^ (i + 1) ∧ Tr k (-k - n) n} = ∅ :=
      Set.eq_empty_of_forall_notMem fun k hk => hk.2.2.2.2.2.1 hn
    simp [this]
  have hc : ∀ a b, (Rset n a b).encard ≤ ((6 : ℕ) : ℕ∞) := fun a b =>
    card_resonant_vertical n hn a b
  have hR : ∀ a b, (Rset n a b).Finite := fun a b => Set.finite_of_encard_le_coe (hc a b)
  have hR6 : ∀ a b, (hR a b).toFinset.card ≤ 6 := fun a b => by
    have := hc a b
    rw [(hR a b).encard_eq_coe_toFinset_card] at this
    exact_mod_cast this
  set I : Finset ℤ := Finset.Icc (-(2 ^ (i + 1) : ℤ)) (2 ^ (i + 1)) with hI
  set box : Finset (ℤ × ℤ) := I ×ˢ I with hbox
  set U : Finset Mode := box.biUnion fun ab => (hR ab.1 ab.2).toFinset.image (mk3 ab.1 ab.2)
    with hU
  have hsub : {k | (2 : ℝ) ^ i ≤ absk k ∧ absk k < 2 ^ (i + 1) ∧ Tr k (-k - n) n} ⊆
      (U : Set Mode) := by
    rintro k ⟨-, hk, h0, -, -, -, σ₁, σ₂, σ₃, hl⟩
    refine Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨(k 0, k 1), ?_, ?_⟩)
    · exact Finset.mem_product.2 ⟨coord_mem hk 0, coord_mem hk 1⟩
    · refine Finset.mem_image.2 ⟨k 2, (hR _ _).mem_toFinset.2 ?_, mk3_eta k⟩
      refine ⟨σ₁, σ₂, σ₃, ?_⟩
      simp only [mk3_eta]
      simpa only [lam] using hl
  have hcard : U.card ≤ box.card * 6 := Finset.card_biUnion_le_card_mul _ _ _ fun ab _ =>
    Finset.card_image_le.trans (hR6 _ _)
  have hI2 : (I.card : ℝ) ≤ 5 * 2 ^ i := by
    have e : I.card = 2 ^ (i + 2) + 1 := by
      rw [hI, Int.card_Icc]
      have : ((2 : ℤ) ^ (i + 1) + 1 - -(2 ^ (i + 1) : ℤ)) = ((2 ^ (i + 2) + 1 : ℕ) : ℤ) := by
        push_cast
        ring
      rw [this, Int.toNat_natCast]
    rw [e]
    push_cast
    have : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
    rw [pow_add]
    linarith
  have hU2 : (U.card : ℝ) ≤ 150 * 4 ^ i := by
    have h1 : (U.card : ℝ) ≤ (I.card : ℝ) * I.card * 6 := by
      have : U.card ≤ I.card * I.card * 6 := by
        simpa [hbox, Finset.card_product] using hcard
      exact_mod_cast this
    have h2 : (I.card : ℝ) * I.card ≤ (5 * 2 ^ i) * (5 * 2 ^ i) := by gcongr
    have h3 : (4 : ℝ) ^ i = 2 ^ i * 2 ^ i := by
      rw [← mul_pow]
      norm_num
    rw [h3]
    nlinarith
  have h1 : ({k | (2 : ℝ) ^ i ≤ absk k ∧ absk k < 2 ^ (i + 1) ∧ Tr k (-k - n) n}.encard : ℝ≥0∞) ≤
      (U.card : ℝ≥0∞) := by
    have := (Set.encard_le_encard hsub).trans_eq (Set.encard_coe_eq_coe_finsetCard U)
    exact_mod_cast this
  refine h1.trans ?_
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal hU2

/-! ### The resonant sum -/

/-- `u_k = |k| ‖f_k‖`. -/
private def uu (f : Field) (k : Mode) : ℝ := absk k * ‖f k‖

private lemma summable_uu_sq {f : Field} (hf : Adm 2 f) : Summable fun k => uu f k ^ 2 :=
  summable_grad_sq hf.mz

/-- `‖f‖_{3/2}² ≤ ‖f‖₁ ‖f‖₂`, in the form used by `restricted_conv`. -/
private lemma cauchy_uu {f : Field} (hf : Adm 2 f) :
    Summable (fun k => absk k * uu f k ^ 2) ∧
      ∑' k, absk k * uu f k ^ 2 ≤ hnorm 1 f * hnorm 2 f := by
  have hc2 : Summable fun k => (absSq k * ‖f k‖) ^ 2 :=
    hf.inH.congr fun k => by rw [sobWeight_two, mul_pow]
  have h := cs_equiv (a := uu f) (c := fun k => absSq k * ‖f k‖)
    (fun k => mul_nonneg (absk_nonneg k) (norm_nonneg _))
    (fun k => mul_nonneg (absSq_nonneg k) (norm_nonneg _)) (summable_uu_sq hf) hc2
    (Equiv.refl Mode)
  have e : ∀ k, uu f k * (absSq k * ‖f k‖) = absk k * uu f k ^ 2 := fun k => by
    simp only [uu, ← absk_sq]
    ring
  have e1 : ∑' k, uu f k ^ 2 = ∑' k, sobWeight 1 k * ‖f k‖ ^ 2 :=
    tsum_congr fun k => by rw [sobWeight_one, uu, mul_pow, absk_sq]
  have e2 : ∑' k, (absSq k * ‖f k‖) ^ 2 = ∑' k, sobWeight 2 k * ‖f k‖ ^ 2 :=
    tsum_congr fun k => by rw [sobWeight_two, mul_pow]
  simp only [Equiv.refl_apply, e, e1, e2] at h
  exact h

open Classical in
/-- The resonant triple sum of `u`. -/
private def resSum (f : Field) (x : Mode × Mode) : ℝ :=
  if Tr x.1 x.2 (-x.1 - x.2) then uu f x.1 * uu f x.2 * uu f (-x.1 - x.2) else 0

private lemma resSum_bound {f : Field} (hf : Adm 2 f) :
    Summable (resSum f) ∧
      ∑' x, resSum f x ≤ 6 * Real.sqrt 300 * (hnorm 1 f ^ 2 * hnorm 2 f) := by
  have h := restricted_conv Tr 150 (by norm_num)
    (fun k m n h => ⟨ne_zero_of_third h.2.1, ne_zero_of_third h.2.2.1,
      ne_zero_of_third h.2.2.2.1⟩)
    (fun k m n h => h.1) (fun k m n h => h.swap₁) (fun k m n h => h.swap₂) fib_encard (uu f)
    (fun k => mul_nonneg (absk_nonneg k) (norm_nonneg _)) (cauchy_uu hf).1 (summable_uu_sq hf)
  refine ⟨h.1, h.2.trans ?_⟩
  have e1 : ∑' k, uu f k ^ 2 = hnorm 1 f ^ 2 := by
    rw [hnorm, Real.sq_sqrt (tsum_nonneg fun k => mul_nonneg (sobWeight_nonneg _ _) (sq_nonneg _))]
    exact tsum_congr fun k => by rw [sobWeight_one, uu, mul_pow, absk_sq]
  have e2 : hnorm 1 f = Real.sqrt (hnorm 1 f ^ 2) := (Real.sqrt_sq (Real.sqrt_nonneg _)).symm
  rw [e1, ← e2, show (2 * 150 : ℝ) = 300 by norm_num]
  have h1 : 0 ≤ hnorm 1 f := Real.sqrt_nonneg _
  have := mul_le_mul_of_nonneg_right (cauchy_uu hf).2 h1
  have h6 : 0 ≤ 6 * Real.sqrt 300 := by positivity
  calc _ ≤ 6 * Real.sqrt 300 * ((hnorm 1 f * hnorm 2 f) * hnorm 1 f) := by
        rw [mul_assoc (6 * Real.sqrt 300)]
        exact mul_le_mul_of_nonneg_left this h6
    _ = _ := by ring

/-! ### The two parts of `-|r|² = r·p + r·q` -/

/-- The `r·p` part. -/
private def g1 (f : Field) (x : Mode × Mode) : ℂ :=
  ((-rdot (-(x.1 + x.2)) x.1 : ℝ) : ℂ) * xSum f x.1 x.2

/-- The `r·q` part. -/
private def g2 (f : Field) (x : Mode × Mode) : ℂ :=
  ((-rdot (-(x.1 + x.2)) x.2 : ℝ) : ℂ) * xSum f x.1 x.2

private lemma g_add (f : Field) (x : Mode × Mode) :
    g1 f x + g2 f x = (absSq (x.1 + x.2) : ℂ) * xSum f x.1 x.2 := by
  rw [g1, g2, absSq_split, ← add_mul]
  push_cast
  ring

private lemma norm_ofReal_rdot_le (r p : Mode) : ‖((-rdot r p : ℝ) : ℂ)‖ ≤ absk r * absk p := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_neg]
  exact abs_rdot_le r p

private lemma norm_g1_le {f : Field} (hf : PiF f = f) (x : Mode × Mode) :
    ‖g1 f x‖ ≤ Real.sqrt 8 * resSum f x := by
  obtain ⟨p, q⟩ := x
  simp only [g1, resSum]
  rw [← neg_add']
  have h₀ : (0 : ℝ) ≤ Real.sqrt 8 := Real.sqrt_nonneg _
  by_cases hT : Tr p q (-(p + q))
  · rw [ite_eq_left hT, norm_mul]
    have h1 := norm_ofReal_rdot_le (-(p + q)) p
    have h2 := norm_xSum_le f p q
    calc _ ≤ (absk (-(p + q)) * absk p) *
          (Real.sqrt 8 * (absk q * ‖f p‖ * ‖f q‖ * ‖f (-(p + q))‖)) := by
          have := absk_nonneg p
          have := absk_nonneg (-(p + q))
          gcongr
      _ = _ := by
          simp only [uu]
          ring
  · rw [ite_eq_right hT, xSum_zero hf hT]
    simp

private lemma summable_g2 {f : Field} (hf : Adm 2 f) : Summable (g2 f) := by
  have hc2 : Summable fun k => (absSq k * ‖f k‖) ^ 2 :=
    hf.inH.congr fun k => by rw [sobWeight_two, mul_pow]
  have hd2 : Summable fun k => (absk k * ‖f (-k)‖) ^ 2 := by
    have := (Equiv.neg Mode).summable_iff.mpr (summable_grad_sq hf.mz)
    refine this.congr fun k => ?_
    simp only [Function.comp, Equiv.neg_apply, absk_neg]
  have h := (triple_bound (b := fun k => ‖f k‖) (a := fun k => absSq k * ‖f k‖)
    (c := fun k => absk k * ‖f (-k)‖) (fun k => norm_nonneg _)
    (fun k => mul_nonneg (absSq_nonneg k) (norm_nonneg _))
    (fun k => mul_nonneg (absk_nonneg k) (norm_nonneg _))
    (summable_wiener hf.inH) hc2 hd2).1
  refine Summable.of_norm_bounded (h.mul_left (Real.sqrt 8)) fun x => ?_
  obtain ⟨p, q⟩ := x
  simp only [g2]
  rw [norm_mul]
  have h1 := norm_ofReal_rdot_le (-(p + q)) q
  have h2 := norm_xSum_le f p q
  calc _ ≤ (absk (-(p + q)) * absk q) *
        (Real.sqrt 8 * (absk q * ‖f p‖ * ‖f q‖ * ‖f (-(p + q))‖)) := by
        have := absk_nonneg q
        have := absk_nonneg (-(p + q))
        gcongr
    _ = _ := by
        simp only [absk_neg, ← absk_sq]
        ring

private lemma tsum_g2 (f : Field) : ∑' x, g2 f x = 0 := by
  refine tsum_anti fun p q => ?_
  have h1 : -(p + -(p + q)) = q := by abel
  simp only [g2, h1, xSum_anti, rdot_comm q (-(p + q))]
  ring

/-- The weighted triad sum reduces to the `r·p` part. -/
private lemma tsum_weighted {f : Field} (hf : Adm 2 f) (hf' : PiF f = f) :
    ∑' x : Mode × Mode, (sobWeight 1 (x.1 + x.2) : ℂ) * tripT resM f f f x.1 x.2 =
      ∑' x, g1 f x := by
  set H : Mode × Mode → ℂ := fun x => g1 f x + g2 f x with hH
  have hs1 : Summable (g1 f) := by
    refine Summable.of_norm_bounded ((resSum_bound hf).1.mul_left (Real.sqrt 8)) (norm_g1_le hf')
  have hs2 := summable_g2 hf
  have hs : Summable H := hs1.add hs2
  have hsw : Summable fun x : Mode × Mode => H x.swap :=
    (Equiv.prodComm Mode Mode).summable_iff.mpr hs
  have heq : ∀ x : Mode × Mode, (sobWeight 1 (x.1 + x.2) : ℂ) * tripT resM f f f x.1 x.2 =
      (1 / 2) * (H x + H x.swap) := fun x => by
    simp only [hH, g_add, Prod.fst_swap, Prod.snd_swap, add_comm x.2 x.1, sobWeight_one,
      tripT_eq_half]
    ring
  have hval : ∑' x : Mode × Mode, H x.swap = ∑' x, H x := (Equiv.prodComm Mode Mode).tsum_eq H
  have hH' : ∑' x, H x = ∑' x, g1 f x := by
    rw [hs1.tsum_add hs2, tsum_g2, add_zero]
  rw [tsum_congr heq, tsum_mul_left, hs.tsum_add hsw, hval, hH']
  ring

/-- `Proposition prop:flux`: for real fast `f ∈ H²`,
`|⟨Q_res(f,f), Δf⟩| ≤ C_F ‖f‖₁² ‖f‖₂`. -/
theorem flux_le {f : Field} (hf : Adm 2 f) (hf' : PiF f = f) :
    |pair 1 f (Qres f f)| ≤ CF * hnorm 1 f ^ 2 * hnorm 2 f := by
  have hpair : pair 1 f (Qres f f) = _ := pair_eq_tsum (tripT resM f f f)
    (inner_Qm resM_bdd hf.real hf.mz hf.mz) (summable_tripT resM_bdd le_rfl hf.mz hf.mz hf.mz)
  obtain ⟨hs, hb⟩ := resSum_bound hf
  have hnorm' : ‖∑' x, g1 f x‖ ≤ ∑' x, Real.sqrt 8 * resSum f x :=
    tsum_of_norm_bounded (hs.mul_left _).hasSum (norm_g1_le hf')
  have hc : CF = Real.sqrt 8 * (6 * Real.sqrt 300) := by
    rw [CF, show (2400 : ℝ) = 8 * 300 by norm_num, Real.sqrt_mul (by norm_num)]
    ring
  rw [hpair, tsum_weighted hf hf']
  refine (Complex.abs_re_le_norm _).trans (hnorm'.trans ?_)
  rw [tsum_mul_left, hc]
  have := mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg 8)
  linarith [this, show Real.sqrt 8 * (6 * Real.sqrt 300) * hnorm 1 f ^ 2 * hnorm 2 f =
    Real.sqrt 8 * (6 * Real.sqrt 300 * (hnorm 1 f ^ 2 * hnorm 2 f)) by ring]

end OVNS
