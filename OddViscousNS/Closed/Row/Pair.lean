import OddViscousNS.Closed.Row.Sym

/-!
# The pair lemma for large outputs

With `v(j) = 9/(2+λ_j)²`, `a(j) = v(j)/j`: for `|k|² ≥ 1936`,
`pterm k c p ≤ 36 h_k |c|² a(|p|²) a(|k-p|²) / 4.64`.

The heart is `T1`: `(AC-y²) S ≤ (9/4) A²B²C²` for `B = A + C - 2y`, `y² ≤ AC`, where
`S = AB(A-B)² + BC(B-C)² + CA(C-A)²`.  With `X = 4(AC-y²)`, `σ₁ = A+B+C`, `σ₂ = AB+BC+CA`,
`σ₃ = ABC`: `S = 3σ₁σ₃ - σ₂X`, `4σ₂ - σ₁² = X`, so
`9σ₃² - XS = (3σ₃ - σ₁X/2)² + X³/4 ≥ 0`.
-/

open scoped ENNReal

noncomputable section

namespace OVNS
namespace Row

/-- `v(j) = 9/(2+λ_j)²`. -/
def vv (j : ℕ) : ℝ := 9 / (2 + lamW j) ^ 2

/-- `a(j) = v(j)/j`, with `a(0) = 0`. -/
def aa (j : ℕ) : ℝ := vv j / j

lemma lamW_nonneg (j : ℕ) : 0 ≤ lamW j := by
  unfold lamW
  split
  · positivity
  · exact zero_le_one

lemma lamW_gt {j : ℕ} (hj : 120 < j) : lamW j = 1 := by
  have h : lamEdges.findIdx? (fun e => decide (j ≤ e)) = none := by
    rw [List.findIdx?_eq_none_iff]
    intro e he
    have : e ≤ 120 := by
      have hall : lamEdges.all (fun e => Nat.ble e 120) = true := by decide
      exact Nat.le_of_ble_eq_true (List.all_eq_true.mp hall e he)
    simp only [decide_eq_false_iff_not, not_le]
    omega
  simp only [lamW, h]

lemma vv_gt {j : ℕ} (hj : 120 < j) : vv j = 1 := by
  rw [vv, lamW_gt hj]; norm_num

lemma vv_nonneg (j : ℕ) : 0 ≤ vv j := by unfold vv; positivity

lemma aa_nonneg (j : ℕ) : 0 ≤ aa j := by
  have := vv_nonneg j; unfold aa; positivity

/-- `T1`. -/
lemma T1 (A B C y : ℝ) (hy : y ^ 2 ≤ A * C) (hB : B = A + C - 2 * y) :
    (A * C - y ^ 2) * (A * B * (A - B) ^ 2 + B * C * (B - C) ^ 2 + C * A * (C - A) ^ 2) ≤
      9 / 4 * (A ^ 2 * B ^ 2 * C ^ 2) := by
  set X := 4 * (A * C - y ^ 2) with hX
  have hX0 : 0 ≤ X := by rw [hX]; linarith
  have e : 9 * (A * B * C) ^ 2 - X * (A * B * (A - B) ^ 2 + B * C * (B - C) ^ 2 + C * A * (C - A) ^ 2)
      = (3 * (A * B * C) - (A + B + C) * X / 2) ^ 2 + X ^ 3 / 4 := by
    subst hB; rw [hX]; ring
  have h3 : 0 ≤ X ^ 3 / 4 := by positivity
  have := sq_nonneg (3 * (A * B * C) - (A + B + C) * X / 2)
  have h4 : X * (A * B * (A - B) ^ 2 + B * C * (B - C) ^ 2 + C * A * (C - A) ^ 2) ≤
      9 * (A * B * C) ^ 2 := by linarith
  rw [hX] at h4
  nlinarith [h4]

/-- The polynomial core of the pair lemma, with a metric defect `η` on the small leg. -/
lemma pair_core (a b η A B C y : ℝ) (ha : a = 29 / 100) (hb : b = 117 / 500)
    (hA0 : 0 < A) (hAB : A ≤ B) (hAC : 4 * A ≤ C) (hB : B = A + C - 2 * y) (hy : y ^ 2 ≤ A * C)
    (hC0 : 0 < C) (hη0 : 0 ≤ η) (hη : η ^ 2 * (12 * A) ≤ 9 / 4 * a * B ^ 2 * (b + η)) :
    (C * (B * (a * (C - B)) ^ 2 + A * (a * (A - C) + η) ^ 2)
        + (η * (B - C)) ^ 2 + A * B * (a * (B - A) - η) ^ 2) * (A * C - y ^ 2) ≤
      225 / 29 * C * ((a * C + b) * (a * A + b + η) * (a * B + b)) * (A * B) := by
  have hBpos : 0 < B := by linarith
  have hD : 0 ≤ A * C - y ^ 2 := by linarith
  have hT1 := T1 A B C y hy hB
  have hsplit : C * (B * (a * (C - B)) ^ 2 + A * (a * (A - C) + η) ^ 2)
        + (η * (B - C)) ^ 2 + A * B * (a * (B - A) - η) ^ 2 =
      a ^ 2 * (A * B * (A - B) ^ 2 + B * C * (B - C) ^ 2 + C * A * (C - A) ^ 2)
        + 2 * a * A * η * (A * (B + C) - B ^ 2 - C ^ 2)
        + η ^ 2 * (A * C + A * B + (B - C) ^ 2) := by ring
  rw [hsplit]
  have hAC' : A ≤ C := by linarith
  have hneg : A * (B + C) - B ^ 2 - C ^ 2 ≤ 0 := by
    have h1 := mul_le_mul_of_nonneg_right hAB hBpos.le
    have h2 := mul_le_mul_of_nonneg_right hAC' hC0.le
    nlinarith
  have ha0 : 0 < a := by rw [ha]; norm_num
  have hb0 : 0 < b := by rw [hb]; norm_num
  have h1 : a ^ 2 * (A * B * (A - B) ^ 2 + B * C * (B - C) ^ 2 + C * A * (C - A) ^ 2) * (A * C - y ^ 2)
      ≤ a ^ 2 * (9 / 4 * (A ^ 2 * B ^ 2 * C ^ 2)) := by
    have := mul_le_mul_of_nonneg_left hT1 (sq_nonneg a)
    linarith
  have h2 : 2 * a * A * η * (A * (B + C) - B ^ 2 - C ^ 2) * (A * C - y ^ 2) ≤ 0 := by
    have h0 : 0 ≤ 2 * a * A * η * (A * C - y ^ 2) := by positivity
    have := mul_nonneg h0 (sub_nonneg.2 hneg)
    linarith
  -- the defect quadratic term
  obtain ⟨hyabs', hyabs⟩ := abs_le_of_sq_le_sq' (show (2 * y) ^ 2 ≤ (A + C) ^ 2 by
    nlinarith [sq_nonneg (A - C)]) (by positivity)
  have hBC : (B - C) ^ 2 ≤ 2 * A ^ 2 + 8 * (A * C) := by
    have : B - C = A - 2 * y := by rw [hB]; ring
    rw [this]
    have := sq_nonneg (A + 2 * y)
    linarith
  have hBle : B ≤ 2 * A + 2 * C := by rw [hB]; linarith
  have h3 : A * C + A * B + (B - C) ^ 2 ≤ 12 * A * C := by
    have h1 := mul_le_mul_of_nonneg_left hBle hA0.le
    have h2 := mul_le_mul_of_nonneg_left hAC hA0.le
    linarith
  have h4 : η ^ 2 * (A * C + A * B + (B - C) ^ 2) * (A * C - y ^ 2) ≤
      η ^ 2 * (12 * A * C) * (A * C) := by
    have hyy : A * C - y ^ 2 ≤ A * C := by linarith [sq_nonneg y]
    have h5 := mul_le_mul_of_nonneg_left h3 (sq_nonneg η)
    have h6 : 0 ≤ η ^ 2 * (A * C + A * B + (B - C) ^ 2) := by positivity
    calc η ^ 2 * (A * C + A * B + (B - C) ^ 2) * (A * C - y ^ 2)
        ≤ η ^ 2 * (A * C + A * B + (B - C) ^ 2) * (A * C) := mul_le_mul_of_nonneg_left hyy h6
      _ ≤ η ^ 2 * (12 * A * C) * (A * C) := mul_le_mul_of_nonneg_right h5 (by positivity)
  have h7 : η ^ 2 * (12 * A * C) * (A * C) ≤ 9 / 4 * a * A * B ^ 2 * C ^ 2 * (b + η) := by
    have := mul_le_mul_of_nonneg_left hη (show 0 ≤ A * C ^ 2 by positivity)
    calc η ^ 2 * (12 * A * C) * (A * C) = A * C ^ 2 * (η ^ 2 * (12 * A)) := by ring
      _ ≤ A * C ^ 2 * (9 / 4 * a * B ^ 2 * (b + η)) := this
      _ = 9 / 4 * a * A * B ^ 2 * C ^ 2 * (b + η) := by ring
  have hR : 225 / 29 * C * (a * C * (a * A + b + η) * (a * B)) * (A * B) ≤
      225 / 29 * C * ((a * C + b) * (a * A + b + η) * (a * B + b)) * (A * B) := by
    have h8 : a * C * (a * A + b + η) * (a * B) ≤ (a * C + b) * (a * A + b + η) * (a * B + b) := by
      have h9 : 0 ≤ a * A + b + η := by positivity
      have h10 : 0 ≤ a * C := by positivity
      have h11 : 0 ≤ a * B := by positivity
      have h14 : a * C * (a * B) ≤ (a * C + b) * (a * B + b) := by
        have h15 : 0 ≤ b * (a * C) := by positivity
        have h16 : 0 ≤ b * (a * B) := by positivity
        have h17 : 0 ≤ b * b := by positivity
        linarith
      calc a * C * (a * A + b + η) * (a * B) = (a * C * (a * B)) * (a * A + b + η) := by ring
        _ ≤ ((a * C + b) * (a * B + b)) * (a * A + b + η) :=
            mul_le_mul_of_nonneg_right h14 h9
        _ = _ := by ring
    have h12 : 0 ≤ 225 / 29 * C := by positivity
    have h13 : 0 ≤ A * B := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h8 h12) h13
  have hE : 225 / 29 * C * (a * C * (a * A + b + η) * (a * B)) * (A * B) =
      a ^ 2 * (9 / 4 * (A ^ 2 * B ^ 2 * C ^ 2)) + 9 / 4 * a * A * B ^ 2 * C ^ 2 * (b + η) := by
    have : (225 : ℝ) / 29 = 9 / (4 * a) := by rw [ha]; norm_num
    rw [this]; field_simp; ring
  have := add_mul (a ^ 2 * (A * B * (A - B) ^ 2 + B * C * (B - C) ^ 2 + C * A * (C - A) ^ 2)
      + 2 * a * A * η * (A * (B + C) - B ^ 2 - C ^ 2)) (η ^ 2 * (A * C + A * B + (B - C) ^ 2))
      (A * C - y ^ 2)
  rw [this, add_mul]
  linarith

/-- The polynomial core when both legs are affine. -/
lemma pair_core0 (a b A B C y : ℝ) (ha : a = 29 / 100) (hb : b = 117 / 500)
    (hA0 : 0 < A) (hB0 : 0 < B) (hB : B = A + C - 2 * y) (hy : y ^ 2 ≤ A * C) (hC0 : 0 < C) :
    (C * (B * (a * (C - B)) ^ 2 + A * (a * (A - C)) ^ 2) + A * B * (a * (B - A)) ^ 2)
        * (A * C - y ^ 2) ≤
      225 / 29 * C * ((a * C + b) * (a * A + b) * (a * B + b)) * (A * B) := by
  have hT1 := T1 A B C y hy hB
  have ha0 : 0 < a := by rw [ha]; norm_num
  have hb0 : 0 < b := by rw [hb]; norm_num
  have e : (C * (B * (a * (C - B)) ^ 2 + A * (a * (A - C)) ^ 2) + A * B * (a * (B - A)) ^ 2)
      = a ^ 2 * (A * B * (A - B) ^ 2 + B * C * (B - C) ^ 2 + C * A * (C - A) ^ 2) := by ring
  rw [e, mul_assoc]
  have h1 := mul_le_mul_of_nonneg_left hT1 (sq_nonneg a)
  have h2 : a * C * (a * A) * (a * B) ≤ (a * C + b) * (a * A + b) * (a * B + b) := by
    have h3 : 0 ≤ a * C := by positivity
    have h4 : 0 ≤ a * A := by positivity
    have h5 : 0 ≤ a * B := by positivity
    have h6 : a * C * (a * A) ≤ (a * C + b) * (a * A + b) := by
      have h15 : 0 ≤ b * (a * C) := by positivity
      have h16 : 0 ≤ b * (a * A) := by positivity
      have h17 : 0 ≤ b * b := by positivity
      linarith
    exact mul_le_mul h6 (by linarith) h5 (by positivity)
  have h7 : 225 / 29 * C * (a * C * (a * A) * (a * B)) * (A * B) ≤
      225 / 29 * C * ((a * C + b) * (a * A + b) * (a * B + b)) * (A * B) := by
    have h12 : 0 ≤ 225 / 29 * C := by positivity
    have h13 : 0 ≤ A * B := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 h12) h13
  have hE : 225 / 29 * C * (a * C * (a * A) * (a * B)) * (A * B) =
      a ^ 2 * (9 / 4 * (A ^ 2 * B ^ 2 * C ^ 2)) := by
    have : (225 : ℝ) / 29 = 9 / (4 * a) := by rw [ha]; norm_num
    rw [this]; field_simp
  linarith

lemma hmet_defect {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ 32) :
    0 ≤ hmet j - (29 / 100 * (j : ℝ) + 117 / 500) ∧
      hmet j - (29 / 100 * (j : ℝ) + 117 / 500) ≤ 2 := by
  interval_cases j <;> norm_num [hmet, hmetTable]

lemma dZ_sq_le (p k : Mode) : dZ p k ^ 2 ≤ absSq p * absSq k := by
  simp only [dZ, absSq]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

lemma nsq_pos_of_ne {p : Mode} (hp : p ≠ 0) : 1 ≤ nsq p := by
  by_contra h
  have : nsq p = 0 := by omega
  exact hp ((nsq_eq_zero_iff p).1 this)

/-- From the polynomial bound on the Gram numerator to the summand. -/
lemma pterm_le_of_core (k p : Mode) (c : R3) (hc : dR k c = 0) (hp : p ≠ 0) (hl : k - p ≠ 0)
    (hk : k ≠ 0) (hAh : 0 < hm p) (hBh : 0 < hm (k - p)) (hCh : 0 < hm k)
    (hW : Wk lamW k p ^ 2 = vv (nsq p) * vv (nsq (k - p)))
    (hcore : (absSq k * (absSq (k - p) * (hm k - hm (k - p)) ^ 2 + absSq p * (hm p - hm k) ^ 2)
        + Lst k p ^ 2 + absSq p * absSq (k - p) * (hm (k - p) - hm p) ^ 2)
        * (absSq p * absSq k - dZ p k ^ 2) ≤
      225 / 29 * absSq k * (hm k * hm p * hm (k - p)) * (absSq p * absSq (k - p))) :
    pterm k c p ≤ 36 * hm k * nR c * (aa (nsq p) * aa (nsq (k - p))) / (464 / 100) := by
  have hA : 0 < absSq p := lt_of_lt_of_le one_pos (one_le_absSq hp)
  have hB : 0 < absSq (k - p) := lt_of_lt_of_le one_pos (one_le_absSq hl)
  have hC : 0 < absSq k := lt_of_lt_of_le one_pos (one_le_absSq hk)
  have hn := nR_nonneg c
  have hpar := parseval p k c hc
  set A := absSq p
  set B := absSq (k - p)
  set C := absSq k
  set hA' := hm p
  set hB' := hm (k - p)
  set hC' := hm k
  set G₁ := B * (hC' - hB') ^ 2 + A * (hA' - hC') ^ 2 with hG₁
  set G₂ := Lst k p ^ 2 + A * B * (hB' - hA') ^ 2 with hG₂
  set T := dR p (crR k c) ^ 2 with hT
  set P := dR p c ^ 2 with hP
  have hT0 : 0 ≤ T := sq_nonneg _
  have hP0 : 0 ≤ P := sq_nonneg _
  have hG₁0 : 0 ≤ G₁ := by positivity
  have hG₂0 : 0 ≤ G₂ := by positivity
  have hD : T + C * P = (A * C - dZ p k ^ 2) * nR c := by linarith
  have h1 : C * (G₁ * T + G₂ * P) ≤ (C * G₁ + G₂) * (T + C * P) := by
    have h2 : 0 ≤ C ^ 2 * G₁ * P := by positivity
    have h3 : 0 ≤ G₂ * T := by positivity
    linarith [show (C * G₁ + G₂) * (T + C * P) = C * (G₁ * T + G₂ * P) + C ^ 2 * G₁ * P + G₂ * T by ring]
  have h2 : (C * G₁ + G₂) * (T + C * P) ≤
      225 / 29 * C * (hC' * hA' * hB') * (A * B) * nR c := by
    rw [hD, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ hn
    have : (C * G₁ + G₂) = C * (B * (hC' - hB') ^ 2 + A * (hA' - hC') ^ 2) + Lst k p ^ 2
        + A * B * (hB' - hA') ^ 2 := by rw [hG₁, hG₂]; ring
    rw [this]; exact hcore
  have h3 : G₁ * T + G₂ * P ≤ 225 / 29 * (hC' * hA' * hB') * (A * B) * nR c := by
    have := h1.trans h2
    have h4 : C * (G₁ * T + G₂ * P) ≤ C * (225 / 29 * (hC' * hA' * hB') * (A * B) * nR c) := by
      calc _ ≤ _ := this
        _ = _ := by ring
    exact le_of_mul_le_mul_left h4 hC
  have hden : 0 < A ^ 2 * B ^ 2 * hA' * hB' := by positivity
  have hterm : pterm k c p = Wk lamW k p ^ 2 * (G₁ * T + G₂ * P) / (A ^ 2 * B ^ 2 * hA' * hB') := by
    have e1 : w1 k p = Wk lamW k p ^ 2 * G₁ / (A ^ 2 * B ^ 2 * hA' * hB') := rfl
    have e2 : w2 k p = Wk lamW k p ^ 2 * G₂ / (A ^ 2 * B ^ 2 * hA' * hB') := rfl
    rw [pterm, e1, e2]
    ring
  rw [hterm, hW, div_le_iff₀ hden]
  have hv : 0 ≤ vv (nsq p) * vv (nsq (k - p)) := mul_nonneg (vv_nonneg _) (vv_nonneg _)
  have hAe : (nsq p : ℝ) = A := nsq_cast p
  have hBe : (nsq (k - p) : ℝ) = B := nsq_cast (k - p)
  have hrhs : 36 * hC' * nR c * (aa (nsq p) * aa (nsq (k - p))) / (464 / 100) *
      (A ^ 2 * B ^ 2 * hA' * hB') =
      vv (nsq p) * vv (nsq (k - p)) * (225 / 29 * (hC' * hA' * hB') * (A * B) * nR c) := by
    simp only [aa, hAe, hBe]
    field_simp
    ring
  rw [hrhs]
  exact mul_le_mul_of_nonneg_left h3 hv

/-- The pair lemma, ordered case. -/
lemma pair_ordered (k p : Mode) (c : R3) (hc : dR k c = 0) (hC : 1936 ≤ nsq k) (hp : p ≠ 0)
    (hl : k - p ≠ 0) (hAB : nsq p ≤ nsq (k - p)) :
    pterm k c p ≤ 36 * hm k * nR c * (aa (nsq p) * aa (nsq (k - p))) / (464 / 100) := by
  have hk : k ≠ 0 := fun h => by
    rw [h] at hC
    simp [(nsq_eq_zero_iff (0 : Mode)).2 rfl] at hC
  have hA1 := nsq_pos_of_ne hp
  have hAe : (nsq p : ℝ) = absSq p := nsq_cast p
  have hBe : (nsq (k - p) : ℝ) = absSq (k - p) := nsq_cast (k - p)
  have hCe : (nsq k : ℝ) = absSq k := nsq_cast k
  set A := absSq p with hAdef
  set B := absSq (k - p) with hBdef
  set C := absSq k with hCdef
  set y := dZ p k with hydef
  have hBy : B = A + C - 2 * y := by rw [hBdef, absSq_sub]; ring
  have hyle : y ^ 2 ≤ A * C := dZ_sq_le p k
  have hC' : (1936 : ℝ) ≤ C := by rw [← hCe]; exact_mod_cast hC
  have hA' : (1 : ℝ) ≤ A := by rw [← hAe]; exact_mod_cast hA1
  have hABr : A ≤ B := by rw [← hAe, ← hBe]; exact_mod_cast hAB
  -- `B ≥ 484`
  have hB484 : (484 : ℝ) ≤ B := by
    obtain ⟨_, h⟩ := abs_le_of_sq_le_sq' (show (4 * y) ^ 2 ≤ (4 * A + C) ^ 2 by
      nlinarith [sq_nonneg (4 * A - C)]) (by positivity)
    linarith
  have hB484n : 484 ≤ nsq (k - p) := by
    have : ((484 : ℕ) : ℝ) ≤ (nsq (k - p) : ℝ) := by rw [hBe]; exact_mod_cast hB484
    exact_mod_cast this
  have hW : Wk lamW k p ^ 2 = vv (nsq p) * vv (nsq (k - p)) := by
    rw [Wk, lamW_gt (show 120 < nsq k by omega), lamW_gt (show 120 < nsq (k - p) by omega),
      vv_gt (show 120 < nsq (k - p) by omega), vv]
    have : 0 ≤ lamW (nsq p) := lamW_nonneg _
    field_simp
    ring
  have hhk : hm k = 29 / 100 * C + 117 / 500 := by
    rw [hm, hmet_affine (by omega), hCe]; ring
  have hhl : hm (k - p) = 29 / 100 * B + 117 / 500 := by
    rw [hm, hmet_affine (by omega), hBe]; ring
  have hhk0 : 0 < hm k := by rw [hhk]; positivity
  have hhl0 : 0 < hm (k - p) := by rw [hhl]; positivity
  have hhp0 : 0 < hm p := hmet_pos hA1
  refine pterm_le_of_core k p c hc hp hl hk hhp0 hhl0 hhk0 hW ?_
  have hA0 : 0 < A := by linarith
  have hC0 : 0 < C := by linarith
  have hB0 : 0 < B := by linarith
  rcases le_or_gt (nsq p) 32 with h32 | h32
  · obtain ⟨hη0, hη2⟩ := hmet_defect hA1 h32
    set η := hmet (nsq p) - (29 / 100 * (nsq p : ℝ) + 117 / 500) with hη
    have hhp : hm p = 29 / 100 * A + 117 / 500 + η := by
      rw [hη, hm, hAe]; ring
    have hA32 : A ≤ 32 := by rw [← hAe]; exact_mod_cast h32
    have hcond : η ^ 2 * (12 * A) ≤ 9 / 4 * (29 / 100) * B ^ 2 * (117 / 500 + η) := by
      have h1 : η ^ 2 ≤ 4 := by nlinarith
      have h2 : η ^ 2 * (12 * A) ≤ 4 * (12 * 32) :=
        mul_le_mul h1 (by linarith) (by positivity) (by norm_num)
      have h3 : (484 : ℝ) ^ 2 ≤ B ^ 2 := by nlinarith
      have h4 : 9 / 4 * (29 / 100) * (484 : ℝ) ^ 2 * (117 / 500) ≤
          9 / 4 * (29 / 100) * B ^ 2 * (117 / 500 + η) := by
        apply mul_le_mul (by nlinarith) (by linarith) (by norm_num) (by positivity)
      norm_num at h4 ⊢
      linarith
    have := pair_core (29 / 100) (117 / 500) η A B C y rfl rfl hA0 hABr (by linarith) hBy hyle hC0
      hη0 hcond
    have hL : Lst k p = η * (B - C) := by
      simp only [Lst, hhk, hhl, hhp, ← hAdef, ← hBdef, ← hCdef]; ring
    rw [hL, hhk, hhl, hhp]
    refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_))
    · ring
    · ring
  · have hhp : hm p = 29 / 100 * A + 117 / 500 := by
      rw [hm, hmet_affine (by omega), hAe]; ring
    have := pair_core0 (29 / 100) (117 / 500) A B C y rfl rfl hA0 hB0 hBy hyle hC0
    have hL : Lst k p = 0 := by
      simp only [Lst, hhk, hhl, hhp, ← hAdef, ← hBdef, ← hCdef]; ring
    rw [hL, hhk, hhl, hhp]
    refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_))
    · ring
    · ring

/-- **The pair lemma.** -/
theorem pair_le (k p : Mode) (c : R3) (hc : dR k c = 0) (hC : 1936 ≤ nsq k) :
    pterm k c p ≤ 36 * hm k * nR c * (aa (nsq p) * aa (nsq (k - p))) / (464 / 100) := by
  by_cases hp : p = 0
  · subst hp
    simp [pterm, w1, w2, absSq_zero, aa, nsq, sub_zero]
  by_cases hl : k - p = 0
  · have h0 : nsq (0 : Mode) = 0 := (nsq_eq_zero_iff _).2 rfl
    simp [pterm, w1, w2, hl, absSq_zero, aa, h0]
  rcases le_total (nsq p) (nsq (k - p)) with h | h
  · exact pair_ordered k p c hc hC hp hl h
  · have := pair_ordered k (k - p) c hc hC hl (by simpa using hp) (by simpa using h)
    rw [pterm_symm k p c hc, sub_sub_self'] at this
    rwa [mul_comm (aa (nsq p))]

end Row
end OVNS
