import OddViscousNS.Quant.Joint.Quartic.Def

/-!
# The fourth correction: the total phase and the denominator (step J5, node N11)

Bodies 34, 35:
* `psi_gap`: `|Ψ| ≥ (13/16)|s|` on the near mask and the high complement, at every helicity: "`|Ψ| ≥
  |n|(|h| − |l|) − |Φ| ≥ c'|s|`", with the fixed ratio `H₀ = 16`;
* `R_phase`: `|1/(−Σ₄ + i r Ψ)| ≤ (16/13)/(q|s|)`;
* `R_static`: `K/|−Σ₄ + i r Ψ| ≤ 2 q^{−1/2}|s|^{−1/2}`, Body 35's static gain;
* `R_eps`: `1/|−Σ₄ + i r Ψ| ≤ 2 q^{−1+ε}|s|^{−1−ε}`, Body 35's interpolation, with Body 43's uniform
  constant in `0 ≤ ε ≤ 1`.
-/

noncomputable section

namespace OVNS.Quant.Quartic

open OVNS.Quant.Metric

/-- The labels on which a term can be nonzero: slow `s`, fast `l, q, e`. -/
structure Act (x : L4) : Prop where
  s : x.2.2 2 = 0
  l : inL x 2 ≠ 0
  q : x.2.1 2 ≠ 0
  e : outE x 2 ≠ 0

variable {x : L4}

lemma p_eq (x : L4) : x.2.2 + inL x = x.1 := by
  simp only [inL]
  abel

lemma Act.two (hx : Act x) : x.1 2 = inL x 2 := by
  have h := congrFun (p_eq x) 2
  simp only [Pi.add_apply, hx.s, zero_add] at h
  exact h.symm

lemma Act.p (hx : Act x) : x.1 2 ≠ 0 := by
  rw [hx.two]
  exact hx.l

lemma Act.ne_q (hx : Act x) : x.2.1 ≠ 0 := fun h => hx.q (by simp [h])

lemma Act.ne_p (hx : Act x) : x.1 ≠ 0 := fun h => hx.p (by simp [h])

lemma Act.ne_l (hx : Act x) : inL x ≠ 0 := fun h => hx.l (by simp [h])

lemma Act.ne_e (hx : Act x) : outE x ≠ 0 := fun h => hx.e (by simp [h])

lemma Act.ne_k (hx : Act x) : x.1 + x.2.1 ≠ 0 := fun h => hx.ne_e (by simp [outE, h])

lemma absk_outE (x : L4) : absk (outE x) = absk (x.1 + x.2.1) := absk_neg _

lemma absSq_outE (x : L4) : absSq (outE x) = absSq (x.1 + x.2.1) := absSq_neg _

/-- The lengths on the high complement. -/
structure Sep (x : L4) : Prop where
  sep : 16 * absk (inL x) < absk x.2.2

lemma sep_of (h : hiMu x.2.2 (inL x) ≠ 0) : Sep x := ⟨hi_sep h⟩

lemma Sep.l_ge (hx : Act x) : 1 ≤ absk (inL x) := one_le_absk hx.ne_l

lemma Sep.s_pos (h : Sep x) (hx : Act x) : 16 < absk x.2.2 := by
  have := Sep.l_ge hx
  have := h.sep
  linarith

lemma Sep.p_le (h : Sep x) : absk x.1 ≤ 17 / 16 * absk x.2.2 := by
  have h1 := absk_add_le x.2.2 (inL x)
  rw [p_eq] at h1
  have := h.sep
  linarith

lemma Sep.l_le (h : Sep x) : absk (inL x) ≤ absk x.2.2 := by
  have := h.sep
  have := absk_nonneg (inL x)
  linarith

/-- `|p| ≥ |s| − |l|`. -/
lemma p_ge (x : L4) : absk x.2.2 ≤ absk x.1 + absk (inL x) := by
  have h1 := absk_sub_le x.1 (inL x)
  have e : x.1 - inL x = x.2.2 := by
    simp only [inL]
    abel
  rw [e] at h1
  exact h1

/-- The inner phase of two fast modes with one vertical. -/
lemma lam_diff {l p : Mode} (h2 : l 2 = p 2) (hn : p 2 ≠ 0) (d a : Sgn) :
    absk p - absk l ≤ |lam d l - lam a p| := by
  have hn1 : (1 : ℝ) ≤ |(p 2 : ℝ)| := by
    have : (1 : ℤ) ≤ |p 2| := Int.one_le_abs hn
    exact_mod_cast this
  have e : lam d l - lam a p = (p 2 : ℝ) * (sg d * absk l - sg a * absk p) := by
    simp only [lam, h2]
    ring
  rw [e, abs_mul]
  have hl := absk_nonneg l
  have hp := absk_nonneg p
  have h3 : absk p - absk l ≤ |sg d * absk l - sg a * absk p| := by
    cases d <;> cases a <;> simp only [sg, Bool.false_eq_true, ite_false, ite_true] <;>
      rw [le_abs] <;> first | (left; linarith) | (right; linarith)
  have h4 := abs_nonneg (sg d * absk l - sg a * absk p)
  nlinarith only [h3, h4, hn1]

/-- The total phase is the outer phase plus the inner difference. -/
lemma psi_eq (d a b c : Sgn) (x : L4) :
    psiQ d b c x = Phi a b c x.1 x.2.1 + (lam d (inL x) - lam a x.1) := by
  simp only [psiQ, Phi, outE, lam_neg]
  ring

variable {d a b c : Sgn}

/-- **The total phase is separated**, for every helicity. -/
theorem psi_gap (hx : Act x) (h : Sep x) (hN : NearT a b c x.1 x.2.1) :
    13 / 16 * absk x.2.2 ≤ |psiQ d b c x| := by
  have h1 := lam_diff (d := d) (a := a) hx.two.symm hx.p
  have h2 : |lam d (inL x) - lam a x.1| ≤
      |psiQ d b c x| + |Phi a b c x.1 x.2.1| := by
    rw [psi_eq d a b c x]
    have e : lam d (inL x) - lam a x.1 = (Phi a b c x.1 x.2.1 + (lam d (inL x) - lam a x.1)) +
        (-Phi a b c x.1 x.2.1) := by ring
    conv_lhs => rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]
  have h3 := hN.2.2
  have h4 := p_ge x
  have h5 := h.sep
  have h6 := Sep.l_ge hx
  linarith

/-- The denominator of a channel. -/
def Rq (r : ℝ) (d b c : Sgn) (x : L4) : ℝ := ‖resolv (-1) (heatQ x) (r * psiQ d b c x)‖

lemma Rq_nonneg (r : ℝ) (d b c : Sgn) (x : L4) : 0 ≤ Rq r d b c x := norm_nonneg _

/-- The heat of the four ancestors. -/
lemma heat_ge (x : L4) : absSq x.2.2 ≤ heatQ x ∧ absSq x.2.1 ≤ heatQ x ∧
    absSq (x.1 + x.2.1) ≤ heatQ x := by
  have h1 := absSq_nonneg x.2.2
  have h2 := absSq_nonneg (inL x)
  have h3 := absSq_nonneg x.2.1
  have h4 := absSq_nonneg (outE x)
  have e := absSq_outE x
  unfold heatQ
  refine ⟨by linarith, by linarith, by linarith⟩

lemma heat_pos (hx : Act x) : 0 < heatQ x := by
  have h1 := one_le_absSq hx.ne_q
  have h2 := (heat_ge x).2.1
  linarith

/-- **The largest leg against the four heats**: `K² ≤ 2 Σ₄`. -/
lemma mx_sq_le (h : Sep x) (hx : Act x) : mxL x.1 x.2.1 ^ 2 ≤ 2 * heatQ x := by
  obtain ⟨h1, h2, h3⟩ := heat_ge x
  have hH : 0 ≤ heatQ x := (heat_pos hx).le
  have hp : absk x.1 ^ 2 ≤ 2 * heatQ x := by
    have h4 := Sep.p_le h
    have h5 : absk x.1 ^ 2 ≤ (17 / 16 * absk x.2.2) ^ 2 :=
      pow_le_pow_left₀ (absk_nonneg _) h4 2
    have h6 : absk x.2.2 ^ 2 = absSq x.2.2 := absk_sq _
    nlinarith only [h5, h6, h1]
  have hq : absk x.2.1 ^ 2 ≤ 2 * heatQ x := by
    rw [absk_sq]
    linarith
  have he : absk (x.1 + x.2.1) ^ 2 ≤ 2 * heatQ x := by
    rw [absk_sq]
    linarith
  unfold mxL
  rcases max_cases (absk x.1) (max (absk x.2.1) (absk (x.1 + x.2.1))) with ⟨h4, -⟩ | ⟨h4, -⟩
  · rw [h4]
    exact hp
  · rw [h4]
    rcases max_cases (absk x.2.1) (absk (x.1 + x.2.1)) with ⟨h5, -⟩ | ⟨h5, -⟩
    · rw [h5]
      exact hq
    · rw [h5]
      exact he

/-- The denominator against the phase. -/
theorem R_phase {r : ℝ} (hr : r ≠ 0) (hx : Act x) (h : Sep x) (hN : NearT a b c x.1 x.2.1) :
    Rq r d b c x * (|r| * absk x.2.2) ≤ 16 / 13 := by
  have hq : 0 < |r| := abs_pos.2 hr
  have hs := Sep.s_pos h hx
  have hg := psi_gap (d := d) hx h hN
  rw [Rq, norm_resolv_sgn (Or.inr rfl)]
  set z := r * psiQ d b c x with hz
  have hz1 : 13 / 16 * (|r| * absk x.2.2) ≤ |z| := by
    rw [hz, abs_mul]
    nlinarith only [mul_le_mul_of_nonneg_left hg hq.le]
  have hz2 : |z| ≤ Real.sqrt (heatQ x ^ 2 + z ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith only [sq_nonneg (heatQ x)])
  have hA : 0 < |r| * absk x.2.2 := by positivity
  have hS : 0 < Real.sqrt (heatQ x ^ 2 + z ^ 2) := by
    have : 0 < |z| := by linarith only [hz1, hA]
    linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hS, one_mul]
  linarith

/-- The denominator against the heat. -/
lemma R_heat (hx : Act x) (r : ℝ) : Rq r d b c x * heatQ x ≤ 1 := by
  have hH := heat_pos hx
  have h1 := norm_resolv_le (ε := -1) (Or.inr rfl) hH (r * psiQ d b c x)
  calc Rq r d b c x * heatQ x ≤ 1 / heatQ x * heatQ x :=
        mul_le_mul_of_nonneg_right h1 hH.le
    _ = 1 := by field_simp

/-- **The static gain** of Body 35: `K/|−Σ₄ + i r Ψ| ≤ 2/√(q|s|)`. -/
theorem R_static {r : ℝ} (hr : r ≠ 0) (hx : Act x) (h : Sep x) (hN : NearT a b c x.1 x.2.1) :
    Rq r d b c x * mxL x.1 x.2.1 * Real.sqrt (|r| * absk x.2.2) ≤ 2 := by
  have hR := Rq_nonneg r d b c x
  have h1 := R_phase (d := d) hr hx h hN
  have h2 := R_heat (d := d) (b := b) (c := c) hx r
  have h3 := mx_sq_le h hx
  have hq : 0 < |r| := abs_pos.2 hr
  have hs := Sep.s_pos h hx
  have hA : 0 ≤ |r| * absk x.2.2 := by positivity
  have hmx : 0 ≤ mxL x.1 x.2.1 := (absk_nonneg _).trans (le_mxL _ _).1
  have h4 : Rq r d b c x * mxL x.1 x.2.1 ^ 2 ≤ 2 := by
    have := mul_le_mul_of_nonneg_left h3 hR
    nlinarith only [this, h2]
  have h5 : (Rq r d b c x * mxL x.1 x.2.1 * Real.sqrt (|r| * absk x.2.2)) ^ 2 ≤ 2 ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hA]
    have e : Rq r d b c x ^ 2 * mxL x.1 x.2.1 ^ 2 * (|r| * absk x.2.2) =
        (Rq r d b c x * mxL x.1 x.2.1 ^ 2) * (Rq r d b c x * (|r| * absk x.2.2)) := by ring
    rw [e]
    have := mul_le_mul h4 h1 (by positivity) (by norm_num)
    linarith only [this]
  exact (pow_le_pow_iff_left₀ (by positivity) (by norm_num) two_ne_zero).1 h5

/-- The interpolation of two bounds of a number. -/
lemma rpow_interp {R A B c ε : ℝ} (hR : 0 ≤ R) (hA : 0 < A) (hB : 0 < B) (hc : 1 ≤ c)
    (h1 : R * A ≤ c) (h2 : R * B ≤ 1) (h0 : 0 ≤ ε) (h3 : ε ≤ 1) :
    R * (A ^ (1 - ε) * B ^ ε) ≤ c := by
  rcases hR.eq_or_lt with hz | hp
  · rw [← hz, zero_mul]
    linarith
  have e : R * (A ^ (1 - ε) * B ^ ε) = (R * A) ^ (1 - ε) * (R * B) ^ ε := by
    rw [Real.mul_rpow hR hA.le, Real.mul_rpow hR hB.le]
    have e1 : R ^ (1 - ε) * R ^ ε = R := by
      rw [← Real.rpow_add hp]
      simp
    calc R * (A ^ (1 - ε) * B ^ ε) = (R ^ (1 - ε) * R ^ ε) * (A ^ (1 - ε) * B ^ ε) := by rw [e1]
      _ = _ := by ring
  rw [e]
  have h4 : (R * A) ^ (1 - ε) ≤ c ^ (1 - ε) :=
    Real.rpow_le_rpow (by positivity) h1 (by linarith)
  have h5 : c ^ (1 - ε) ≤ c ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc (by linarith)
  have h6 : (R * B) ^ ε ≤ 1 := Real.rpow_le_one (by positivity) h2 h0
  rw [Real.rpow_one] at h5
  have h7 : 0 ≤ (R * A) ^ (1 - ε) := by positivity
  have h8 : 0 ≤ (R * B) ^ ε := by positivity
  nlinarith only [h4, h5, h6, h7, h8]

/-- **The interpolated denominator** of Bodies 35, 43, uniform in `ε`:
`q^{1−ε} |s|^{1+ε} / |−Σ₄ + i r Ψ| ≤ 2`. -/
theorem R_eps {r ε : ℝ} (hr : r ≠ 0) (hx : Act x) (h : Sep x) (hN : NearT a b c x.1 x.2.1)
    (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    Rq r d b c x * (|r| ^ (1 - ε) * absk x.2.2 ^ (1 + ε)) ≤ 2 := by
  have hq : 0 < |r| := abs_pos.2 hr
  have hs : 0 < absk x.2.2 := by
    have := Sep.s_pos h hx
    linarith
  have h2 := R_phase (d := d) hr hx h hN
  have h3 := R_heat (d := d) (b := b) (c := c) hx r
  have hB : Rq r d b c x * absSq x.2.2 ≤ 1 :=
    (mul_le_mul_of_nonneg_left (heat_ge x).1 (Rq_nonneg r d b c x)).trans h3
  have hS : 0 < absSq x.2.2 := by
    rw [← absk_sq]
    positivity
  have h4 := rpow_interp (Rq_nonneg r d b c x) (by positivity : 0 < |r| * absk x.2.2) hS
    (by norm_num : (1 : ℝ) ≤ 16 / 13) h2 hB h0 h1
  have e : (|r| * absk x.2.2) ^ (1 - ε) * absSq x.2.2 ^ ε =
      |r| ^ (1 - ε) * absk x.2.2 ^ (1 + ε) := by
    rw [Real.mul_rpow hq.le hs.le, ← absk_sq, ← Real.rpow_natCast, ← Real.rpow_mul hs.le, mul_assoc,
      ← Real.rpow_add hs]
    congr 2
    push_cast
    ring
  rw [e] at h4
  linarith

end OVNS.Quant.Quartic

end
