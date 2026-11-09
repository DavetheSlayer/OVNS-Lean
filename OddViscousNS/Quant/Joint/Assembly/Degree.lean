import OddViscousNS.Quant.Joint.Assembly.Near

/-!
# J6: the degree calculus of the joint role table

`JDeg a b m`: on the scaled caps, `0 ≤ m ≤ C U^a R^b Ex(c', R)`, for every scaling `K, c`.  This is
`JointBelow` with the bookkeeping made compositional: `mul`, `add`, `rpow`, `sqrt`, `mono`, and the
exit `JDeg.below`: a monomial of degree `(a, b)` in `(U, R)` is `≲ Q` as soon as `b ≤ 3` and
`(a − 1)/8 + b ≤ 3` (`U ≤ R^{1/8}`, `JDom.clock_le`).  The two conditions are the two endpoints of
the sector `1 ≤ U ≤ R^{1/8}`, so they are also necessary.

The base degrees are the sizes of survey §1.1 at the caps `CapsScaledJ`:
`(P_F, y, J_F) ~ (1, 0), (1/2, 1/2), (2, 0)`, `(A_S, W_S) ~ (0, 3/2)`, `(B_S, B_H) ~ (0, 2)`,
`J_S ~ (0, 3)`, `(E_S, A_H) ~ (0, 1)`, `1/λ_* ~ (1, −1)`, `P_S(1/λ_*) ~ (1, 4)`.  A polylog of `R`
has degree `(0, 0)` (`JDeg.logR`).

J5 discharges `below₁`, `below₂` with these lemmas, one line per monomial: `Assembly/Roles.lean`
does it for the printed role table.
-/

noncomputable section

namespace OVNS.Quant

/-- **Monomial in the sector**: `U^a R^b ≤ U^{a'} R^{b'}` on the joint domain, under the two
endpoint conditions. -/
theorem JDom.clock_le {R₀ X R a b a' b' : ℝ} (h : JDom R₀ X R) (hb : b ≤ b')
    (hab : (a - a') / 8 + b ≤ b') : jointU X ^ a * R ^ b ≤ jointU X ^ a' * R ^ b' := by
  have hU1 := h.one_lt_U
  have hU0 : 0 < jointU X := by linarith
  have hR1 := h.one_lt_R
  have hR0 := h.R_pos
  have hrU (x : ℝ) : 0 < jointU X ^ x := Real.rpow_pos_of_pos hU0 x
  have hrR (x : ℝ) : 0 < R ^ x := Real.rpow_pos_of_pos hR0 x
  rcases le_total a a' with haa | haa
  · exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le hU1.le haa)
      (Real.rpow_le_rpow_of_exponent_le hR1.le hb) (hrR _).le (hrU _).le
  · have e : jointU X ^ a = jointU X ^ a' * jointU X ^ (a - a') := by
      rw [← Real.rpow_add hU0]
      congr 1
      ring
    have h1 : jointU X ^ (a - a') ≤ R ^ ((a - a') / 8) := by
      calc jointU X ^ (a - a') ≤ (R ^ ((1 : ℝ) / 8)) ^ (a - a') :=
            Real.rpow_le_rpow hU0.le h.U_le (by linarith)
        _ = R ^ ((a - a') / 8) := by
            rw [← Real.rpow_mul hR0.le]
            congr 1
            ring
    rw [e, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (hrU _).le
    calc jointU X ^ (a - a') * R ^ b ≤ R ^ ((a - a') / 8) * R ^ b :=
          mul_le_mul_of_nonneg_right h1 (hrR _).le
      _ = R ^ ((a - a') / 8 + b) := (Real.rpow_add hR0 _ _).symm
      _ ≤ R ^ b' := Real.rpow_le_rpow_of_exponent_le hR1.le hab

/-- **`m` has joint degree `(a, b)`**: on the scaled caps, `0 ≤ m ≤ C U^a R^b Ex(c', R)`. -/
def JDeg (a b : ℝ) (m : ℝ → ℝ → Caps → ℝ) : Prop :=
  ∀ K c : ℝ, 1 ≤ K → 0 ≤ c → ∃ C c' R₀ : ℝ, 0 ≤ C ∧ ∀ X R : ℝ, JDom R₀ X R → ∀ caps : Caps,
    CapsScaledJ K c X R caps → 0 ≤ m X R caps ∧
      m X R caps ≤ C * (jointU X ^ a * R ^ b) * Ex c' R

namespace JDeg

variable {a b a' b' : ℝ} {m m' : ℝ → ℝ → Caps → ℝ}

/-- The degree only grows. -/
theorem mono (h : JDeg a b m) (hb : b ≤ b') (hab : (a - a') / 8 + b ≤ b') : JDeg a' b' m := by
  intro K c hK hc
  obtain ⟨C, c', R₀, hC, hm⟩ := h K c hK hc
  refine ⟨C, c', R₀, hC, fun X R hdom caps hcaps ↦ ?_⟩
  obtain ⟨h0, h1⟩ := hm X R hdom caps hcaps
  refine ⟨h0, h1.trans (mul_le_mul_of_nonneg_right ?_ (Ex_pos _ _).le)⟩
  exact mul_le_mul_of_nonneg_left (hdom.clock_le hb hab) hC

/-- **The exit**: degree at most `(1, 3)` on the sector is `JointBelow`. -/
theorem below (h : JDeg a b m) (hb : b ≤ 3) (hab : (a - 1) / 8 + b ≤ 3) : JointBelow m := by
  intro K c hK hc
  obtain ⟨C, c', R₀, hC, hm⟩ := h K c hK hc
  refine ⟨C, c', R₀, fun X R hdom caps hcaps ↦ (hm X R hdom caps hcaps).2.trans ?_⟩
  have h1 := hdom.clock_le hb hab
  rw [Real.rpow_one, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h1
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hC) (Ex_pos _ _).le

theorem mul (h : JDeg a b m) (h' : JDeg a' b' m') :
    JDeg (a + a') (b + b') fun X R caps ↦ m X R caps * m' X R caps := by
  intro K c hK hc
  obtain ⟨C, e, R₁, hC, hm⟩ := h K c hK hc
  obtain ⟨C', e', R₂, hC', hm'⟩ := h' K c hK hc
  refine ⟨C * C', e + e', max R₁ R₂, mul_nonneg hC hC', fun X R hdom caps hcaps ↦ ?_⟩
  obtain ⟨h0, h1⟩ := hm X R (hdom.mono (le_max_left _ _)) caps hcaps
  obtain ⟨h0', h1'⟩ := hm' X R (hdom.mono (le_max_right _ _)) caps hcaps
  have hU0 : 0 < jointU X := by linarith [hdom.one_lt_U]
  have hR0 := hdom.R_pos
  refine ⟨mul_nonneg h0 h0', (mul_le_mul h1 h1' h0' (h0.trans h1)).trans_eq ?_⟩
  rw [Real.rpow_add hU0, Real.rpow_add hR0, Ex_add]
  ring

theorem add (h : JDeg a b m) (h' : JDeg a b m') :
    JDeg a b fun X R caps ↦ m X R caps + m' X R caps := by
  intro K c hK hc
  obtain ⟨C, e, R₁, hC, hm⟩ := h K c hK hc
  obtain ⟨C', e', R₂, hC', hm'⟩ := h' K c hK hc
  refine ⟨C + C', max e e', max R₁ R₂, add_nonneg hC hC', fun X R hdom caps hcaps ↦ ?_⟩
  obtain ⟨h0, h1⟩ := hm X R (hdom.mono (le_max_left _ _)) caps hcaps
  obtain ⟨h0', h1'⟩ := hm' X R (hdom.mono (le_max_right _ _)) caps hcaps
  have hU0 : 0 < jointU X := by linarith [hdom.one_lt_U]
  have hR0 := hdom.R_pos
  have hM : 0 ≤ jointU X ^ a * R ^ b :=
    mul_nonneg (Real.rpow_nonneg hU0.le _) (Real.rpow_nonneg hR0.le _)
  refine ⟨add_nonneg h0 h0', (add_le_add h1 h1').trans ?_⟩
  have h2 := hdom.Ex_le_Ex (le_max_left e e')
  have h3 := hdom.Ex_le_Ex (le_max_right e e')
  have h4 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hC hM)
  have h5 := mul_le_mul_of_nonneg_left h3 (mul_nonneg hC' hM)
  calc C * (jointU X ^ a * R ^ b) * Ex e R + C' * (jointU X ^ a * R ^ b) * Ex e' R
      ≤ C * (jointU X ^ a * R ^ b) * Ex (max e e') R +
          C' * (jointU X ^ a * R ^ b) * Ex (max e e') R := add_le_add h4 h5
    _ = _ := by ring

theorem rpow (h : JDeg a b m) {e : ℝ} (he : 0 ≤ e) :
    JDeg (a * e) (b * e) fun X R caps ↦ m X R caps ^ e := by
  intro K c hK hc
  obtain ⟨C, c', R₀, hC, hm⟩ := h K c hK hc
  refine ⟨C ^ e, c' * e, R₀, Real.rpow_nonneg hC _, fun X R hdom caps hcaps ↦ ?_⟩
  obtain ⟨h0, h1⟩ := hm X R hdom caps hcaps
  have hU0 : 0 ≤ jointU X := by linarith [hdom.one_lt_U]
  have hR0 := hdom.R_pos.le
  refine ⟨Real.rpow_nonneg h0 _, (Real.rpow_le_rpow h0 h1 he).trans_eq ?_⟩
  have hu := Real.rpow_nonneg hU0 a
  have hr := Real.rpow_nonneg hR0 b
  rw [Real.mul_rpow (mul_nonneg hC (mul_nonneg hu hr)) (Ex_pos _ _).le, Ex_rpow,
    Real.mul_rpow hC (mul_nonneg hu hr), Real.mul_rpow hu hr, ← Real.rpow_mul hU0,
    ← Real.rpow_mul hR0]

theorem pow (h : JDeg a b m) (n : ℕ) :
    JDeg (a * n) (b * n) fun X R caps ↦ m X R caps ^ n := by
  have h1 := h.rpow (Nat.cast_nonneg n)
  simpa only [Real.rpow_natCast] using h1

theorem sqrt (h : JDeg a b m) :
    JDeg (a / 2) (b / 2) fun X R caps ↦ Real.sqrt (m X R caps) := by
  have h1 := h.rpow (e := 1 / 2) (by norm_num)
  simp only [← Real.sqrt_eq_rpow] at h1
  convert h1 using 1 <;> ring

/-- Constants have degree zero. -/
theorem const {k : ℝ} (hk : 0 ≤ k) : JDeg 0 0 fun _ _ _ ↦ k := fun _ _ _ _ ↦
  ⟨k, 0, 0, hk, fun X R _ _ _ ↦ ⟨hk, by simp [Ex_zero]⟩⟩

theorem const_mul {k : ℝ} (hk : 0 ≤ k) (h : JDeg a b m) :
    JDeg a b fun X R caps ↦ k * m X R caps := by
  simpa using (const hk).mul h

/-- `Ex(c, R)` has degree zero. -/
theorem ex (e : ℝ) : JDeg 0 0 fun _ R _ ↦ Ex e R := fun _ _ _ _ ↦
  ⟨1, e, 0, zero_le_one, fun X R _ _ _ ↦ ⟨(Ex_pos _ _).le, by simp⟩⟩

theorem R : JDeg 0 1 fun _ R _ ↦ R := fun _ _ _ _ ↦
  ⟨1, 0, 0, zero_le_one, fun X R hdom _ _ ↦ ⟨hdom.R_pos.le, by simp [Ex_zero]⟩⟩

theorem U : JDeg 1 0 fun X _ _ ↦ jointU X := fun _ _ _ _ ↦
  ⟨1, 0, 0, zero_le_one, fun X R hdom _ _ ↦
    ⟨by linarith [hdom.one_lt_U], by simp [Ex_zero]⟩⟩

/-- `T = U^{1/2} R^{1/2}`. -/
theorem T_eq {R₀ X R : ℝ} (hdom : JDom R₀ X R) :
    jointT X R = jointU X ^ ((1 : ℝ) / 2) * R ^ ((1 : ℝ) / 2) := by
  have hU0 : 0 ≤ jointU X := by linarith [hdom.one_lt_U]
  rw [jointT, Real.sqrt_eq_rpow, Real.mul_rpow hU0 hdom.R_pos.le]

theorem T : JDeg (1 / 2) (1 / 2) fun X R _ ↦ jointT X R := fun _ _ _ _ ↦
  ⟨1, 0, 0, zero_le_one, fun X R hdom _ _ ↦
    ⟨jointT_nonneg _ _, by beta_reduce; rw [T_eq hdom]; simp [Ex_zero]⟩⟩

/-- The force radius `φ = R − X` has degree `(0, 1)`. -/
theorem phi : JDeg 0 1 fun X R _ ↦ R - X := fun _ _ _ _ ↦
  ⟨1, 0, 0, zero_le_one, fun X R hdom _ _ ↦
    ⟨by linarith [hdom.X_le_R], by
      have := hdom.one_lt_X
      simp only [Real.rpow_zero, Real.rpow_one, one_mul, Ex_zero, mul_one]
      linarith⟩⟩

/-- `log R ≤ Ex(4, R)` on the domain. -/
theorem log_le_Ex {R₀ X R : ℝ} (hdom : JDom R₀ X R) : Real.log R ≤ Ex 4 R := by
  have hL := hdom.one_lt_log
  have hl := hdom.one_le_loglog
  set L := Real.log R with hLd
  set l := Real.log L with hld
  have hL0 : 0 < L := by linarith
  have h1 : l / 2 ≤ Real.sqrt L := by
    have h2 : Real.log (Real.sqrt L) = l / 2 := Real.log_sqrt hL0.le
    have h3 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hL0)
    linarith
  have h2 : l ^ 2 ≤ 4 * L := by
    have h3 : (l / 2) ^ 2 ≤ Real.sqrt L ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
    rw [Real.sq_sqrt hL0.le] at h3
    nlinarith
  have hl0 : 0 < l := by linarith
  have h3 : l ≤ 4 * L / l := by
    rw [le_div_iff₀ hl0]
    nlinarith
  calc L = Real.exp l := (Real.exp_log hL0).symm
    _ ≤ Real.exp (4 * L / l) := Real.exp_le_exp.2 h3
    _ = Ex 4 R := rfl

/-- `1 + log R` has degree zero. -/
theorem logR : JDeg 0 0 fun _ R _ ↦ 1 + Real.log R := fun _ _ _ _ ↦
  ⟨2, 4, 0, by norm_num, fun X R hdom _ _ ↦ by
    have h1 := hdom.one_lt_log
    have h2 := log_le_Ex hdom
    simp only [Real.rpow_zero, mul_one]
    exact ⟨by linarith, by linarith⟩⟩

/-! ### The caps -/

/-- From a scaled upper bound on a cap to the degree of its positive part. -/
private theorem cap {f : Caps → ℝ}
    (hf : ∀ {K c X R : ℝ} {caps : Caps}, 1 ≤ K → 0 ≤ c → JDom 0 X R → CapsScaledJ K c X R caps →
      f caps ≤ K * Ex c R * (jointU X ^ a * R ^ b)) : JDeg a b fun _ _ caps ↦ cp (f caps) := by
  intro K c hK hc
  refine ⟨K, c, 0, by linarith, fun X R hdom caps hcaps ↦ ⟨cp_nonneg _, ?_⟩⟩
  have hU0 : 0 ≤ jointU X := by linarith [hdom.one_lt_U]
  have hM : 0 ≤ jointU X ^ a * R ^ b :=
    mul_nonneg (Real.rpow_nonneg hU0 _) (Real.rpow_nonneg hdom.R_pos.le _)
  have hK0 : 0 ≤ K := by linarith
  have hE := Ex_pos c R
  refine cp_le (by positivity) ((hf hK hc hdom hcaps).trans_eq ?_)
  ring

theorem PF : JDeg 1 0 fun _ _ caps ↦ cp caps.PF :=
  cap fun {_ _ _ _ _} _ _ _ h ↦ by simpa using h.1.2

theorem yF : JDeg (1 / 2) (1 / 2) fun _ _ caps ↦ cp caps.yF :=
  cap fun {_ _ _ _ _} _ _ hdom h ↦ by simpa [T_eq hdom] using h.2.1.2

theorem JF : JDeg 2 0 fun _ _ caps ↦ cp caps.JF :=
  cap fun {K c X R caps} _ _ _ h ↦ by
    have h1 := h.2.2.1.2
    have e : jointU X ^ (2 : ℝ) = jointU X ^ 2 := Real.rpow_two _
    simpa [e] using h1

theorem AS : JDeg 0 (3 / 2) fun _ _ caps ↦ cp caps.AS :=
  cap fun {_ _ _ _ _} _ _ _ h ↦ by simpa [slowExpHA] using h.2.2.2.1

theorem BS : JDeg 0 2 fun _ _ caps ↦ cp caps.BS :=
  cap fun {_ _ _ _ _} _ _ _ h ↦ by simpa [slowExpHA] using h.2.2.2.2.1

theorem JS : JDeg 0 3 fun _ _ caps ↦ cp caps.JS :=
  cap fun {_ _ _ _ _} _ _ _ h ↦ by simpa [slowExpHA] using h.2.2.2.2.2.1

theorem WS : JDeg 0 (3 / 2) fun _ _ caps ↦ cp caps.WS :=
  cap fun {_ _ _ _ _} _ _ _ h ↦ by simpa [slowExpHA] using h.2.2.2.2.2.2.1

theorem ES : JDeg 0 1 fun _ _ caps ↦ cp caps.ES :=
  cap fun {_ _ _ _ _} _ _ _ h ↦ by simpa using h.2.2.2.2.2.2.2.1

theorem AH : JDeg 0 1 fun _ _ caps ↦ cp caps.AH :=
  cap fun {_ _ _ _ _} _ _ _ h ↦ by simpa using h.2.2.2.2.2.2.2.2.1

theorem BH : JDeg 0 2 fun _ _ caps ↦ cp caps.BH :=
  cap fun {K c X R caps} _ _ _ h ↦ by
    have h1 := h.2.2.2.2.2.2.2.2.2
    have e : R ^ (2 : ℝ) = R ^ 2 := Real.rpow_two _
    simpa [e] using h1

/-- `M_∞ = C Ex(c, R) R` has degree `(0, 1)`. -/
theorem Minf {C e : ℝ} (hC : 0 ≤ C) : JDeg 0 1 fun _ R _ ↦ C * Ex e R * R := by
  have h := ((ex e).const_mul hC).mul R
  simpa using h

/-- `1/λ_*` has degree `(1, −1)`: the clip length, `≍ U/R`. -/
theorem invLam : JDeg 1 (-1) fun X R caps ↦ 1 / jointLam X R caps := by
  intro K c hK hc
  refine ⟨K ^ 2, 2 * c, 0, by positivity, fun X R hdom caps hcaps ↦ ?_⟩
  obtain ⟨⟨hP1, hP⟩, -⟩ := hcaps
  have hR0 := hdom.R_pos
  have hU0 : 0 < jointU X := by linarith [hdom.one_lt_U]
  have hK0 : 0 < K := by linarith
  have hPF : 0 < caps.PF := lt_of_lt_of_le (div_pos hU0 hK0) hP1
  have hE := Ex_pos c R
  have hUR : 0 < jointU X * R := mul_pos hU0 hR0
  beta_reduce
  rw [jointLam_eq hdom hPF]
  refine ⟨by positivity, ?_⟩
  have h2 : caps.PF ^ 2 ≤ (K * Ex c R * jointU X) ^ 2 := pow_le_pow_left₀ hPF.le hP 2
  have e1 : Ex (2 * c) R = Ex c R ^ 2 := by
    rw [two_mul, Ex_add]
    ring
  have e2 : jointU X ^ (1 : ℝ) * R ^ (-1 : ℝ) = jointU X / R := by
    rw [Real.rpow_one, Real.rpow_neg_one]
    rfl
  rw [e1, e2]
  rw [div_le_iff₀ hUR]
  have h3 : K ^ 2 * (jointU X / R) * Ex c R ^ 2 * (jointU X * R) =
      (K * Ex c R * jointU X) ^ 2 := by
    field_simp
  rw [h3]
  nlinarith [sq_nonneg (K * Ex c R * jointU X)]

/-- `P_S(1/λ_*)` has degree `(1, 4)` (`P_S ≲ R⁴ + R⁵/λ_* ≲ U R⁴`, Body 47). -/
theorem price {C e : ℝ} (hC : 0 ≤ C) :
    JDeg 1 4 fun X R caps ↦ slowPrice C (Ex e R) R (1 / jointLam X R caps) := by
  have h1 : JDeg 0 4 fun _ R _ ↦ R ^ 4 := by simpa using R.pow 4
  have h2 : JDeg 0 5 fun _ R _ ↦ R ^ 5 := by simpa using R.pow 5
  have h3 := h1.mono (a' := 1) (b' := 4) le_rfl (by norm_num)
  have h4 := invLam.mul h2
  have h5 : JDeg 1 4 fun X R caps ↦ R ^ 4 + 1 / jointLam X R caps * R ^ 5 :=
    h3.add (by convert h4 using 1 <;> norm_num)
  have h6 := ((ex e).const_mul hC).mul h5
  simpa [slowPrice, mul_assoc] using h6

end JDeg

end OVNS.Quant

end
