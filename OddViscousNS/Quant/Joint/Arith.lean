import OddViscousNS.Quant.Joint.Interfaces

/-!
# Theorem 1.2, joint large force: the arithmetic of the subpower and of the clocks

Pure real arithmetic for `Joint/Regimes.lean` (all proved).
* `Ex`: exponent laws (`Ex_add`, `Ex_rpow`, `Ex_neg`), monotonicity in the exponent (`Ex_le_Ex`),
  the subpower bound `Ex c R ≤ R^ε` (`Ex_le_rpow`);
* the origin of the joint theorem's factor: `q^{−a} Ex(c, q)` is decreasing (`rpow_neg_mul_Ex_le`),
  so one trial `T = C Q Ex(C₀, R)` pays a near condition for every larger `q` (`near_pay`);
* the domain and the clocks: `U ≤ R^{1/8}`, `√R ≤ T`, `X ≤ T ≤ R` (`JDom.*`), and the guards of the
  virtual barrier `C_G P_F ≤ T/P_F`, `P_F ≤ T` (`joint_guards`);
* **the payment of the true monomials**: `highAnc_below` (rows 2, 3 of Table quant-metric, with the
  `δ₀` companion), `rootFloor_below` (the raised floor, for `qSFull`), and the closure of
  `JointBelow` under `max` and constants, whence `JointInterfaces.below₂Full`, `belowSFull`.
-/

noncomputable section

namespace OVNS.Quant

/-! ### The subpower -/

theorem Ex_pos (c t : ℝ) : 0 < Ex c t := Real.exp_pos _

theorem Ex_add (a b t : ℝ) : Ex (a + b) t = Ex a t * Ex b t := by
  unfold Ex
  rw [← Real.exp_add]
  congr 1
  ring

theorem Ex_rpow (c a t : ℝ) : Ex c t ^ a = Ex (c * a) t := by
  unfold Ex
  rw [← Real.exp_mul]
  congr 1
  ring

theorem Ex_zero (t : ℝ) : Ex 0 t = 1 := by simp [Ex]

theorem Ex_neg (c t : ℝ) : Ex (-c) t = (Ex c t)⁻¹ := by
  unfold Ex
  rw [← Real.exp_neg]
  congr 1
  ring

/-- `Ex` is monotone in the exponent where `log t / log log t ≥ 0`. -/
theorem Ex_le_Ex {a b t : ℝ} (hab : a ≤ b) (ht : 0 ≤ Real.log t)
    (hl : 0 ≤ Real.log (Real.log t)) : Ex a t ≤ Ex b t :=
  Real.exp_le_exp.2 (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hab ht) hl)

/-- `Ex c t ≥ 1` for `c ≥ 0`. -/
theorem one_le_Ex {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ Real.log t)
    (hl : 0 ≤ Real.log (Real.log t)) : 1 ≤ Ex c t := by
  rw [← Ex_zero t]
  exact Ex_le_Ex hc ht hl

/-- The subpower is below every power, once `log log R ≥ c/ε`. -/
theorem Ex_le_rpow {c ε R : ℝ} (hR : 1 < R) (hl : 0 < Real.log (Real.log R))
    (h : c ≤ ε * Real.log (Real.log R)) : Ex c R ≤ R ^ ε := by
  have hR0 : 0 < R := by linarith
  have hlog : 0 < Real.log R := Real.log_pos hR
  rw [Real.rpow_def_of_pos hR0]
  refine Real.exp_le_exp.2 ?_
  rw [div_le_iff₀ hl]
  nlinarith

/-- A number is below a small power of a large `R`. -/
theorem le_rpow_of_large {A ε R : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) (h : A ^ (1 / ε) ≤ R) :
    A ≤ R ^ ε := by
  calc A = (A ^ (1 / ε)) ^ ε := by
        rw [← Real.rpow_mul hA, one_div_mul_cancel hε.ne', Real.rpow_one]
    _ ≤ R ^ ε := Real.rpow_le_rpow (Real.rpow_nonneg hA _) h hε.le

/-- `C ≥ A^n` gives `A ≤ C^{1/n}`. -/
theorem le_rpow_of_pow_le {A C : ℝ} {n : ℕ} (hn : n ≠ 0) (hA : 0 ≤ A) (h : A ^ n ≤ C) :
    A ≤ C ^ ((1 : ℝ) / n) := by
  calc A = (A ^ n) ^ ((1 : ℝ) / n) := by
        rw [one_div, Real.pow_rpow_inv_natCast hA hn]
    _ ≤ C ^ ((1 : ℝ) / n) := Real.rpow_le_rpow (pow_nonneg hA n) h (by positivity)

/-- `R ≥ exp(exp B)` gives `log log R ≥ B`. -/
theorem le_loglog {B R : ℝ} (h : Real.exp (Real.exp B) ≤ R) : B ≤ Real.log (Real.log R) := by
  have h0 : 0 < R := lt_of_lt_of_le (Real.exp_pos _) h
  have h1 : Real.exp B ≤ Real.log R := (Real.le_log_iff_exp_le h0).2 h
  exact (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) h1)).2 h1

/-- **`q^{−a} Ex(c, q)` is decreasing** past `log log q ≥ c/a`.  (No calculus:
`t/log t − s/log s ≤ (t − s)/log s` for `s ≤ t`.) -/
theorem rpow_neg_mul_Ex_le {a c q₁ q₂ : ℝ} (hc : 0 ≤ c) (hq₁ : 1 < q₁)
    (hl : 1 < Real.log q₁) (hq : q₁ ≤ q₂) (h : c ≤ a * Real.log (Real.log q₁)) :
    q₂ ^ (-a) * Ex c q₂ ≤ q₁ ^ (-a) * Ex c q₁ := by
  have h0 : 0 < q₁ := by linarith
  have h0' : 0 < q₂ := by linarith
  set s := Real.log q₁ with hs
  set t := Real.log q₂ with ht
  have hst : s ≤ t := Real.log_le_log h0 hq
  have hs0 : 0 < s := by linarith
  have hls : 0 < Real.log s := Real.log_pos hl
  have hlt : Real.log s ≤ Real.log t := Real.log_le_log hs0 hst
  rw [Real.rpow_def_of_pos h0, Real.rpow_def_of_pos h0']
  unfold Ex
  rw [← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  rw [← hs, ← ht]
  have h1 : c * t / Real.log t ≤ c * t / Real.log s :=
    div_le_div_of_nonneg_left (mul_nonneg hc (by linarith)) hls hlt
  have h2 : c * t / Real.log s - c * s / Real.log s ≤ a * (t - s) := by
    rw [← sub_div, div_le_iff₀ hls]
    nlinarith
  nlinarith

/-- Up to `t ≤ R⁴`, the subpower at `t` costs at most the factor `4` in the exponent at `R`. -/
theorem Ex_le_of_le_pow_four {c t R : ℝ} (hc : 0 ≤ c) (hR : 1 < R) (hl : 1 < Real.log R)
    (hRt : R ≤ t) (ht : t ≤ R ^ 4) : Ex c t ≤ Ex (4 * c) R := by
  have hR0 : 0 < R := by linarith
  have ht0 : 0 < t := by linarith
  have h1 : Real.log R ≤ Real.log t := Real.log_le_log hR0 hRt
  have h2 : Real.log t ≤ 4 * Real.log R := by
    have := Real.log_le_log ht0 ht
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have h3 : 0 < Real.log (Real.log R) := Real.log_pos hl
  have h4 : Real.log (Real.log R) ≤ Real.log (Real.log t) :=
    Real.log_le_log (by linarith) h1
  refine Real.exp_le_exp.2 ?_
  have h5 : c * Real.log t ≤ 4 * c * Real.log R := by
    calc c * Real.log t ≤ c * (4 * Real.log R) := mul_le_mul_of_nonneg_left h2 hc
      _ = 4 * c * Real.log R := by ring
  exact div_le_div₀ (mul_nonneg (by linarith) (by linarith)) h5 h3 h4

/-- **The near payment.**  With a near moment `N(q) ≤ C_n q^{−a} Ex(c_n, q)` and a leading
coefficient `L ≤ C_L Q^a Ex(c_L, R)`, the trial `T = C Q Ex(C₀, R)` gives `L N(q) ≤ 1` for all
`q ≥ T`, as soon as `C_L C_n ≤ C^a` and `c_L + 4 c_n ≤ a C₀`, provided `R ≤ T ≤ R⁴`.  This is the
origin of the subpower of the joint theorem (survey §1.3).  At a tie (`a = 1/2`, role 15/31)
nothing else can pay it. -/
theorem near_pay {a CL cL Cn cn C C₀ Q R q Lc Nq : ℝ} (ha : 0 ≤ a) (hCL : 0 ≤ CL) (hCn : 0 ≤ Cn)
    (hcn : 0 ≤ cn) (hC : 0 < C) (hQ : 0 < Q) (hR1 : 1 < R) (hlR : 1 < Real.log R)
    (hR : cn ≤ a * Real.log (Real.log R)) (hlow : R ≤ C * Q * Ex C₀ R)
    (hup : C * Q * Ex C₀ R ≤ R ^ 4) (hCa : CL * Cn ≤ C ^ a) (hC₀ : cL + 4 * cn ≤ a * C₀)
    (hq : C * Q * Ex C₀ R ≤ q) (hL0 : 0 ≤ Lc) (hL : Lc ≤ CL * Q ^ a * Ex cL R)
    (hN : Nq ≤ Cn * q ^ (-a) * Ex cn q) : Lc * Nq ≤ 1 := by
  have hl0 : 0 < Real.log R := by linarith
  have hll : 0 < Real.log (Real.log R) := Real.log_pos hlR
  set Tr := C * Q * Ex C₀ R with hTr
  have hTr0 : 0 < Tr := by linarith
  have hltr : 1 < Real.log Tr := hlR.trans_le (Real.log_le_log (by linarith) hlow)
  have hmono : Real.log (Real.log R) ≤ Real.log (Real.log Tr) :=
    Real.log_le_log hl0 (Real.log_le_log (by linarith) hlow)
  have hcna : cn ≤ a * Real.log (Real.log Tr) := hR.trans (mul_le_mul_of_nonneg_left hmono ha)
  have h1 : q ^ (-a) * Ex cn q ≤ Tr ^ (-a) * Ex cn Tr :=
    rpow_neg_mul_Ex_le hcn (by linarith) hltr hq hcna
  have h2 : Tr ^ (-a) = C ^ (-a) * Q ^ (-a) * Ex (C₀ * -a) R := by
    rw [hTr, Real.mul_rpow (by positivity) (Ex_pos _ _).le, Real.mul_rpow hC.le hQ.le, Ex_rpow]
  have h3 : Ex cn Tr ≤ Ex (4 * cn) R := Ex_le_of_le_pow_four hcn hR1 hlR hlow hup
  have hC1 : CL * Cn * C ^ (-a) ≤ 1 := by
    rw [Real.rpow_neg hC.le, ← div_eq_mul_inv, div_le_one (Real.rpow_pos_of_pos hC _)]
    exact hCa
  have hQ1 : Q ^ a * Q ^ (-a) = 1 := by
    rw [← Real.rpow_add hQ, add_neg_cancel, Real.rpow_zero]
  have hE1 : Ex cL R * (Ex (C₀ * -a) R * Ex (4 * cn) R) ≤ 1 := by
    rw [← Ex_add, ← Ex_add, ← Ex_zero R]
    exact Ex_le_Ex (by linarith) hl0.le hll.le
  have hE2 : 0 ≤ C ^ (-a) * Q ^ (-a) * Ex (C₀ * -a) R :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hC.le _) (Real.rpow_nonneg hQ.le _)) (Ex_pos _ _).le
  have hqa : 0 ≤ Tr ^ (-a) * Ex cn Tr :=
    mul_nonneg (Real.rpow_nonneg hTr0.le _) (Ex_pos _ _).le
  have h4 : Nq ≤ Cn * (Tr ^ (-a) * Ex cn Tr) := by
    calc Nq ≤ Cn * q ^ (-a) * Ex cn q := hN
      _ = Cn * (q ^ (-a) * Ex cn q) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 hCn
  have h5 : Tr ^ (-a) * Ex cn Tr ≤ C ^ (-a) * Q ^ (-a) * Ex (C₀ * -a) R * Ex (4 * cn) R := by
    rw [h2]
    exact mul_le_mul_of_nonneg_left h3 hE2
  calc Lc * Nq ≤ Lc * (Cn * (Tr ^ (-a) * Ex cn Tr)) := mul_le_mul_of_nonneg_left h4 hL0
    _ ≤ (CL * Q ^ a * Ex cL R) * (Cn * (Tr ^ (-a) * Ex cn Tr)) :=
        mul_le_mul_of_nonneg_right hL (mul_nonneg hCn hqa)
    _ ≤ (CL * Q ^ a * Ex cL R) *
          (Cn * (C ^ (-a) * Q ^ (-a) * Ex (C₀ * -a) R * Ex (4 * cn) R)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 hCn)
          (mul_nonneg (mul_nonneg hCL (Real.rpow_nonneg hQ.le _)) (Ex_pos _ _).le)
    _ = (CL * Cn * C ^ (-a)) * (Q ^ a * Q ^ (-a)) *
          (Ex cL R * (Ex (C₀ * -a) R * Ex (4 * cn) R)) := by ring
    _ ≤ 1 := by
        rw [hQ1, mul_one]
        have h7 : 0 ≤ Ex cL R * (Ex (C₀ * -a) R * Ex (4 * cn) R) :=
          mul_nonneg (Ex_pos _ _).le (mul_nonneg (Ex_pos _ _).le (Ex_pos _ _).le)
        exact (mul_le_mul_of_nonneg_right hC1 h7).trans (by simpa using hE1)

/-! ### The domain and the clocks -/

section Domain

variable {R₀ X R : ℝ}

theorem three_le_exp_exp : 3 ≤ Real.exp (Real.exp 1) := by
  have h1 := Real.add_one_le_exp (1 : ℝ)
  have h2 := Real.add_one_le_exp (Real.exp 1)
  linarith

/-- The domain only shrinks with `R₀`. -/
theorem JDom.mono {R₁ : ℝ} (h : JDom R₀ X R) (hR : R₁ ≤ R₀) : JDom R₁ X R :=
  ⟨h.1, max_le (hR.trans ((le_max_left _ _).trans h.2)) ((le_max_right _ _).trans h.2)⟩

theorem JDom.three_le_X (h : JDom R₀ X R) : 3 ≤ X := three_le_exp_exp.trans h.1

theorem JDom.one_lt_X (h : JDom R₀ X R) : 1 < X := by linarith [h.three_le_X]

theorem JDom.R₀_le (h : JDom R₀ X R) : R₀ ≤ R := (le_max_left _ _).trans h.2

theorem JDom.pow_le (h : JDom R₀ X R) : X ^ (24 : ℝ) ≤ R := (le_max_right _ _).trans h.2

/-- `X ≤ R`. -/
theorem JDom.X_le_R (h : JDom R₀ X R) : X ≤ R := by
  have h1 : X ^ (1 : ℝ) ≤ X ^ (24 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le h.one_lt_X.le (by norm_num)
  rw [Real.rpow_one] at h1
  exact h1.trans h.pow_le

theorem JDom.one_lt_R (h : JDom R₀ X R) : 1 < R := h.one_lt_X.trans_le h.X_le_R

theorem JDom.R_pos (h : JDom R₀ X R) : 0 < R := by linarith [h.one_lt_R]

/-- `log R ≥ e`. -/
theorem JDom.exp_one_le_log (h : JDom R₀ X R) : Real.exp 1 ≤ Real.log R := by
  rw [Real.le_log_iff_exp_le h.R_pos]
  exact h.1.trans h.X_le_R

/-- `log R > 1`. -/
theorem JDom.one_lt_log (h : JDom R₀ X R) : 1 < Real.log R := by
  have := h.exp_one_le_log
  have := Real.add_one_le_exp (1 : ℝ)
  linarith

theorem JDom.log_nonneg (h : JDom R₀ X R) : 0 ≤ Real.log R := by linarith [h.one_lt_log]

/-- `log log R ≥ 1`. -/
theorem JDom.one_le_loglog (h : JDom R₀ X R) : 1 ≤ Real.log (Real.log R) := by
  rw [Real.le_log_iff_exp_le (by linarith [h.one_lt_log])]
  exact h.exp_one_le_log

theorem JDom.loglog_pos (h : JDom R₀ X R) : 0 < Real.log (Real.log R) := by
  linarith [h.one_le_loglog]

theorem JDom.one_le_Ex (h : JDom R₀ X R) {c : ℝ} (hc : 0 ≤ c) : 1 ≤ Ex c R :=
  OVNS.Quant.one_le_Ex hc h.log_nonneg h.loglog_pos.le

theorem JDom.Ex_le_Ex (h : JDom R₀ X R) {a b : ℝ} (hab : a ≤ b) : Ex a R ≤ Ex b R :=
  OVNS.Quant.Ex_le_Ex hab h.log_nonneg h.loglog_pos.le

/-- `1 ≤ U`, indeed `X ≤ U`. -/
theorem JDom.X_le_U (h : JDom R₀ X R) : X ≤ jointU X := by
  have h1 : X ^ (1 : ℝ) ≤ X ^ ((1719 : ℝ) / 719) :=
    Real.rpow_le_rpow_of_exponent_le h.one_lt_X.le (by norm_num)
  rwa [Real.rpow_one] at h1

theorem JDom.one_lt_U (h : JDom R₀ X R) : 1 < jointU X := h.one_lt_X.trans_le h.X_le_U

/-- **`U ≤ R^{1/8}`** (TeX: `β < 3`). -/
theorem JDom.U_le (h : JDom R₀ X R) : jointU X ≤ R ^ ((1 : ℝ) / 8) := by
  have hX0 : 0 < X := by linarith [h.one_lt_X]
  have h1 : X ^ ((3 : ℝ)) ≤ R ^ ((1 : ℝ) / 8) := by
    calc X ^ (3 : ℝ) = (X ^ (24 : ℝ)) ^ ((1 : ℝ) / 8) := by
          rw [← Real.rpow_mul hX0.le]
          norm_num
      _ ≤ R ^ ((1 : ℝ) / 8) :=
          Real.rpow_le_rpow (Real.rpow_nonneg hX0.le _) h.pow_le (by norm_num)
  refine le_trans ?_ h1
  exact Real.rpow_le_rpow_of_exponent_le h.one_lt_X.le (by norm_num)

theorem jointT_nonneg (X R : ℝ) : 0 ≤ jointT X R := Real.sqrt_nonneg _

/-- `T² = UR`. -/
theorem JDom.T_sq (h : JDom R₀ X R) : jointT X R ^ 2 = jointU X * R :=
  Real.sq_sqrt (mul_nonneg (by linarith [h.one_lt_U]) h.R_pos.le)

/-- `√R ≤ T`. -/
theorem JDom.sqrt_le_T (h : JDom R₀ X R) : R ^ ((1 : ℝ) / 2) ≤ jointT X R := by
  rw [← Real.sqrt_eq_rpow]
  refine Real.sqrt_le_sqrt ?_
  have := mul_le_mul_of_nonneg_right h.one_lt_U.le h.R_pos.le
  linarith

/-- `X ≤ T`. -/
theorem JDom.X_le_T (h : JDom R₀ X R) : X ≤ jointT X R := by
  refine Real.le_sqrt_of_sq_le ?_
  have h1 : 1 ≤ X := h.one_lt_X.le
  have h2 : X ≤ jointU X := h.X_le_U
  nlinarith [h.X_le_R]

theorem JDom.T_pos (h : JDom R₀ X R) : 0 < jointT X R := by
  linarith [h.X_le_T, h.one_lt_X]

/-- `R ≤ Q`. -/
theorem JDom.R_le_Q (h : JDom R₀ X R) : R ≤ jointQ X R := by
  have h1 := h.one_lt_R
  have h2 := h.one_lt_U
  unfold jointQ
  have h3 : R ≤ R ^ 3 := le_self_pow₀ h1.le (by norm_num)
  nlinarith

theorem JDom.Q_pos (h : JDom R₀ X R) : 0 < jointQ X R := by linarith [h.R_le_Q, h.one_lt_R]

/-- `C U R³ Ex(C₀, R) ≤ R⁴` for `C, Ex(C₀, R) ≤ R^{1/4}`. -/
theorem JDom.trial_le (h : JDom R₀ X R) {C E : ℝ} (hE0 : 0 ≤ E)
    (hC : C ≤ R ^ ((1 : ℝ) / 4)) (hE : E ≤ R ^ ((1 : ℝ) / 4)) :
    C * jointQ X R * E ≤ R ^ 4 := by
  have hR0 := h.R_pos
  have hU := h.U_le
  have hU0 : 0 ≤ jointU X := by linarith [h.one_lt_U]
  have e : R ^ ((1 : ℝ) / 4) * R ^ ((1 : ℝ) / 8) * R ^ ((1 : ℝ) / 4) ≤ R := by
    rw [← Real.rpow_add hR0, ← Real.rpow_add hR0]
    calc R ^ ((1 : ℝ) / 4 + 1 / 8 + 1 / 4) ≤ R ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h.one_lt_R.le (by norm_num)
      _ = R := Real.rpow_one R
  unfold jointQ
  have hr : ∀ x : ℝ, 0 ≤ R ^ x := fun x ↦ Real.rpow_nonneg hR0.le x
  calc C * (jointU X * R ^ 3) * E = (C * jointU X * E) * R ^ 3 := by ring
    _ ≤ (R ^ ((1 : ℝ) / 4) * R ^ ((1 : ℝ) / 8) * R ^ ((1 : ℝ) / 4)) * R ^ 3 :=
        mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul hC hU hU0 (hr _)) hE hE0
          (mul_nonneg (hr _) (hr _))) (by positivity)
    _ ≤ R * R ^ 3 := mul_le_mul_of_nonneg_right e (by positivity)
    _ = R ^ 4 := by ring

/-- **The guards of the virtual barrier** (correction 3 of `Joint/Interfaces.lean`): if
`P ≤ K Ex U` with `K, Ex ≤ R^{1/32}` and `C_G ≤ R^{1/8}`, then `C_G P ≤ T/P` (the resonant term is
below the virtual coefficient, without any kinetic scale) and `P ≤ T` (`B_* ≥ 1`, so clips are
shorter than one unit). -/
theorem JDom.guards (h : JDom R₀ X R) {K E CG P : ℝ} (hP0 : 0 < P) (hE0 : 0 ≤ E)
    (hP : P ≤ K * E * jointU X) (hK : K ≤ R ^ ((1 : ℝ) / 32)) (hE : E ≤ R ^ ((1 : ℝ) / 32))
    (hCG : CG ≤ R ^ ((1 : ℝ) / 8)) : CG * P ≤ jointT X R / P ∧ P ≤ jointT X R := by
  have hR0 := h.R_pos
  have hR1 := h.one_lt_R
  have hU0 : 0 ≤ jointU X := by linarith [h.one_lt_U]
  have hr : ∀ x : ℝ, 0 ≤ R ^ x := fun x ↦ Real.rpow_nonneg hR0.le x
  have hP1 : P ≤ R ^ ((3 : ℝ) / 16) := by
    calc P ≤ K * E * jointU X := hP
      _ ≤ R ^ ((1 : ℝ) / 32) * R ^ ((1 : ℝ) / 32) * R ^ ((1 : ℝ) / 8) :=
          mul_le_mul (mul_le_mul hK hE hE0 (hr _)) h.U_le hU0 (mul_nonneg (hr _) (hr _))
      _ = R ^ ((3 : ℝ) / 16) := by
          rw [← Real.rpow_add hR0, ← Real.rpow_add hR0]
          norm_num
  have hP2 : P ^ 2 ≤ R ^ ((3 : ℝ) / 8) := by
    calc P ^ 2 ≤ (R ^ ((3 : ℝ) / 16)) ^ 2 := pow_le_pow_left₀ hP0.le hP1 2
      _ = R ^ ((3 : ℝ) / 8) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hR0.le]
          norm_num
  have hT : R ^ ((1 : ℝ) / 2) ≤ jointT X R := h.sqrt_le_T
  constructor
  · rw [le_div_iff₀ hP0]
    calc CG * P * P = CG * P ^ 2 := by ring
      _ ≤ R ^ ((1 : ℝ) / 8) * R ^ ((3 : ℝ) / 8) := mul_le_mul hCG hP2 (sq_nonneg _) (hr _)
      _ = R ^ ((1 : ℝ) / 2) := by
          rw [← Real.rpow_add hR0]
          norm_num
      _ ≤ jointT X R := hT
  · exact hP1.trans ((Real.rpow_le_rpow_of_exponent_le hR1.le (by norm_num)).trans hT)

end Domain

/-! ### The closure of `JointBelow` -/

/-- `JointBelow` is stable under `max`. -/
theorem JointBelow.sup {q q' : ℝ → ℝ → Caps → ℝ} (h : JointBelow q) (h' : JointBelow q') :
    JointBelow fun X R caps ↦ max (q X R caps) (q' X R caps) := by
  intro K c hK hc
  obtain ⟨C₁, B₁, R₁, h₁⟩ := h K c hK hc
  obtain ⟨C₂, B₂, R₂, h₂⟩ := h' K c hK hc
  refine ⟨max C₁ 0 + max C₂ 0, max B₁ B₂, max R₁ R₂, fun X R hdom caps hcaps ↦ ?_⟩
  have hQ := hdom.Q_pos.le
  have h1 := le_max_right C₁ 0
  have h2 := le_max_right C₂ 0
  have pay : ∀ {C' B' x : ℝ}, C' ≤ max C₁ 0 + max C₂ 0 → B' ≤ max B₁ B₂ →
      x ≤ C' * jointQ X R * Ex B' R →
      x ≤ (max C₁ 0 + max C₂ 0) * jointQ X R * Ex (max B₁ B₂) R := fun hC hB hx ↦
    hx.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hQ) (Ex_pos _ _).le).trans
      (mul_le_mul_of_nonneg_left (hdom.Ex_le_Ex hB) (by positivity)))
  refine max_le (pay ?_ (le_max_left _ _) (h₁ X R (hdom.mono (le_max_left _ _)) caps hcaps))
    (pay ?_ (le_max_right _ _) (h₂ X R (hdom.mono (le_max_right _ _)) caps hcaps))
  · linarith [le_max_left C₁ 0]
  · linarith [le_max_left C₂ 0]

/-- `JointBelow` is stable under a nonnegative constant. -/
theorem JointBelow.const_mul {q : ℝ → ℝ → Caps → ℝ} (h : JointBelow q) {a : ℝ} (ha : 0 ≤ a) :
    JointBelow fun X R caps ↦ a * q X R caps := by
  intro K c hK hc
  obtain ⟨C, B, R₀, hq⟩ := h K c hK hc
  refine ⟨a * C, B, R₀, fun X R hdom caps hcaps ↦ ?_⟩
  calc a * q X R caps ≤ a * (C * jointQ X R * Ex B R) :=
        mul_le_mul_of_nonneg_left (hq X R hdom caps hcaps) ha
    _ = a * C * jointQ X R * Ex B R := by ring

/-! ### The rows 2, 3 of Table quant-metric and the raised floor are paid -/

/-- The arithmetic of the two rows.  The variables are `κ = 1/λ_*`, `σ = √R`, and `e` a common
bound: `b ≤ e R²`, `W, M ≤ e R σ`, `κ R ≤ e² U`, `C_S Ex ≤ e`.  The row `rowM2` is `≤ e⁵ U R³`, the
row `rowM3` is `≤ 6 e⁵ U R³`.  The `δ₀` term alone is `≤ 2 e⁵ U R^{5/2}`: below `Q`, with a gap. -/
private lemma highAnc_alg {e U R σ κ b W M P : ℝ} (he : 1 ≤ e) (hU : 1 ≤ U) (hσ : 1 ≤ σ)
    (hσR : σ ^ 2 = R) (hκ0 : 0 ≤ κ) (hκ : κ * R ≤ e ^ 2 * U) (hb0 : 0 ≤ b) (hb : b ≤ e * R ^ 2)
    (hW : W ≤ e * (R * σ)) (hM : M ≤ e * R) (hP : P ≤ e * (R ^ 4 + κ * R ^ 5)) :
    b ^ 3 * κ / R ^ 2 + (W + M) * b * (Real.sqrt (P * κ) / R ^ 2 + delta0 * κ) ≤
      7 * e ^ 5 * (U * R ^ 3) := by
  have hR1 : 1 ≤ R := by rw [← hσR]; nlinarith
  have hR0 : 0 < R := by linarith
  have he0 : 0 < e := by linarith
  have hU0 : 0 < U := by linarith
  have hσ0 : 0 < σ := by linarith
  -- the first row
  have h1 : b ^ 3 * κ / R ^ 2 ≤ e ^ 5 * (U * R ^ 3) := by
    rw [div_le_iff₀ (by positivity)]
    have hb3 : b ^ 3 ≤ (e * R ^ 2) ^ 3 := pow_le_pow_left₀ hb0 hb 3
    calc b ^ 3 * κ ≤ (e * R ^ 2) ^ 3 * κ := mul_le_mul_of_nonneg_right hb3 hκ0
      _ = e ^ 3 * R ^ 5 * (κ * R) := by ring
      _ ≤ e ^ 3 * R ^ 5 * (e ^ 2 * U) := mul_le_mul_of_nonneg_left hκ (by positivity)
      _ = e ^ 5 * (U * R ^ 3) * R ^ 2 := by ring
  -- the root
  have hPκ : P * κ ≤ (2 * e ^ 3 * U * (R * σ)) ^ 2 := by
    have h2 : P * κ ≤ e * (R ^ 4 + κ * R ^ 5) * κ := mul_le_mul_of_nonneg_right hP hκ0
    have h3 : R ^ 4 * κ ≤ R ^ 3 * (e ^ 2 * U) := by
      calc R ^ 4 * κ = R ^ 3 * (κ * R) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hκ (by positivity)
    have h4 : (κ * R) ^ 2 ≤ (e ^ 2 * U) ^ 2 := pow_le_pow_left₀ (by positivity) hκ 2
    have h5 : κ * R ^ 5 * κ ≤ R ^ 3 * (e ^ 2 * U) ^ 2 := by
      calc κ * R ^ 5 * κ = R ^ 3 * (κ * R) ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)
    have h6 : (R ^ 4 + κ * R ^ 5) * κ ≤ 2 * (e ^ 4 * U ^ 2 * R ^ 3) := by
      have h7 : e ^ 2 * U ≤ e ^ 4 * U ^ 2 := by
        have : 1 ≤ e ^ 2 * U := by nlinarith
        nlinarith
      have h8 : R ^ 3 * (e ^ 2 * U) ≤ R ^ 3 * (e ^ 4 * U ^ 2) :=
        mul_le_mul_of_nonneg_left h7 (by positivity)
      nlinarith only [h3, h5, h8]
    have h9 : e * ((R ^ 4 + κ * R ^ 5) * κ) ≤ e * (2 * (e ^ 4 * U ^ 2 * R ^ 3)) :=
      mul_le_mul_of_nonneg_left h6 he0.le
    have h10 : e ^ 5 ≤ e ^ 6 := pow_le_pow_right₀ he (by norm_num)
    have h11 : e ^ 5 * (U ^ 2 * R ^ 3) ≤ e ^ 6 * (U ^ 2 * R ^ 3) :=
      mul_le_mul_of_nonneg_right h10 (by positivity)
    have e1 : (2 * e ^ 3 * U * (R * σ)) ^ 2 = 4 * e ^ 6 * U ^ 2 * R ^ 2 * σ ^ 2 := by ring
    rw [e1, hσR]
    have e2 : e * (R ^ 4 + κ * R ^ 5) * κ = e * ((R ^ 4 + κ * R ^ 5) * κ) := by ring
    nlinarith only [h2, h9, h11, e2, mul_nonneg (mul_nonneg (pow_nonneg he0.le 6)
      (pow_nonneg hU0.le 2)) (pow_nonneg hR0.le 3)]
  have hroot : Real.sqrt (P * κ) ≤ 2 * e ^ 3 * U * (R * σ) :=
    Real.sqrt_le_iff.2 ⟨by positivity, hPκ⟩
  -- the bracket, multiplied by `R²`
  have hδ : delta0 * κ * R ^ 2 ≤ e ^ 3 * U * (R * σ) := by
    have h2 : delta0 ≤ 1 := by norm_num [delta0]
    have h3 : 0 ≤ delta0 := by norm_num [delta0]
    have h4 : delta0 * κ * R ^ 2 ≤ 1 * κ * R ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hκ0) (by positivity)
    have h5 : κ * R ^ 2 ≤ e ^ 2 * U * R := by
      calc κ * R ^ 2 = κ * R * R := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hκ hR0.le
    have h6 : e ^ 2 * U * R ≤ e ^ 3 * U * (R * σ) := by
      have h7 : e ^ 2 ≤ e ^ 3 := pow_le_pow_right₀ he (by norm_num)
      have h8 : R ≤ R * σ := le_mul_of_one_le_right hR0.le hσ
      exact mul_le_mul (mul_le_mul_of_nonneg_right h7 hU0.le) h8 hR0.le (by positivity)
    linarith
  have hbr : Real.sqrt (P * κ) / R ^ 2 + delta0 * κ ≤ 3 * e ^ 3 * U * (R * σ) / R ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have e1 : (Real.sqrt (P * κ) / R ^ 2 + delta0 * κ) * R ^ 2 =
        Real.sqrt (P * κ) + delta0 * κ * R ^ 2 := by
      field_simp
    rw [e1]
    linarith
  have hWM : W + M ≤ 2 * e * (R * σ) := by
    have h2 : e * R ≤ e * (R * σ) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hR0.le hσ) he0.le
    linarith
  have hprod : (W + M) * b ≤ 2 * e * (R * σ) * (e * R ^ 2) :=
    mul_le_mul hWM hb hb0 (by positivity)
  have hbr0 : 0 ≤ Real.sqrt (P * κ) / R ^ 2 + delta0 * κ := by
    have : 0 ≤ delta0 := by norm_num [delta0]
    positivity
  have h2 : (W + M) * b * (Real.sqrt (P * κ) / R ^ 2 + delta0 * κ) ≤
      6 * e ^ 5 * (U * R ^ 3) := by
    calc (W + M) * b * (Real.sqrt (P * κ) / R ^ 2 + delta0 * κ)
        ≤ (2 * e * (R * σ) * (e * R ^ 2)) * (3 * e ^ 3 * U * (R * σ) / R ^ 2) :=
          mul_le_mul hprod hbr hbr0 (by positivity)
      _ = 6 * e ^ 5 * (U * R ^ 2 * σ ^ 2) := by
          field_simp
          ring
      _ = 6 * e ^ 5 * (U * R ^ 3) := by rw [hσR]; ring
  linarith

/-- `1/λ_* ≤ e² U/R` on scaled caps, at the virtual coefficient `B_* = T/P_F`. -/
theorem jointLam_eq {R₀ X R : ℝ} (hdom : JDom R₀ X R) {caps : Caps} (hP : 0 < caps.PF) :
    1 / jointLam X R caps = 11 / 16 * caps.PF ^ 2 / (jointU X * R) := by
  have hT := hdom.T_sq
  have hU := hdom.one_lt_U
  have hR := hdom.R_pos
  have hUR : 0 < jointU X * R := mul_pos (by linarith) hR
  unfold jointLam jointBs
  rw [lamStar_jointBs hP.ne', hT]
  field_simp

/-- **The rows 2, 3 are `≲ Q` on scaled caps**, up to the subpower: the true monomials pay at `Q`
exactly as the TeX says, and neither dropping the fitted `a b` nor keeping the `δ₀` companion breaks
a payment. -/
theorem highAnc_le {C cS K c R₀ X R : ℝ} (hC : 0 ≤ C) (hcS : 0 ≤ cS) (hK : 1 ≤ K) (hc : 0 ≤ c)
    (hdom : JDom R₀ X R) {caps : Caps} (hcaps : CapsScaledJ K c X R caps) :
    highAnc C (Ex cS R) X R caps ≤
      7 * (1 + K + C) ^ 5 * jointQ X R * Ex (5 * (c + cS)) R := by
  obtain ⟨⟨hP1, hP⟩, -, -, -, hB, -, hW, -, -, -⟩ := hcaps
  have hR1 := hdom.one_lt_R
  have hR0 := hdom.R_pos
  have hU1 := hdom.one_lt_U
  have hU0 : 0 < jointU X := by linarith
  have hK0 : 0 < K := by linarith
  have hEc : 1 ≤ Ex c R := hdom.one_le_Ex hc
  have hEs : 1 ≤ Ex cS R := hdom.one_le_Ex hcS
  set e := 1 + K * Ex c R + C * Ex cS R with he
  have hKE0 : 0 ≤ K * Ex c R := by positivity
  have hCE0 : 0 ≤ C * Ex cS R := by positivity
  have he1 : 1 ≤ e := by linarith
  have he0 : 0 < e := by linarith
  have heK : K * Ex c R ≤ e := by linarith
  have heC : C * Ex cS R ≤ e := by linarith
  have hPF : 0 < caps.PF := lt_of_lt_of_le (div_pos hU0 hK0) hP1
  set σ := Real.sqrt R with hσd
  have hσR : σ ^ 2 = R := Real.sq_sqrt hR0.le
  have hσ1 : 1 ≤ σ := Real.one_le_sqrt.2 hR1.le
  have hσ0 : 0 < σ := by linarith
  -- the three caps
  have e32 : R ^ slowExpHA.eW = R * σ := by
    have h1 : R ^ slowExpHA.eW = R ^ (1 : ℝ) * R ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_add hR0]
      norm_num [slowExpHA]
    rw [h1, Real.rpow_one, hσd, Real.sqrt_eq_rpow]
  have e2 : R ^ slowExpHA.eB = R ^ 2 := by
    simp only [slowExpHA]
    exact_mod_cast Real.rpow_natCast R 2
  have hW' : cp caps.WS ≤ e * (R * σ) := by
    refine cp_le (by positivity) (hW.trans ?_)
    rw [e32]
    exact mul_le_mul_of_nonneg_right heK (by positivity)
  have hB' : cp caps.BS ≤ e * R ^ 2 := by
    refine cp_le (by positivity) (hB.trans ?_)
    rw [e2]
    exact mul_le_mul_of_nonneg_right heK (by positivity)
  have hM' : C * Ex cS R * R ≤ e * R := mul_le_mul_of_nonneg_right heC hR0.le
  -- `κ = 1/λ_*`
  set κ := 1 / jointLam X R caps with hκd
  have hκe : κ = 11 / 16 * caps.PF ^ 2 / (jointU X * R) := jointLam_eq hdom hPF
  have hUR : 0 < jointU X * R := mul_pos hU0 hR0
  have hκ0 : 0 ≤ κ := by rw [hκe]; positivity
  have hPF2 : caps.PF ≤ e * jointU X :=
    hP.trans (mul_le_mul_of_nonneg_right heK hU0.le)
  have hκR : κ * R ≤ e ^ 2 * jointU X := by
    rw [hκe]
    have h1 : 11 / 16 * caps.PF ^ 2 / (jointU X * R) * R = 11 / 16 * caps.PF ^ 2 / jointU X := by
      field_simp
    rw [h1, div_le_iff₀ hU0]
    have h2 : caps.PF ^ 2 ≤ (e * jointU X) ^ 2 := pow_le_pow_left₀ hPF.le hPF2 2
    nlinarith [mul_nonneg (sq_nonneg e) (sq_nonneg (jointU X))]
  have hlam : jointLam X R caps = 1 / κ := by
    rw [hκd, one_div_one_div]
  -- the price
  set P := slowPrice C (Ex cS R) R κ with hPd
  have hP0 : 0 ≤ P := by rw [hPd]; unfold slowPrice; positivity
  have hPle : P ≤ e * (R ^ 4 + κ * R ^ 5) :=
    mul_le_mul_of_nonneg_right heC (by positivity)
  have hmain := highAnc_alg (M := C * Ex cS R * R) he1 hU1.le hσ1 hσR hκ0 hκR (cp_nonneg _) hB' hW'
    hM' hPle
  have heq : highAnc C (Ex cS R) X R caps = cp caps.BS ^ 3 * κ / R ^ 2 +
      (cp caps.WS + C * Ex cS R * R) * cp caps.BS *
        (Real.sqrt (P * κ) / R ^ 2 + delta0 * κ) := by
    unfold highAnc rowM2 rowM3 jointD
    rw [← hκd, ← hPd, hlam]
    simp only [one_mul, div_eq_mul_inv, inv_inv, mul_inv]
    ring
  rw [heq]
  refine hmain.trans ?_
  have hEt : 1 ≤ Ex (c + cS) R := hdom.one_le_Ex (by linarith)
  have hE1 : Ex c R ≤ Ex (c + cS) R := hdom.Ex_le_Ex (by linarith)
  have hE2 : Ex cS R ≤ Ex (c + cS) R := hdom.Ex_le_Ex (by linarith)
  have heb : e ≤ (1 + K + C) * Ex (c + cS) R := by
    have h1 : K * Ex c R ≤ K * Ex (c + cS) R := mul_le_mul_of_nonneg_left hE1 hK0.le
    have h2 : C * Ex cS R ≤ C * Ex (c + cS) R := mul_le_mul_of_nonneg_left hE2 hC
    rw [he]
    nlinarith only [h1, h2, hEt]
  have h5 : e ^ 5 ≤ (1 + K + C) ^ 5 * Ex (5 * (c + cS)) R := by
    have h6 := pow_le_pow_left₀ he0.le heb 5
    have e5 : Ex (5 * (c + cS)) R = Ex (c + cS) R ^ 5 := by
      have := Ex_rpow (c + cS) 5 R
      rw [mul_comm 5]
      rw [← this]
      exact (Real.rpow_natCast _ 5).symm ▸ by norm_num
    rw [e5, ← mul_pow]
    exact h6
  have hQ0 := hdom.Q_pos.le
  have e6 : jointQ X R = jointU X * R ^ 3 := rfl
  calc 7 * e ^ 5 * (jointU X * R ^ 3) ≤
        7 * ((1 + K + C) ^ 5 * Ex (5 * (c + cS)) R) * jointQ X R := by
        rw [← e6]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h5 (by norm_num)) hQ0
    _ = _ := by ring

/-- **The rows 2, 3 of Table quant-metric are paid**: the inverse prices are `≤ C Q Ex(C₀, R)`. -/
theorem highAnc_below {C cS : ℝ} (hC : 0 ≤ C) (hcS : 0 ≤ cS) :
    JointBelow fun X R caps ↦ highAnc C (Ex cS R) X R caps := fun K c hK hc ↦
  ⟨7 * (1 + K + C) ^ 5, 5 * (c + cS), 0, fun _ _ hdom _ hcaps ↦ highAnc_le hC hcS hK hc hdom hcaps⟩

/-- **The raised floor is `≲ Q`** on scaled caps (in fact `≲ R³ + U R` at its top): no risk to `Q`.
-/
theorem rootFloor_below : JointBelow fun X R caps ↦ rootFloor X (R - X) caps := by
  intro K c hK hc
  refine ⟨2 ^ 21 * (1 + c4) * (1 + K) ^ 2, 2 * c, 0, fun X R hdom caps hcaps ↦ ?_⟩
  obtain ⟨-, ⟨-, hY⟩, -, -, hB, -, -, -, -, -⟩ := hcaps
  have hR1 := hdom.one_lt_R
  have hR0 := hdom.R_pos
  have hU1 := hdom.one_lt_U
  have hU0 : 0 < jointU X := by linarith
  have hX1 := hdom.one_lt_X
  have hXR := hdom.X_le_R
  have hEc : 1 ≤ Ex c R := hdom.one_le_Ex hc
  have hc4 := c4_pos
  set e := 1 + K * Ex c R with he
  have hK0 : 0 < K := by linarith
  have hKE0 : 0 ≤ K * Ex c R := by positivity
  have he1 : 1 ≤ e := by linarith
  have heK : K * Ex c R ≤ e := by linarith
  have e2 : R ^ slowExpHA.eB = R ^ 2 := by
    simp only [slowExpHA]
    exact_mod_cast Real.rpow_natCast R 2
  have hT0 := hdom.T_pos
  have hy : cp caps.yF ≤ e * jointT X R := cp_le (by positivity)
    (hY.trans (mul_le_mul_of_nonneg_right heK hT0.le))
  have hB' : cp caps.BS ≤ e * R ^ 2 := by
    refine cp_le (by positivity) (hB.trans ?_)
    rw [e2]
    exact mul_le_mul_of_nonneg_right heK (by positivity)
  have hy2 : cp caps.yF ^ 2 ≤ e ^ 2 * (jointU X * R) := by
    have := pow_le_pow_left₀ (cp_nonneg _) hy 2
    rwa [mul_pow, hdom.T_sq] at this
  have hU : jointU X ≤ R := by
    refine hdom.U_le.trans ?_
    calc R ^ ((1 : ℝ) / 8) ≤ R ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hR1.le (by norm_num)
      _ = R := Real.rpow_one R
  have hT : jointT X R ≤ R := by
    have h1 : jointT X R ≤ Real.sqrt (R * R) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hU hR0.le)
    rwa [Real.sqrt_mul_self hR0.le] at h1
  have hR2 : R ≤ R ^ 2 := le_self_pow₀ hR1.le (by norm_num)
  have hyR : cp caps.yF ≤ e * R ^ 2 :=
    hy.trans (mul_le_mul_of_nonneg_left (hT.trans hR2) (by linarith))
  have hTotal : totalY X caps ≤ 8 * (e * R ^ 2) := by
    have h1 : 1 ≤ e * R ^ 2 := by nlinarith
    have h2 : X ≤ e * R ^ 2 := by nlinarith
    unfold totalY
    linarith
  have hTotal0 : 0 ≤ totalY X caps := by
    have := cp_nonneg caps.yF
    have := cp_nonneg caps.BS
    unfold totalY
    positivity
  have hφ0 : 0 ≤ R - X := by linarith
  have hφ : R - X ≤ R := by linarith
  set Q := jointU X * R ^ 3 with hQ
  have hQ1 : R ^ 3 ≤ Q := le_mul_of_one_le_left (by positivity) hU1.le
  have hR3 : R ^ 2 ≤ R ^ 3 := pow_le_pow_right₀ hR1.le (by norm_num)
  have hR3' : R ≤ R ^ 3 := hR2.trans hR3
  have h1R : 1 ≤ R ^ 3 := one_le_pow₀ hR1.le
  have he2 : e ≤ e ^ 2 := by nlinarith
  have heQ : Q ≤ e ^ 2 * Q := le_mul_of_one_le_left (by positivity) (by nlinarith)
  have t1 : 2 + 4 * (R - X) + 2 ^ 9 * (R - X) ≤ 518 * (e ^ 2 * Q) := by nlinarith
  have t2 : 2 ^ 12 * totalY X caps ≤ 2 ^ 15 * (e ^ 2 * Q) := by
    have : e * R ^ 2 ≤ e ^ 2 * Q := mul_le_mul he2 (hR3.trans hQ1) (by positivity) (by positivity)
    nlinarith
  have t3 : 2 ^ 5 * c4 * totalY X caps * (R - X) ≤ 2 ^ 8 * c4 * (e ^ 2 * Q) := by
    have h1 : totalY X caps * (R - X) ≤ 8 * (e * R ^ 2) * R :=
      mul_le_mul hTotal hφ hφ0 (by positivity)
    have h2 : e * R ^ 2 * R ≤ e ^ 2 * Q := by
      have e3 : e * R ^ 2 * R = e * R ^ 3 := by ring
      rw [e3]
      exact mul_le_mul he2 hQ1 (by positivity) (by positivity)
    have h3 := mul_le_mul_of_nonneg_left (h1.trans (by nlinarith : 8 * (e * R ^ 2) * R ≤
      8 * (e ^ 2 * Q))) (by positivity : 0 ≤ 2 ^ 5 * c4)
    nlinarith only [h3]
  have t4 : 2 ^ 20 * (1 + c4) * cp caps.yF ^ 2 ≤ 2 ^ 20 * (1 + c4) * (e ^ 2 * Q) := by
    refine mul_le_mul_of_nonneg_left (hy2.trans ?_) (by positivity)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul_of_nonneg_left (hR3') hU0.le
  have hEt : e ^ 2 ≤ (1 + K) ^ 2 * Ex (2 * c) R := by
    have h1 : e ≤ (1 + K) * Ex c R := by
      rw [he]
      nlinarith only [hEc]
    have h2 := pow_le_pow_left₀ (by linarith) h1 2
    have e5 : Ex (2 * c) R = Ex c R ^ 2 := by
      rw [two_mul, Ex_add]
      ring
    rw [e5, ← mul_pow]
    exact h2
  have hQ0 : 0 ≤ Q := by positivity
  have hc1 : 0 ≤ 1 + c4 := by linarith
  have hfin : rootFloor X (R - X) caps ≤ 2 ^ 21 * (1 + c4) * (e ^ 2 * Q) := by
    unfold rootFloor
    have h0 : 0 ≤ e ^ 2 * Q := by positivity
    nlinarith only [t1, t2, t3, t4, h0, hc4, mul_nonneg hc4.le h0]
  refine hfin.trans ?_
  have e7 : jointQ X R = Q := rfl
  rw [e7]
  calc 2 ^ 21 * (1 + c4) * (e ^ 2 * Q) ≤
        2 ^ 21 * (1 + c4) * (((1 + K) ^ 2 * Ex (2 * c) R) * Q) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hEt hQ0) (by positivity)
    _ = _ := by ring

/-- `q₂Full` is below `Q`: the rows 2, 3 are paid here, the other roles by `below₂`. -/
theorem JointInterfaces.below₂Full {D : JointData} (hD : JointInterfaces D) :
    JointBelow D.q₂Full :=
  hD.below₂.sup ((highAnc_below (hD.CS_ge.trans' zero_le_one) hD.cS_nonneg).const_mul hD.Cm_nonneg)

/-- `qSFull` is below `Q`: the raised floor is paid here and through `below₀`, the other slow roles
by `belowS`. -/
theorem JointInterfaces.belowSFull {D : JointData} (hD : JointInterfaces D) :
    JointBelow D.qSFull :=
  hD.belowS.sup (JointBelow.const_mul (rootFloor_below.sup
    (hD.below₀.const_mul (by norm_num : (0 : ℝ) ≤ 16))) (by norm_num))

end OVNS.Quant

end
