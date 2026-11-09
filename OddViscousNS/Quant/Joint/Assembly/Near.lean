import OddViscousNS.Quant.Joint.Arith

/-!
# J6: the near coefficients `LN`, `LP` and the two ties

`jointLN`, `jointLP` are the leading coefficients of `JointData`, fixed for the whole of J5:
`NearPaid (jointLN …) (jointLP …) nearN nearP` is the hypothesis `nearPaid` of `JointPiece`.

**What the energies consume** (report `t12_j6_assembly.md` §4, with the sources).  With
`q = |r|`, `N = nearN q`, `P = nearP q`, and the library's `nearD1_le`, `nearD2_le`, the native
differential in a direction `h` costs `C₀ N ‖h‖₁ b_F²` at weight one, `C₀ N ‖h‖₂ b_F c_F` at two:
* the low mixed direction has `‖h_lo‖_m ≲ M_∞ ‖F‖_{m+1}` (Body 27; Lean: `hnorm_Qlo_le`), hence the
  coefficient `M_∞ y`, tied at `Q^{1/2}`;
* the purefast direction has the fixed-force coefficient `√P_F y^{3/2}` (roles 15, 31);
* the genuine filter direction has `‖H_ψ‖₁ ≤ 1`, hence the constant, inside the floor `Q^{1/2}`;
* the high mixed direction is not paid here: it is removed by `Q₄`, `Q₄,₁`.
The proper profile is consumed by the static and heat roles 13, 14, 16, 17, with coefficient `y`,
and by the quartics, with `P q⁻¹ ·` (TeX Lemma quant-quartic); there the role is
`q^{−4/3} U B_S² ≲ 1` (survey §1.2, `(U B_S²)^{3/4}`), that is `U^{1/4} √B_S · P ≲ 1`.

**Design.**  `LeadBelow` is the only constraint on `LN`, `LP` from the regimes layer, and in E5-J,
E8-J the near condition is a hypothesis: so every monomial below `Q^a` may be added free of charge,
and this is what the floors `Q^{1/2}`, `Q^{1/3}` and the slack `Ex(1, R)` do.  The floors make the
near payment caps-free; `Ex(1, R) ≥ 1` absorbs any polylogarithm of `R` at these ties (which `Ex`
in `q` could not, since the near role is not a threshold).  The normalizations `KN`, `KP` are free
parameters of the package: their values have no derivation yet (caveat (A1)).

`leadN_jointLN`, `leadP_jointLP` are the fields `leadN`, `leadP` of `JointInterfaces`:
* `leadN`: `(M_∞ y)² ≲ R² T² = Q`, the tie that produces `Ex` (survey §1.3).  The purefast term has
  the gap `(U T)^{1/2} ≤ R`;
* `leadP`: `U^{1/4} √B_S ≲ U^{1/4} R ≤ U^{1/3} R = Q^{1/3}`, that is `U^{3/4} R³ ≤ Q`.
-/

noncomputable section

namespace OVNS.Quant

/-- **The leading coefficient of the native moment**, with `M_∞ = C_S Ex(c_S, R) R`:
`K_N Ex(1, R) (M_∞ y + √P_F y^{3/2} + Q^{1/2})`. -/
def jointLN (KN CS cS X R : ℝ) (caps : Caps) : ℝ :=
  KN * Ex 1 R * (CS * Ex cS R * R * cp caps.yF +
    Real.sqrt (cp caps.PF) * cp caps.yF ^ ((3 : ℝ) / 2) + jointQ X R ^ ((1 : ℝ) / 2))

/-- **The leading coefficient of the proper moment**:
`K_P Ex(1, R) (U^{1/4} √B_S + y + Q^{1/3})`. -/
def jointLP (KP X R : ℝ) (caps : Caps) : ℝ :=
  KP * Ex 1 R * (jointU X ^ ((1 : ℝ) / 4) * Real.sqrt (cp caps.BS) + cp caps.yF +
    jointQ X R ^ ((1 : ℝ) / 3))

section Clocks

variable {R₀ X R : ℝ}

/-- `U ≤ R`. -/
theorem JDom.U_le_self (h : JDom R₀ X R) : jointU X ≤ R :=
  h.U_le.trans (by
    calc R ^ ((1 : ℝ) / 8) ≤ R ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h.one_lt_R.le (by norm_num)
      _ = R := Real.rpow_one R)

/-- `T ≤ R`. -/
theorem JDom.T_le_self (h : JDom R₀ X R) : jointT X R ≤ R := by
  have hR := h.R_pos
  have h1 : jointT X R ≤ Real.sqrt (R * R) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right h.U_le_self hR.le)
  rwa [Real.sqrt_mul_self hR.le] at h1

/-- `R T = Q^{1/2}`: the low mixed tie. -/
theorem JDom.mul_T_eq (h : JDom R₀ X R) : R * jointT X R = jointQ X R ^ ((1 : ℝ) / 2) := by
  have hT := h.T_pos
  have hR := h.R_pos
  rw [← Real.sqrt_eq_rpow]
  symm
  rw [Real.sqrt_eq_iff_mul_self_eq h.Q_pos.le (by positivity)]
  have hT2 := h.T_sq
  have e : R * jointT X R * (R * jointT X R) = R ^ 2 * jointT X R ^ 2 := by ring
  rw [e, hT2]
  unfold jointQ
  ring

/-- `T ≤ Q^{1/3}`. -/
theorem JDom.T_le_Q (h : JDom R₀ X R) : jointT X R ≤ jointQ X R ^ ((1 : ℝ) / 3) := by
  have hT := h.T_pos
  have hR := h.one_lt_R
  have hU := h.one_lt_U
  have hTR := h.T_le_self
  have hT2 := h.T_sq
  have h3 : jointT X R ^ 3 ≤ jointQ X R := by
    have e : jointT X R ^ 3 = jointT X R * (jointU X * R) := by rw [← hT2]; ring
    have h1 : jointT X R * (jointU X * R) ≤ R * (jointU X * R) :=
      mul_le_mul_of_nonneg_right hTR (by positivity)
    have h2 : R * (jointU X * R) ≤ jointU X * R ^ 3 := by
      have h4 : R ^ 2 ≤ R ^ 3 := pow_le_pow_right₀ hR.le (by norm_num)
      have e2 : R * (jointU X * R) = jointU X * R ^ 2 := by ring
      rw [e2]
      exact mul_le_mul_of_nonneg_left h4 (by positivity)
    rw [e]
    exact h1.trans h2
  simpa using le_rpow_of_pow_le (A := jointT X R) (C := jointQ X R) (n := 3) (by norm_num) hT.le h3

/-- `Q^{1/3} = U^{1/3} R`. -/
theorem JDom.Q_rpow_third (h : JDom R₀ X R) :
    jointQ X R ^ ((1 : ℝ) / 3) = jointU X ^ ((1 : ℝ) / 3) * R := by
  have hR := h.R_pos
  have hU : 0 ≤ jointU X := by linarith [h.one_lt_U]
  have e : (R ^ 3) ^ ((1 : ℝ) / 3) = R := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    norm_num
  unfold jointQ
  rw [Real.mul_rpow hU (by positivity), e]

/-- `U^{1/4} R ≤ Q^{1/3}`: the tie of the `H¹` quartic, `U^{3/4} R³ ≤ Q`. -/
theorem JDom.quartic_tie (h : JDom R₀ X R) :
    jointU X ^ ((1 : ℝ) / 4) * R ≤ jointQ X R ^ ((1 : ℝ) / 3) := by
  rw [h.Q_rpow_third]
  refine mul_le_mul_of_nonneg_right ?_ h.R_pos.le
  exact Real.rpow_le_rpow_of_exponent_le h.one_lt_U.le (by norm_num)

end Clocks

theorem one_le_Ex_mul {K c R₀ X R : ℝ} (hK : 1 ≤ K) (hc : 0 ≤ c) (hdom : JDom R₀ X R) :
    1 ≤ K * Ex c R := one_le_mul_of_one_le_of_one_le hK (hdom.one_le_Ex hc)

private lemma rpow_three_halves {Y : ℝ} (hY : 0 ≤ Y) : Y ^ ((3 : ℝ) / 2) = Y * Real.sqrt Y := by
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add' hY (by norm_num), Real.rpow_one,
    Real.sqrt_eq_rpow]

/-- The purefast term against the low mixed tie: `√p Y^{3/2} ≤ E² R T`. -/
private lemma purefast_le {p Y E U T R : ℝ} (hp0 : 0 ≤ p) (hY0 : 0 ≤ Y) (hE : 0 ≤ E) (hU0 : 0 ≤ U)
    (hT0 : 0 ≤ T) (hR : 0 ≤ R) (hp : p ≤ E * U) (hY : Y ≤ E * T) (hUR : U ≤ R) (hTR : T ≤ R) :
    Real.sqrt p * Y ^ ((3 : ℝ) / 2) ≤ E ^ 2 * (R * T) := by
  rw [rpow_three_halves hY0]
  have h1 : Real.sqrt p * Real.sqrt Y ≤ E * R := by
    rw [← Real.sqrt_mul hp0, Real.sqrt_le_left (by positivity)]
    calc p * Y ≤ (E * U) * (E * T) := mul_le_mul hp hY hY0 (by positivity)
      _ ≤ (E * R) * (E * R) := mul_le_mul (mul_le_mul_of_nonneg_left hUR hE)
          (mul_le_mul_of_nonneg_left hTR hE) (by positivity) (by positivity)
      _ = (E * R) ^ 2 := by ring
  calc Real.sqrt p * (Y * Real.sqrt Y) = (Real.sqrt p * Real.sqrt Y) * Y := by ring
    _ ≤ (E * R) * (E * T) := mul_le_mul h1 hY hY0 (by positivity)
    _ = E ^ 2 * (R * T) := by ring

/-- **The native tie**: `(M_∞ y)² ≲ Q` up to the subpower, the field `leadN`. -/
theorem leadN_jointLN {KN CS cS : ℝ} (hKN : 0 ≤ KN) (hCS : 0 ≤ CS) (hcS : 0 ≤ cS) :
    LeadBelow (1 / 2) (jointLN KN CS cS) := by
  intro K c hK hc
  refine ⟨KN * (CS * K + K ^ 2 + 1), 1 + cS + 2 * c, 0, fun X R hdom caps hcaps ↦ ?_⟩
  obtain ⟨⟨-, hP⟩, ⟨-, hY⟩, -⟩ := hcaps
  have hR := hdom.R_pos
  have hU0 : 0 < jointU X := by linarith [hdom.one_lt_U]
  have hT0 := hdom.T_pos
  have hE1 := one_le_Ex_mul hK hc hdom
  set E := K * Ex c R with hE
  have hE0 : 0 ≤ E := by linarith
  have hEx (a : ℝ) : 0 < Ex a R := Ex_pos _ _
  have hp : cp caps.PF ≤ E * jointU X := cp_le (by positivity) hP
  have hy : cp caps.yF ≤ E * jointT X R := cp_le (by positivity) hY
  have hp0 := cp_nonneg caps.PF
  have hy0 := cp_nonneg caps.yF
  have hQ0 : 0 ≤ jointQ X R ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hdom.Q_pos.le _
  have hTerm0 : 0 ≤ Real.sqrt (cp caps.PF) * cp caps.yF ^ ((3 : ℝ) / 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hy0 _)
  constructor
  · unfold jointLN
    have := hEx 1
    have := hEx cS
    positivity
  have hpure := purefast_le hp0 hy0 hE0 hU0.le hT0.le hR.le hp hy hdom.U_le_self hdom.T_le_self
  have hlow : CS * Ex cS R * R * cp caps.yF ≤ CS * Ex cS R * E * (R * jointT X R) := by
    have h0 : 0 ≤ CS * Ex cS R * R := by have := hEx cS; positivity
    calc CS * Ex cS R * R * cp caps.yF ≤ CS * Ex cS R * R * (E * jointT X R) :=
          mul_le_mul_of_nonneg_left hy h0
      _ = _ := by ring
  set e := Ex (cS + 2 * c) R with he
  have he1 : 1 ≤ e := hdom.one_le_Ex (by positivity)
  have hE' : CS * Ex cS R * E ≤ CS * K * e := by
    have e1 : CS * Ex cS R * E = CS * K * Ex (cS + c) R := by
      rw [hE, Ex_add]
      ring
    rw [e1]
    exact mul_le_mul_of_nonneg_left (hdom.Ex_le_Ex (by linarith)) (by positivity)
  have hE2 : E ^ 2 ≤ K ^ 2 * e := by
    have e1 : E ^ 2 = K ^ 2 * Ex (2 * c) R := by
      rw [hE, two_mul, Ex_add]
      ring
    rw [e1]
    exact mul_le_mul_of_nonneg_left (hdom.Ex_le_Ex (by linarith)) (by positivity)
  have hbr : CS * Ex cS R * R * cp caps.yF + Real.sqrt (cp caps.PF) * cp caps.yF ^ ((3 : ℝ) / 2) +
      jointQ X R ^ ((1 : ℝ) / 2) ≤
      (CS * K + K ^ 2 + 1) * e * jointQ X R ^ ((1 : ℝ) / 2) := by
    rw [← hdom.mul_T_eq] at hQ0 ⊢
    have h1 := mul_le_mul_of_nonneg_right hE' hQ0
    have h2 := mul_le_mul_of_nonneg_right hE2 hQ0
    have h3 := mul_le_mul_of_nonneg_right he1 hQ0
    nlinarith only [h1, h2, h3, hlow, hpure]
  have e2 : Ex (1 + cS + 2 * c) R = Ex 1 R * e := by
    rw [he, add_assoc, Ex_add]
  unfold jointLN
  rw [e2]
  calc KN * Ex 1 R * _ ≤ KN * Ex 1 R * ((CS * K + K ^ 2 + 1) * e * jointQ X R ^ ((1 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hbr (mul_nonneg hKN (hEx 1).le)
    _ = _ := by ring

/-- **The proper tie**: `U^{3/4} R³ ≤ Q`, the field `leadP`. -/
theorem leadP_jointLP {KP : ℝ} (hKP : 0 ≤ KP) : LeadBelow (1 / 3) (jointLP KP) := by
  intro K c hK hc
  refine ⟨3 * KP * K, 1 + c, 0, fun X R hdom caps hcaps ↦ ?_⟩
  obtain ⟨-, ⟨-, hY⟩, -, -, hB, -⟩ := hcaps
  have hR := hdom.R_pos
  have hU0 : 0 < jointU X := by linarith [hdom.one_lt_U]
  have hT0 := hdom.T_pos
  have hE1 := one_le_Ex_mul hK hc hdom
  have hEx (a : ℝ) : 0 < Ex a R := Ex_pos _ _
  set E := K * Ex c R with hE
  have hE0 : 0 ≤ E := by linarith
  have e2 : R ^ slowExpHA.eB = R ^ 2 := by
    simp only [slowExpHA]
    exact_mod_cast Real.rpow_natCast R 2
  have hb : cp caps.BS ≤ E * R ^ 2 := cp_le (by positivity) (by rwa [e2] at hB)
  have hy : cp caps.yF ≤ E * jointT X R := cp_le (by positivity) hY
  have hb0 := cp_nonneg caps.BS
  have hy0 := cp_nonneg caps.yF
  have hQ0 : 0 ≤ jointQ X R ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hdom.Q_pos.le _
  have hU4 : 0 ≤ jointU X ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hU0.le _
  constructor
  · unfold jointLP
    have := hEx 1
    positivity
  have hroot : Real.sqrt (cp caps.BS) ≤ E * R := by
    rw [Real.sqrt_le_left (by positivity)]
    calc cp caps.BS ≤ E * R ^ 2 := hb
      _ ≤ E ^ 2 * R ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        nlinarith
      _ = (E * R) ^ 2 := by ring
  have h1 : jointU X ^ ((1 : ℝ) / 4) * Real.sqrt (cp caps.BS) ≤
      E * jointQ X R ^ ((1 : ℝ) / 3) := by
    calc jointU X ^ ((1 : ℝ) / 4) * Real.sqrt (cp caps.BS)
        ≤ jointU X ^ ((1 : ℝ) / 4) * (E * R) := mul_le_mul_of_nonneg_left hroot hU4
      _ = E * (jointU X ^ ((1 : ℝ) / 4) * R) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdom.quartic_tie hE0
  have h2 : cp caps.yF ≤ E * jointQ X R ^ ((1 : ℝ) / 3) :=
    hy.trans (mul_le_mul_of_nonneg_left hdom.T_le_Q hE0)
  have h3 : jointQ X R ^ ((1 : ℝ) / 3) ≤ E * jointQ X R ^ ((1 : ℝ) / 3) :=
    le_mul_of_one_le_left hQ0 hE1
  have e3 : Ex (1 + c) R = Ex 1 R * Ex c R := Ex_add _ _ _
  unfold jointLP
  rw [e3]
  calc KP * Ex 1 R * _ ≤ KP * Ex 1 R * (3 * (E * jointQ X R ^ ((1 : ℝ) / 3))) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hKP (hEx 1).le)
    _ = _ := by rw [hE]; ring

/-! ### The prospective exponent of the quartics -/

/-- **`q^{−1+ε} ≤ e⁵ (1/q + R⁻⁵)`** at `ε ≤ 1/(8 + log R)`, for every `q ≥ 1` (TeX Lemma
quant-quartic: "on a trial `q_* ≤ R⁵`, `q_*^ε ≤ e⁵`; for all larger `q` the fixed exponent still
gives decreasing magnitude").  So the moving exponent of `Q₄,₁` costs a constant and leaves no
`R`-dependent exponent in `q₁`: with `LP P ≤ 1` the debit `q^{−1+ε} P(q) Z` is at most
`e⁵ (1/q + R⁻⁵) Z/LP`, a plain threshold `Z/LP`. -/
theorem rpow_eps_le {R q ε : ℝ} (hR : 1 ≤ R) (hq : 1 ≤ q) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hε : ε * (8 + Real.log R) ≤ 1) :
    q ^ (-1 + ε) ≤ Real.exp 5 * (1 / q + 1 / R ^ 5) := by
  have hR0 : 0 < R := by linarith
  have hq0 : 0 < q := by linarith
  have hlog : 0 ≤ Real.log R := Real.log_nonneg hR
  have hR5 : 0 < R ^ 5 := by positivity
  have hRe : (R ^ 5) ^ ε ≤ Real.exp 5 := by
    rw [Real.rpow_def_of_pos hR5, Real.log_pow]
    refine Real.exp_le_exp.2 ?_
    push_cast
    nlinarith
  have he := Real.exp_pos 5
  have hi : 0 ≤ 1 / q := by positivity
  have hi' : 0 ≤ 1 / R ^ 5 := by positivity
  rcases le_total q (R ^ 5) with h | h
  · calc q ^ (-1 + ε) = q ^ ε * (1 / q) := by
          rw [Real.rpow_add hq0, Real.rpow_neg_one, one_div]
          ring
      _ ≤ (R ^ 5) ^ ε * (1 / q) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hq0.le h hε0) hi
      _ ≤ Real.exp 5 * (1 / q) := mul_le_mul_of_nonneg_right hRe hi
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) he.le
  · calc q ^ (-1 + ε) ≤ (R ^ 5) ^ (-1 + ε) :=
          Real.rpow_le_rpow_of_nonpos hR5 h (by linarith)
      _ = (R ^ 5) ^ ε * (1 / R ^ 5) := by
          rw [Real.rpow_add hR5, Real.rpow_neg_one, one_div]
          ring
      _ ≤ Real.exp 5 * (1 / R ^ 5) := mul_le_mul_of_nonneg_right hRe hi'
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) he.le

/-! ### The shares, as the energies read them -/

section Shares

variable {KN KP CS cS R₀ X R Nq Pq : ℝ} {caps : Caps}

/-- **The native shares of `LN N ≤ 1`**, summand by summand: the low mixed, the purefast and the
floor. -/
theorem native_shares (hKN : 0 ≤ KN) (hCS : 0 ≤ CS) (hdom : JDom R₀ X R) (hNq : 0 ≤ Nq)
    (h : jointLN KN CS cS X R caps * Nq ≤ 1) :
    KN * Ex 1 R * (CS * Ex cS R * R * cp caps.yF) * Nq ≤ 1 ∧
      KN * Ex 1 R * (Real.sqrt (cp caps.PF) * cp caps.yF ^ ((3 : ℝ) / 2)) * Nq ≤ 1 ∧
      KN * Ex 1 R * jointQ X R ^ ((1 : ℝ) / 2) * Nq ≤ 1 := by
  have hE := Ex_pos 1 R
  have ha : 0 ≤ KN * Ex 1 R := by positivity
  have h1 : 0 ≤ CS * Ex cS R * R * cp caps.yF := by
    have := Ex_pos cS R
    have := hdom.R_pos
    have := cp_nonneg caps.yF
    positivity
  have h2 : 0 ≤ Real.sqrt (cp caps.PF) * cp caps.yF ^ ((3 : ℝ) / 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (cp_nonneg _) _)
  have h3 : 0 ≤ jointQ X R ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hdom.Q_pos.le _
  have key : ∀ {a b : ℝ}, 0 ≤ b → a + b = CS * Ex cS R * R * cp caps.yF +
      Real.sqrt (cp caps.PF) * cp caps.yF ^ ((3 : ℝ) / 2) + jointQ X R ^ ((1 : ℝ) / 2) →
      KN * Ex 1 R * a * Nq ≤ 1 := fun {a b} hb hab ↦ by
    refine le_trans ?_ h
    unfold jointLN
    rw [← hab]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) ha) hNq
  exact ⟨key (add_nonneg h2 h3) (by ring), key (add_nonneg h1 h3) (by ring),
    key (add_nonneg h1 h2) (by ring)⟩

/-- **The proper shares of `LP P ≤ 1`**, summand by summand: the quartic, the static and heat
coefficient `y`, and the floor. -/
theorem proper_shares (hKP : 0 ≤ KP) (hdom : JDom R₀ X R) (hPq : 0 ≤ Pq)
    (h : jointLP KP X R caps * Pq ≤ 1) :
    KP * Ex 1 R * (jointU X ^ ((1 : ℝ) / 4) * Real.sqrt (cp caps.BS)) * Pq ≤ 1 ∧
      KP * Ex 1 R * cp caps.yF * Pq ≤ 1 ∧ KP * Ex 1 R * jointQ X R ^ ((1 : ℝ) / 3) * Pq ≤ 1 := by
  have hE := Ex_pos 1 R
  have ha : 0 ≤ KP * Ex 1 R := by positivity
  have hU0 : 0 ≤ jointU X := by linarith [hdom.one_lt_U]
  have h1 : 0 ≤ jointU X ^ ((1 : ℝ) / 4) * Real.sqrt (cp caps.BS) :=
    mul_nonneg (Real.rpow_nonneg hU0 _) (Real.sqrt_nonneg _)
  have h2 := cp_nonneg caps.yF
  have h3 : 0 ≤ jointQ X R ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hdom.Q_pos.le _
  have key : ∀ {a b : ℝ}, 0 ≤ b → a + b = jointU X ^ ((1 : ℝ) / 4) * Real.sqrt (cp caps.BS) +
      cp caps.yF + jointQ X R ^ ((1 : ℝ) / 3) → KP * Ex 1 R * a * Pq ≤ 1 := fun {a b} hb hab ↦ by
    refine le_trans ?_ h
    unfold jointLP
    rw [← hab]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) ha) hPq
  exact ⟨key (add_nonneg h2 h3) (by ring), key (add_nonneg h1 h3) (by ring),
    key (add_nonneg h1 h2) (by ring)⟩

end Shares

end OVNS.Quant

end
