import OddViscousNS.Quant.Energy.NearJ.Direct

/-!
# J1: the near profiles with explicit subpower

**`jointProfiles : JointProfiles nearN nearP`**: for `q ≥ e⁵`,
`nearN q ≤ 48384 q^{−1/2} Ex(c, q)` and `nearP q ≤ 48384 q^{−1/3} Ex(c, q)`, with
`c = cMom/2 = 3 cTau + 4`, `cTau = 2 log 2 + 16/log²2`.

**`nearProfiles_of_joint`**: `JointProfiles nearN nearP` implies `NearProfiles nearN nearP`, the
statement left `sorry` in `Near/Profiles.lean` (`nearProfiles`).  Nothing here imports that file, so
it may import this one: `theorem nearProfiles := nearProfiles_of_joint jointProfiles`.

Assembly, at `q = v¹²`: the small outputs `K ≤ v²` by `momN_low`, the high outputs `K ≥ v²` by
`momN_high`, `momP_high`, whose logarithm is paid by `Ex`; then the supremum and the square roots.
The far term `2⁷ q^{−3/4}` of `nearP` is below `q^{−1/3}`.
-/

noncomputable section

namespace OVNS.Quant.NearJ

/-- The exponent of the subpower of the squared moments. -/
def cMom : ℝ := 6 * cTau + 8

theorem cMom_nonneg : 0 ≤ cMom := by
  have := cTau_nonneg
  unfold cMom
  positivity

/-- **All outputs**: at `q = v¹²`, `log q ≥ 5`, `momN q k ≤ 253728 Ex(cMom, q)/q` and
`momP q k ≤ 253728 Ex(cMom, q) q^{−2/3}`. -/
theorem mom_le_joint {v : ℝ} (hv : 1 ≤ v) (hq : 5 ≤ Real.log (v ^ 12)) (k : Mode) :
    momN (v ^ 12) k ≤ 253728 * Ex cMom (v ^ 12) / v ^ 12 ∧
      momP (v ^ 12) k ≤ 253728 * Ex cMom (v ^ 12) / v ^ 8 := by
  have hv0 : 0 < v := by linarith
  set q := v ^ 12 with hqdef
  have hq0 : 0 < q := by positivity
  set E := Ex cMom q with hE
  have hE0 : 0 < E := Ex_pos _ _
  by_cases hk : k 2 = 0
  · have h0 := momN_eq_zero_of_slow (q := q) hk
    constructor
    · rw [h0]
      positivity
    · rw [momP, h0, mul_zero]
      positivity
  rcases le_total (absk k) (v ^ 2) with hK | hK
  · -- the small outputs
    have hK0 := absk_nonneg k
    have hK6 : absk k ^ 6 ≤ q := by
      calc absk k ^ 6 ≤ (v ^ 2) ^ 6 := pow_le_pow_left₀ hK0 hK 6
        _ = q := by
          rw [hqdef]
          ring
    have h1 : momN q k ≤ 52920 * E / q := momN_low hq hq0 hk hK6
    have h2 : momN q k ≤ 253728 * E / q := h1.trans (by gcongr; norm_num)
    refine ⟨h2, ?_⟩
    have hKsq : absk k ^ 2 ≤ v ^ 4 := by
      calc absk k ^ 2 ≤ (v ^ 2) ^ 2 := pow_le_pow_left₀ hK0 hK 2
        _ = v ^ 4 := by ring
    unfold momP
    calc absk k ^ 2 * momN q k ≤ v ^ 4 * (253728 * E / q) :=
          mul_le_mul hKsq h2 (momN_nonneg _ _) (by positivity)
      _ = 253728 * E / v ^ 8 := by
          rw [hqdef]
          field_simp
  · -- the high outputs
    have hL5 : 5 ≤ Real.log q := hq
    have hLv : Real.log q = 12 * Real.log v := by
      rw [hqdef, Real.log_pow]
      norm_num
    have hlL : 0 ≤ Real.log (Real.log q) := Real.log_nonneg (by linarith)
    have hX : 1 + Real.log v ≤ E := by
      calc 1 + Real.log v ≤ Real.log q ^ 2 := by nlinarith
        _ ≤ Ex 8 q := sq_log_le_Ex (by linarith)
        _ ≤ E := Ex_le_Ex (by have := cTau_nonneg; unfold cMom; linarith) (by linarith) hlL
    constructor
    · exact (momN_high hv hk hK).trans (by gcongr)
    · exact (momP_high hv hk hK).trans (by gcongr)

/-- `(v¹²)^a = v^{−n}` for `12 a = −n`. -/
theorem rpow_twelve {v : ℝ} (hv : 0 < v) {a : ℝ} {n : ℕ} (h : 12 * a = -(n : ℝ)) :
    (v ^ 12) ^ a = (v ^ n)⁻¹ := by
  rw [← Real.rpow_natCast v 12, ← Real.rpow_mul hv.le]
  push_cast
  rw [h, Real.rpow_neg hv.le, Real.rpow_natCast]

/-- `N(q) ≤ 48384 v⁻⁶ Ex(cMom/2, q)` at `q = v¹²`. -/
theorem nearN_le_joint {v : ℝ} (hv : 1 ≤ v) (hq : 5 ≤ Real.log (v ^ 12)) :
    nearN (v ^ 12) ≤ 48384 * (v ^ 6)⁻¹ * Ex (cMom / 2) (v ^ 12) := by
  have hv0 : 0 < v := by linarith
  set q := v ^ 12 with hqdef
  set E := Ex (cMom / 2) q with hE
  have hE0 : 0 < E := Ex_pos _ _
  have hE2 : Ex cMom q = E ^ 2 := by
    rw [hE, Ex_pow]
    congr 1
    push_cast
    ring
  have hM : MomN q ≤ 253728 * E ^ 2 / v ^ 12 := by
    rw [← hE2]
    exact MomN_le fun k => (mom_le_joint hv hq k).1
  have hs : Real.sqrt (MomN q) ≤ 504 * (v ^ 6)⁻¹ * E := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, hM.trans ?_⟩
    have e : (504 * (v ^ 6)⁻¹ * E) ^ 2 = 254016 * E ^ 2 / v ^ 12 := by
      field_simp
      ring
    rw [e]
    gcongr
    norm_num
  unfold nearN
  linarith

/-- `P(q) ≤ 9200 v⁻⁴ Ex(cMom/2, q)` at `q = v¹²`; the far term is `2⁷ v⁻⁹`. -/
theorem nearP_le_joint {v : ℝ} (hv : 1 ≤ v) (hq : 5 ≤ Real.log (v ^ 12)) :
    nearP (v ^ 12) ≤ 9200 * (v ^ 4)⁻¹ * Ex (cMom / 2) (v ^ 12) := by
  have hv0 : 0 < v := by linarith
  set q := v ^ 12 with hqdef
  set E := Ex (cMom / 2) q with hE
  have hE0 : 0 < E := Ex_pos _ _
  have hL5 : 5 ≤ Real.log q := hq
  have hE1 : 1 ≤ E :=
    one_le_Ex (by have := cMom_nonneg; positivity) (by linarith) (Real.log_nonneg (by linarith))
  have hE2 : Ex cMom q = E ^ 2 := by
    rw [hE, Ex_pow]
    congr 1
    push_cast
    ring
  have hM : MomP q ≤ 253728 * E ^ 2 / v ^ 8 := by
    rw [← hE2]
    exact MomP_le fun k => (mom_le_joint hv hq k).2
  have hs : Real.sqrt (MomP q) ≤ 504 * (v ^ 4)⁻¹ * E := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, hM.trans ?_⟩
    have e : (504 * (v ^ 4)⁻¹ * E) ^ 2 = 254016 * E ^ 2 / v ^ 8 := by
      field_simp
      ring
    rw [e]
    gcongr
    norm_num
  have hfar : q ^ (-(3 : ℝ) / 4) = (v ^ 9)⁻¹ := rpow_twelve hv0 (by norm_num)
  have hv94 : (v ^ 9)⁻¹ ≤ (v ^ 4)⁻¹ := by
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_right₀ hv (by norm_num)
  have hfar2 : (v ^ 9)⁻¹ ≤ (v ^ 4)⁻¹ * E := by
    have h4 : 0 ≤ (v ^ 4)⁻¹ := by positivity
    nlinarith
  unfold nearP
  rw [hfar]
  have e2 : (2 : ℝ) ^ 7 = 128 := by norm_num
  rw [e2]
  have h4 : 0 ≤ (v ^ 4)⁻¹ * E := by positivity
  nlinarith

end OVNS.Quant.NearJ

namespace OVNS.Quant

open NearJ

/-- **J1, the joint near profiles** (TeX eq. quant-profiles): for `q ≥ e⁵`,
`N(q) ≤ 48384 q^{−1/2} Ex(c, q)`, `P(q) ≤ 48384 q^{−1/3} Ex(c, q)`, `c = 3 cTau + 4`. -/
theorem jointProfiles : JointProfiles nearN nearP := by
  refine ⟨cMom / 2, 48384, Real.exp 5, by have := cMom_nonneg; positivity, by norm_num,
    fun q hq => ?_⟩
  have hq0 : 0 < q := lt_of_lt_of_le (Real.exp_pos _) hq
  have hq5 : 5 ≤ Real.log q := (Real.le_log_iff_exp_le hq0).2 hq
  have hq1 : 1 ≤ q := (Real.one_le_exp (by norm_num)).trans hq
  obtain ⟨v, hv1, rfl⟩ : ∃ v : ℝ, 1 ≤ v ∧ q = v ^ 12 := by
    refine ⟨q ^ ((1 : ℝ) / 12), Real.one_le_rpow hq1 (by norm_num), ?_⟩
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
    norm_num
  have hv0 : 0 < v := by linarith
  have hE0 : 0 < Ex (cMom / 2) (v ^ 12) := Ex_pos _ _
  rw [rpow_twelve hv0 (n := 6) (by norm_num), rpow_twelve hv0 (n := 4) (by norm_num)]
  refine ⟨nearN_le_joint hv1 hq5, (nearP_le_joint hv1 hq5).trans ?_⟩
  gcongr
  norm_num

/-- From the joint form to the fixed-`δ` form, for profiles bounded on `q ≥ 1`: `Ex(c, q) ≤ q^δ`
once `log log q ≥ c/δ`, and the bounded range is paid by the bound `D`. -/
theorem nearProfiles_of_jointProfiles {N P : ℝ → ℝ} (h : JointProfiles N P) {D : ℝ} (hD : 0 ≤ D)
    (hN : ∀ q : ℝ, 1 ≤ q → N q ≤ D) (hP : ∀ q : ℝ, 1 ≤ q → P q ≤ D) : NearProfiles N P := by
  intro δ hδ
  obtain ⟨c, C, q₀, hc, hC, hJ⟩ := h
  set B := max 1 (c / δ) with hB
  set Q := max (max q₀ 1) (Real.exp (Real.exp B)) with hQ
  have hQ1 : 1 ≤ Q := (le_max_right _ _).trans (le_max_left _ _)
  have hQ0 : 0 < Q := by linarith
  refine ⟨C + D * Q, fun q hq => ?_⟩
  have hq0 : 0 < q := by linarith
  have hC' : C ≤ C + D * Q := by
    have := mul_nonneg hD hQ0.le
    linarith
  rcases le_total Q q with hQq | hqQ
  · -- large `q`
    have h1 : q₀ ≤ q := ((le_max_left _ _).trans (le_max_left _ _)).trans hQq
    have h2 : Real.exp (Real.exp B) ≤ q := (le_max_right _ _).trans hQq
    have hll : B ≤ Real.log (Real.log q) := le_loglog h2
    have hB1 : 1 ≤ B := le_max_left _ _
    have hBc : c / δ ≤ B := le_max_right _ _
    have hq1 : 1 < q := lt_of_lt_of_le (Real.one_lt_exp_iff.2 (Real.exp_pos _)) h2
    have hl0 : 0 < Real.log (Real.log q) := by linarith
    have hcδ : c ≤ δ * Real.log (Real.log q) := by
      have : c / δ ≤ Real.log (Real.log q) := hBc.trans hll
      rw [div_le_iff₀ hδ] at this
      linarith
    have hEx : Ex c q ≤ q ^ δ := Ex_le_rpow hq1 hl0 hcδ
    obtain ⟨h3, h4⟩ := hJ q h1
    constructor
    · calc N q ≤ C * q ^ (-(1 : ℝ) / 2) * Ex c q := h3
        _ ≤ C * q ^ (-(1 : ℝ) / 2) * q ^ δ := by gcongr
        _ = C * q ^ (-1 / 2 + δ) := by
            rw [Real.rpow_add hq0]
            ring_nf
        _ ≤ (C + D * Q) * q ^ (-1 / 2 + δ) := by gcongr
    · calc P q ≤ C * q ^ (-(1 : ℝ) / 3) * Ex c q := h4
        _ ≤ C * q ^ (-(1 : ℝ) / 3) * q ^ δ := by gcongr
        _ = C * q ^ (-1 / 3 + δ) := by
            rw [Real.rpow_add hq0]
            ring_nf
        _ ≤ (C + D * Q) * q ^ (-1 / 3 + δ) := by gcongr
  · -- bounded `q`: `1 ≤ Q q^{−1} ≤ Q q^{a}` for `a ≥ −1`
    have hlow : ∀ a : ℝ, -1 ≤ a → 1 ≤ Q * q ^ a := by
      intro a ha
      have h1 : q ^ (-1 : ℝ) ≤ q ^ a := Real.rpow_le_rpow_of_exponent_le hq ha
      rw [Real.rpow_neg_one] at h1
      have h2 : 1 ≤ Q * q⁻¹ := by
        rw [← div_eq_mul_inv]
        exact (one_le_div hq0).2 hqQ
      calc 1 ≤ Q * q⁻¹ := h2
        _ ≤ Q * q ^ a := by gcongr
    have hbd : ∀ a : ℝ, -1 ≤ a → D ≤ (C + D * Q) * q ^ a := by
      intro a ha
      have h1 := hlow a ha
      have h2 : 0 ≤ q ^ a := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h1 hD, mul_nonneg hC h2]
    exact ⟨(hN q hq).trans (hbd _ (by linarith)), (hP q hq).trans (hbd _ (by linarith))⟩

/-- **`JointProfiles` gives the `−1/3` profile** of `NearProfiles`: the leftover `sorry` of the
near layer, `nearProfiles` in `Near/Profiles.lean`, is `nearProfiles_of_joint jointProfiles`. -/
theorem nearProfiles_of_joint (h : JointProfiles nearN nearP) : NearProfiles nearN nearP := by
  have hs : Real.sqrt 108 ≤ 11 := by
    rw [show (11 : ℝ) = Real.sqrt (11 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  refine nearProfiles_of_jointProfiles h (D := 96 * 11 + 18 * 11 + 2 ^ 7) (by norm_num)
    (fun q _ => ?_) (fun q hq => ?_)
  · have h1 : Real.sqrt (MomN q) ≤ Real.sqrt 108 := Real.sqrt_le_sqrt (MomN_le_const q)
    have h2 : 0 ≤ Real.sqrt (MomN q) := Real.sqrt_nonneg _
    unfold nearN
    norm_num
    linarith
  · have h1 : Real.sqrt (MomP q) ≤ Real.sqrt 108 := Real.sqrt_le_sqrt (MomP_le_const q)
    have hq0 : 0 < q := by linarith
    have h3 : q ^ (-(3 : ℝ) / 4) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq (by norm_num)
    unfold nearP
    norm_num at h3 ⊢
    linarith

end OVNS.Quant

end
