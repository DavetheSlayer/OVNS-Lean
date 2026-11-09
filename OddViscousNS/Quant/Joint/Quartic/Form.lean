import OddViscousNS.Quant.Joint.Quartic.Term1

/-!
# The fourth correction: the positive bounds of the forms (step J5, node N11)

`pos4`: the proper trilinear map with the first array a slow ⋆ fibre product, the whole positive input
of Bodies 34, 35, 46.  Then every form is bounded, with a slow `T`, a fast `W` in the inner slot, fast
`U`, `V` in the outer slots, `q = |r|`, `√𝔐 = √𝔐_P(q)`:

Weight two (Bodies 34, 46), `Q2_sb`: `|Q₄(T, W, U, V)| ≤ 3·2¹⁴ q⁻¹ √𝔐 ‖T‖₂ L_h(W) ‖U‖₂ ‖V‖₂`.  One
estimate pays the static bound and the four insertions of Body 46:
`|Q₄| ≲ κ B L b²`, `|Rem| ≲ κ {B L b ‖N_F‖₂ + B b² L_h(N_F) + L b² ‖N_S‖₂}`, `κ = q⁻¹ √𝔐`.
`J2_sb`: the source, with `‖T‖₃` and no `q⁻¹`.

Weight one (Body 35): `Q1_static_sb`, `Q1_in_sb`, `Q1_q_sb`, `Q1_e_sb`, `J1_sb`.
-/

noncomputable section

namespace OVNS.Quant.Quartic

open OVNS.Quant.Metric

variable {α β B C : Mode → ℝ} {a L b c : ℝ}

/-! ### A. The positive map -/

/-- The labels `(p, q, s)` as a pair of a triad and a slow label. -/
def l4Equiv : L4 ≃ (Mode × Mode) × Mode where
  toFun x := ((x.1, x.2.1), x.2.2)
  invFun z := (z.1.1, z.1.2, z.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The positive map of the quartic.** -/
theorem pos4 (q : ℝ) (hα : L2B α a) (hαs : ∀ s, s 2 ≠ 0 → α s = 0) (hβ : LhB β L)
    (hB : L2B B b) (hC : L2B C c) :
    SB (fun x : L4 => kT q (x.1, x.2.1) * (α x.2.2 * β (inL x) * B x.2.1 * C (outE x)))
      (3 * (Real.sqrt (MomP q) * (a * L * b * c))) := by
  obtain ⟨hS, hA⟩ := LhB.conv hα hαs hβ
  have ht := tri_pos q hA hB hC
  set H : (Mode × Mode) × Mode → ℝ := fun z =>
    kT q z.1 * (α z.2 * β (z.1.1 - z.2) * B z.1.2 * C (-(z.1.1 + z.1.2))) with hH
  have hH0 : ∀ z, 0 ≤ H z := fun z => mul_nonneg (kT_nonneg q _)
    (mul_nonneg (mul_nonneg (mul_nonneg (hα.nn _) (hβ.nn _)) (hB.nn _)) (hC.nn _))
  have hfib : ∀ i : Mode × Mode, SB (fun s => H (i, s))
      (kT q i * (cvS α β i.1 * B i.2 * C (-(i.1 + i.2)))) := fun i => by
    have h1 := (hS i.1).mul_left (kT q i * (B i.2 * C (-(i.1 + i.2))))
    refine ⟨h1.congr fun s => ?_, ?_⟩
    · simp only [hH]
      ring
    · refine le_of_eq ?_
      have e : ∀ s, H (i, s) = kT q i * (B i.2 * C (-(i.1 + i.2))) * (α s * β (i.1 - s)) :=
        fun s => by
        simp only [hH]
        ring
      simp only [e]
      rw [tsum_mul_left]
      simp only [cvS]
      ring
  have hs := SB.prod hH0 hfib ht
  exact SB.equiv' l4Equiv hs fun x => rfl

/-! ### B. The slots -/

/-- A slow first slot and fast other slots. -/
structure Slots (T W U V : Field) : Prop where
  T : PiS T = T
  W : PiF W = W
  U : PiF U = U
  V : PiF V = V

variable {T W U V : Field} {j : ℕ} {r τ : ℝ} {x : L4}

lemma termQ_zero₁ (w u v : V3) : termQ j r x τ 0 w u v = 0 := by simp [termQ, coreQ_zero₁]

lemma termQ_zero₂ (t u v : V3) : termQ j r x τ t 0 u v = 0 := by simp [termQ, coreQ_zero₂]

lemma termQ_zero₃ (t w v : V3) : termQ j r x τ t w 0 v = 0 := by simp [termQ, coreQ_zero₃]

lemma termQ_zero₄ (t w u : V3) : termQ j r x τ t w u 0 = 0 := by simp [termQ, coreQ_zero₄]

lemma srcQ_zero₁ (w u v : V3) : srcQ j r x τ 0 w u v = 0 := by simp [srcQ, coreQ_zero₁]

lemma srcQ_zero₂ (t u v : V3) : srcQ j r x τ t 0 u v = 0 := by simp [srcQ, coreQ_zero₂]

lemma srcQ_zero₃ (t w v : V3) : srcQ j r x τ t w 0 v = 0 := by simp [srcQ, coreQ_zero₃]

lemma srcQ_zero₄ (t w u : V3) : srcQ j r x τ t w u 0 = 0 := by simp [srcQ, coreQ_zero₄]

/-- A label which is not active carries a zero amplitude. -/
lemma Slots.zero (hS : Slots T W U V) (hx : ¬ Act x) :
    T x.2.2 = 0 ∨ W (inL x) = 0 ∨ U x.2.1 = 0 ∨ V (outE x) = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨h1, h2, h3, h4⟩ := hne
  refine hx ⟨?_, ?_, ?_, ?_⟩
  · by_contra h
    exact h1 (slow_zero hS.T h)
  · intro h
    exact h2 (fast_zero hS.W h)
  · intro h
    exact h3 (fast_zero hS.U h)
  · intro h
    exact h4 (fast_zero hS.V h)

/-- A term vanishes off the active labels. -/
lemma Slots.term_zero (hS : Slots T W U V) (hx : ¬ Act x) :
    termQ j r x τ (T x.2.2) (W (inL x)) (U x.2.1) (V (outE x)) = 0 := by
  rcases hS.zero hx with h | h | h | h <;> rw [h]
  · exact termQ_zero₁ _ _ _
  · exact termQ_zero₂ _ _ _
  · exact termQ_zero₃ _ _ _
  · exact termQ_zero₄ _ _ _

/-- A source term vanishes off the active labels. -/
lemma Slots.src_zero (hS : Slots T W U V) (hx : ¬ Act x) :
    srcQ j r x τ (T x.2.2) (W (inL x)) (U x.2.1) (V (outE x)) = 0 := by
  rcases hS.zero hx with h | h | h | h <;> rw [h]
  · exact srcQ_zero₁ _ _ _
  · exact srcQ_zero₂ _ _ _
  · exact srcQ_zero₃ _ _ _
  · exact srcQ_zero₄ _ _ _

lemma up_nrm (U : Field) (k : Mode) : up (nrm U) k = absk k ^ 2 * ‖U k‖ := by
  simp only [up, nrm, absk_sq]

lemma up_gr (U : Field) (k : Mode) : up (gr U) k = absk k ^ 3 * ‖U k‖ := by
  simp only [up, gr, ← absk_sq]
  ring

/-- `|s|^{3/2} ‖T_s‖` is `ℓ²` with norm `‖T‖_{3/2}`. -/
lemma l2B_h32 (hT : InH (3 / 2) T) :
    L2B (fun s => absk s * Real.sqrt (absk s) * ‖T s‖) (hnorm (3 / 2) T) := by
  have e : ∀ k, (absk k * Real.sqrt (absk k) * ‖T k‖) ^ 2 = sobWeight (3 / 2) k * ‖T k‖ ^ 2 := by
    intro k
    by_cases hk : k = 0
    · subst hk
      simp [sobWeight, show absk 0 = 0 from absk_eq_zero.2 rfl]
    · have h0 := absk_nonneg k
      have e1 : (2 * (3 / 2) : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
      rw [mul_pow, mul_pow, Real.sq_sqrt h0]
      simp only [sobWeight, hk, ite_false, e1, Real.rpow_natCast]
      ring
  refine ⟨fun k => by have := absk_nonneg k; positivity, hT.congr fun k => (e k).symm, ?_⟩
  simp only [e]
  rfl

/-! ### C. Weight two -/

/-- **The quartic at weight two**: the single positive estimate of Bodies 34, 46. -/
theorem Q2_sb (hr : r ≠ 0) (hS : Slots T W U V) (hT : InH 2 T) (hW : LhB (nrm W) L) (hU : InH 2 U)
    (hV : InH 2 V) (τ : ℝ) :
    SB (fun x : L4 => ‖termQ 2 r x τ (T x.2.2) (W (inL x)) (U x.2.1) (V (outE x))‖)
      (2 ^ 14 / |r| * (3 * (Real.sqrt (MomP |r|) *
        (hnorm 2 T * L * hnorm 2 U * hnorm 2 V)))) := by
  have hq : 0 < |r| := abs_pos.2 hr
  have hP := pos4 |r| (l2B_up hT) (fun s hs => by simp [up, nrm, slow_zero hS.T hs]) hW
    (l2B_up hU) (l2B_up hV)
  refine (hP.const_mul (by positivity : 0 ≤ 2 ^ 14 / |r|)).of_le (fun x => norm_nonneg _) fun x => ?_
  by_cases hx : Act x
  · refine (termQ_two_le hr hx τ _ _ _ _).trans (le_of_eq ?_)
    simp only [up_nrm, nrm, absk_outE]
    ring
  · rw [hS.term_zero hx, norm_zero]
    exact mul_nonneg (by positivity) (mul_nonneg (kT_nonneg _ _) (mul_nonneg (mul_nonneg
      (mul_nonneg ((l2B_up hT).nn _) (hW.nn _)) ((l2B_up hU).nn _)) ((l2B_up hV).nn _)))

/-- `|Q₄(T, W, U, V)|`. -/
theorem norm_Q4F_two_le (hr : r ≠ 0) (hS : Slots T W U V) (hT : InH 2 T) (hW : LhB (nrm W) L)
    (hU : InH 2 U) (hV : InH 2 V) (τ : ℝ) :
    ‖Q4F 2 r τ T W U V‖ ≤ 2 ^ 14 / |r| * (3 * (Real.sqrt (MomP |r|) *
        (hnorm 2 T * L * hnorm 2 U * hnorm 2 V))) := by
  have h := Q2_sb hr hS hT hW hU hV τ
  exact (norm_tsum_le_tsum_norm h.1).trans h.2

/-- **The source at weight two**, on `T ∈ H³`. -/
theorem J2_sb (r : ℝ) (hS : Slots T W U V) (hT : MZ 3 T) (hW : LhB (nrm W) L) (hU : InH 2 U)
    (hV : InH 2 V) (τ : ℝ) :
    SB (fun x : L4 => ‖srcQ 2 r x τ (T x.2.2) (W (inL x)) (U x.2.1) (V (outE x))‖)
      (2 ^ 14 * (3 * (Real.sqrt (MomP |r|) * (hnorm 3 T * L * hnorm 2 U * hnorm 2 V)))) := by
  have hP := pos4 |r| (l2B_up_gr hT) (fun s hs => by simp [up, gr, slow_zero hS.T hs]) hW
    (l2B_up hU) (l2B_up hV)
  refine (hP.const_mul (by positivity : (0 : ℝ) ≤ 2 ^ 14)).of_le (fun x => norm_nonneg _) fun x => ?_
  by_cases hx : Act x
  · refine (srcQ_two_le hx r τ _ _ _ _).trans (le_of_eq ?_)
    simp only [up_nrm, up_gr, nrm, absk_outE]
    ring
  · rw [hS.src_zero hx, norm_zero]
    exact mul_nonneg (by positivity) (mul_nonneg (kT_nonneg _ _) (mul_nonneg (mul_nonneg
      (mul_nonneg ((l2B_up_gr hT).nn _) (hW.nn _)) ((l2B_up hU).nn _)) ((l2B_up hV).nn _)))

/-! ### D. Weight one -/

/-- **`Q₄,₁`, the static bound** (Body 35). -/
theorem Q1_static_sb (hr : r ≠ 0) (hS : Slots T W U V) (hT : InH (3 / 2) T) (hW : LhB (nrm W) L)
    (hU : InH 1 U) (hV : InH 1 V) (τ : ℝ) :
    SB (fun x : L4 => ‖termQ 1 r x τ (T x.2.2) (W (inL x)) (U x.2.1) (V (outE x))‖)
      (2 ^ 12 / Real.sqrt |r| * (3 * (Real.sqrt (MomP |r|) *
        (hnorm (3 / 2) T * L * hnorm 1 U * hnorm 1 V)))) := by
  have hq : 0 < |r| := abs_pos.2 hr
  have hsq : 0 < Real.sqrt |r| := Real.sqrt_pos.2 hq
  have hP := pos4 |r| (l2B_h32 hT) (fun s hs => by simp [slow_zero hS.T hs]) hW
    (l2B_gr hU) (l2B_gr hV)
  refine (hP.const_mul (by positivity : 0 ≤ 2 ^ 12 / Real.sqrt |r|)).of_le
    (fun x => norm_nonneg _) fun x => ?_
  by_cases hx : Act x
  · have h := termQ_one_static hr hx τ (T x.2.2) (W (inL x)) (U x.2.1) (V (outE x))
    refine ((le_div_iff₀' hsq).2 h).trans_eq ?_
    simp only [gr, nrm, absk_outE]
    ring
  · rw [hS.term_zero hx, norm_zero]
    exact mul_nonneg (by positivity) (mul_nonneg (kT_nonneg _ _) (mul_nonneg (mul_nonneg
      (mul_nonneg ((l2B_h32 hT).nn _) (hW.nn _)) ((l2B_gr hU).nn _)) ((l2B_gr hV).nn _)))

section Eps

variable {ε : ℝ} {L' : ℝ}

/-- The size of the bound of a pair of placements. -/
private lemma pair_nn {P₁ P₂ : L4 → ℝ} {c : ℝ} (hc : 0 ≤ c) (h1 : ∀ x, 0 ≤ P₁ x)
    (h2 : ∀ x, 0 ≤ P₂ x) (x : L4) : 0 ≤ c * (P₁ x + P₂ x) :=
  mul_nonneg hc (add_nonneg (h1 x) (h2 x))

/-- **`Q₄,₁`, a slow or an inner fast direction** (Body 35): the weighted fibre on the inner slot,
`H²` on an exterior. -/
theorem Q1_in_sb (hr : r ≠ 0) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (hS : Slots T W U V) (hT : InH 1 T)
    (hW : LhB (fun k => (absk k)⁻¹ ^ ε * ‖W k‖) L) (hU : InH 2 U) (hV : InH 2 V) (τ : ℝ) :
    SB (fun x : L4 => ‖termQ 1 r x τ (T x.2.2) (W (inL x)) (U x.2.1) (V (outE x))‖)
      (2 ^ 13 / |r| ^ (1 - ε) * (3 * (Real.sqrt (MomP |r|) * (hnorm 1 T * L * hnorm 2 U * hnorm 1 V)) +
        3 * (Real.sqrt (MomP |r|) * (hnorm 1 T * L * hnorm 1 U * hnorm 2 V)))) := by
  have hq : 0 < |r| := abs_pos.2 hr
  have hqe : 0 < |r| ^ (1 - ε) := Real.rpow_pos_of_pos hq _
  have aT := l2B_gr hT
  have aU := l2B_up hU
  have aU1 := l2B_gr (hU.mono (by norm_num : (1 : ℝ) ≤ 2))
  have aV := l2B_up hV
  have aV1 := l2B_gr (hV.mono (by norm_num : (1 : ℝ) ≤ 2))
  have hsl : ∀ s : Mode, s 2 ≠ 0 → gr T s = 0 := fun s hs => by simp [gr, slow_zero hS.T hs]
  have p1 := pos4 |r| aT hsl hW aU aV1
  have p2 := pos4 |r| aT hsl hW aU1 aV
  refine ((p1.add p2).const_mul (by positivity : 0 ≤ 2 ^ 13 / |r| ^ (1 - ε))).of_le
    (fun x => norm_nonneg _) fun x => ?_
  by_cases hx : Act x
  · have h := termQ_one_in hr h0 h1 hx τ (T x.2.2) (W (inL x)) (U x.2.1) (V (outE x))
    refine ((le_div_iff₀' hqe).2 h).trans_eq ?_
    simp only [gr, up_nrm, absk_outE]
    ring
  · rw [hS.term_zero hx, norm_zero]
    refine pair_nn (by positivity) (fun x => mul_nonneg (kT_nonneg _ _) (mul_nonneg (mul_nonneg
      (mul_nonneg (aT.nn _) (hW.nn _)) (aU.nn _)) (aV1.nn _))) (fun x => mul_nonneg (kT_nonneg _ _)
      (mul_nonneg (mul_nonneg (mul_nonneg (aT.nn _) (hW.nn _)) (aU1.nn _)) (aV.nn _))) x

/-- **`Q₄,₁`, a direction in the outer slot `q`** (Body 35). -/
theorem Q1_q_sb (hr : r ≠ 0) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (hS : Slots T W U V) (hT : InH 2 T)
    (hW : LhB (nrm W) L) (hU : InH 1 U) (hV : InH 2 V) (τ : ℝ) :
    SB (fun x : L4 => ‖termQ 1 r x τ (T x.2.2) (W (inL x)) (U x.2.1) (V (outE x))‖)
      (2 ^ 13 / |r| ^ (1 - ε) * (3 * (Real.sqrt (MomP |r|) * (hnorm 2 T * L * hnorm 1 U * hnorm 1 V)) +
        3 * (Real.sqrt (MomP |r|) * (hnorm 1 T * L * hnorm 1 U * hnorm 2 V)))) := by
  have hq : 0 < |r| := abs_pos.2 hr
  have hqe : 0 < |r| ^ (1 - ε) := Real.rpow_pos_of_pos hq _
  have aT := l2B_up hT
  have aT1 := l2B_gr (hT.mono (by norm_num : (1 : ℝ) ≤ 2))
  have aU := l2B_gr hU
  have aV := l2B_up hV
  have aV1 := l2B_gr (hV.mono (by norm_num : (1 : ℝ) ≤ 2))
  have p1 := pos4 |r| aT (fun s hs => by simp [up, nrm, slow_zero hS.T hs]) hW aU aV1
  have p2 := pos4 |r| aT1 (fun s hs => by simp [gr, slow_zero hS.T hs]) hW aU aV
  refine ((p1.add p2).const_mul (by positivity : 0 ≤ 2 ^ 13 / |r| ^ (1 - ε))).of_le
    (fun x => norm_nonneg _) fun x => ?_
  by_cases hx : Act x
  · have h := termQ_one_q hr h0 h1 hx τ (T x.2.2) (W (inL x)) (U x.2.1) (V (outE x))
    refine ((le_div_iff₀' hqe).2 h).trans_eq ?_
    simp only [gr, up_nrm, nrm, absk_outE]
    ring
  · rw [hS.term_zero hx, norm_zero]
    refine pair_nn (by positivity) (fun x => mul_nonneg (kT_nonneg _ _) (mul_nonneg (mul_nonneg
      (mul_nonneg (aT.nn _) (hW.nn _)) (aU.nn _)) (aV1.nn _))) (fun x => mul_nonneg (kT_nonneg _ _)
      (mul_nonneg (mul_nonneg (mul_nonneg (aT1.nn _) (hW.nn _)) (aU.nn _)) (aV.nn _))) x

/-- **`Q₄,₁`, a direction in the outer slot `e`** (Body 35). -/
theorem Q1_e_sb (hr : r ≠ 0) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (hS : Slots T W U V) (hT : InH 2 T)
    (hW : LhB (nrm W) L) (hU : InH 2 U) (hV : InH 1 V) (τ : ℝ) :
    SB (fun x : L4 => ‖termQ 1 r x τ (T x.2.2) (W (inL x)) (U x.2.1) (V (outE x))‖)
      (2 ^ 13 / |r| ^ (1 - ε) * (3 * (Real.sqrt (MomP |r|) * (hnorm 2 T * L * hnorm 1 U * hnorm 1 V)) +
        3 * (Real.sqrt (MomP |r|) * (hnorm 1 T * L * hnorm 2 U * hnorm 1 V)))) := by
  have hq : 0 < |r| := abs_pos.2 hr
  have hqe : 0 < |r| ^ (1 - ε) := Real.rpow_pos_of_pos hq _
  have aT := l2B_up hT
  have aT1 := l2B_gr (hT.mono (by norm_num : (1 : ℝ) ≤ 2))
  have aU := l2B_up hU
  have aU1 := l2B_gr (hU.mono (by norm_num : (1 : ℝ) ≤ 2))
  have aV := l2B_gr hV
  have p1 := pos4 |r| aT (fun s hs => by simp [up, nrm, slow_zero hS.T hs]) hW aU1 aV
  have p2 := pos4 |r| aT1 (fun s hs => by simp [gr, slow_zero hS.T hs]) hW aU aV
  refine ((p1.add p2).const_mul (by positivity : 0 ≤ 2 ^ 13 / |r| ^ (1 - ε))).of_le
    (fun x => norm_nonneg _) fun x => ?_
  by_cases hx : Act x
  · have h := termQ_one_e hr h0 h1 hx τ (T x.2.2) (W (inL x)) (U x.2.1) (V (outE x))
    refine ((le_div_iff₀' hqe).2 h).trans_eq ?_
    simp only [gr, up_nrm, nrm, absk_outE]
    ring
  · rw [hS.term_zero hx, norm_zero]
    refine pair_nn (by positivity) (fun x => mul_nonneg (kT_nonneg _ _) (mul_nonneg (mul_nonneg
      (mul_nonneg (aT.nn _) (hW.nn _)) (aU1.nn _)) (aV.nn _))) (fun x => mul_nonneg (kT_nonneg _ _)
      (mul_nonneg (mul_nonneg (mul_nonneg (aT1.nn _) (hW.nn _)) (aU.nn _)) (aV.nn _))) x

end Eps

/-- **The source at weight one**: no `H³` is used. -/
theorem J1_sb (r : ℝ) (hS : Slots T W U V) (hT : InH 2 T) (hW : LhB (nrm W) L) (hU : InH 2 U)
    (hV : InH 2 V) (τ : ℝ) :
    SB (fun x : L4 => ‖srcQ 1 r x τ (T x.2.2) (W (inL x)) (U x.2.1) (V (outE x))‖)
      (2 ^ 13 * (3 * (Real.sqrt (MomP |r|) * (hnorm 2 T * L * hnorm 2 U * hnorm 1 V)) +
        3 * (Real.sqrt (MomP |r|) * (hnorm 2 T * L * hnorm 1 U * hnorm 2 V)))) := by
  have aT := l2B_up hT
  have aU := l2B_up hU
  have aU1 := l2B_gr (hU.mono (by norm_num : (1 : ℝ) ≤ 2))
  have aV := l2B_up hV
  have aV1 := l2B_gr (hV.mono (by norm_num : (1 : ℝ) ≤ 2))
  have hsl : ∀ s : Mode, s 2 ≠ 0 → up (nrm T) s = 0 := fun s hs => by
    simp [up, nrm, slow_zero hS.T hs]
  have p1 := pos4 |r| aT hsl hW aU aV1
  have p2 := pos4 |r| aT hsl hW aU1 aV
  refine ((p1.add p2).const_mul (by positivity : (0 : ℝ) ≤ 2 ^ 13)).of_le
    (fun x => norm_nonneg _) fun x => ?_
  by_cases hx : Act x
  · refine (srcQ_one_le hx r τ _ _ _ _).trans_eq ?_
    simp only [gr, up_nrm, nrm, absk_outE]
    ring
  · rw [hS.src_zero hx, norm_zero]
    exact mul_nonneg (by positivity) (add_nonneg (mul_nonneg (kT_nonneg _ _) (mul_nonneg
      (mul_nonneg (mul_nonneg (aT.nn _) (hW.nn _)) (aU.nn _)) (aV1.nn _)))
      (mul_nonneg (kT_nonneg _ _) (mul_nonneg (mul_nonneg (mul_nonneg (aT.nn _) (hW.nn _))
        (aU1.nn _)) (aV.nn _))))

end OVNS.Quant.Quartic

end
