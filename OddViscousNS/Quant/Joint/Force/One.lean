import OddViscousNS.Quant.Joint.Force.Thr

/-!
# The force in the `H¹` energy: `N̄`, `π` (step J5, node N12)

Bodies 15, 45: `E' + n b² ≤ … + N b + q_f`, `N = 18h/16 + P_F k`, `q_f = 64 P_F² h`, `h = ‖H_ψ‖₁`.

Here the force slots of `joint1RHS` are bounded by `N_f b_F + f_f`, at every time of the piece:
* `N_f = 2 hBd`: the direct term and the metric pairs, by the operator norm `κ ≤ 1` of the metric;
* `f_f = 24 c₄ P_F² hBd`: the native differential, `|D₁(F; h)| ≤ 24 c₄ a_F² ‖h‖₁`, "tested".

**`N̄`, `π`.**  `force1_final`: `∫ N_f² ≤ 1`, `∫ f_f ≤ 1` at the threshold `force1Q`, which is
`≲ Q`.  So the force takes the share `1` of `(C_N X)²`, `(C_π X)²`, for `X ≥ 1`, with constants
independent of `φ` and of the cap scale: all the dependence on `φ` is in the threshold, as in the
fixed-force layer (`h1Nbar = h1Pi = 1`).  The TeX's `π ≍ X` is an upper bound that is not needed
for the force: its tested price is `U²R^{5/2}` "even discarding the positive `π` denominators"
(Body 45).

No pointwise bound on `H_ψ` is used: `∫ f_f` is `P_F²` times `‖h‖_{L¹_t}`, time Cauchy on `h_L`, as
in Body 45.  With `‖h‖_{L^∞_t}` instead, `P_F² j_L` would have degree `(2, 3)`, above `Q`.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞} {u : ℝ}

/-- The operator norm of `X₂` at the caps. -/
def X2StC (r D : ℝ) (caps : Caps) : ℝ :=
  Cst / |r| * ((1 + Real.sqrt (1 + Real.log D)) * cp caps.AS ^ 2 +
    2 * (cp caps.AS * cp caps.WS) + cp caps.BS ^ 2 / D) +
    Cst / |r| ^ 2 * D * (cp caps.AS * cp caps.BS)

/-- The operator norm of the metric at the caps. -/
def kapJ (r D M : ℝ) (caps : Caps) : ℝ :=
  2 ^ 8 * cp caps.BS / |r| + 2 * X2StC r D caps + 2 * (CZ / |r| * M * cp caps.BS)

/-- `X₂` at the caps. -/
lemma X2St_le {D : ℝ} (hD : 1 ≤ D) {S : Field} {caps : Caps}
    (hW : wiener S ≤ cp caps.WS) (hA : hnorm 1 S ≤ cp caps.AS) (hB : hnorm 2 S ≤ cp caps.BS) :
    X2St r D S ≤ X2StC r D caps := by
  have hW0 := wiener_nonneg S
  have hA0 := hnorm_nonneg 1 S
  have hB0 := hnorm_nonneg 2 S
  have hD0 : 0 < D := by linarith
  have hC : 0 ≤ Cst := by unfold Cst; positivity
  have hAc := cp_nonneg caps.AS
  have hBc := cp_nonneg caps.BS
  have hWc := cp_nonneg caps.WS
  have hL := Real.sqrt_nonneg (1 + Real.log D)
  unfold X2St X2StC
  gcongr

/-- **The threshold of the metric**: `κ ≤ 1`.  This is the coercivity of the energy at `D = R`,
which N14 pays anyway. -/
def forceK (D M : ℝ) (caps : Caps) : ℝ :=
  2 ^ 10 * cp caps.BS +
    2 ^ 4 * (Cst * ((1 + Real.sqrt (1 + Real.log D)) * cp caps.AS ^ 2 +
      2 * (cp caps.AS * cp caps.WS) + cp caps.BS ^ 2 / D)) +
    rootQ 2 (2 ^ 4 * (Cst * (D * (cp caps.AS * cp caps.BS)))) +
    8 * (CZ * M * cp caps.BS)

/-- **The threshold of the `H¹` force**: the budget of J4, the operator norm, and the four
monomials `h_L`, `h_Q` (source), `P_F² h_L`, `P_F² h_Q` (tested). -/
def force1Q (φ D M : ℝ) (caps : Caps) : ℝ :=
  jointBudget φ caps + forceK D M caps + 2 ^ 3 * hLc φ caps + rootQ 2 (2 ^ 3 * hQc φ) +
    2 ^ 8 * c4 * cp caps.PF ^ 2 * hLc φ caps + rootQ 2 (2 ^ 8 * c4 * cp caps.PF ^ 2 * hQc φ)

lemma CZ_nonneg : 0 ≤ CZ := by
  have := Ce_pos
  unfold CZ
  positivity

lemma Cst_nonneg : 0 ≤ Cst := by unfold Cst; positivity

lemma forceK_nonneg {D M : ℝ} (hD : 0 ≤ D) (hM : 0 ≤ M) (caps : Caps) : 0 ≤ forceK D M caps := by
  have hB := cp_nonneg caps.BS
  have hA := cp_nonneg caps.AS
  have hW := cp_nonneg caps.WS
  have hCs := Cst_nonneg
  have hZ := CZ_nonneg
  have h1 := Real.sqrt_nonneg (1 + Real.log D)
  have h2 := rootQ_nonneg 2 (by positivity :
    0 ≤ 2 ^ 4 * (Cst * (D * (cp caps.AS * cp caps.BS))))
  unfold forceK
  positivity

private lemma four_le {a b c d q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h : a + b + c + d ≤ q) : a ≤ q ∧ b ≤ q ∧ c ≤ q ∧ d ≤ q := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

private lemma six_le {a b c d e f q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (he : 0 ≤ e) (hf : 0 ≤ f) (h : a + b + c + d + e + f ≤ q) :
    a ≤ q ∧ b ≤ q ∧ c ≤ q ∧ d ≤ q ∧ e ≤ q ∧ f ≤ q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- `κ ≤ 1` at the threshold. -/
lemma kapJ_le {D M : ℝ} (hD : 1 ≤ D) (hM : 0 ≤ M) {caps : Caps} (hq0 : 0 < |r|)
    (hk : forceK D M caps ≤ |r|) : kapJ r D M caps ≤ 1 := by
  have hD0 : 0 < D := by linarith
  have hB := cp_nonneg caps.BS
  have hA := cp_nonneg caps.AS
  have hW := cp_nonneg caps.WS
  have hC := Cst_nonneg
  have hL := Real.sqrt_nonneg (1 + Real.log D)
  have hZ := CZ_nonneg
  set S1 := Cst * ((1 + Real.sqrt (1 + Real.log D)) * cp caps.AS ^ 2 +
      2 * (cp caps.AS * cp caps.WS) + cp caps.BS ^ 2 / D) with hS1
  set S2 := Cst * (D * (cp caps.AS * cp caps.BS)) with hS2
  have hS10 : 0 ≤ S1 := by positivity
  have hS20 : 0 ≤ S2 := by positivity
  have hr2 := rootQ_nonneg 2 (by positivity : 0 ≤ 2 ^ 4 * S2)
  have hz : 0 ≤ CZ * M * cp caps.BS := by positivity
  obtain ⟨h1, h2, h3, h4⟩ := four_le (by positivity : 0 ≤ 2 ^ 10 * cp caps.BS)
    (by positivity : 0 ≤ 2 ^ 4 * S1) hr2 (by positivity : 0 ≤ 8 * (CZ * M * cp caps.BS)) hk
  have h5 : 2 ^ 4 * S2 ≤ |r| ^ 2 := by
    have := le_rpow_of_rootQ (by norm_num) (by positivity) h3
    rwa [Real.rpow_two] at this
  have e : kapJ r D M caps = 2 ^ 8 * cp caps.BS / |r| + 2 * (S1 / |r|) + 2 * (S2 / |r| ^ 2) +
      2 * (CZ * M * cp caps.BS / |r|) := by
    simp only [kapJ, X2StC, hS1, hS2]
    ring
  rw [e]
  have t1 : 2 ^ 8 * cp caps.BS / |r| ≤ 1 / 4 := by
    rw [div_le_iff₀ hq0]
    linarith
  have t2 : S1 / |r| ≤ 1 / 16 := by
    rw [div_le_iff₀ hq0]
    linarith
  have t3 : S2 / |r| ^ 2 ≤ 1 / 16 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have t4 : CZ * M * cp caps.BS / |r| ≤ 1 / 8 := by
    rw [div_le_iff₀ hq0]
    linarith
  linarith

/-- **The force slots at weight one**, on the prefix: `force1 ≤ N_f b_F + f_f`. -/
theorem force1_le_caps (h : ActualSol μ φ r g y Ty) {caps : Caps} {s t D M : ℝ}
    (hP : OnPrefix caps r g y s t) (hs : 0 ≤ s) (ht : ENNReal.ofReal t < Ty)
    (hsup : ∀ u ∈ Icc s t, slowSup r g y u ≤ M) (hD : 1 ≤ D) (hq0 : 0 < |r|)
    (hk : forceK D M caps ≤ |r|) (hu : u ∈ Icc s t) :
    force1 r g y u ≤ 2 * hBd φ r g y u * fastNorm 2 r g y u +
      24 * c4 * cp caps.PF ^ 2 * hBd φ r g y u := by
  have hr : r ≠ 0 := abs_pos.1 hq0
  have hu0 : 0 ≤ u := hs.trans hu.1
  have huT := lt_lifespan hu.2 ht
  have hφ : 0 ≤ φ := (hnorm_nonneg 2 g).trans h.force_le
  obtain ⟨cF1, -, cS1, cS2, cW⟩ := hP.1 u hu
  have hM0 : 0 ≤ M := slowSup_nonneg.trans (hsup u hu)
  have hWc : wiener (Sp r g y u) ≤ cp caps.WS := cW.trans (le_cp _)
  have hAc : hnorm 1 (Sp r g y u) ≤ cp caps.AS := cS1.trans (le_cp _)
  have hBc : hnorm 2 (Sp r g y u) ≤ cp caps.BS := cS2.trans (le_cp _)
  have hPc : fastNorm 1 r g y u ≤ cp caps.PF := cF1.trans (le_cp _)
  have hmain := force1_le h hr hu0 huT hD (hsup u hu)
  obtain ⟨-, hHle⟩ := Hf_one h hr hu0 huT
  have hh0 := hnorm_nonneg 1 (Hf r g y u)
  have hb0 : 0 ≤ fastNorm 2 r g y u := hnorm_nonneg _ _
  have ha0 : 0 ≤ fastNorm 1 r g y u := hnorm_nonneg _ _
  have hK := kapJ_le hD hM0 hq0 hk
  set h1 := hnorm 1 (Hf r g y u) with hh1
  have hle1 : h1 ≤ hBd φ r g y u := hHle
  have hkap : 2 ^ 8 * hnorm 2 (Sp r g y u) / |r| + 2 * X2St r D (Sp r g y u) +
      2 * (CZ / |r| * M * hnorm 2 (Sp r g y u)) ≤ kapJ r D M caps := by
    have hZ := CZ_nonneg
    have a1 : 2 ^ 8 * hnorm 2 (Sp r g y u) / |r| ≤ 2 ^ 8 * cp caps.BS / |r| := by gcongr
    have a2 := X2St_le (r := r) hD hWc hAc hBc
    have a3 : CZ / |r| * M * hnorm 2 (Sp r g y u) ≤ CZ / |r| * M * cp caps.BS :=
      mul_le_mul_of_nonneg_left hBc (by positivity)
    unfold kapJ
    linarith
  have h0k : 0 ≤ 2 ^ 8 * hnorm 2 (Sp r g y u) / |r| + 2 * X2St r D (Sp r g y u) +
      2 * (CZ / |r| * M * hnorm 2 (Sp r g y u)) := by
    have h2 := X2St_nonneg r hD (Sp r g y u)
    have h3 := hnorm_nonneg 2 (Sp r g y u)
    have hZ := CZ_nonneg
    positivity
  have hcoef : 1 + (2 ^ 8 * hnorm 2 (Sp r g y u) / |r| + 2 * X2St r D (Sp r g y u) +
      2 * (CZ / |r| * M * hnorm 2 (Sp r g y u))) ≤ 2 := by linarith
  have hBd0 := hBd_nonneg hφ r g y u
  have t1 : (1 + (2 ^ 8 * hnorm 2 (Sp r g y u) / |r| + 2 * X2St r D (Sp r g y u) +
      2 * (CZ / |r| * M * hnorm 2 (Sp r g y u)))) * (h1 * fastNorm 2 r g y u) ≤
      2 * hBd φ r g y u * fastNorm 2 r g y u := by
    calc _ ≤ 2 * (h1 * fastNorm 2 r g y u) :=
          mul_le_mul_of_nonneg_right hcoef (mul_nonneg hh0 hb0)
      _ = 2 * h1 * fastNorm 2 r g y u := by ring
      _ ≤ _ := by gcongr
  have t2 : 24 * c4 * h1 * fastNorm 1 r g y u ^ 2 ≤ 24 * c4 * cp caps.PF ^ 2 * hBd φ r g y u := by
    have hc := c4_pos
    have h2 : fastNorm 1 r g y u ^ 2 ≤ cp caps.PF ^ 2 := pow_le_pow_left₀ ha0 hPc 2
    calc 24 * c4 * h1 * fastNorm 1 r g y u ^ 2 = 24 * c4 * fastNorm 1 r g y u ^ 2 * h1 := by ring
      _ ≤ _ := by gcongr
  linarith

/-- **The force in the `H¹` energy**: on a piece, at every time, `force1 ≤ N_f b_F + f_f`, with
`N_f = 2 hBd`, `f_f = 24 c₄ P_F² hBd`, `∫ N_f² ≤ 1`, `∫ f_f ≤ 1`. -/
theorem force1_final (h : ActualSol μ φ r g y Ty) {caps : Caps} {s t D M : ℝ}
    (hP : OnPrefix caps r g y s t) (hs : 0 ≤ s) (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty)
    (hlen : t - s ≤ 4) (hsup : ∀ u ∈ Icc s t, slowSup r g y u ≤ M) (hD : 1 ≤ D)
    (hq : force1Q φ D M caps ≤ |r|) :
    (∀ u ∈ Icc s t, force1 r g y u ≤ 2 * hBd φ r g y u * fastNorm 2 r g y u +
      24 * c4 * cp caps.PF ^ 2 * hBd φ r g y u) ∧
    (∀ u ∈ Icc s t, 0 ≤ 24 * c4 * cp caps.PF ^ 2 * hBd φ r g y u) ∧
    IntervalIntegrable (fun u => (2 * hBd φ r g y u) ^ 2) volume s t ∧
    IntervalIntegrable (fun u => 24 * c4 * cp caps.PF ^ 2 * hBd φ r g y u) volume s t ∧
    (∫ u in s..t, (2 * hBd φ r g y u) ^ 2) ≤ 1 ∧
    (∫ u in s..t, 24 * c4 * cp caps.PF ^ 2 * hBd φ r g y u) ≤ 1 := by
  have hφ : 0 ≤ φ := (hnorm_nonneg 2 g).trans h.force_le
  have hM : 0 ≤ M := slowSup_nonneg.trans (hsup s ⟨le_rfl, hst⟩)
  have hD0 : 0 < D := by linarith
  have hc := c4_pos
  have hP2 : 0 ≤ cp caps.PF ^ 2 := sq_nonneg _
  have hL := hLc_nonneg hφ caps
  have hQ := hQc_nonneg φ
  have hk0 : 0 ≤ forceK D M caps := forceK_nonneg hD0.le hM caps
  have hB : 0 ≤ jointBudget φ caps := zero_le_one.trans (jointBudget_floors hφ caps).1
  have r1 := rootQ_nonneg 2 (by positivity : 0 ≤ 2 ^ 3 * hQc φ)
  have r2 := rootQ_nonneg 2 (by positivity : 0 ≤ 2 ^ 8 * c4 * cp caps.PF ^ 2 * hQc φ)
  have t3 : 0 ≤ 2 ^ 3 * hLc φ caps := by positivity
  have t4 : 0 ≤ 2 ^ 8 * c4 * cp caps.PF ^ 2 * hLc φ caps := by positivity
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := six_le hB hk0 t3 r1 t4 r2 hq
  have hq1 : 1 ≤ |r| := (jointBudget_floors hφ caps).1.trans q1
  have hq0 : 0 < |r| := by linarith
  obtain ⟨hI, hV⟩ := hBd_sq_int h hs hst ht hlen hP
  have hb0 : ∀ u, 0 ≤ hBd φ r g y u := hBd_nonneg hφ r g y
  obtain ⟨hI1, hC⟩ := clip_cauchy hst hb0 hI hV
  set x := hLc φ caps / |r| with hx
  set z := hQc φ / |r| ^ 2 with hz
  have hx0 : 0 ≤ x := by positivity
  have hz0 : 0 ≤ z := by positivity
  have hx1 : x ≤ 1 / 8 := by
    rw [hx, div_le_iff₀ hq0]
    linarith
  have hz1 : z ≤ 1 / 8 := by
    have h3 := le_rpow_of_rootQ (by norm_num) (by positivity) q4
    rw [Real.rpow_two] at h3
    rw [hz, div_le_iff₀ (by positivity)]
    linarith
  set Y := 2 ^ 8 * c4 * cp caps.PF ^ 2 with hY
  have hY0 : 0 ≤ Y := by positivity
  have hYx : Y * x ≤ 1 := by
    have e : Y * x = Y * hLc φ caps / |r| := by rw [hx]; ring
    rw [e, div_le_iff₀ hq0]
    linarith
  have hYz : Y * z ≤ 1 := by
    have h3 := le_rpow_of_rootQ (by norm_num) (by positivity) q6
    rw [Real.rpow_two] at h3
    have e : Y * z = Y * hQc φ / |r| ^ 2 := by rw [hz]; ring
    rw [e, div_le_iff₀ (by positivity)]
    linarith
  have hE : ∫ u in s..t, (2 * hBd φ r g y u) ^ 2 = 4 * ∫ u in s..t, hBd φ r g y u ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    ring
  have hF : ∫ u in s..t, 24 * c4 * cp caps.PF ^ 2 * hBd φ r g y u =
      24 * c4 * cp caps.PF ^ 2 * ∫ u in s..t, hBd φ r g y u :=
    intervalIntegral.integral_const_mul _ _
  have hsq : (t - s) * (3 * x ^ 2 + 3 * z ^ 2) ≤ (4 * (x + z)) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hlen (by positivity : 0 ≤ 3 * x ^ 2 + 3 * z ^ 2)
    have h2 : 0 ≤ x * z := by positivity
    nlinarith only [h1, h2]
  have hL2 : ∫ u in s..t, hBd φ r g y u ≤ 4 * (x + z) := by
    refine hC.trans (Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩)
    refine le_trans (mul_le_mul_of_nonneg_left le_rfl (sub_nonneg.2 hst)) hsq
  have hI4 : IntervalIntegrable (fun u => (2 * hBd φ r g y u) ^ 2) volume s t := by
    have e : (fun u => (2 * hBd φ r g y u) ^ 2) = fun u => 4 * hBd φ r g y u ^ 2 := by
      funext u
      ring
    rw [e]
    exact hI.const_mul 4
  refine ⟨fun u hu => force1_le_caps h hP hs ht hsup hD hq0 q2 hu, fun u _ => ?_,
    hI4, hI1.const_mul _, ?_, ?_⟩
  · have := hb0 u
    positivity
  · rw [hE]
    nlinarith only [hV, hx0, hz0, hx1, hz1]
  · rw [hF]
    have h3 : 24 * c4 * cp caps.PF ^ 2 * ∫ u in s..t, hBd φ r g y u ≤
        24 * c4 * cp caps.PF ^ 2 * (4 * (x + z)) :=
      mul_le_mul_of_nonneg_left hL2 (by positivity)
    have e : 24 * c4 * cp caps.PF ^ 2 * (4 * (x + z)) = 3 / 8 * (Y * x + Y * z) := by
      rw [hY]
      ring
    rw [e] at h3
    linarith

/-- **The source part of `force1Q`**: `1 ≤ q`, `h_L/q ≤ 1/8`, `h_Q/q² ≤ 1/8`. -/
lemma force1Q_source {D M : ℝ} {caps : Caps} (hφ : 0 ≤ φ) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hq : force1Q φ D M caps ≤ |r|) :
    1 ≤ |r| ∧ hLc φ caps / |r| ≤ 1 / 8 ∧ hQc φ / |r| ^ 2 ≤ 1 / 8 := by
  have hc := c4_pos
  have hP2 : 0 ≤ cp caps.PF ^ 2 := sq_nonneg _
  have hL := hLc_nonneg hφ caps
  have hQ := hQc_nonneg φ
  have hk0 := forceK_nonneg hD hM caps
  have hB := (jointBudget_floors hφ caps).1
  have r1 := rootQ_nonneg 2 (by positivity : 0 ≤ 2 ^ 3 * hQc φ)
  have r2 := rootQ_nonneg 2 (by positivity : 0 ≤ 2 ^ 8 * c4 * cp caps.PF ^ 2 * hQc φ)
  have t3 : 0 ≤ 2 ^ 3 * hLc φ caps := by positivity
  have t4 : 0 ≤ 2 ^ 8 * c4 * cp caps.PF ^ 2 * hLc φ caps := by positivity
  obtain ⟨q1, -, q3, q4, -, -⟩ := six_le (zero_le_one.trans hB) hk0 t3 r1 t4 r2 hq
  have hq1 : 1 ≤ |r| := hB.trans q1
  have hq0 : 0 < |r| := by linarith
  refine ⟨hq1, ?_, ?_⟩
  · rw [div_le_iff₀ hq0]
    linarith
  · have h3 := le_rpow_of_rootQ (by norm_num) (by positivity) q4
    rw [Real.rpow_two] at h3
    rw [div_le_iff₀ (by positivity)]
    linarith

/-- **`N̄`, `π` for the force**, uniformly in `φ` and with constants independent of the caps: at
`X ≥ 1`, the force slots take at most the share `1` of `(C_N X)²`, `(C_π X)²` as soon as
`1 ≤ C_N`, `1 ≤ C_π`: `∫ N_f² ≤ (C_N X)²`, `∫ f_f ≤ (C_π X)²`. -/
theorem force1_tolerance (h : ActualSol μ φ r g y Ty) {caps : Caps} {s t D M X CN Cp : ℝ}
    (hP : OnPrefix caps r g y s t) (hs : 0 ≤ s) (hst : s ≤ t) (ht : ENNReal.ofReal t < Ty)
    (hlen : t - s ≤ 4) (hsup : ∀ u ∈ Icc s t, slowSup r g y u ≤ M) (hD : 1 ≤ D)
    (hq : force1Q φ D M caps ≤ |r|) (hX : 1 ≤ X) (hCN : 1 ≤ CN) (hCp : 1 ≤ Cp) :
    (∫ u in s..t, (2 * hBd φ r g y u) ^ 2) ≤ (CN * X) ^ 2 ∧
      (∫ u in s..t, 24 * c4 * cp caps.PF ^ 2 * hBd φ r g y u) ≤ (Cp * X) ^ 2 := by
  obtain ⟨-, -, -, -, h1, h2⟩ := force1_final h hP hs hst ht hlen hsup hD hq
  have e1 : (1 : ℝ) ≤ (CN * X) ^ 2 := one_le_pow₀ (one_le_mul_of_one_le_of_one_le hCN hX)
  have e2 : (1 : ℝ) ≤ (Cp * X) ^ 2 := one_le_pow₀ (one_le_mul_of_one_le_of_one_le hCp hX)
  exact ⟨h1.trans e1, h2.trans e2⟩

end OVNS.Quant.Metric

end
