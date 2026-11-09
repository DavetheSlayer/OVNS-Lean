import OddViscousNS.Quant.Joint.Force.Herm

/-!
# The force pairs at one time (step J5, node N12)

Fixed-time bounds on the slots of the joint energy identities in which the force sits: for a fast
`H` (the force `H_{ψ,F}`, Lean `Hf`), slow `S`, fast `F`.

Weight two (LOCAL363, Bodies 40, 41): the half derivative is put on `H`, so `H` costs `‖H‖₁`:
* `two_X1`: `X₁`, the comparable and separated parts, `(q^{−1/2} b + q⁻¹ c_S) ‖H‖₁ b_F`;
* `two_X2`, `two_X2'`: `X₂`, both slots, low and high ancestors;
* `two_Z`, `two_Z'`: `Z`, both slots.

Weight one (`F225`, Bodies 15, 45): no half is needed, the operator norm of the metric is enough:
`one_X1`, `one_X2`, `one_X2'`, `one_Z`, `one_Z'`.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

open GN (SupBd)

variable {r τ : ℝ} {S F H : Field} {M : ℝ}

/-! ### A. The energy coordinates -/

/-- The energy coordinates of a field. -/
lemma l2_zOf {m : ℕ} {u : Field} (hu : InH m u) (h0 : u 0 = 0) :
    (Summable fun k => ‖zOf m u k‖ ^ 2) ∧ l2n (zOf m u) = hnorm m u := by
  have hn : ∀ k, ‖zOf m u k‖ = wtd m u k := fun k => by
    simp only [zOf, norm_smul, Complex.norm_real, Real.norm_of_nonneg
      (pow_nonneg (absk_nonneg k) m), wtd]
  have e1 := summable_wtd_sq m hu h0
  have e2 := sqrt_tsum_wtd_sq (u := u) m h0
  refine ⟨by simpa only [hn] using e1, ?_⟩
  simp only [l2n, hn]
  exact e2

lemma zOf_add_one (u : Field) : zOf 1 (zOf 1 u) = zOf 2 u := zOf_zOf_one u

/-! ### B. The output half of `Z` with its cut -/

/-- The constant of `ZForm_half_q`. -/
def CZh : ℝ := 25600 * c4 + 4 * (44 * (Ce * (41 * 3)))

lemma CZh_pos : 0 < CZh := by
  have := c4_pos
  have := Ce_pos
  unfold CZh
  positivity

/-- **The output half of `Z`** (Body 40), at the cut `u₀ = q⁻⁴`, on `W ≤ q`:
`‖A^{1/2} Z‖ ≤ C q⁻¹ (1 + M (1 + ln q)) b`.  Body 40 cuts at `q⁻²` and needs
`‖h_u‖₂ ≲ M b u^{−1/2}`;
the Wiener bound `‖h_u‖₂ ≲ W b u^{−1/2}` of `ZForm_half_le` has the same effect at this cut, since
`q ≥ W` is paid by the raised floor.  Only the coefficient of the logarithm changes. -/
theorem ZForm_half_q {s : ℕ} (hs : s = 1 ∨ s = 2) (hr1 : 1 ≤ |r|) (τ : ℝ) (hS : Adm 2 S)
    (hS' : PiS S = S) (hM : SupBd S M) (hW : wiener S ≤ |r|) {G : Field}
    (hG : Summable fun k => ‖G k‖ ^ 2) (hG1 : Summable fun k => ‖zOf 1 G k‖ ^ 2) (hG' : PiF G = G)
    (hF : Summable fun k => ‖F k‖ ^ 2) (hF' : PiF F = F) (hGl : ∀ k, leray k (G k) = G k)
    (hFl : ∀ k, leray k (F k) = F k) :
    ‖ZForm 1 s r τ S S (zOf 1 G) F‖ ≤
      CZh / |r| * (1 + M * (1 + Real.log |r|)) * hnorm 2 S * (l2n G * l2n F) := by
  have hq : 0 < |r| := by linarith
  have hr : r ≠ 0 := abs_pos.1 hq
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hu₀ : 0 < (|r| ^ 4)⁻¹ := by positivity
  have hu₁ : (|r| ^ 4)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hr1)
  have h := ZForm_half_le hs hr τ hS hS' hM hG hG1 hG' hF hF' hGl hFl hu₀ hu₁
  have hs1 : Real.sqrt (|r| ^ 4)⁻¹ = (|r| ^ 2)⁻¹ := by
    rw [show |r| ^ 4 = (|r| ^ 2) ^ 2 by ring, ← inv_pow, Real.sqrt_sq (by positivity)]
  have hl : Real.log (1 / (|r| ^ 4)⁻¹) = 4 * Real.log |r| := by
    rw [one_div, inv_inv, Real.log_pow]
    norm_num
  rw [hs1, hl] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (mul_nonneg (l2n_nonneg _) (l2n_nonneg _)))
  have hb := hnorm_nonneg 2 S
  have hc := c4_pos
  have hCe := Ce_pos
  have hL : 0 ≤ Real.log |r| := Real.log_nonneg hr1
  have h1 : 25600 * c4 * wiener S * hnorm 2 S * (|r| ^ 2)⁻¹ ≤ 25600 * c4 / |r| * hnorm 2 S := by
    have e : 25600 * c4 / |r| * hnorm 2 S =
        25600 * c4 * |r| * hnorm 2 S * (|r| ^ 2)⁻¹ := by
      field_simp
    rw [e]
    gcongr
  have h2 : 44 * (Ce * (41 * 3)) / |r| * M * hnorm 2 S * (1 + 4 * Real.log |r|) ≤
      4 * (44 * (Ce * (41 * 3))) / |r| * M * hnorm 2 S * (1 + Real.log |r|) := by
    have h3 : 0 ≤ 44 * (Ce * (41 * 3)) / |r| * M * hnorm 2 S := by positivity
    have e : 4 * (44 * (Ce * (41 * 3))) / |r| * M * hnorm 2 S * (1 + Real.log |r|) =
        44 * (Ce * (41 * 3)) / |r| * M * hnorm 2 S * (4 * (1 + Real.log |r|)) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) h3
  have h4 : 0 ≤ 4 * (44 * (Ce * (41 * 3))) / |r| * hnorm 2 S := by positivity
  have h5 : 0 ≤ 25600 * c4 / |r| * M * hnorm 2 S * (1 + Real.log |r|) := by positivity
  have h6 : 0 ≤ 4 * (44 * (Ce * (41 * 3))) / |r| * hnorm 2 S * 1 := by positivity
  have e2 : CZh / |r| * (1 + M * (1 + Real.log |r|)) * hnorm 2 S =
      25600 * c4 / |r| * hnorm 2 S + 25600 * c4 / |r| * M * hnorm 2 S * (1 + Real.log |r|) +
        (4 * (44 * (Ce * (41 * 3))) / |r| * hnorm 2 S * 1 +
          4 * (44 * (Ce * (41 * 3))) / |r| * M * hnorm 2 S * (1 + Real.log |r|)) := by
    unfold CZh
    ring
  rw [e2]
  linarith

/-! ### C. Weight two -/

/-- The coefficient of the pair of `X₁`: LOCAL363. -/
def X1Cf (r : ℝ) (S : Field) : ℝ :=
  1536 * Real.sqrt 17 / Real.sqrt |r| * hnorm 2 S + 2 ^ 11 * c4 / |r| * hnorm 3 S

/-- The coefficient of the pair of `X₂`: Body 41. -/
def X2Cf (r D : ℝ) (S : Field) : ℝ := X2Lo r D S S + Cm2 / |r| * (hnorm 2 S * tailB D S)

/-- The coefficient of the pair of `Z`: Body 40. -/
def ZCf (r M : ℝ) (S : Field) : ℝ := CZh / |r| * (1 + M * (1 + Real.log |r|)) * hnorm 2 S

/-- **The pair of `X₁` at weight two** (LOCAL363): the two slots, as they stand in `coreRHS`. -/
theorem two_X1 (hr : r ≠ 0) (τ : ℝ) (hS : MZ 3 S) (hS' : PiS S = S) (hSr : IsReal S) (hF : MZ 2 F)
    (hH : MZ 2 H) (hH' : PiF H = H) :
    |2 * pair 2 F (X1op r τ S H) + 2 * pair 2 H (X1op r τ S F)| ≤
      X1Cf r S * (hnorm 1 H * hnorm 2 F) := by
  have hS2 : MZ 2 S := hS.mono' (by norm_num)
  have e := X1Form_re (s := 2) (Or.inr rfl) r τ hS2 hSr hF hH
  have hH1 : InH ((1 : ℕ) : ℝ) H := by
    simpa using hH.inH.mono (by norm_num : (1 : ℝ) ≤ 2)
  have hF2 : InH ((2 : ℕ) : ℝ) F := by simpa using hF.inH
  obtain ⟨s1, n1⟩ := l2_zOf hH1 hH.mean
  obtain ⟨s2, n2⟩ := l2_zOf hF2 hF.mean
  have hz : PiF (zOf 1 H) = zOf 1 H := Fam.PiF_zOf hH'
  have h1 := X1Form_half_right_le (Or.inr rfl) hr τ hS hS' s2 s1 hz
  rw [zOf_add_one, n1, n2] at h1
  simp only [Nat.cast_ofNat] at e
  rw [← e]
  refine (Complex.abs_re_le_norm _).trans (h1.trans (le_of_eq ?_))
  unfold X1Cf
  simp only [Nat.cast_one, Nat.cast_ofNat]
  ring

/-- **The pair of `X₂` at weight two** (Body 41): the force on the test. -/
theorem two_X2 (hr : r ≠ 0) (τ : ℝ) {D : ℝ} (hD : 1 ≤ D) (hS : MZ 2 S) (hS' : PiS S = S)
    (hF : MZ 2 F) (hH : MZ 1 H) (hF' : PiF F = F) :
    ‖X2Form 1 2 r τ S S (zOf 2 H) (zOf 2 F)‖ ≤ X2Cf r D S * (hnorm 1 H * hnorm 2 F) := by
  have hH1 : InH ((1 : ℕ) : ℝ) H := by simpa using hH.inH
  have hF2 : InH ((2 : ℕ) : ℝ) F := by simpa using hF.inH
  obtain ⟨s1, n1⟩ := l2_zOf hH1 hH.mean
  obtain ⟨s2, n2⟩ := l2_zOf hF2 hF.mean
  have hz : PiF (zOf 2 F) = zOf 2 F := Fam.PiF_zOf hF'
  have h1 := X2Half_total_le hr τ hD hS hS' s1 s2 hz
  rw [n1, n2, ← X2Form_zOf, zOf_add_one] at h1
  simpa only [Nat.cast_one, Nat.cast_ofNat, X2Cf] using h1

/-- **The pair of `X₂` at weight two**: the force on the input. -/
theorem two_X2' (hr : r ≠ 0) (τ : ℝ) {D : ℝ} (hD : 1 ≤ D) (hS : MZ 2 S) (hS' : PiS S = S)
    (hSr : IsReal S) (hF : MZ 2 F) (hH : MZ 1 H) (hF' : PiF F = F) :
    ‖X2Form 1 2 r τ S S (zOf 2 F) (zOf 2 H)‖ ≤ X2Cf r D S * (hnorm 1 H * hnorm 2 F) := by
  rw [X2Form_conj 2 r τ hSr hSr, RCLike.norm_conj]
  exact two_X2 hr τ hD hS hS' hF hH hF'

/-- **The pair of `Z` at weight two** (Body 40): the force on the test. -/
theorem two_Z (hr1 : 1 ≤ |r|) (τ : ℝ) (hS : Adm 2 S) (hS' : PiS S = S) (hM : SupBd S M)
    (hW : wiener S ≤ |r|) (hF : MZ 2 F) (hF' : PiF F = F) (hFs : IsSolenoidal F) (hH : MZ 2 H)
    (hH' : PiF H = H) (hHs : IsSolenoidal H) :
    ‖ZForm 1 2 r τ S S (zOf 2 H) (zOf 2 F)‖ ≤ ZCf r M S * (hnorm 1 H * hnorm 2 F) := by
  have hH1 : InH ((1 : ℕ) : ℝ) H := by
    simpa using hH.inH.mono (by norm_num : (1 : ℝ) ≤ 2)
  have hH2 : InH ((2 : ℕ) : ℝ) H := by simpa using hH.inH
  have hF2 : InH ((2 : ℕ) : ℝ) F := by simpa using hF.inH
  obtain ⟨s1, n1⟩ := l2_zOf hH1 hH.mean
  obtain ⟨s2, n2⟩ := l2_zOf hF2 hF.mean
  obtain ⟨s3, -⟩ := l2_zOf hH2 hH.mean
  have hz : PiF (zOf 2 F) = zOf 2 F := Fam.PiF_zOf hF'
  have hz1 : PiF (zOf 1 H) = zOf 1 H := Fam.PiF_zOf hH'
  have h1 := ZForm_half_q (s := 2) (Or.inr rfl) hr1 τ hS hS' hM hW (G := zOf 1 H) s1
    (by rw [zOf_add_one]; exact s3) hz1 s2 hz (leray_zOf hHs hH.mean · 1)
    (leray_zOf hFs hF.mean · 2)
  rw [zOf_add_one, n1, n2] at h1
  simpa only [Nat.cast_one, Nat.cast_ofNat, ZCf] using h1

/-- **The pair of `Z` at weight two**: the force on the input. -/
theorem two_Z' (hr1 : 1 ≤ |r|) (τ : ℝ) (hS : Adm 2 S) (hS' : PiS S = S) (hM : SupBd S M)
    (hW : wiener S ≤ |r|) (hF : MZ 2 F) (hF' : PiF F = F) (hFs : IsSolenoidal F) (hH : MZ 2 H)
    (hH' : PiF H = H) (hHs : IsSolenoidal H) :
    ‖ZForm 1 2 r τ S S (zOf 2 F) (zOf 2 H)‖ ≤ ZCf r M S * (hnorm 1 H * hnorm 2 F) := by
  rw [ZForm_conj 2 r τ hS.real hS.real, RCLike.norm_conj]
  exact two_Z hr1 τ hS hS' hM hW hF hF' hFs hH hH' hHs

/-! ### D. Weight one -/

/-- The operator norm of `X₂` (Body 36). -/
def X2St (r D : ℝ) (S : Field) : ℝ :=
  Cst / |r| * ((1 + Real.sqrt (1 + Real.log D)) * hnorm 1 S ^ 2 +
    2 * (hnorm 1 S * wiener S) + hnorm 2 S ^ 2 / D) + Cst / |r| ^ 2 * D * (hnorm 1 S * hnorm 2 S)

/-- **The pair of `X₂` at weight one**: on the two slots, by the operator norm. -/
theorem one_X2 (hr : r ≠ 0) (τ : ℝ) {D : ℝ} (hD : 1 ≤ D) (hS : MZ 2 S) (hS' : PiS S = S)
    (hF : MZ 1 F) (hH : MZ 1 H) (hF' : PiF F = F) (hH' : PiF H = H) :
    ‖X2Form 1 1 r τ S S (zOf 1 H) (zOf 1 F)‖ ≤ X2St r D S * (hnorm 1 H * hnorm 1 F) ∧
      ‖X2Form 1 1 r τ S S (zOf 1 F) (zOf 1 H)‖ ≤ X2St r D S * (hnorm 1 H * hnorm 1 F) := by
  have hH1 : InH ((1 : ℕ) : ℝ) H := by simpa using hH.inH
  have hF1 : InH ((1 : ℕ) : ℝ) F := by simpa using hF.inH
  obtain ⟨s1, n1⟩ := l2_zOf hH1 hH.mean
  obtain ⟨s2, n2⟩ := l2_zOf hF1 hF.mean
  have hz : PiF (zOf 1 F) = zOf 1 F := Fam.PiF_zOf hF'
  have hz1 : PiF (zOf 1 H) = zOf 1 H := Fam.PiF_zOf hH'
  have hμ : ∀ x : I3, ‖(1 : I3 → ℂ) x‖ ≤ 1 := fun x => by simp
  have h1 := X2Form_static_le (s := 1) (Or.inl rfl) hr τ hD hS hS' hS hS' s1 s2 hz hμ
  have h2 := X2Form_static_le (s := 1) (Or.inl rfl) hr τ hD hS hS' hS hS' s2 s1 hz1 hμ
  rw [n1, n2] at h1 h2
  have e : ∀ A B : ℝ, Cst / |r| * ((1 + Real.sqrt (1 + Real.log D)) *
      (hnorm 1 S * hnorm 1 S) + hnorm 1 S * wiener S + hnorm 1 S * wiener S +
        hnorm 2 S * hnorm 2 S / D) * (A * B) +
      Cst / |r| ^ 2 * D * (hnorm 1 S * hnorm 2 S) * (A * B) = X2St r D S * (A * B) := fun A B => by
    unfold X2St
    ring
  rw [e] at h1 h2
  simp only [Nat.cast_one] at h1 h2
  exact ⟨h1, h2.trans_eq (by ring)⟩

/-- **The pair of `Z` at weight one**, on the two slots, by the operator norm (Body 30). -/
theorem one_Z (hr : r ≠ 0) (τ : ℝ) (hS : Adm 2 S) (hS' : PiS S = S) (hM : SupBd S M) (hF : MZ 1 F)
    (hF' : PiF F = F) (hFs : IsSolenoidal F) (hH : MZ 1 H) (hH' : PiF H = H)
    (hHs : IsSolenoidal H) :
    ‖ZForm 1 1 r τ S S (zOf 1 H) (zOf 1 F)‖ ≤ CZ / |r| * M * hnorm 2 S * (hnorm 1 H * hnorm 1 F) ∧
      ‖ZForm 1 1 r τ S S (zOf 1 F) (zOf 1 H)‖ ≤
        CZ / |r| * M * hnorm 2 S * (hnorm 1 H * hnorm 1 F) := by
  have hH1 : InH ((1 : ℕ) : ℝ) H := by simpa using hH.inH
  have hF1 : InH ((1 : ℕ) : ℝ) F := by simpa using hF.inH
  obtain ⟨s1, n1⟩ := l2_zOf hH1 hH.mean
  obtain ⟨s2, n2⟩ := l2_zOf hF1 hF.mean
  have hz : PiF (zOf 1 F) = zOf 1 F := Fam.PiF_zOf hF'
  have hz1 : PiF (zOf 1 H) = zOf 1 H := Fam.PiF_zOf hH'
  have h1 := ZForm_le (s := 1) (Or.inl rfl) hr τ hS hS' hM s1 hz1 s2 hz
    (leray_zOf hHs hH.mean · 1) (leray_zOf hFs hF.mean · 1)
  have h2 := ZForm_le (s := 1) (Or.inl rfl) hr τ hS hS' hM s2 hz s1 hz1
    (leray_zOf hFs hF.mean · 1) (leray_zOf hHs hH.mean · 1)
  rw [n1, n2] at h1 h2
  simp only [Nat.cast_one] at h1 h2
  exact ⟨h1, h2.trans_eq (by ring)⟩

end OVNS.Quant.Metric

end
