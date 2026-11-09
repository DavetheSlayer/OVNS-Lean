import OddViscousNS.Quant.Joint.Metric.Group1
import OddViscousNS.Quant.Joint.Force.Final

/-!
# The direction `B(S, S)` in the metric, at both weights (nodes N5, N7, N10)

`TIMED_METRIC_PROOF_V2.md` §8.4, §9.3.  What is left of the bracket `−T_s` of `(2.5)` after the group
of the last edge is the slow derivative `D_S Y[B(S, S)]` of `Y = X₂ + Z`, `hBY` of `Force/H0Slot.lean`.

* `hBY_one_le`: (8.9), at weight one, for every mask.
* `hBY_two_le`: §9.3, at weight two: `X2diff_le`, `X2diff_le'`, `Zdiff_le`, `Zdiff_le'` off the
  high-intermediate sector, whose mask is left to `DSX2Form`.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

open GN (SupBd)
open OVNS.Quant.Quartic

variable {r τ D M : ℝ} {S F z : Field}

/-- `‖B(S, S)‖₀ ≤ 3 M_∞ a_S`. -/
lemma Bslow_l2 (hS : Adm 2 S) (hS' : PiS S = S) (hM : SupBd S M) :
    (Summable fun k => ‖Bslow S k‖ ^ 2) ∧ l2n (Bslow S) ≤ 3 * M * hnorm 1 S := by
  obtain ⟨hm, -, -⟩ := Bslow_facts hS hS' hM
  have h1 : MZ 0 (Bslow S) := hm.mono' (by norm_num)
  refine ⟨mz_l2 le_rfl h1, ?_⟩
  rw [l2n_eq_hnorm0 hm.mean]
  have h2 := GN.hnorm_Qphase_slow 0 hS hS' hM
  rwa [Qphase_slow_eq 0 hS'] at h2

/-- `diff1B` is monotone. -/
lemma diff1B_mono {q c₁ c₂ f₀ f₀' f₁ f₁' W a e L : ℝ} (hq : 0 < q) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hW : 0 ≤ W) (ha : 0 ≤ a) (he : 0 ≤ e) (hL : 0 ≤ L) (h0 : f₀ ≤ f₀') (h1 : f₁ ≤ f₁') :
    diff1B q c₁ c₂ f₀ f₁ W a e L ≤ diff1B q c₁ c₂ f₀' f₁' W a e L := by
  unfold diff1B
  gcongr

/-- The bound of `D_S Y[B]` at weight one, on both families. -/
def BY1 (q D M a W b e d : ℝ) : ℝ :=
  2 * diff1B q (2 ^ 15) (2 ^ 15) (3 * M * a) (41 * M * b) W a e
      (Real.sqrt (9 + 8 * Real.log D) * e + 5 / D * d) +
    2 * diff1B q (2 ^ 11) 0 (3 * M * a) (41 * M * b) W a e
      (Real.sqrt (9 + 8 * Real.log D) * e + 5 / D * d)

/-- **`(8.9)`**: the slow derivative at weight one, on the actual `B(S, S)`. -/
theorem hBY_one_le (hr : r ≠ 0) (τ : ℝ) (hD : 1 ≤ D) (hS : Adm 2 S) (hS' : PiS S = S)
    (hM : SupBd S M) (hF : Adm 2 F) (hF' : PiF F = F) :
    ‖X2Form 1 1 r τ (Bslow S) S (zOf 1 F) (zOf 1 F) + X2Form 1 1 r τ S (Bslow S) (zOf 1 F) (zOf 1 F)‖ +
      ‖ZForm 1 1 r τ (Bslow S) S (zOf 1 F) (zOf 1 F) + ZForm 1 1 r τ S (Bslow S) (zOf 1 F) (zOf 1 F)‖ ≤
      BY1 |r| D M (hnorm 1 S) (wiener S) (hnorm 2 S) (hnorm 1 F) (hnorm 2 F) := by
  have hq : 0 < |r| := abs_pos.2 hr
  have hD0 : 0 < D := by linarith
  have hF1 : InH ((1 : ℕ) : ℝ) F := by
    simpa using hF.inH.mono (by norm_num : (1 : ℝ) ≤ 2)
  obtain ⟨hz, nz⟩ := l2_zOf hF1 hF.mean
  have nz' : l2n (zOf 1 F) = hnorm 1 F := by simpa using nz
  have hzB : L2B (nrm (zOf 1 F)) (hnorm 1 F) := by
    have := l2B_nrm hz
    rwa [nz'] at this
  have hLF := lhB_log hD hF.inH hF'
  obtain ⟨hf1, hf2, hf3⟩ := Bslow_facts hS hS' hM
  obtain ⟨hl, hl3⟩ := Bslow_l2 hS hS' hM
  have hμ : ∀ x : I3, ‖(1 : I3 → ℂ) x‖ ≤ 1 := fun x => by simp
  obtain ⟨t1, t2, t3, t4⟩ := Y_diff_one hr τ hl hf1.inH hf2 hS.mz hS' hF' hzB hLF hμ
  set L := Real.sqrt (9 + 8 * Real.log D) * hnorm 1 F + 5 / D * hnorm 2 F with hL
  have hL0 : 0 ≤ L := by
    have := hnorm_nonneg 1 F
    have := hnorm_nonneg 2 F
    positivity
  have hW0 := wiener_nonneg S
  have ha0 := hnorm_nonneg 1 S
  have he0 := hnorm_nonneg 1 F
  have m1 := diff1B_mono (c₁ := 2 ^ 15) (c₂ := 2 ^ 15) hq (by norm_num) (by norm_num) hW0 ha0 he0
    hL0 hl3 hf3
  have m2 := diff1B_mono (c₁ := 2 ^ 11) (c₂ := 0) hq (by norm_num) le_rfl hW0 ha0 he0
    hL0 hl3 hf3
  have e : BY1 |r| D M (hnorm 1 S) (wiener S) (hnorm 2 S) (hnorm 1 F) (hnorm 2 F) =
      2 * diff1B |r| (2 ^ 15) (2 ^ 15) (3 * M * hnorm 1 S) (41 * M * hnorm 2 S) (wiener S) (hnorm 1 S)
        (hnorm 1 F) L + 2 * diff1B |r| (2 ^ 11) 0 (3 * M * hnorm 1 S) (41 * M * hnorm 2 S) (wiener S)
        (hnorm 1 S) (hnorm 1 F) L := rfl
  rw [e]
  have n1 := norm_add_le (X2Form 1 1 r τ (Bslow S) S (zOf 1 F) (zOf 1 F))
    (X2Form 1 1 r τ S (Bslow S) (zOf 1 F) (zOf 1 F))
  have n2 := norm_add_le (ZForm 1 1 r τ (Bslow S) S (zOf 1 F) (zOf 1 F))
    (ZForm 1 1 r τ S (Bslow S) (zOf 1 F) (zOf 1 F))
  linarith

/-! ### Weight two -/

/-- The terms of `X₂` with a slow `H¹` direction. -/
lemma X2_dir_summable (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ : ℝ) {h : Field} (hh : InH 1 h)
    (hh0 : h 0 = 0) (hh' : PiS h = h) (hS : MZ 2 S) (hS' : PiS S = S)
    (hz : Summable fun k => ‖z k‖ ^ 2) (hz' : PiF z = z) :
    (Summable fun x : I3 => inner ℂ (z x.1)
      (X2b s r τ h S x.1 x.2.1 x.2.2 (z (x.1 - x.2.1 - x.2.2)))) ∧
    (Summable fun x : I3 => inner ℂ (z x.1)
      (X2b s r τ S h x.1 x.2.1 x.2.2 (z (x.1 - x.2.1 - x.2.2)))) := by
  obtain ⟨s1, -, s2, -⟩ := Fam.form_dir (famX2_bd hs hr) τ hh hh0 hh' hS hS' hz hz'
  refine ⟨s1.congr fun x => ?_, s2.congr fun x => ?_⟩ <;>
    dsimp only [Fam.T, oTerm, X2b, Hx, inJ₂, famX2, twoRoot, tR]

/-- The high-intermediate mask and its complement. -/
lemma X2Form_mask {s : ℕ} {f g z : Field} {μ : I3 → ℂ} (hμ : ∀ x, ‖μ x‖ ≤ 1)
    (hs : Summable fun x : I3 => inner ℂ (z x.1)
      (X2b s r τ f g x.1 x.2.1 x.2.2 (z (x.1 - x.2.1 - x.2.2)))) :
    X2Form 1 s r τ f g z z = X2Form (1 - μ) s r τ f g z z + X2Form μ s r τ f g z z := by
  have s1 : Summable fun x : I3 => μ x * inner ℂ (z x.1)
      (X2b s r τ f g x.1 x.2.1 x.2.2 (z (x.1 - x.2.1 - x.2.2))) := by
    refine Summable.of_norm_bounded hs.norm fun x => ?_
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hμ x)
  have s2 : Summable fun x : I3 => (1 - μ) x * inner ℂ (z x.1)
      (X2b s r τ f g x.1 x.2.1 x.2.2 (z (x.1 - x.2.1 - x.2.2))) := by
    refine (hs.sub s1).congr fun x => ?_
    simp only [Pi.sub_apply, Pi.one_apply]
    ring
  simp only [X2Form_one]
  rw [X2Form, X2Form, ← s2.tsum_add s1]
  refine tsum_congr fun x => ?_
  simp only [Pi.sub_apply, Pi.one_apply]
  ring

lemma norm_hiIntMask_le (x : I3) : ‖hiIntMask D x‖ ≤ 1 := by
  unfold hiIntMask
  split_ifs <;> simp

lemma norm_one_sub_hiIntMask (x : I3) : ‖(1 - hiIntMask D) x‖ ≤ 1 := by
  simp only [Pi.sub_apply, Pi.one_apply, hiIntMask]
  split_ifs <;> simp

/-- The bound of `D_S Y[B]` at weight two, off the high-intermediate sector. -/
def BY2 (D q f₀ f₁ W a b e c : ℝ) : ℝ :=
  2 * diffB D q f₀ f₁ W b e e c c + 2 * zB 1 q f₀ f₁ W a b e e c c

/-- **§9.3**: the slow derivative at weight two.  `z = A F`, `e = ‖z‖₀ = b_F`, `c = ‖z‖₁ = c_F`. -/
theorem hBY_two_le (hr : r ≠ 0) (τ : ℝ) (hD : 0 ≤ D) (hS : Adm 2 S) (hS' : PiS S = S)
    (hM : SupBd S M) (hz : Summable fun k => ‖z k‖ ^ 2)
    (hz1 : Summable fun k => ‖zOf 1 z k‖ ^ 2) (hz' : PiF z = z) :
    ‖X2Form 1 2 r τ (Bslow S) S z z + X2Form 1 2 r τ S (Bslow S) z z‖ ≤
        2 * diffB D |r| (l2n (Bslow S)) (hnorm 1 (Bslow S)) (wiener S) (hnorm 2 S)
          (l2n z) (l2n z) (l2n (zOf 1 z)) (l2n (zOf 1 z)) +
          ‖DSX2Form (hiIntMask D) 2 r τ (Bslow S) S z z‖ ∧
      ‖ZForm 1 2 r τ (Bslow S) S z z + ZForm 1 2 r τ S (Bslow S) z z‖ ≤
        2 * zB 1 |r| (l2n (Bslow S)) (hnorm 1 (Bslow S)) (wiener S) (hnorm 1 S) (hnorm (1 + 1) S)
          (l2n z) (l2n z) (l2n (zOf 1 z)) (l2n (zOf 1 z)) := by
  obtain ⟨hf1, hf2, -⟩ := Bslow_facts hS hS' hM
  obtain ⟨hl, -⟩ := Bslow_l2 hS hS' hM
  have hBr : IsReal (Bslow S) := (majorized_res.real 0 S S hS hS).PiS'
  obtain ⟨s1, s2⟩ := X2_dir_summable (s := 2) (Or.inr rfl) hr τ hf1.inH hf1.mean hf2 hS.mz hS' hz hz'
  have hμ0 : ∀ x : I3, D < absk (x.1 - x.2.1) → 4 * absk x.1 ≤ absk (x.1 - x.2.1) →
      4 * absk (x.1 - x.2.1 - x.2.2) ≤ absk (x.1 - x.2.1) → (1 - hiIntMask D) x = 0 := by
    intro x h1 h2 h3
    simp only [Pi.sub_apply, Pi.one_apply, hiIntMask, h1, h2, h3, and_self, ↓reduceIte, sub_self]
  have b1 := X2diff_le hr τ hD hz hz1 hz hz1 hl hf1.inH hf2 hf1.mean hS.mz hS' hz'
    norm_one_sub_hiIntMask hμ0
  have b2 := X2diff_le' hr τ hD hz hz1 hz hz1 hl hf1.inH hf2 hf1.mean hBr hS.mz hS' hS.real hz'
    norm_one_sub_hiIntMask hμ0
  have e1 := X2Form_mask (μ := hiIntMask D) norm_hiIntMask_le s1
  have e2 := X2Form_mask (μ := hiIntMask D) norm_hiIntMask_le s2
  constructor
  · rw [e1, e2]
    have e3 : ∀ a b c d : ℂ, a + b + (c + d) = (a + c) + (b + d) := fun a b c d => by ring
    rw [e3]
    refine (norm_add_le _ _).trans ?_
    have := norm_add_le (X2Form (1 - hiIntMask D) 2 r τ (Bslow S) S z z)
      (X2Form (1 - hiIntMask D) 2 r τ S (Bslow S) z z)
    have e4 : X2Form (hiIntMask D) 2 r τ (Bslow S) S z z + X2Form (hiIntMask D) 2 r τ S (Bslow S) z z =
        DSX2Form (hiIntMask D) 2 r τ (Bslow S) S z z := rfl
    rw [e4]
    linarith
  · have hμ1 : ∀ x : I3, ‖(1 : I3 → ℂ) x‖ ≤ 1 := fun x => by simp
    have hS1 : MZ (1 + 1) S := by
      rw [show (1 : ℝ) + 1 = 2 by norm_num]
      exact hS.mz
    have b3 := Zdiff_le hr τ (by norm_num : (0 : ℝ) < 1) hz hz1 hz hz1 hl ⟨hf1.inH, hf1.mean⟩ hf2
      hS.mz hS1 hS' hz' hμ1
    have b4 := Zdiff_le' hr τ (by norm_num : (0 : ℝ) < 1) hz hz1 hz hz1 hl ⟨hf1.inH, hf1.mean⟩ hf2
      hS.mz hS1 hS' hz' hμ1
    refine (norm_add_le _ _).trans ?_
    linarith

end OVNS.Quant.Metric

end
