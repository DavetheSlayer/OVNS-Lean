import OddViscousNS.Closed.Forced.Moment.Master
import OddViscousNS.Closed.Forced.Moment.Exterior
import OddViscousNS.Closed.Forced.Moment.Lattice
import OddViscousNS.Closed.Forced.Moment.ParamsCf

/-!
# The `c_f` moment bound: `|C|² ≤ (1.18 + .176 X/Y) K Y Z²` on `.020 < t ≤ .042`

Row `PCf`: `a = .18`, `bL = .022·8 = .176`, `λ = .031`, `K = .41085²/1.202`, `W ∈ [1/4, 2]`,
`J < 800`.  Pointwise bound as for the aligned row (exterior + kernel table via the coverage
hypothesis `hcov` = `coverCf` of `Moment/RowsCf.lean`); the exterior bound drops the `bL/h` term
(weights `≥ 1`).  Then `cubic_le_moment` with the exact first factor `1 + a + bL·X/Y`.
-/

open Set

namespace OVNS

namespace Forced

namespace Mom

/-- The coverage fact proved by the kernel certificates (`coverCf`). -/
def CoverCf : Prop :=
  ∀ Cl : ℕ, 1 ≤ Cl → Cl < 800 → ∃ lo hi, lo ≤ Cl ∧ Cl < hi ∧ rangeOk PCf lo hi = true

/-- `rawR` in the `r`-form of `exterior_bound`, keeping the weights `1 + bL/h`. -/
private lemma rawR_eq (a bL : ℝ) {Cu Cv : ℕ} (hJ : (0 : ℝ) < (Cu : ℝ) + Cv)
    (gl gh W : ℝ) :
    rawR a bL Cu Cv gl gh W =
      (gl * W / ((1 + bL / hmet Cu) * W + 4 * a * ((Cu : ℝ) / (Cu + Cv))) +
        gh * W / ((1 + bL / hmet Cv) * W + 4 * a * (1 - (Cu : ℝ) / (Cu + Cv)))) / 2 := by
  unfold rawR
  have h2 : 4 * a * (Cv : ℝ) / ((Cu : ℝ) + Cv) = 4 * a * (1 - (Cu : ℝ) / (Cu + Cv)) := by
    field_simp
    ring
  rw [h2, mul_div_assoc (4 * a) (Cu : ℝ)]

/-- The `c_f` pointwise bound. -/
theorem pointwise_cf (hcov : CoverCf) {t : ℝ} (ht1 : 2 / 100 < t) (ht2 : t ≤ 42 / 1000) :
    PointwiseW gOVNS (18 / 100) (176 / 1000) t (31 / 1000)
      ((41085 / 100000) ^ 2 / (1202 / 1000)) := by
  intro p l hp hl hnc
  have ht0 : 0 < t := by linarith
  obtain ⟨hu, hv⟩ := ne_zero_of_nonColl hnc
  have hCu := one_le_nsq hu
  have hCv := one_le_nsq hv
  rw [Tpair_eq_rawR gOVNS ht0 hp hl hnc]
  set Cu := nsq (p + l) with hCu_def
  set Cv := nsq (p - l) with hCv_def
  have hCu' : (1 : ℝ) ≤ Cu := by exact_mod_cast hCu
  have hCv' : (1 : ℝ) ≤ Cv := by exact_mod_cast hCv
  have hJ : (0 : ℝ) < (Cu : ℝ) + Cv := by linarith
  have hWe : Wpair t p l = 4 / (t * ((Cu : ℝ) + Cv)) := Wpair_eq ht0 p l
  set W := Wpair t p l with hW_def
  have hW0 : 0 < W := by rw [hWe]; positivity
  by_cases hout : W < 1 / 4 ∨ 2 < W
  · rw [rawR_eq _ _ hJ]
    have hr0 : (0 : ℝ) ≤ (Cu : ℝ) / (Cu + Cv) := by positivity
    have hr1 : (Cu : ℝ) / (Cu + Cv) ≤ 1 := by
      rw [div_le_one hJ]; linarith
    have hul : (1 : ℝ) ≤ 1 + 176 / 1000 / hmet Cu :=
      le_add_of_nonneg_right (div_nonneg (by norm_num) (hmet_pos hCu).le)
    have huh : (1 : ℝ) ≤ 1 + 176 / 1000 / hmet Cv :=
      le_add_of_nonneg_right (div_nonneg (by norm_num) (hmet_pos hCv).le)
    exact exterior_bound (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [M₀]) (by norm_num [M₀]) (by norm_num [M₀]) (by norm_num [M₀]) hW0 hout
      hr0 hr1 (gOVNS_nonneg _) (gOVNS_le_M₀ _) (gOVNS_nonneg _) (gOVNS_le_M₀ _) hul huh
  · push Not at hout
    obtain ⟨hWlo, hWhi⟩ := hout
    have htW : 4 = t * ((Cu : ℝ) + Cv) * W := by rw [hWe]; field_simp
    have htW' : 1 / 200 < t * W := by nlinarith
    have hJ800r : (Cu : ℝ) + Cv < 800 := by
      by_contra hc
      push Not at hc
      nlinarith [mul_le_mul_of_nonneg_left hc (le_of_lt (lt_trans (by norm_num) htW'))]
    have hJ800 : Cu + Cv < 800 := by exact_mod_cast hJ800r
    have hmod := nsq_mod_four p l
    rw [← hCu_def, ← hCv_def] at hmod
    have hpa : ((PCf.a : ℚ) : ℝ) = 18 / 100 := by simp [PCf]; norm_num
    have hpb : ((PCf.bL : ℚ) : ℝ) = 176 / 1000 := by simp [PCf]; norm_num
    have hpl : ((PCf.lam : ℚ) : ℝ) = 31 / 1000 := by simp [PCf]
    have hpK : ((PCf.K : ℚ) : ℝ) = (41085 / 100000) ^ 2 / (1202 / 1000) := by
      simp [PCf]; norm_num
    have key : ∀ Cl Ch : ℕ, Cl + Ch = Cu + Cv → 1 ≤ Cl → Cl ≤ Ch →
        (Ch - Cl) % 4 = 0 →
        Ch < 1024 → rep3 Cl = true → rep3 Ch = true →
        rawR (18 / 100) (176 / 1000) Cl Ch (gOVNS Cl) (gOVNS Ch) W - 31 / 1000 * (W - 1) ≤
          (41085 / 100000) ^ 2 / (1202 / 1000) := by
      intro Cl Ch hsum h1 hle hm hCh hrl hrh
      have hsumr : (Cl : ℝ) + Ch = Cu + Cv := by exact_mod_cast hsum
      obtain ⟨lo, hi, hlo, hhi, hok⟩ := hcov Cl h1 (by omega)
      have hIcc : W ∈ Icc (wLo PCf Cl Ch : ℝ) (wHi PCf Cl Ch : ℝ) := by
        unfold wLo wHi
        simp only [PCf, show ¬((1 / 50 : ℚ) = 0) by norm_num, ↓reduceIte]
        push_cast
        rw [hsumr]
        constructor
        · refine max_le (by linarith) ?_
          rw [hWe]
          exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
            (mul_le_mul_of_nonneg_right (by linarith) hJ.le)
        · refine le_min (by linarith) ?_
          rw [hWe]
          exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
            (mul_le_mul_of_nonneg_right (by linarith) hJ.le)
      have := rangeOk_sound (P := PCf) (by simp [PCf]; norm_num) (by simp [PCf]; norm_num)
        (by simp [PCf]; norm_num) (by simp [PCf]) (by simp [PCf]) (by simp [PCf]) hok hlo hhi
        h1 hle (by simp only [PCf]; omega) hm
        (mem_keys_of_rep3 (by omega) hrl) (mem_keys_of_rep3 hCh hrh) hIcc
      rw [hpa, hpb, hpl, hpK] at this
      exact this.le
    have hru := rep3_nsq (z := p + l) (by omega)
    have hrv := rep3_nsq (z := p - l) (by omega)
    rw [← hCu_def] at hru
    rw [← hCv_def] at hrv
    rcases le_total Cu Cv with h | h
    · exact key Cu Cv rfl hCu h (by omega) (by omega) hru hrv
    · rw [rawR_symm]
      exact key Cv Cu (by omega) hCv h (by omega) (by omega) hrv hru

/-- `|C(w)|² ≤ (1.18 + .176 X/Y) K Y Z²` whenever `.020 < Y/Z ≤ .042`. -/
theorem cubic_sq_le_cf (hcov : CoverCf) (hRB : RowBound gOVNS) {w : Field} (hw : Adm 2 w)
    (hw0 : w ≠ 0) (ht1 : 2 / 100 < tYZ w) (ht2 : tYZ w ≤ 42 / 1000) :
    |cubic w| ^ 2 ≤ (118 / 100 + 176 / 1000 * (Xr w / Yr w)) *
      ((41085 / 100000) ^ 2 / (1202 / 1000)) * Yr w * Zr w ^ 2 := by
  have hpt := pointwise_cf hcov ht1 ht2
  have h := cubic_le_moment hRB hw hw0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num : (31 / 1000 : ℝ) ≤ (41085 / 100000) ^ 2 / (1202 / 1000)) hpt
  rwa [show (1 : ℝ) + 18 / 100 = 118 / 100 by norm_num] at h

end Mom

end Forced

end OVNS
