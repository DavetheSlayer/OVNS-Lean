import OddViscousNS.Closed.Forced.Moment.Master
import OddViscousNS.Closed.Forced.Moment.Exterior
import OddViscousNS.Closed.Forced.Moment.Lattice
import OddViscousNS.Closed.Forced.Moment.Params

/-!
# The aligned-moment cubic bound: `|C| ≤ c₁ √Y Z` on `.020 < t ≤ .030`, `c₁ = .4137`

Row `PAl`: `a = .18`, `bL = 0`, `λ = .034`, `K = c₁²/1.18`, `W ∈ [1/4, 2]`, `J < 800`.
Pointwise bound: exterior `W` by `exterior_bound` (four rational checks), central `W` by the
kernel-checked table (the coverage hypothesis `hcov`, supplied by `coverAl` of `Moment/Rows.lean`, and `rangeOk_sound`) after `Tpair_eq_rawR`; then `cubic_le_moment`.
-/

open Set

namespace OVNS

namespace Forced

namespace Mom

/-- The coverage fact proved by the kernel certificates (`coverAl`). -/
def CoverAl : Prop :=
  ∀ Cl : ℕ, 1 ≤ Cl → Cl < 800 → ∃ lo hi, lo ≤ Cl ∧ Cl < hi ∧ rangeOk PAl lo hi = true

/-- `rawR` with `bL = 0` in the `r`-form of `exterior_bound`. -/
private lemma rawR_zero_eq (a : ℝ) {Cu Cv : ℕ} (hJ : (0 : ℝ) < (Cu : ℝ) + Cv)
    (gl gh W : ℝ) :
    rawR a 0 Cu Cv gl gh W = (gl * W / (1 * W + 4 * a * ((Cu : ℝ) / (Cu + Cv))) +
      gh * W / (1 * W + 4 * a * (1 - (Cu : ℝ) / (Cu + Cv)))) / 2 := by
  unfold rawR
  have h2 : 4 * a * (Cv : ℝ) / ((Cu : ℝ) + Cv) = 4 * a * (1 - (Cu : ℝ) / (Cu + Cv)) := by
    field_simp
    ring
  rw [h2]
  simp only [zero_div, add_zero]
  rw [mul_div_assoc (4 * a) (Cu : ℝ)]

/-- The aligned pointwise bound. -/
theorem pointwise_aligned (hcov : CoverAl) {t : ℝ} (ht1 : 2 / 100 < t) (ht2 : t ≤ 3 / 100) :
    PointwiseW gOVNS (18 / 100) 0 t (34 / 1000) ((4137 / 10000) ^ 2 / (118 / 100)) := by
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
  · rw [rawR_zero_eq _ hJ]
    have hr0 : (0 : ℝ) ≤ (Cu : ℝ) / (Cu + Cv) := by positivity
    have hr1 : (Cu : ℝ) / (Cu + Cv) ≤ 1 := by
      rw [div_le_one hJ]; linarith
    exact exterior_bound (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [M₀]) (by norm_num [M₀]) (by norm_num [M₀]) (by norm_num [M₀]) hW0 hout
      hr0 hr1 (gOVNS_nonneg _) (gOVNS_le_M₀ _) (gOVNS_nonneg _) (gOVNS_le_M₀ _) le_rfl le_rfl
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
    have hpa : ((PAl.a : ℚ) : ℝ) = 18 / 100 := by simp [PAl]; norm_num
    have hpb : ((PAl.bL : ℚ) : ℝ) = 0 := by simp [PAl]
    have hpl : ((PAl.lam : ℚ) : ℝ) = 34 / 1000 := by simp [PAl]; norm_num
    have hpK : ((PAl.K : ℚ) : ℝ) = (4137 / 10000) ^ 2 / (118 / 100) := by simp [PAl]; norm_num
    have key : ∀ Cl Ch : ℕ, Cl + Ch = Cu + Cv → 1 ≤ Cl → Cl ≤ Ch →
        (Ch - Cl) % 4 = 0 →
        Ch < 1024 → rep3 Cl = true → rep3 Ch = true →
        rawR (18 / 100) 0 Cl Ch (gOVNS Cl) (gOVNS Ch) W - 34 / 1000 * (W - 1) ≤
          (4137 / 10000) ^ 2 / (118 / 100) := by
      intro Cl Ch hsum h1 hle hm hCh hrl hrh
      have hsumr : (Cl : ℝ) + Ch = Cu + Cv := by exact_mod_cast hsum
      obtain ⟨lo, hi, hlo, hhi, hok⟩ := hcov Cl h1 (by omega)
      have hIcc : W ∈ Icc (wLo PAl Cl Ch : ℝ) (wHi PAl Cl Ch : ℝ) := by
        unfold wLo wHi
        simp only [PAl, show ¬((1 / 50 : ℚ) = 0) by norm_num, ↓reduceIte]
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
      have := rangeOk_sound (P := PAl) (by simp [PAl]; norm_num) (by simp [PAl])
        (by simp [PAl]; norm_num) (by simp [PAl]) (by simp [PAl]) (by simp [PAl]) hok hlo hhi
        h1 hle (by simp only [PAl]; omega) hm
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

/-- `|C(w)| ≤ .4137 √Y Z` whenever `.020 < Y/Z ≤ .030`. -/
theorem cubic_le_aligned (hcov : CoverAl) (hRB : RowBound gOVNS) {w : Field} (hw : Adm 2 w)
    (hw0 : w ≠ 0)
    (ht1 : 2 / 100 < tYZ w) (ht2 : tYZ w ≤ 3 / 100) :
    |cubic w| ≤ 4137 / 10000 * Real.sqrt (Yr w) * Zr w := by
  have hpt := pointwise_aligned hcov ht1 ht2
  have h := cubic_le_moment hRB hw hw0 (by norm_num) le_rfl (by norm_num)
    (by norm_num : (34 / 1000 : ℝ) ≤ (4137 / 10000) ^ 2 / (118 / 100)) hpt
  have hY := Yr_pos_of_ne hw hw0
  have hZ := Zr_pos_of_ne hw hw0
  have h2 : |cubic w| ^ 2 ≤ (4137 / 10000 * Real.sqrt (Yr w) * Zr w) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hY.le]
    calc |cubic w| ^ 2 ≤ _ := h
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity) two_ne_zero).1 h2

end Mom

end Forced

end OVNS
