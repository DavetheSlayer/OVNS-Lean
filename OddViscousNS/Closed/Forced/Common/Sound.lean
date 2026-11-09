import OddViscousNS.Closed.Forced.Common.Defs
import OddViscousNS.Closed.Forced.Check.Sound
import OddViscousNS.Closed.Forced.Moment.Small
import OddViscousNS.Closed.Forced.Moment.Aligned
import OddViscousNS.Closed.Forced.Moment.Cf
import OddViscousNS.Closed.Forced.Moment.SupportLine
import OddViscousNS.Closed.Forced.Kinetic

/-!
# Soundness of the common-row checker

The moment-regime cubic bounds enter through `MomentOracle` (discharged by the kernel coverage
facts in `Common/Final.lean`).  `MFace.sound`: on the closed moment face, for the regime containing
`t = Y/Z`, the cubic bound gives the heat `H_act = 1 − s c U` (`√Y ≤ s U`), the trial heat `H` with
the debit `δ` (`Z < Y/t_lo` when `t > t_lo`) shifts the support coefficient `c ↦ c − δ`, and the
affine face maximum with the margin closes.  `MTerm.sound`: the late exclusion (`tYZ_le_of_face`)
puts `t` in one of the terminal regimes, tested by the scalar test (`Z ≥ Y/t_hi`) or by the pure-`Y`
support.  `Win.heat`: `H_s Z − D_q Y ≤ Z + C` wherever `Y ≤ s² Y*`.
-/

open Set

namespace OVNS

namespace Forced

namespace Com

open Chk

/-- The cubic bounds used by the common row. -/
structure MomentOracle : Prop where
  small : ∀ {w : Field}, Adm 2 w → w ≠ 0 → tYZ w ≤ 2 / 100 →
    |cubic w| ≤ 20517 / 50000 * Real.sqrt (Yr w) * Zr w
  aligned : ∀ {w : Field}, Adm 2 w → w ≠ 0 → 2 / 100 < tYZ w → tYZ w ≤ 3 / 100 →
    |cubic w| ≤ 4137 / 10000 * Real.sqrt (Yr w) * Zr w
  cf : ∀ {w : Field}, Adm 2 w → w ≠ 0 → 2 / 100 < tYZ w → tYZ w ≤ 42 / 1000 →
    |cubic w| ^ 2 ≤ (118 / 100 + 176 / 1000 * (Xr w / Yr w)) *
      ((41085 / 100000) ^ 2 / (1202 / 1000)) * Yr w * Zr w ^ 2
  kappa : ∀ {w : Field}, Adm 2 w → |cubic w| ≤ κ₀ * Real.sqrt (Yr w) * Zr w

private lemma affine_le_max {a b lo hi y : ℝ} (h1 : lo ≤ y) (h2 : y ≤ hi) :
    a * y + b ≤ max (a * lo + b) (a * hi + b) := by
  rcases le_total 0 a with ha | ha
  · exact le_max_of_le_right (by nlinarith)
  · exact le_max_of_le_left (by nlinarith)

private lemma Nsq_nonneg (r m : ℝ) (v : Field) : 0 ≤ Nsq r m v := by
  unfold Nsq
  refine tsum_nonneg fun k ↦ ?_
  split_ifs
  · exact le_rfl
  · positivity

/-- `√Y ≤ s q` from `Y ≤ s² q²`. -/
private lemma sqrt_le_of {Y s q : ℝ} (hs : 0 ≤ s) (hq : 0 ≤ q) (h : Y ≤ s ^ 2 * q ^ 2) :
    Real.sqrt Y ≤ s * q := by
  rw [show s ^ 2 * q ^ 2 = (s * q) ^ 2 by ring] at h
  exact (Real.sqrt_le_sqrt h).trans_eq (Real.sqrt_sq (mul_nonneg hs hq))

/-- The heat `(1 − s c U) Z ≤ Z + C` from `|C| ≤ c √Y Z` and `√Y ≤ s U`. -/
private lemma heat_c {Y Z C s U c : ℝ} (hc : 0 ≤ c) (hZ : 0 ≤ Z)
    (hC : |C| ≤ c * Real.sqrt Y * Z) (hsq : Real.sqrt Y ≤ s * U) :
    (1 - s * c * U) * Z ≤ Z + C := by
  have h1 : c * Real.sqrt Y * Z ≤ c * (s * U) * Z :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hc) hZ
  have h2 := neg_abs_le C
  nlinarith

private lemma rotF_ne (τ : ℝ) {v : Field} (hv : Adm 2 v) (hv0 : v ≠ 0) : rotF τ v ≠ 0 := by
  intro h
  have h1 := Zr_rotF τ hv
  rw [h] at h1
  have h2 := Zr_pos_of_ne hv hv0
  have h3 : Zr (0 : Field) = 0 := by simp [Zr]
  linarith

private lemma tYZ_rotF (τ : ℝ) {v : Field} (hv : Adm 2 v) : tYZ (rotF τ v) = tYZ v := by
  unfold tYZ
  rw [Yr_rotF τ hv, Zr_rotF τ hv]

private lemma Coef.val_nonneg (c : Coef) : (0 : ℝ) ≤ (c.val : ℝ) := by
  cases c <;> norm_num [Coef.val]

/-- The face regimes cover `(t₀, ∞)`. -/
private lemma coverOk_mem : ∀ (regs : List MRegime) (t₀ : ℚ), coverOk t₀ regs = true →
    ∀ t : ℝ, (t₀ : ℝ) < t → ∃ R ∈ regs, (R.tlo : ℝ) < t ∧ ∀ h, R.thi = some h → t ≤ h
  | [], _, h, _, _ => by simp [coverOk] at h
  | R :: rest, t₀, h, t, ht => by
    simp only [coverOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hlo, hrest⟩ := h
    rcases hR : R.thi with _ | h'
    · exact ⟨R, List.mem_cons_self .., by rw [hlo]; exact ht,
        fun x hx ↦ by rw [hR] at hx; cases hx⟩
    · rw [hR] at hrest
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hrest
      by_cases hth : t ≤ h'
      · exact ⟨R, List.mem_cons_self .., by rw [hlo]; exact ht,
          fun x hx ↦ by rw [hR] at hx; cases hx; exact hth⟩
      · obtain ⟨R', hR', h1, h2⟩ := coverOk_mem rest h' hrest.2 t (lt_of_not_ge hth)
        exact ⟨R', List.mem_cons_of_mem _ hR', h1, h2⟩

/-- The terminal regimes cover `(t₀, τ]`. -/
private lemma tcoverOk_mem : ∀ (regs : List TRegime) (t₀ τ : ℚ), tcoverOk t₀ τ regs = true →
    ∀ t : ℝ, (t₀ : ℝ) < t → t ≤ τ → ∃ R ∈ regs, (R.tlo : ℝ) < t ∧ t ≤ R.thi
  | [], t₀, τ, h, t, h1, h2 => by
    simp only [tcoverOk, decide_eq_true_eq] at h
    subst h
    exact absurd (h1.trans_le h2) (lt_irrefl _)
  | R :: rest, t₀, τ, h, t, h1, h2 => by
    simp only [tcoverOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hlo, -⟩, hrest⟩ := h
    by_cases hth : t ≤ R.thi
    · exact ⟨R, List.mem_cons_self .., by rw [hlo]; exact h1, hth⟩
    · obtain ⟨R', hR', h3, h4⟩ := tcoverOk_mem rest R.thi τ hrest t (lt_of_not_ge hth) h2
      exact ⟨R', List.mem_cons_of_mem _ hR', h3, h4⟩

/-- The cubic bound in a face regime. -/
private lemma mreg_cubic (hO : MomentOracle) {R : MRegime} (hdom : R.domOk = true)
    {w : Field} (hw : Adm 2 w) (hw0 : w ≠ 0) (hlo : (R.tlo : ℝ) < tYZ w)
    (hhi : ∀ h, R.thi = some h → tYZ w ≤ h) :
    |cubic w| ≤ (R.coef.val : ℝ) * Real.sqrt (Yr w) * Zr w := by
  rcases R with ⟨tlo, thi, coef, H, δ, sp⟩
  cases coef with
  | small =>
    rcases thi with _ | h
    · simp [MRegime.domOk] at hdom
    · simp only [MRegime.domOk, decide_eq_true_eq] at hdom
      have h1 := hhi h rfl
      have h2 : (h : ℝ) ≤ 2 / 100 := by
        have := (Rat.cast_le (K := ℝ)).2 hdom; push_cast at this; linarith
      have := hO.small hw hw0 (h1.trans h2)
      norm_num [Coef.val] at this ⊢; exact this
  | aligned =>
    rcases thi with _ | h
    · simp [MRegime.domOk] at hdom
    · simp only [MRegime.domOk, Bool.and_eq_true, decide_eq_true_eq] at hdom
      have h1 := hhi h rfl
      have h2 : (h : ℝ) ≤ 3 / 100 := by
        have := (Rat.cast_le (K := ℝ)).2 hdom.2; push_cast at this; linarith
      have h3 : (2 / 100 : ℝ) ≤ tlo := by
        have := (Rat.cast_le (K := ℝ)).2 hdom.1; push_cast at this; linarith
      have := hO.aligned hw hw0 (h3.trans_lt hlo) (h1.trans h2)
      norm_num [Coef.val] at this ⊢; exact this
  | kappa =>
    have := hO.kappa hw
    norm_num [Coef.val, κ₀] at this ⊢; exact this

/-- The heat with the debit: `−m (Z + C) ≤ −m H Z + δ Y`. -/
private lemma debit_heat {m Hact H δ tlo Y Z C c s U : ℝ} (hm : 0 ≤ m) (hc : 0 ≤ c)
    (hZ : 0 ≤ Z) (hC : |C| ≤ c * Real.sqrt Y * Z) (hsq : Real.sqrt Y ≤ s * U)
    (hHact : Hact = 1 - s * c * U) (hlo : tlo * Z < Y)
    (hdeb : (tlo = 0 ∧ H = Hact ∧ δ = 0) ∨ (0 < tlo ∧ δ = m * max 0 (H - Hact) / tlo)) :
    -m * (Z + C) ≤ -m * H * Z + δ * Y := by
  have hh := heat_c hc hZ hC hsq
  rw [← hHact] at hh
  have h1 : -m * (Z + C) ≤ -m * Hact * Z := by nlinarith
  rcases hdeb with ⟨-, rfl, rfl⟩ | ⟨htlo, rfl⟩
  · linarith
  · have hZle : Z ≤ Y / tlo := by rw [le_div_iff₀ htlo]; linarith
    have h2 : m * (H - Hact) * Z ≤ m * max 0 (H - Hact) * Z :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_right _ _) hm) hZ
    have h3 : m * max 0 (H - Hact) * Z ≤ m * max 0 (H - Hact) * (Y / tlo) :=
      mul_le_mul_of_nonneg_left hZle (mul_nonneg hm (le_max_left _ _))
    have h4 : m * max 0 (H - Hact) / tlo * Y = m * max 0 (H - Hact) * (Y / tlo) := by ring
    linarith

/-- The moment face, for the regime containing `t`, with a given cubic bound. -/
private lemma mface_core {f0 s : ℚ} (hs : 0 < s) {F : MFace} (hU0 : 0 ≤ F.U)
    (hUsq : F.B + 1 / 1000 ≤ F.U ^ 2) (hm0 : 0 < F.m) {R : MRegime}
    (hR : R.ok s f0 F.B F.E F.m F.U = true) {v g : Field} (hv : Adm 2 v) (hg : Adm 2 g)
    (hgn : hnorm 2 g ≤ f0 * s) (τ : ℝ) {C : ℝ}
    (hC : |C| ≤ (R.coef.val : ℝ) * Real.sqrt (Yr v) * Zr v)
    (hlo : (R.tlo : ℝ) * Zr v < Yr v)
    (hY : Yr v ∈ Icc ((s : ℝ) ^ 2 * F.B) ((s : ℝ) ^ 2 * (F.B + 1 / 1000)))
    (hX : Xr v = (s : ℝ) ^ 2 * F.E - F.m * (Yr v - (s : ℝ) ^ 2 * F.B)) :
    -J1r v - F.m * (Zr v + C) + (wPair ωX v (rotF τ g) + F.m * wPair ωY v (rotF τ g)) < 0 := by
  simp only [MRegime.ok, Bool.and_eq_true, decide_eq_true_eq] at hR
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, htlo0⟩, -⟩, hr⟩, hmm⟩, hHH⟩, hsp⟩, hdeb⟩, hmar⟩ := hR
  have hdebR : ((R.tlo : ℝ) = 0 ∧ (R.H : ℝ) = 1 - s * R.coef.val * F.U ∧ (R.δ : ℝ) = 0) ∨
      (0 < (R.tlo : ℝ) ∧
        (R.δ : ℝ) = F.m * max 0 ((R.H : ℝ) - (1 - s * R.coef.val * F.U)) / R.tlo) := by
    split_ifs at hdeb with h0
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hdeb
      left
      exact ⟨by exact_mod_cast h0, by exact_mod_cast hdeb.1, by exact_mod_cast hdeb.2⟩
    · simp only [decide_eq_true_eq] at hdeb
      right
      refine ⟨by exact_mod_cast lt_of_le_of_ne htlo0 (Ne.symm h0), ?_⟩
      rw [hdeb]; push_cast; ring
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hU0R : (0 : ℝ) ≤ F.U := by exact_mod_cast hU0
  have hUsqR : (F.B : ℝ) + 1 / 1000 ≤ (F.U : ℝ) ^ 2 := by
    have h2 := (Rat.cast_le (K := ℝ)).2 hUsq; push_cast at h2; linarith
  have hm0R : (0 : ℝ) ≤ F.m := by exact_mod_cast hm0.le
  have hmarR : (0 : ℝ) < -(max (-((R.sp.c : ℝ) - R.δ) * F.B + R.sp.M * F.E)
      (-((R.sp.c : ℝ) - R.δ) * (F.B + 1 / 1000) + R.sp.M * (F.E - F.m / 1000))) -
      f0 ^ 2 / (4 * R.sp.ε) := by
    have h2 := (Rat.cast_lt (K := ℝ)).2 hmar; push_cast at h2; linarith
  have hε : (0 : ℝ) < R.sp.ε := by
    have h' := hsp
    simp only [Supp.ok, Bool.and_eq_true, decide_eq_true_eq] at h'
    exact_mod_cast h'.1.1.1.1.2
  have hX0 := Xr_nonneg hv
  have hYZ := Yr_le_Zr hv
  -- heat with debit
  have hsqrt : Real.sqrt (Yr v) ≤ s * F.U :=
    sqrt_le_of hsR.le hU0R (hY.2.trans (by gcongr))
  have hheat := debit_heat hm0R (Coef.val_nonneg R.coef) (hX0.trans ((Xr_le_Yr hv).trans hYZ))
    hC hsqrt rfl hlo hdebR
  -- pairing
  have hN0 := Nsq_nonneg 1 F.m v
  have hpair := force_pair_N_le τ hg hv zero_le_one hm0R
  rw [one_mul] at hpair
  have hpair2 : wPair ωX v (rotF τ g) + F.m * wPair ωY v (rotF τ g) ≤
      (f0 * s) * Real.sqrt (Nsq 1 F.m v) :=
    (le_abs_self _).trans (hpair.trans
      (mul_le_mul_of_nonneg_right hgn (Real.sqrt_nonneg _)))
  have hyoung := young_force (f := (f0 : ℝ) * s) hε (Real.sqrt_nonneg (Nsq 1 F.m v))
  rw [Real.sq_sqrt hN0] at hyoung
  -- support
  have hsupp := Supp.apply hsp hv
  rw [hr, hmm, hHH] at hsupp
  push_cast at hsupp
  -- affine maximum
  have haff := affine_le_max (a := -(R.sp.M : ℝ) * F.m - (R.sp.c - R.δ))
    (b := (R.sp.M : ℝ) * ((s : ℝ) ^ 2 * F.E) + R.sp.M * F.m * ((s : ℝ) ^ 2 * F.B)) hY.1 hY.2
  have hmax : max ((-(R.sp.M : ℝ) * F.m - (R.sp.c - R.δ)) * ((s : ℝ) ^ 2 * F.B) +
      (R.sp.M * ((s : ℝ) ^ 2 * F.E) + R.sp.M * F.m * ((s : ℝ) ^ 2 * F.B)))
      ((-(R.sp.M : ℝ) * F.m - (R.sp.c - R.δ)) * ((s : ℝ) ^ 2 * (F.B + 1 / 1000)) +
      (R.sp.M * ((s : ℝ) ^ 2 * F.E) + R.sp.M * F.m * ((s : ℝ) ^ 2 * F.B))) =
      (s : ℝ) ^ 2 * max (-((R.sp.c : ℝ) - R.δ) * F.B + R.sp.M * F.E)
      (-((R.sp.c : ℝ) - R.δ) * (F.B + 1 / 1000) + R.sp.M * (F.E - F.m / 1000)) := by
    rw [mul_max_of_nonneg _ _ (by positivity)]
    congr 1 <;> ring
  rw [hmax] at haff
  have hfin : (s : ℝ) ^ 2 * (max (-((R.sp.c : ℝ) - R.δ) * F.B + R.sp.M * F.E)
      (-((R.sp.c : ℝ) - R.δ) * (F.B + 1 / 1000) + R.sp.M * (F.E - F.m / 1000)) +
      f0 ^ 2 / (4 * R.sp.ε)) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) (by linarith)
  have hfs : ((f0 : ℝ) * s) ^ 2 / (4 * R.sp.ε) = (s : ℝ) ^ 2 * (f0 ^ 2 / (4 * R.sp.ε)) := by
    ring
  rw [hX] at hsupp
  nlinarith

/-- Moment face: the normal derivative of `X + mY` is strictly negative on the closed face. -/
theorem MFace.sound (hO : MomentOracle) {f0 s : ℚ} (hs : 0 < s) {F : MFace}
    (hF : F.ok s f0 = true) {v g : Field} (hv : Adm 2 v) (hv0 : v ≠ 0) (hg : Adm 2 g)
    (hgn : hnorm 2 g ≤ f0 * s) (τ : ℝ)
    (hY : Yr v ∈ Icc ((s : ℝ) ^ 2 * F.B) ((s : ℝ) ^ 2 * (F.B + 1 / 1000)))
    (hX : Xr v = (s : ℝ) ^ 2 * F.E - F.m * (Yr v - (s : ℝ) ^ 2 * F.B)) :
    -J1r v - F.m * (Zr v + cubic (rotF τ v)) +
      (wPair ωX v (rotF τ g) + F.m * wPair ωY v (rotF τ g)) < 0 := by
  simp only [MFace.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hF
  obtain ⟨⟨⟨⟨hU0, hUsq⟩, hm0⟩, hcov⟩, hall⟩ := hF
  have hYp := Yr_pos_of_ne hv hv0
  have hZp := Zr_pos_of_ne hv hv0
  have ht0 : (0 : ℝ) < tYZ v := div_pos hYp hZp
  obtain ⟨R, hRmem, hRlo, hRhi⟩ := coverOk_mem F.regs 0 hcov (tYZ v) (by simpa using ht0)
  have hR := hall R hRmem
  have hdom : R.domOk = true := by
    simp only [MRegime.ok, Bool.and_eq_true] at hR
    exact hR.1.1.1.1.1.1.1.1
  have hC := mreg_cubic hO hdom (hv.rotF τ) (rotF_ne τ hv hv0)
    (by rw [tYZ_rotF τ hv]; exact hRlo) (by rw [tYZ_rotF τ hv]; exact hRhi)
  rw [Yr_rotF τ hv, Zr_rotF τ hv] at hC
  have hlo : (R.tlo : ℝ) * Zr v < Yr v := by
    have := hRlo
    unfold tYZ at this
    rwa [lt_div_iff₀ hZp] at this
  exact mface_core hs hU0 hUsq hm0 hR hv hg hgn τ hC hlo hY hX

/-- The terminal coefficient is nonnegative. -/
private lemma treg_c_nonneg {s f0 Y E U : ℚ} {R : TRegime} (hR : R.ok s f0 Y E U = true) :
    (0 : ℝ) ≤ (R.coef.val : ℝ) := by
  simp only [TRegime.ok, Bool.and_eq_true, decide_eq_true_eq] at hR
  obtain ⟨⟨⟨⟨-, -⟩, -⟩, hcoef⟩, -⟩ := hR
  rcases R with ⟨tlo, thi, coef, H, test⟩
  cases coef with
  | small => norm_num [TCoef.val]
  | cf c =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcoef
    simp only [TCoef.val]
    exact_mod_cast hcoef.1.2

/-- The cubic bound in a terminal regime. -/
private lemma treg_cubic (hO : MomentOracle) {s f0 : ℚ} {T : MTerm} {R : TRegime}
    (hR : R.ok s f0 T.Y T.E T.U = true) {w : Field} (hw : Adm 2 w) (hw0 : w ≠ 0)
    (hlo : (R.tlo : ℝ) < tYZ w) (hhi : tYZ w ≤ R.thi) (hXY : Xr w / Yr w ≤ (T.E : ℝ) / T.Y) :
    |cubic w| ≤ (R.coef.val : ℝ) * Real.sqrt (Yr w) * Zr w := by
  simp only [TRegime.ok, Bool.and_eq_true, decide_eq_true_eq] at hR
  obtain ⟨⟨⟨⟨-, -⟩, -⟩, hcoef⟩, -⟩ := hR
  rcases R with ⟨tlo, thi, coef, H, test⟩
  cases coef with
  | small =>
    simp only [decide_eq_true_eq] at hcoef
    have h2 : (thi : ℝ) ≤ 2 / 100 := by
      have := (Rat.cast_le (K := ℝ)).2 hcoef; push_cast at this; linarith
    have := hO.small hw hw0 (hhi.trans h2)
    norm_num [TCoef.val] at this ⊢; exact this
  | cf c =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcoef
    obtain ⟨⟨⟨h1, h2⟩, hc0⟩, hcsq⟩ := hcoef
    have h1R : (2 / 100 : ℝ) ≤ tlo := by
      have := (Rat.cast_le (K := ℝ)).2 h1; push_cast at this; linarith
    have h2R : (thi : ℝ) ≤ 42 / 1000 := by
      have := (Rat.cast_le (K := ℝ)).2 h2; push_cast at this; linarith
    have hc0R : (0 : ℝ) ≤ c := by exact_mod_cast hc0
    have hcsqR : (118 / 100 + 176 / 1000 * ((T.E : ℝ) / T.Y)) *
        ((41085 / 100000) ^ 2 / (1202 / 1000)) ≤ (c : ℝ) ^ 2 := by
      have := (Rat.cast_le (K := ℝ)).2 hcsq; push_cast at this; linarith
    have hcub := hO.cf hw hw0 (h1R.trans_lt hlo) (hhi.trans h2R)
    have hY0 : 0 ≤ Yr w := (Xr_nonneg hw).trans (Xr_le_Yr hw)
    have hP : 0 ≤ Yr w * Zr w ^ 2 := by positivity
    have hb : |cubic w| ^ 2 ≤ ((c : ℝ) * Real.sqrt (Yr w) * Zr w) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hY0]
      have e1 := mul_le_mul_of_nonneg_right
        (show 118 / 100 + 176 / 1000 * (Xr w / Yr w) ≤ 118 / 100 + 176 / 1000 * ((T.E : ℝ) / T.Y)
          by linarith)
        (show (0 : ℝ) ≤ (41085 / 100000) ^ 2 / (1202 / 1000) * (Yr w * Zr w ^ 2) by positivity)
      have e2 := mul_le_mul_of_nonneg_right hcsqR hP
      nlinarith
    simp only [TCoef.val]
    exact (pow_le_pow_iff_left₀ (abs_nonneg _)
      (mul_nonneg (mul_nonneg hc0R (Real.sqrt_nonneg _)) (hY0.trans (Yr_le_Zr hw)))
      two_ne_zero).1 hb

/-- The terminal face, in the regime containing `t`, with a given cubic bound. -/
private lemma mterm_core {f0 s : ℚ} (hs : 0 < s) {T : MTerm} (hU0 : 0 ≤ T.U)
    (hUsq : T.Y ≤ T.U ^ 2) {R : TRegime} (hR : R.ok s f0 T.Y T.E T.U = true) {v g : Field}
    (hv : Adm 2 v) (hg : Adm 2 g) (hgn : hnorm 2 g ≤ f0 * s) (τ : ℝ) {C : ℝ}
    (hC : |C| ≤ (R.coef.val : ℝ) * Real.sqrt (Yr v) * Zr v) (hthi : 0 < (R.thi : ℝ))
    (hhi : Yr v ≤ R.thi * Zr v) (hY : Yr v = (s : ℝ) ^ 2 * T.Y)
    (hX : Xr v ≤ (s : ℝ) ^ 2 * T.E) :
    -(Zr v + C) + wPair ωY v (rotF τ g) < 0 := by
  have hc := treg_c_nonneg hR
  simp only [TRegime.ok, Bool.and_eq_true, decide_eq_true_eq] at hR
  obtain ⟨⟨⟨⟨hH, hH0⟩, -⟩, -⟩, htest⟩ := hR
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hU0R : (0 : ℝ) ≤ T.U := by exact_mod_cast hU0
  have hUsqR : (T.Y : ℝ) ≤ (T.U : ℝ) ^ 2 := by exact_mod_cast hUsq
  have hHR : (R.H : ℝ) = 1 - s * R.coef.val * T.U := by exact_mod_cast hH
  have hH0R : (0 : ℝ) < R.H := by exact_mod_cast hH0
  have hX0 := Xr_nonneg hv
  have hZ0 : 0 ≤ Zr v := hX0.trans ((Xr_le_Yr hv).trans (Yr_le_Zr hv))
  have hsqrt : Real.sqrt (Yr v) ≤ s * T.U :=
    sqrt_le_of hsR.le hU0R (hY.le.trans (by gcongr))
  have hheat := heat_c hc hZ0 hC hsqrt
  rw [← hHR] at hheat
  rcases hRt : R.test with qE | sp
  · rw [hRt] at htest
    simp only [Bool.and_eq_true, decide_eq_true_eq] at htest
    obtain ⟨⟨⟨-, hq0⟩, hqsq⟩, hmar⟩ := htest
    have hq0R : (0 : ℝ) ≤ qE := by exact_mod_cast hq0
    have hqsqR : (T.E : ℝ) ≤ (qE : ℝ) ^ 2 := by exact_mod_cast hqsq
    have hmarR : (0 : ℝ) < R.H * T.Y / R.thi - f0 * qE := by exact_mod_cast hmar
    have hsqX : Real.sqrt (Xr v) ≤ s * qE := sqrt_le_of hsR.le hq0R (hX.trans (by gcongr))
    have hp := (le_abs_self _).trans (force_pair_Y_le τ hg hv)
    have h1 : hnorm 2 g * Real.sqrt (Xr v) ≤ hnorm 2 g * (s * qE) :=
      mul_le_mul_of_nonneg_left hsqX (hnorm_nonneg _ _)
    have h2 : hnorm 2 g * (s * qE) ≤ f0 * s * (s * qE) :=
      mul_le_mul_of_nonneg_right hgn (by positivity)
    have hZ' : Yr v / R.thi ≤ Zr v := by rw [div_le_iff₀ hthi]; linarith
    have h3 : (R.H : ℝ) * (Yr v / R.thi) ≤ R.H * Zr v := mul_le_mul_of_nonneg_left hZ' hH0R.le
    have h4 : (R.H : ℝ) * (Yr v / R.thi) = (s : ℝ) ^ 2 * (R.H * T.Y / R.thi) := by
      rw [hY]; ring
    have hfin : (s : ℝ) ^ 2 * (R.H * T.Y / R.thi - f0 * qE) > 0 := by positivity
    nlinarith
  · rw [hRt] at htest
    simp only [Bool.and_eq_true, decide_eq_true_eq] at htest
    obtain ⟨⟨⟨⟨hr, hmm⟩, hHH⟩, hsp⟩, hmar⟩ := htest
    have hmarR : (0 : ℝ) < sp.c * T.Y - max 0 (sp.M : ℝ) * T.E - f0 ^ 2 / (4 * sp.ε) := by
      have h2 := (Rat.cast_lt (K := ℝ)).2 hmar; push_cast at h2; linarith
    have hε : (0 : ℝ) < sp.ε := by
      have h' := hsp
      simp only [Supp.ok, Bool.and_eq_true, decide_eq_true_eq] at h'
      exact_mod_cast h'.1.1.1.1.2
    have hN0 := Nsq_nonneg 0 1 v
    have hpair := force_pair_N_le τ hg hv le_rfl zero_le_one
    rw [zero_mul, zero_add, one_mul] at hpair
    have hpair2 : wPair ωY v (rotF τ g) ≤ (f0 * s) * Real.sqrt (Nsq 0 1 v) :=
      (le_abs_self _).trans (hpair.trans
        (mul_le_mul_of_nonneg_right hgn (Real.sqrt_nonneg _)))
    have hyoung := young_force (f := (f0 : ℝ) * s) hε (Real.sqrt_nonneg (Nsq 0 1 v))
    rw [Real.sq_sqrt hN0] at hyoung
    have hsupp := Supp.apply hsp hv
    rw [hr, hmm, hHH] at hsupp
    push_cast at hsupp
    have hM1 : (sp.M : ℝ) * Xr v ≤ max 0 (sp.M : ℝ) * Xr v :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hX0
    have hM2 : max 0 (sp.M : ℝ) * Xr v ≤ max 0 (sp.M : ℝ) * ((s : ℝ) ^ 2 * T.E) :=
      mul_le_mul_of_nonneg_left hX (le_max_left _ _)
    have hfin : (s : ℝ) ^ 2 * (sp.c * T.Y - max 0 (sp.M : ℝ) * T.E - f0 ^ 2 / (4 * sp.ε))
        > 0 := mul_pos (by positivity) hmarR
    have hfs : ((f0 : ℝ) * s) ^ 2 / (4 * sp.ε) = (s : ℝ) ^ 2 * (f0 ^ 2 / (4 * sp.ε)) := by
      ring
    rw [hY] at hsupp
    nlinarith

/-- Terminal face: `Y` strictly decreases. -/
theorem MTerm.sound (hO : MomentOracle) {f0 s : ℚ} (hs : 0 < s) {T : MTerm}
    (hT : T.ok s f0 = true) {v g : Field} (hv : Adm 2 v) (hv0 : v ≠ 0) (hg : Adm 2 g)
    (hgn : hnorm 2 g ≤ f0 * s) (τ : ℝ) (hY : Yr v = (s : ℝ) ^ 2 * T.Y)
    (hX : Xr v ≤ (s : ℝ) ^ 2 * T.E) :
    -(Zr v + cubic (rotF τ v)) + wPair ωY v (rotF τ g) < 0 := by
  simp only [MTerm.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hT
  obtain ⟨⟨⟨⟨⟨⟨⟨hU0, hUsq⟩, hY0⟩, -⟩, hτ0⟩, hlate⟩, hcov⟩, hall⟩ := hT
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hY0R : (0 : ℝ) < T.Y := by exact_mod_cast hY0
  have hτR : (0 : ℝ) < T.τ := by exact_mod_cast hτ0
  have hYp := Yr_pos_of_ne hv hv0
  have hZp := Zr_pos_of_ne hv hv0
  have ht0 : (0 : ℝ) < tYZ v := div_pos hYp hZp
  have hlateR : 1 / (T.τ : ℝ) ≤ 13191 / 212 - 63940773 / 212000 * ((T.E : ℝ) / T.Y) := by
    have := (Rat.cast_le (K := ℝ)).2 hlate; push_cast at this; linarith
  have hEY : (s : ℝ) ^ 2 * T.E / ((s : ℝ) ^ 2 * T.Y) = (T.E : ℝ) / T.Y :=
    mul_div_mul_left _ _ (by positivity)
  have htτ : tYZ v ≤ T.τ := tYZ_le_of_face hv hv0 (by positivity) hτR hY.ge hX
    (by rw [hEY]; exact hlateR)
  obtain ⟨R, hRmem, hRlo, hRhi⟩ :=
    tcoverOk_mem T.regs 0 T.τ hcov (tYZ v) (by simpa using ht0) htτ
  have hR := hall R hRmem
  have hXY : Xr v / Yr v ≤ (T.E : ℝ) / T.Y := by
    rw [← hEY, ← hY]
    exact div_le_div_of_nonneg_right hX hYp.le
  have hC := treg_cubic hO hR (hv.rotF τ) (rotF_ne τ hv hv0)
    (by rw [tYZ_rotF τ hv]; exact hRlo) (by rw [tYZ_rotF τ hv]; exact hRhi)
    (by rw [Xr_rotF τ hv, Yr_rotF τ hv]; exact hXY)
  rw [Yr_rotF τ hv, Zr_rotF τ hv] at hC
  have hhi : Yr v ≤ R.thi * Zr v := by
    have := hRhi
    unfold tYZ at this
    rwa [div_le_iff₀ hZp] at this
  exact mterm_core hs hU0 hUsq hR hv hg hgn τ hC (ht0.trans_le hRhi) hhi hY hX

/-- A debit step: `H Z ≤ Z + C`, `(H_s − H)/a ≤ D_q`, `a Z < Y` give `H_s Z − D_q Y ≤ Z + C`. -/
private lemma debit_step {Hs H Dq Y Z C a : ℝ} (ha : 0 < a) (hd : (Hs - H) / a ≤ Dq)
    (hDq : 0 ≤ Dq) (hZ : 0 ≤ Z) (hZa : a * Z < Y) (hh : H * Z ≤ Z + C) :
    Hs * Z - Dq * Y ≤ Z + C := by
  have hd' : Hs - H ≤ Dq * a := (div_le_iff₀ ha).1 hd
  have h1 := mul_le_mul_of_nonneg_right hd' hZ
  have h2 := mul_le_mul_of_nonneg_left hZa.le hDq
  nlinarith

/-- The window heat with debits: `H_s Z − D_q Y ≤ Z + C` wherever `Y ≤ s² Y*`. -/
theorem Win.heat (hO : MomentOracle) {f0 s : ℚ} {J : ℕ} (hs : 0 < s) {T : MTerm} {W : Win}
    (hT : T.ok s f0 = true) (hW : W.ok s f0 J T = true) {v : Field} (hv : Adm 2 v) (τ : ℝ)
    (hY : Yr v ≤ (s : ℝ) ^ 2 * T.Y) :
    (W.Hs : ℝ) * Zr v - W.Dq * Yr v ≤ Zr v + cubic (rotF τ v) := by
  simp only [Win.ok, Bool.and_eq_true, decide_eq_true_eq] at hW
  obtain ⟨⟨⟨⟨⟨⟨⟨hHs, hHm⟩, hHg⟩, -⟩, hDq0⟩, hdm⟩, hdg⟩, -⟩ := hW
  simp only [MTerm.ok, Bool.and_eq_true, decide_eq_true_eq] at hT
  obtain ⟨⟨⟨⟨⟨⟨⟨hU0, hUsq⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hT
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hU0R : (0 : ℝ) ≤ T.U := by exact_mod_cast hU0
  have hUsqR : (T.Y : ℝ) ≤ (T.U : ℝ) ^ 2 := by exact_mod_cast hUsq
  have hHsR : (W.Hs : ℝ) = 1 - s * (20517 / 50000) * T.U := by
    have := congrArg (fun x : ℚ ↦ (x : ℝ)) hHs; push_cast at this; linarith
  have hHmR : (W.Hm : ℝ) = 1 - s * (4137 / 10000) * T.U := by
    have := congrArg (fun x : ℚ ↦ (x : ℝ)) hHm; push_cast at this; linarith
  have hHgR : (W.Hg : ℝ) = 1 - s * κ₀ * T.U := by
    have := congrArg (fun x : ℚ ↦ (x : ℝ)) hHg; push_cast at this; rw [κ₀]; linarith
  have hDq0R : (0 : ℝ) ≤ W.Dq := by exact_mod_cast hDq0
  have hdmR : ((W.Hs : ℝ) - W.Hm) / (1 / 50) ≤ W.Dq := by
    have := (Rat.cast_le (K := ℝ)).2 hdm; push_cast at this; linarith
  have hdgR : ((W.Hs : ℝ) - W.Hg) / (3 / 100) ≤ W.Dq := by
    have := (Rat.cast_le (K := ℝ)).2 hdg; push_cast at this; linarith
  by_cases hv0 : v = 0
  · subst hv0
    rw [show rotF τ 0 = 0 by simpa using rotF_sub τ 0 0]
    simp [Zr, Yr, cubic]
  have hY0 : 0 ≤ Yr v := (Xr_nonneg hv).trans (Xr_le_Yr hv)
  have hYp := Yr_pos_of_ne hv hv0
  have hZp := Zr_pos_of_ne hv hv0
  have hsqrt : Real.sqrt (Yr v) ≤ s * T.U :=
    sqrt_le_of hsR.le hU0R (hY.trans (by gcongr))
  have hw := hv.rotF τ
  have hw0 := rotF_ne τ hv hv0
  have ht := tYZ_rotF τ hv
  rcases le_or_gt (tYZ v) (2 / 100) with h1 | h1
  · have hC := hO.small hw hw0 (by rw [ht]; exact h1)
    rw [Yr_rotF τ hv, Zr_rotF τ hv] at hC
    have hh := heat_c (by norm_num) hZp.le hC hsqrt
    rw [hHsR]
    nlinarith [mul_nonneg hDq0R hY0]
  have hZ50 : 2 / 100 * Zr v < Yr v := by
    have := h1; unfold tYZ at this; rwa [lt_div_iff₀ hZp] at this
  rcases le_or_gt (tYZ v) (3 / 100) with h2 | h2
  · have hC := hO.aligned hw hw0 (by rw [ht]; exact h1) (by rw [ht]; exact h2)
    rw [Yr_rotF τ hv, Zr_rotF τ hv] at hC
    have hh := heat_c (by norm_num) hZp.le hC hsqrt
    rw [← hHmR] at hh
    exact debit_step (a := 2 / 100) (by norm_num)
      (by rw [show (2 / 100 : ℝ) = 1 / 50 by norm_num]; exact hdmR) hDq0R hZp.le hZ50 hh
  · have hZ3 : 3 / 100 * Zr v < Yr v := by
      have := h2; unfold tYZ at this; rwa [lt_div_iff₀ hZp] at this
    have hC := hO.kappa hw
    rw [Yr_rotF τ hv, Zr_rotF τ hv] at hC
    have hh := heat_c (by norm_num [κ₀]) hZp.le hC hsqrt
    rw [← hHgR] at hh
    exact debit_step (by norm_num) hdgR hDq0R hZp.le hZ3 hh

end Com

end Forced

end OVNS
