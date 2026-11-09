import OddViscousNS.Closed.Forced.Check.Defs
import OddViscousNS.Closed.Forced.Support
import OddViscousNS.Closed.Forced.Laws
import OddViscousNS.Closed.Forced.Kinetic
import OddViscousNS.Closed.Cubic

/-!
# Soundness of the forced face checker

Every `Bool` check of `Forced/Check/Defs.lean` implies the corresponding real inequality, at the
level of the heat solution `v` (scale `s`, so that the certificate's `w`-cell `(B, E, m)` is the
`v`-cell `(s²B, s²E, m)`, the force bound is `‖g‖₂ ≤ f₀ s`, and `k = s κ₀`):

* `Supp.sound`: the shell inequality `(S)` for all `j ≥ 1` (direct checks + `support_of_finite`);
* `SFace.sound`: on the closed slope face, `−J₁ − m(Z + C) + ⟨R g, (I + m h)v⟩ < 0` for any `C`
  with `|C| ≤ κ₀ √Y Z` (the heat `H ≤ 1 − κ₀ √Y`, Young with the certified `ε`, the support
  inequality, and the affine face maximum);
* `KFace.sound`: on a kinetic face, `−J₁ + ⟨R g, v⟩ < 0`;
* `Term.sound`: on the terminal face, `−(Z + C) + ⟨R g, h v⟩ < 0`; `Term.heat`: the heat
  `H* Z ≤ Z + C` wherever `Y ≤ s² Y*`.
-/

open Set

namespace OVNS

namespace Forced

namespace Chk

theorem hq_cast (j : ℕ) : ((hq j : ℚ) : ℝ) = hmet j := by
  unfold hq hmet
  split_ifs <;> push_cast <;> ring

theorem Gq_cast (r m H ε c : ℚ) (j : ℕ) :
    ((Gq r m H ε c j : ℚ) : ℝ) = Fsh r m H ε j + c * hmet j := by
  unfold Gq Fsh
  push_cast
  rw [hq_cast]

/-- A checked support witness certifies `(S)` for every `j ≥ 1`. -/
theorem Supp.sound {w : Supp} (h : w.ok = true) :
    ∀ j : ℕ, 1 ≤ j → Fsh w.r w.m w.H w.ε j + w.c * hmet j ≤ w.M := by
  simp only [Supp.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨hr, hm⟩, hε⟩, hd⟩, hJ⟩, hΔ⟩, hfin⟩ := h
  refine support_of_finite (r := w.r) (m := w.m) (H := w.H) (ε := w.ε) (c := w.c) (M := w.M)
    (by exact_mod_cast hr) (by exact_mod_cast hm) (by exact_mod_cast hε.le)
    (by exact_mod_cast hd) hJ
    (by have h2 := (Rat.cast_le (K := ℝ)).2 hΔ; push_cast at h2; linarith) ?_
  intro j hj1 hjJ
  have hj := hfin (j - 1) (by omega)
  rw [show j - 1 + 1 = j by omega] at hj
  rw [← Gq_cast]
  exact_mod_cast hj

/-- The support inequality for an admissible field. -/
theorem Supp.apply {w : Supp} (h : w.ok = true) {v : Field} (hv : Adm 2 v) :
    -(w.r : ℝ) * J1r v - w.m * w.H * Zr v + w.ε * Nsq w.r w.m v ≤ w.M * Xr v - w.c * Yr v := by
  have h' := h
  simp only [Supp.ok, Bool.and_eq_true, decide_eq_true_eq] at h'
  obtain ⟨⟨⟨⟨⟨⟨hr, hm⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h'
  exact support_shells (by exact_mod_cast hr) (by exact_mod_cast hm) (Supp.sound h) hv

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

/-- The heat bound `H Z ≤ Z + C` from `√Y ≤ s q`, `H = 1 − k q`, `k = s κ₀`. -/
private lemma heat_of {Y Z C s q k H : ℝ} (hk : k = s * κ₀) (hH : H = 1 - k * q)
    (hZ : 0 ≤ Z) (hC : |C| ≤ κ₀ * Real.sqrt Y * Z) (hsq : Real.sqrt Y ≤ s * q) :
    H * Z ≤ Z + C := by
  have hκ : (0 : ℝ) ≤ κ₀ := by norm_num [κ₀]
  have h1 : κ₀ * Real.sqrt Y * Z ≤ κ₀ * (s * q) * Z :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hκ) hZ
  have h2 := neg_abs_le C
  rw [hH, hk]
  nlinarith

/-- Slope face: the normal derivative of `X + mY` is strictly negative on the closed face. -/
theorem SFace.sound {k f0 s : ℚ} (hs : 0 < s) (hk : (k : ℝ) = s * κ₀) {F : SFace}
    (hF : F.ok k f0 = true) {v g : Field} (hv : Adm 2 v) (hg : Adm 2 g)
    (hgn : hnorm 2 g ≤ f0 * s) (τ : ℝ) {C : ℝ} (hC : |C| ≤ κ₀ * Real.sqrt (Yr v) * Zr v)
    (hY : Yr v ∈ Icc ((s : ℝ) ^ 2 * F.B) ((s : ℝ) ^ 2 * (F.B + 1 / 1000)))
    (hX : Xr v = (s : ℝ) ^ 2 * F.E - F.m * (Yr v - (s : ℝ) ^ 2 * F.B)) :
    -J1r v - F.m * (Zr v + C) + (wPair ωX v (rotF τ g) + F.m * wPair ωY v (rotF τ g)) < 0 := by
  simp only [SFace.ok, Bool.and_eq_true, decide_eq_true_eq] at hF
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hq0, hqsq⟩, hH⟩, hm0⟩, hr⟩, hmm⟩, hHH⟩, hsp⟩, hmar⟩ := hF
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hq0R : (0 : ℝ) ≤ F.q := by exact_mod_cast hq0
  have hqsqR : (F.B : ℝ) + 1 / 1000 ≤ (F.q : ℝ) ^ 2 := by
    have h2 := (Rat.cast_le (K := ℝ)).2 hqsq; push_cast at h2; linarith
  have hHR : (F.H : ℝ) = 1 - k * F.q := by exact_mod_cast hH
  have hm0R : (0 : ℝ) ≤ F.m := by exact_mod_cast hm0
  have hmarR : (0 : ℝ) < -(max (-(F.sp.c : ℝ) * F.B + F.sp.M * F.E)
      (-F.sp.c * (F.B + 1 / 1000) + F.sp.M * (F.E - F.m * (1 / 1000)))) -
      f0 ^ 2 / (4 * F.sp.ε) := by
    have h2 := (Rat.cast_lt (K := ℝ)).2 hmar; push_cast at h2; linarith
  have hε : (0 : ℝ) < F.sp.ε := by
    have h' := hsp
    simp only [Supp.ok, Bool.and_eq_true, decide_eq_true_eq] at h'
    exact_mod_cast h'.1.1.1.1.2
  have hX0 := Xr_nonneg hv
  have hXY := Xr_le_Yr hv
  have hYZ := Yr_le_Zr hv
  -- heat
  have hsqrt : Real.sqrt (Yr v) ≤ s * F.q :=
    sqrt_le_of hsR.le hq0R (hY.2.trans (by gcongr))
  have hheat := heat_of hk hHR (by linarith) hC hsqrt
  have hheat' : -(F.m : ℝ) * (Zr v + C) ≤ -F.m * F.H * Zr v := by nlinarith
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
  have haff := affine_le_max (a := -(F.sp.M : ℝ) * F.m - F.sp.c)
    (b := (F.sp.M : ℝ) * ((s : ℝ) ^ 2 * F.E) + F.sp.M * F.m * ((s : ℝ) ^ 2 * F.B)) hY.1 hY.2
  have hmax : max ((-(F.sp.M : ℝ) * F.m - F.sp.c) * ((s : ℝ) ^ 2 * F.B) +
      (F.sp.M * ((s : ℝ) ^ 2 * F.E) + F.sp.M * F.m * ((s : ℝ) ^ 2 * F.B)))
      ((-(F.sp.M : ℝ) * F.m - F.sp.c) * ((s : ℝ) ^ 2 * (F.B + 1 / 1000)) +
      (F.sp.M * ((s : ℝ) ^ 2 * F.E) + F.sp.M * F.m * ((s : ℝ) ^ 2 * F.B))) =
      (s : ℝ) ^ 2 * max (-(F.sp.c : ℝ) * F.B + F.sp.M * F.E)
      (-F.sp.c * (F.B + 1 / 1000) + F.sp.M * (F.E - F.m * (1 / 1000))) := by
    rw [mul_max_of_nonneg _ _ (by positivity)]
    congr 1 <;> ring
  rw [hmax] at haff
  have hfin : (s : ℝ) ^ 2 * (max (-(F.sp.c : ℝ) * F.B + F.sp.M * F.E)
      (-F.sp.c * (F.B + 1 / 1000) + F.sp.M * (F.E - F.m * (1 / 1000))) +
      f0 ^ 2 / (4 * F.sp.ε)) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) (by linarith)
  have hfs : ((f0 : ℝ) * s) ^ 2 / (4 * F.sp.ε) = (s : ℝ) ^ 2 * (f0 ^ 2 / (4 * F.sp.ε)) := by
    ring
  rw [hX] at hsupp
  nlinarith

/-- Kinetic face: `X` strictly decreases. -/
theorem KFace.sound {f0 s : ℚ} (hs : 0 < s) {F : KFace} (hF : F.ok f0 = true) {v g : Field}
    (hv : Adm 2 v) (hg : Adm 2 g) (hgn : hnorm 2 g ≤ f0 * s) (τ : ℝ)
    (hY : (s : ℝ) ^ 2 * F.B ≤ Yr v) (hX : Xr v = (s : ℝ) ^ 2 * F.E) :
    -J1r v + wPair ωX v (rotF τ g) < 0 := by
  simp only [KFace.ok, Bool.and_eq_true, decide_eq_true_eq] at hF
  obtain ⟨⟨hq0, hqsq⟩, hmar⟩ := hF
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hq0R : (0 : ℝ) ≤ F.qE := by exact_mod_cast hq0
  have hqsqR : (F.E : ℝ) ≤ (F.qE : ℝ) ^ 2 := by exact_mod_cast hqsq
  have hmarR : (0 : ℝ) < F.B - f0 * F.qE := by exact_mod_cast hmar
  have hYJ := Yr_le_J1r hv
  have hsqrt : Real.sqrt (Xr v) ≤ s * F.qE :=
    sqrt_le_of hsR.le hq0R (hX.le.trans (by gcongr))
  have hp := (le_abs_self _).trans (force_pair_X_le τ hg hv)
  have h1 : hnorm 2 g * Real.sqrt (Xr v) ≤ hnorm 2 g * (s * F.qE) :=
    mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)
  have h2 : hnorm 2 g * (s * F.qE) ≤ f0 * s * (s * F.qE) :=
    mul_le_mul_of_nonneg_right hgn (by positivity)
  have hfin : (s : ℝ) ^ 2 * (F.B - f0 * F.qE) > 0 := by positivity
  nlinarith

/-- The terminal heat (helper, used by `Term.sound`). -/
private theorem term_heat {k f0 s : ℚ} (hs : 0 < s) (hk : (k : ℝ) = s * κ₀) {t : Term}
    (ht : t.ok k f0 = true) {v : Field} (hv : Adm 2 v) {C : ℝ}
    (hC : |C| ≤ κ₀ * Real.sqrt (Yr v) * Zr v) (hY : Yr v ≤ (s : ℝ) ^ 2 * t.Y) :
    (t.H : ℝ) * Zr v ≤ Zr v + C := by
  simp only [Term.ok, Bool.and_eq_true, decide_eq_true_eq] at ht
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hq0, hqsq⟩, hH⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := ht
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hq0R : (0 : ℝ) ≤ t.q := by exact_mod_cast hq0
  have hqsqR : (t.Y : ℝ) ≤ (t.q : ℝ) ^ 2 := by exact_mod_cast hqsq
  have hHR : (t.H : ℝ) = 1 - k * t.q := by exact_mod_cast hH
  have hsqrt : Real.sqrt (Yr v) ≤ s * t.q :=
    sqrt_le_of hsR.le hq0R (hY.trans (by gcongr))
  exact heat_of hk hHR ((Xr_nonneg hv).trans ((Xr_le_Yr hv).trans (Yr_le_Zr hv))) hC hsqrt

/-- Terminal face: `Y` strictly decreases. -/
theorem Term.sound {k f0 s : ℚ} (hs : 0 < s) (hk : (k : ℝ) = s * κ₀) {t : Term}
    (ht : t.ok k f0 = true) {v g : Field} (hv : Adm 2 v) (hg : Adm 2 g)
    (hgn : hnorm 2 g ≤ f0 * s) (τ : ℝ) {C : ℝ} (hC : |C| ≤ κ₀ * Real.sqrt (Yr v) * Zr v)
    (hY : Yr v = (s : ℝ) ^ 2 * t.Y) (hX : Xr v ≤ (s : ℝ) ^ 2 * t.E) :
    -(Zr v + C) + wPair ωY v (rotF τ g) < 0 := by
  have hheat := term_heat hs hk ht hv hC hY.le
  simp only [Term.ok, Bool.and_eq_true, decide_eq_true_eq] at ht
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, hr⟩, hmm⟩, hHH⟩, hsp⟩, hmar⟩ := ht
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hmarR : (0 : ℝ) < t.sp.c * t.Y - max 0 (t.sp.M : ℝ) * t.E - f0 ^ 2 / (4 * t.sp.ε) := by
    have h2 := (Rat.cast_lt (K := ℝ)).2 hmar; push_cast at h2; linarith
  have hε : (0 : ℝ) < t.sp.ε := by
    have h' := hsp
    simp only [Supp.ok, Bool.and_eq_true, decide_eq_true_eq] at h'
    exact_mod_cast h'.1.1.1.1.2
  have hX0 := Xr_nonneg hv
  -- pairing
  have hN0 := Nsq_nonneg 0 1 v
  have hpair := force_pair_N_le τ hg hv le_rfl zero_le_one
  rw [zero_mul, zero_add, one_mul] at hpair
  have hpair2 : wPair ωY v (rotF τ g) ≤ (f0 * s) * Real.sqrt (Nsq 0 1 v) :=
    (le_abs_self _).trans (hpair.trans
      (mul_le_mul_of_nonneg_right hgn (Real.sqrt_nonneg _)))
  have hyoung := young_force (f := (f0 : ℝ) * s) hε (Real.sqrt_nonneg (Nsq 0 1 v))
  rw [Real.sq_sqrt hN0] at hyoung
  -- support
  have hsupp := Supp.apply hsp hv
  rw [hr, hmm, hHH] at hsupp
  push_cast at hsupp
  have hM1 : (t.sp.M : ℝ) * Xr v ≤ max 0 (t.sp.M : ℝ) * Xr v :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hX0
  have hM2 : max 0 (t.sp.M : ℝ) * Xr v ≤ max 0 (t.sp.M : ℝ) * ((s : ℝ) ^ 2 * t.E) :=
    mul_le_mul_of_nonneg_left hX (le_max_left _ _)
  have hfin : (s : ℝ) ^ 2 * (t.sp.c * t.Y - max 0 (t.sp.M : ℝ) * t.E - f0 ^ 2 / (4 * t.sp.ε))
      > 0 := mul_pos (by positivity) hmarR
  have hfs : ((f0 : ℝ) * s) ^ 2 / (4 * t.sp.ε) = (s : ℝ) ^ 2 * (f0 ^ 2 / (4 * t.sp.ε)) := by
    ring
  rw [hY] at hsupp
  nlinarith

/-- The terminal heat is valid throughout the region `Y ≤ s² Y*`. -/
theorem Term.heat {k f0 s : ℚ} (hs : 0 < s) (hk : (k : ℝ) = s * κ₀) {t : Term}
    (ht : t.ok k f0 = true) {v : Field} (hv : Adm 2 v) {C : ℝ}
    (hC : |C| ≤ κ₀ * Real.sqrt (Yr v) * Zr v) (hY : Yr v ≤ (s : ℝ) ^ 2 * t.Y) :
    (t.H : ℝ) * Zr v ≤ Zr v + C := by
  exact term_heat hs hk ht hv hC hY

end Chk

end Forced

end OVNS
