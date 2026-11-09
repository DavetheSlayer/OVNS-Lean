import OddViscousNS.Closed.Forced.Moment.Master
import OddViscousNS.Closed.Forced.Moment.Exterior
import OddViscousNS.Closed.Forced.Moment.Lattice
import OddViscousNS.Closed.Forced.Moment.Params

/-!
# The small-moment cubic bound: `|C| ≤ .41034 √Y Z` on `0 < t ≤ .020`

Row `PSm`: `a = .18`, `bL = 0`, `λ = M₀ · 225/1849` (the tangent slope at `W = 1`),
`K = .41034²/1.18`, `W ∈ [1/2, 17/10]`, table part `J < 1024`.  Pointwise bound: exterior `W` by
`exterior_bound`; central `W` with `J < 1024` by the kernel table (coverage hypothesis `hcov` = `coverSm` of `Moment/Rows.lean`, `rangeOk_sound`);
central `W` with `J ≥ 1024` by the row prices (`g(C_h) ≤ M_mid` for `C_h ≥ 512`,
`g(C_l) ≤ .184833` for `C_l ≤ 90`, `g ≤ M₀`, `g(C_h) ≤ M_high` for `C_h ≥ 3600`), convexity in
`r = C_l/J` (`convex_r_bound`) and the six kernel checks (`SmallBig`, the `bigJ*` theorems of `Moment/Rows.lean`; `subdivOkR_sound`).
-/

open Set

namespace OVNS

namespace Forced

namespace Mom

private lemma gTableN_mid :
    gTableN.all (fun e => decide (e.1 < 512 ∨ e.2 ≤ 172754764)) = true := by
  decide +kernel

private lemma gTableN_lo90 :
    gTableN.all (fun e => decide (90 < e.1 ∨ e.2 ≤ 184833000)) = true := by
  decide +kernel

/-- Table prices: `g(C) ≤ M_mid` for `C ≥ 512` (for `C < 1024` only at table keys: the
non-representable `C = 4^a(8b+7)` carry the default price `M₀`). -/
theorem gOVNS_le_mid {C : ℕ} (hC : 512 ≤ C) (hk : C < 1024 → ∃ e ∈ gTableN, e.1 = C) :
    gOVNS C ≤ 172754764 / 1000000000 := by
  rcases lt_or_ge C 1024 with h | h
  · obtain ⟨e, he, rfl⟩ := hk h
    rw [gTable_eq_of_mem he]
    have h' := List.all_eq_true.mp gTableN_mid e he
    simp only [decide_eq_true_eq] at h'
    have h2 : e.2 ≤ 172754764 := by omega
    have h3 : (e.2 : ℝ) ≤ 172754764 := by exact_mod_cast h2
    exact div_le_div_of_nonneg_right h3 (by norm_num)
  · unfold gOVNS
    split_ifs <;> first | omega | norm_num

/-- Table prices: `g(C) ≤ .184833` for table keys `C ≤ 90`. -/
theorem gOVNS_le_lo90 {C : ℕ} (hC : C ≤ 90) (hk : ∃ e ∈ gTableN, e.1 = C) :
    gOVNS C ≤ 184833 / 1000000 := by
  obtain ⟨e, he, rfl⟩ := hk
  rw [gTable_eq_of_mem he]
  have h' := List.all_eq_true.mp gTableN_lo90 e he
  simp only [decide_eq_true_eq] at h'
  have h2 : e.2 ≤ 184833000 := by omega
  have h3 : (e.2 : ℝ) ≤ 184833000 := by exact_mod_cast h2
  calc (e.2 : ℝ) / 1000000000 ≤ 184833000 / 1000000000 :=
        div_le_div_of_nonneg_right h3 (by norm_num)
    _ = 184833 / 1000000 := by norm_num

/-- `g(C) ≤ M_high` for `C ≥ 3600`. -/
theorem gOVNS_le_high {C : ℕ} (hC : 3600 ≤ C) : gOVNS C ≤ 163043 / 1000000 := by
  unfold gOVNS
  split_ifs <;> first | omega | norm_num

/-- The coverage fact proved by the kernel certificates (`coverSm`). -/
def CoverSm : Prop :=
  ∀ Cl : ℕ, 1 ≤ Cl → Cl < 1024 → ∃ lo hi, lo ≤ Cl ∧ Cl < hi ∧ rangeOk PSm lo hi = true

/-- The six large-`J` kernel checks (`W ∈ [1/2, 17/10]`, fuel 22), with the small-moment
`λ = M₀·225/1849` and `K = .41034²/1.18`. -/
def SmallBig : Prop :=
  let a : ℚ := 18 / 100
  let lam : ℚ := 185955292 / 1000000000 * (225 / 1849)
  let K : ℚ := (41034 / 100000) ^ 2 / (118 / 100)
  let Mmid : ℚ := 172754764 / 1000000000
  let Mhigh : ℚ := 163043 / 1000000
  let L90 : ℚ := 184833 / 1000000
  let M0 : ℚ := 185955292 / 1000000000
  subdivOkR a L90 Mmid 0 lam K 22 (1 / 2) (17 / 10) = true ∧
  subdivOkR a L90 Mmid (1 / 2) lam K 22 (1 / 2) (17 / 10) = true ∧
  subdivOkR a M0 Mmid (91 / 7200) lam K 22 (1 / 2) (17 / 10) = true ∧
  subdivOkR a M0 Mmid (1 / 2) lam K 22 (1 / 2) (17 / 10) = true ∧
  subdivOkR a M0 Mhigh 0 lam K 22 (1 / 2) (17 / 10) = true ∧
  subdivOkR a M0 Mhigh (1 / 2) lam K 22 (1 / 2) (17 / 10) = true

/-- With `bL = 0` the pair value is the row-price expression at `r = C_l/J`. -/
private lemma rawR_zero_eq (a : ℝ) {Cl Ch : ℕ} (hJ : 0 < (Cl : ℝ) + Ch) (gl gh W : ℝ) :
    rawR a 0 Cl Ch gl gh W = rawRr a gl gh ((Cl : ℝ) / ((Cl : ℝ) + Ch)) W := by
  unfold rawR rawRr
  have h1 : 4 * a * (Cl : ℝ) / ((Cl : ℝ) + Ch) = 4 * a * ((Cl : ℝ) / ((Cl : ℝ) + Ch)) := by
    ring
  have h2 : 4 * a * (Ch : ℝ) / ((Cl : ℝ) + Ch) = 4 * a * (1 - (Cl : ℝ) / ((Cl : ℝ) + Ch)) := by
    field_simp
    ring
  rw [h1, h2]
  simp only [zero_div, add_zero, one_mul]

/-- The row-price bound from two endpoint kernel checks. -/
private lemma rowprice_bound {L H r0 r1 lam K : ℚ} (hL : 0 ≤ L) (hH : 0 ≤ H) (hr0 : 0 ≤ r0)
    (hr01 : r0 ≤ r1) (hr1 : r1 ≤ 1) (hlam : 0 ≤ lam)
    (h0 : subdivOkR (18 / 100) L H r0 lam K 22 (1 / 2) (17 / 10) = true)
    (h1 : subdivOkR (18 / 100) L H r1 lam K 22 (1 / 2) (17 / 10) = true)
    {gl gh r W : ℝ} (hgl : gl ≤ L) (hgh : gh ≤ H) (hr : r ∈ Icc (r0 : ℝ) r1)
    (hW : W ∈ Icc (1 / 2 : ℝ) (17 / 10)) :
    rawRr (18 / 100) gl gh r W - lam * (W - 1) < K := by
  have hW0 : (0 : ℝ) < W := by linarith [hW.1]
  have hr0' : (0 : ℝ) ≤ r0 := by exact_mod_cast hr0
  have hr1' : (r1 : ℝ) ≤ 1 := by exact_mod_cast hr1
  have hm := rawRr_mono_prices (a := 18 / 100) (W := W) (r := r) (by norm_num) hW0.le
    (hr0'.trans hr.1) (hr.2.trans hr1') hgl hgh
  have hc := convex_r_bound (a := 18 / 100) (by norm_num) hW0 (L := (L : ℝ)) (H := (H : ℝ))
    (by exact_mod_cast hL) (by exact_mod_cast hH) hr0' hr1' hr
  have hW' : W ∈ Icc (((1 / 2 : ℚ)) : ℝ) ((17 / 10 : ℚ) : ℝ) := by
    push_cast
    exact hW
  have e0 := subdivOkR_sound (by norm_num) hL hH hr0 (hr01.trans hr1) hlam (by norm_num) h0 hW'
  have e1 := subdivOkR_sound (by norm_num) hL hH (hr0.trans hr01) hr1 hlam (by norm_num) h1 hW'
  have ha : (((18 / 100 : ℚ)) : ℝ) = 18 / 100 := by push_cast; ring
  rw [ha] at e0 e1
  unfold rawRr at hm e0 e1 ⊢
  rcases max_choice ((L * W / (W + 4 * (18 / 100) * r0) +
    H * W / (W + 4 * (18 / 100) * (1 - r0))) / 2 : ℝ) ((L * W /
    (W + 4 * (18 / 100) * r1) + H * W / (W + 4 * (18 / 100) * (1 - r1))) / 2) with h | h
  · rw [h] at hc
    linarith
  · rw [h] at hc
    linarith

/-- Central `W`, large `J`: the row prices, convexity in `r` and the six kernel checks. -/
private lemma bigJ_case (hbig : SmallBig) {Cl Ch : ℕ} (h1 : 1 ≤ Cl) (hle : Cl ≤ Ch)
    (hJ : 1024 ≤ Cl + Ch) (hkl : Cl < 1024 → ∃ e ∈ gTableN, e.1 = Cl)
    (hkh : Ch < 1024 → ∃ e ∈ gTableN, e.1 = Ch) {W : ℝ} (hW : W ∈ Icc (1 / 2 : ℝ) (17 / 10)) :
    rawRr (18 / 100) (gOVNS Cl) (gOVNS Ch) ((Cl : ℝ) / ((Cl : ℝ) + Ch)) W -
      185955292 / 1000000000 * (225 / 1849) * (W - 1) < (41034 / 100000) ^ 2 / (118 / 100) := by
  simp only [SmallBig] at hbig
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hbig
  have hJr : (0 : ℝ) < (Cl : ℝ) + Ch := by positivity
  have hr0 : (0 : ℝ) ≤ (Cl : ℝ) / ((Cl : ℝ) + Ch) := by positivity
  have hr1 : (Cl : ℝ) / ((Cl : ℝ) + Ch) ≤ 1 / 2 := by
    rw [div_le_iff₀ hJr]
    have : (Cl : ℝ) ≤ Ch := by exact_mod_cast hle
    linarith
  have hmid : gOVNS Ch ≤ 172754764 / 1000000000 := gOVNS_le_mid (by omega) hkh
  rcases lt_or_ge (Cl + Ch) 7200 with h72 | h72
  · rcases le_or_gt Cl 90 with h90 | h90
    · have hlo := gOVNS_le_lo90 h90 (hkl (by omega))
      have key := rowprice_bound (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num)
        (by norm_num) b1 b2 (gl := gOVNS Cl) (gh := gOVNS Ch)
        (r := (Cl : ℝ) / ((Cl : ℝ) + Ch)) (by push_cast; exact hlo) (by push_cast; exact hmid)
        (by push_cast; exact ⟨hr0, hr1⟩) hW
      push_cast at key
      linarith
    · have hr0' : (91 / 7200 : ℝ) ≤ (Cl : ℝ) / ((Cl : ℝ) + Ch) := by
        rw [le_div_iff₀ hJr]
        have : (91 : ℝ) ≤ Cl := by exact_mod_cast h90
        have : (Cl : ℝ) + Ch < 7200 := by exact_mod_cast h72
        nlinarith
      have key := rowprice_bound (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) b3 b4 (gl := gOVNS Cl) (gh := gOVNS Ch)
        (r := (Cl : ℝ) / ((Cl : ℝ) + Ch))
        (by push_cast; exact (gOVNS_le_M₀ Cl).trans_eq (by norm_num [M₀]))
        (by push_cast; exact hmid) (by push_cast; exact ⟨hr0', hr1⟩) hW
      push_cast at key
      linarith
  · have hhigh : gOVNS Ch ≤ 163043 / 1000000 := gOVNS_le_high (by omega)
    have key := rowprice_bound (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num)
      (by norm_num) b5 b6 (gl := gOVNS Cl) (gh := gOVNS Ch)
      (r := (Cl : ℝ) / ((Cl : ℝ) + Ch))
      (by push_cast; exact (gOVNS_le_M₀ Cl).trans_eq (by norm_num [M₀]))
      (by push_cast; exact hhigh) (by push_cast; exact ⟨hr0, hr1⟩) hW
    push_cast at key
    linarith

/-- The pointwise bound for an ordered pair of output radii `C_l ≤ C_h`. -/
private lemma ordered_case (hcov : CoverSm) (hbig : SmallBig) {t : ℝ} (ht0 : 0 < t)
    (ht : t ≤ 2 / 100) {Cl Ch : ℕ} (h1 : 1 ≤ Cl) (hle : Cl ≤ Ch) (hmod : (Ch - Cl) % 4 = 0)
    (hkl : Cl < 1024 → ∃ e ∈ gTableN, e.1 = Cl) (hkh : Ch < 1024 → ∃ e ∈ gTableN, e.1 = Ch) :
    rawR (18 / 100) 0 Cl Ch (gOVNS Cl) (gOVNS Ch) (4 / (t * ((Cl : ℝ) + Ch))) -
      185955292 / 1000000000 * (225 / 1849) * (4 / (t * ((Cl : ℝ) + Ch)) - 1) ≤
      (41034 / 100000) ^ 2 / (118 / 100) := by
  have hJr : (0 : ℝ) < (Cl : ℝ) + Ch := by positivity
  set W : ℝ := 4 / (t * ((Cl : ℝ) + Ch)) with hWdef
  have hW0 : 0 < W := by positivity
  have hr0 : (0 : ℝ) ≤ (Cl : ℝ) / ((Cl : ℝ) + Ch) := by positivity
  have hr1 : (Cl : ℝ) / ((Cl : ℝ) + Ch) ≤ 1 := by
    rw [div_le_iff₀ hJr]
    have : (0 : ℝ) ≤ Ch := by positivity
    linarith
  by_cases hout : W < 1 / 2 ∨ 17 / 10 < W
  · rw [rawR_zero_eq _ hJr]
    unfold rawRr
    have key := exterior_bound (a := 18 / 100) (lam := 185955292 / 1000000000 * (225 / 1849))
      (K := (41034 / 100000) ^ 2 / (118 / 100)) (wlo := 1 / 2) (whi := 17 / 10) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [M₀]) (by norm_num [M₀])
      (by norm_num [M₀]) (by norm_num [M₀]) hW0 hout hr0 hr1 (gOVNS_nonneg Cl)
      (gOVNS_le_M₀ Cl) (gOVNS_nonneg Ch) (gOVNS_le_M₀ Ch) (le_refl 1) (le_refl 1)
    simpa only [one_mul] using key
  have hW : W ∈ Icc (1 / 2 : ℝ) (17 / 10) := by
    simp only [not_or, not_lt] at hout
    exact ⟨hout.1, hout.2⟩
  rcases lt_or_ge (Cl + Ch) 1024 with hJ | hJ
  · obtain ⟨lo, hi, hlo, hhi, hrg⟩ := hcov Cl h1 (by omega)
    have hWI : W ∈ Icc (wLo PSm Cl Ch : ℝ) (wHi PSm Cl Ch : ℝ) := by
      have e1 : (wLo PSm Cl Ch : ℝ) = max (1 / 2) (4 / ((1 / 50) * ((Cl : ℝ) + Ch))) := by
        simp only [wLo, PSm]
        push_cast
        rfl
      have e2 : (wHi PSm Cl Ch : ℝ) = 17 / 10 := by
        norm_num [wHi, PSm]
      rw [e1, e2]
      refine ⟨max_le hW.1 ?_, hW.2⟩
      rw [hWdef]
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact mul_le_mul_of_nonneg_right (by linarith) hJr.le
    have key := rangeOk_sound (P := PSm) (by norm_num [PSm]) (by norm_num [PSm])
      (by norm_num [PSm]) (by norm_num [PSm]) (by norm_num [PSm]) (by norm_num [PSm]) hrg hlo
      hhi h1 hle hJ hmod (hkl (by omega)) (hkh (by omega)) hWI
    have ea : ((PSm.a : ℚ) : ℝ) = 18 / 100 := by norm_num [PSm]
    have eb : ((PSm.bL : ℚ) : ℝ) = 0 := by norm_num [PSm]
    have el : ((PSm.lam : ℚ) : ℝ) = 185955292 / 1000000000 * (225 / 1849) := by norm_num [PSm]
    have eK : ((PSm.K : ℚ) : ℝ) = (41034 / 100000) ^ 2 / (118 / 100) := by norm_num [PSm]
    rw [ea, eb, el, eK] at key
    exact key.le
  · rw [rawR_zero_eq _ hJr]
    exact (bigJ_case hbig h1 hle hJ hkl hkh hW).le

/-- The small-moment pointwise bound. -/
theorem pointwise_small (hcov : CoverSm) (hbig : SmallBig) {t : ℝ} (ht0 : 0 < t)
    (ht : t ≤ 2 / 100) :
    PointwiseW gOVNS (18 / 100) 0 t (185955292 / 1000000000 * (225 / 1849))
      ((41034 / 100000) ^ 2 / (118 / 100)) := by
  intro p l hp hl hnc
  rw [Tpair_eq_rawR gOVNS ht0 hp hl hnc, Wpair_eq ht0]
  obtain ⟨hu, hv⟩ := ne_zero_of_nonColl hnc
  have hmod := nsq_mod_four p l
  have hk : ∀ z : Mode, nsq z < 1024 → ∃ e ∈ gTableN, e.1 = nsq z :=
    fun z hz ↦ mem_keys_of_rep3 hz (rep3_nsq hz)
  rcases le_total (nsq (p + l)) (nsq (p - l)) with h | h
  · exact ordered_case hcov hbig ht0 ht (one_le_nsq hu) h (by omega) (hk _) (hk _)
  · rw [rawR_symm, add_comm ((nsq (p + l) : ℕ) : ℝ)]
    exact ordered_case hcov hbig ht0 ht (one_le_nsq hv) h (by omega) (hk _) (hk _)

/-- `|C(w)| ≤ .41034 √Y Z` whenever `Y/Z ≤ .020`. -/
theorem cubic_le_small (hcov : CoverSm) (hbig : SmallBig) (hRB : RowBound gOVNS) {w : Field}
    (hw : Adm 2 w) (hw0 : w ≠ 0)
    (ht : tYZ w ≤ 2 / 100) :
    |cubic w| ≤ 41034 / 100000 * Real.sqrt (Yr w) * Zr w := by
  have hY := Yr_pos_of_ne hw hw0
  have hZ := Zr_pos_of_ne hw hw0
  have hpt := pointwise_small hcov hbig (div_pos hY hZ) ht
  have hc := cubic_le_moment hRB hw hw0 (by norm_num) le_rfl (by norm_num) (by norm_num) hpt
  have hrhs : 0 ≤ 41034 / 100000 * Real.sqrt (Yr w) * Zr w := by positivity
  have hsq : (41034 / 100000 * Real.sqrt (Yr w) * Zr w) ^ 2 =
      (1 + 18 / 100 + 0 * (Xr w / Yr w)) * ((41034 / 100000) ^ 2 / (118 / 100)) * Yr w *
        Zr w ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hY.le]
    ring
  rw [← hsq] at hc
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) hrhs two_ne_zero).1 hc

end Mom

end Forced

end OVNS
