import OddViscousNS.Quant.Arith.Resonant.Orbit
import OddViscousNS.Sobolev

/-!
# Sorting, the two Cauchy–Schwarz steps, and Sobolev interpolation

* `sorted_sum_le`: a nonnegative symmetric summable function of the legs is at most six times its
  sum over the sorted fibres `∑_n ∑_{k ∈ SFib n} f(−k−n, k)`.
* `fibre_cauchy`: `∑_{k ∈ SFib n} γ a_m b_k ≤ √W(n) √(∑_{fibre} a_m² b_k²)`.
* `output_cauchy`: `∑_n c_n √(∑_{fibre} a_m² b_k²) ≤ ‖c‖_{ℓ²} ‖a‖_{ℓ²} ‖b‖_{ℓ²}`.
* `hnorm_interp`: `‖F‖²_{1+σ/2} ≤ ‖F‖₁^{2−σ} ‖F‖₂^σ` for `0 ≤ σ ≤ 1`.
* `fibre_norm_le`: on the fibre `|n| ≤ 2|k|`.
-/

open Finset

namespace OVNS.Quant

/-- The pair `(m, k)` is sorted: `|m| ≤ |k| ≤ |−(m+k)|`, all three legs fast. -/
private def Srt (y : Mode × Mode) : Prop :=
  absk y.1 ≤ absk y.2 ∧ absk y.2 ≤ absk (-(y.1 + y.2)) ∧ (-(y.1 + y.2)) 2 ≠ 0 ∧ y.2 2 ≠ 0 ∧
    y.1 2 ≠ 0

open Classical in
/-- The restriction of `f` to sorted pairs. -/
private noncomputable def srtPart (f : Mode × Mode → ℝ) (y : Mode × Mode) : ℝ :=
  if Srt y then f y else 0

private lemma srtPart_nonneg {f : Mode × Mode → ℝ} (hf0 : ∀ x, 0 ≤ f x) (y : Mode × Mode) :
    0 ≤ srtPart f y := by
  unfold srtPart; split_ifs
  · exact hf0 y
  · exact le_rfl

private lemma srtPart_le {f : Mode × Mode → ℝ} (hf0 : ∀ x, 0 ≤ f x) (y : Mode × Mode) :
    srtPart f y ≤ f y := by
  unfold srtPart; split_ifs
  · exact le_rfl
  · exact hf0 y

private lemma srt_of {u v w : Mode} (huvw : u + v + w = 0) (h1 : absk u ≤ absk v)
    (h2 : absk v ≤ absk w) (hu : u 2 ≠ 0) (hv : v 2 ≠ 0) (hw : w 2 ≠ 0) : Srt (u, v) := by
  have e : -(u + v) = w := by linear_combination -huvw
  exact ⟨h1, by simpa only [e] using h2, by simpa only [e] using hw, hv, hu⟩

/-- The six relabellings of a triad. -/
private def perm6 : Fin 6 → Equiv.Perm (Mode × Mode) :=
  ![1, rho, rho * rho, iota, rho * iota, iota * rho]

private lemma rho_apply' (y : Mode × Mode) : rho y = (y.2, -(y.1 + y.2)) := rfl

private lemma iota_apply' (y : Mode × Mode) : iota y = (y.1, -(y.1 + y.2)) := rfl

private lemma exists_sorted (x : Mode × Mode) (hx : ∀ j, legs x j 2 ≠ 0) :
    ∃ i, Srt (perm6 i x) := by
  obtain ⟨p, q⟩ := x
  have hp : p 2 ≠ 0 := hx 0
  have hq : q 2 ≠ 0 := hx 1
  have hr : (-(p + q)) 2 ≠ 0 := hx 2
  have hs : p + q + -(p + q) = 0 := by abel
  have e0 : perm6 0 (p, q) = (p, q) := rfl
  have e1 : perm6 1 (p, q) = (q, -(p + q)) := rfl
  have e2 : perm6 2 (p, q) = (-(p + q), p) := by
    simp only [perm6, Matrix.cons_val, Equiv.Perm.mul_apply, rho_apply']
    exact Prod.ext rfl (by simp only; abel)
  have e3 : perm6 3 (p, q) = (p, -(p + q)) := rfl
  have e4 : perm6 4 (p, q) = (-(p + q), q) := by
    simp only [perm6, Matrix.cons_val, Equiv.Perm.mul_apply, rho_apply', iota_apply']
    exact Prod.ext rfl (by simp only; abel)
  have e5 : perm6 5 (p, q) = (q, p) := by
    simp only [perm6, Matrix.cons_val, Equiv.Perm.mul_apply, rho_apply', iota_apply']
    exact Prod.ext rfl (by simp only; abel)
  rcases le_total (absk p) (absk q) with hab | hab <;>
    rcases le_total (absk q) (absk (-(p + q))) with hbc | hbc <;>
    rcases le_total (absk p) (absk (-(p + q))) with hac | hac
  · exact ⟨0, e0 ▸ srt_of hs hab hbc hp hq hr⟩
  · exact ⟨0, e0 ▸ srt_of hs hab hbc hp hq hr⟩
  · exact ⟨3, e3 ▸ srt_of (by abel) hac hbc hp hr hq⟩
  · exact ⟨2, e2 ▸ srt_of (by abel) hac hab hr hp hq⟩
  · exact ⟨5, e5 ▸ srt_of (by abel) hab hac hq hp hr⟩
  · exact ⟨1, e1 ▸ srt_of (by abel) hbc hac hq hr hp⟩
  · exact ⟨4, e4 ▸ srt_of (by abel) hbc hab hr hq hp⟩
  · exact ⟨4, e4 ▸ srt_of (by abel) hbc hab hr hq hp⟩

/-- Sorting: every ordered triad has a sorted relabelling; the sorted fibres cover with
multiplicity at most six. -/
theorem sorted_sum_le {f : Mode × Mode → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hfs : Summable f)
    (hsym : ∀ x, f (rho x) = f x ∧ f (iota x) = f x)
    (hfast : ∀ x, (∃ j, legs x j 2 = 0) → f x = 0) :
    ∑' x, f x ≤ 6 * ∑' n : Mode, ∑' k : Mode, if SFib n k then f (-k - n, k) else 0 := by
  have hSs : Summable (srtPart f) :=
    Summable.of_nonneg_of_le (srtPart_nonneg hf0) (srtPart_le hf0) hfs
  have hfP : ∀ x i, f (perm6 i x) = f x := by
    intro x i
    fin_cases i <;>
      simp [perm6, Equiv.Perm.mul_apply, (hsym _).1, (hsym _).2]
  have hpt : ∀ x, f x ≤ ∑ i, srtPart f (perm6 i x) := by
    intro x
    by_cases h0 : f x = 0
    · rw [h0]; exact Finset.sum_nonneg fun i _ => srtPart_nonneg hf0 _
    have hx : ∀ j, legs x j 2 ≠ 0 := fun j hj => h0 (hfast x ⟨j, hj⟩)
    obtain ⟨i, hi⟩ := exists_sorted x hx
    calc f x = srtPart f (perm6 i x) := by rw [srtPart, ite_eq_left hi, hfP]
      _ ≤ _ := Finset.single_le_sum (fun j _ => srtPart_nonneg hf0 (perm6 j x))
          (Finset.mem_univ i)
  have hPs : ∀ i, Summable fun x => srtPart f (perm6 i x) := fun i =>
    (perm6 i).summable_iff.mpr hSs
  have h1 : ∑' x, f x ≤ 6 * ∑' y, srtPart f y := by
    calc ∑' x, f x ≤ ∑' x, ∑ i, srtPart f (perm6 i x) :=
          hfs.tsum_le_tsum hpt (summable_sum fun i _ => hPs i)
      _ = ∑ i, ∑' x, srtPart f (perm6 i x) := Summable.tsum_finsetSum fun i _ => hPs i
      _ = ∑ _i : Fin 6, ∑' y, srtPart f y :=
          Finset.sum_congr rfl fun i _ => (perm6 i).tsum_eq (srtPart f)
      _ = 6 * ∑' y, srtPart f y := by simp
  let e : Equiv.Perm (Mode × Mode) :=
    Function.Involutive.toPerm (fun p => (-p.2 - p.1, p.2)) fun p => Prod.ext (by simp) rfl
  have he : ∀ n k, srtPart f (e (n, k)) = if SFib n k then f (-k - n, k) else 0 := by
    intro n k
    have hn : -((-k - n) + k) = n := by abel
    have hiff : Srt (e (n, k)) ↔ SFib n k := by
      show Srt (-k - n, k) ↔ _
      simp only [Srt, SFib, hn]
    by_cases h : SFib n k
    · rw [srtPart, ite_eq_left (hiff.mpr h), ite_eq_left h]; rfl
    · rw [srtPart, ite_eq_right (fun h' => h (hiff.mp h')), ite_eq_right h]
  have h2 : ∑' y, srtPart f y = ∑' n : Mode, ∑' k : Mode,
      if SFib n k then f (-k - n, k) else 0 := by
    rw [← e.tsum_eq (srtPart f)]
    rw [Summable.tsum_prod (f := fun p => srtPart f (e p)) (e.summable_iff.mpr hSs)]
    simp only [he]
  rw [← h2]; exact h1

/-- On the sorted fibre, `|n| ≤ 2 |k|` and `0 < |m|`. -/
theorem fibre_norm_le {n k : Mode} (h : SFib n k) :
    absk n ≤ 2 * absk k ∧ 0 < absk (-k - n) ∧ 0 < absk k ∧ 0 < absk n := by
  obtain ⟨h1, -, hn, hk, hm⟩ := h
  have pos : ∀ x : Mode, x 2 ≠ 0 → 0 < absk x := fun x hx =>
    lt_of_lt_of_le one_pos (one_le_absk fun h0 => hx (by simp [h0]))
  refine ⟨?_, pos _ hm, pos _ hk, pos _ hn⟩
  have e : n = -((-k - n) + k) := by abel
  calc absk n = absk ((-k - n) + k) := by rw [e, absk_neg]; congr 1; abel
    _ ≤ absk (-k - n) + absk k := absk_add_le _ _
    _ ≤ 2 * absk k := by linarith

/-- Fixed-output Cauchy–Schwarz with the weight `W(n)`. -/
theorem fibre_cauchy (n : Mode) {a b : Mode → ℝ} (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (hs : Summable fun k => if SFib n k then a (-k - n) ^ 2 * b k ^ 2 else 0) :
    ∑' k, (if SFib n k then gammaR ![-k - n, k, n] * a (-k - n) * b k else 0) ≤
      Real.sqrt (Wfib n) * Real.sqrt (∑' k, if SFib n k then a (-k - n) ^ 2 * b k ^ 2 else 0) := by
  have _ := And.intro ha (And.intro hb hs)
  set S := (finite_ball (absk n)).toFinset
  have hS : ∀ k ∉ S, ¬ SFib n k := fun k hk h => hk (by simpa [S] using h.2.1)
  unfold Wfib
  rw [tsum_eq_sum (s := S) (fun k hk => ite_eq_right (hS k hk)),
    tsum_eq_sum (s := S) (fun k hk => ite_eq_right (hS k hk)),
    tsum_eq_sum (s := S) (fun k hk => ite_eq_right (hS k hk))]
  calc ∑ k ∈ S, (if SFib n k then gammaR ![-k - n, k, n] * a (-k - n) * b k else 0)
      = ∑ k ∈ S, (if SFib n k then gammaR ![-k - n, k, n] else 0) *
          (if SFib n k then a (-k - n) * b k else 0) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        split_ifs <;> ring
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by
        congr 1 <;> congr 1 <;> refine Finset.sum_congr rfl fun k _ => ?_ <;> split_ifs <;> ring

/-- Cauchy–Schwarz for nonnegative real series. -/
private lemma cs_tsum_nonneg {a b : Mode → ℝ} (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (ha2 : Summable fun k => a k ^ 2) (hb2 : Summable fun k => b k ^ 2) :
    ∑' k, a k * b k ≤ Real.sqrt (∑' k, a k ^ 2) * Real.sqrt (∑' k, b k ^ 2) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have ha2' : Summable fun k => a k ^ (2 : ℝ) := by simpa only [Real.rpow_two] using ha2
  have hb2' : Summable fun k => b k ^ (2 : ℝ) := by simpa only [Real.rpow_two] using hb2
  have h := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg hpq ha hb ha2' hb2'
  simpa only [Real.rpow_two, Real.sqrt_eq_rpow, one_div] using h

/-- Output Cauchy–Schwarz. -/
theorem output_cauchy {a b c : Mode → ℝ} (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (hc : ∀ k, 0 ≤ c k) (hsa : Summable fun k => a k ^ 2) (hsb : Summable fun k => b k ^ 2)
    (hsc : Summable fun k => c k ^ 2) :
    ∑' n, c n * Real.sqrt (∑' k, if SFib n k then a (-k - n) ^ 2 * b k ^ 2 else 0) ≤
      Real.sqrt (∑' k, c k ^ 2) * Real.sqrt (∑' k, a k ^ 2) * Real.sqrt (∑' k, b k ^ 2) := by
  have _ := And.intro ha hb
  let G : Mode × Mode → ℝ := fun p => if SFib p.1 p.2 then a (-p.2 - p.1) ^ 2 * b p.2 ^ 2 else 0
  have hG0 : ∀ p, 0 ≤ G p := fun p => by
    simp only [G]; split_ifs
    · positivity
    · exact le_rfl
  let e : Equiv.Perm (Mode × Mode) :=
    Function.Involutive.toPerm (fun p => (-p.2 - p.1, p.2)) fun p => Prod.ext (by simp) rfl
  let H : Mode × Mode → ℝ := fun p => a p.1 ^ 2 * b p.2 ^ 2
  have hH : Summable H :=
    Summable.mul_of_nonneg (f := fun k => a k ^ 2) (g := fun k => b k ^ 2) hsa hsb
      (fun k => sq_nonneg (a k)) (fun k => sq_nonneg (b k))
  have hHe : Summable fun p => H (e p) := e.summable_iff.mpr hH
  have hGH : ∀ p, G p ≤ H (e p) := fun p => by
    simp only [G, H]; split_ifs
    · exact le_rfl
    · positivity
  have hGs : Summable G := Summable.of_nonneg_of_le hG0 hGH hHe
  have hT : Summable fun n => ∑' k, G (n, k) := hGs.prod
  have hTle : ∑' n, ∑' k, G (n, k) ≤ (∑' k, a k ^ 2) * ∑' k, b k ^ 2 := by
    rw [← hGs.tsum_prod]
    calc ∑' p, G p ≤ ∑' p, H (e p) := hGs.tsum_le_tsum hGH hHe
      _ = ∑' p, H p := e.tsum_eq H
      _ = _ := by
        rw [tsum_mul_tsum_of_summable_norm (by simpa only [Real.norm_of_nonneg (sq_nonneg _)]
          using hsa) (by simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hsb)]
  have hT0 : ∀ n, 0 ≤ ∑' k, G (n, k) := fun n => tsum_nonneg fun k => hG0 _
  have hsq : ∀ n, Real.sqrt (∑' k, G (n, k)) ^ 2 = ∑' k, G (n, k) := fun n =>
    Real.sq_sqrt (hT0 n)
  have key := cs_tsum_nonneg (a := c) (b := fun n => Real.sqrt (∑' k, G (n, k))) hc
    (fun n => Real.sqrt_nonneg _) hsc (by simpa only [hsq] using hT)
  simp only [hsq] at key
  calc _ ≤ _ := key
    _ ≤ Real.sqrt (∑' k, c k ^ 2) * Real.sqrt ((∑' k, a k ^ 2) * ∑' k, b k ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hTle) (Real.sqrt_nonneg _)
    _ = _ := by rw [Real.sqrt_mul (tsum_nonneg fun k => sq_nonneg _), mul_assoc]

/-- Sobolev interpolation `‖F‖²_{1+σ/2} ≤ ‖F‖₁^{2−σ} ‖F‖₂^σ`. -/
theorem hnorm_interp {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ 1) {F : Field} (hF : InH 2 F) :
    hnorm (1 + σ / 2) F ^ 2 ≤ hnorm 1 F ^ (2 - σ) * hnorm 2 F ^ σ := by
  rcases h0.eq_or_lt with rfl | hσ
  · norm_num
  set α : ℝ := (2 - σ) / 2 with hα
  set β : ℝ := σ / 2 with hβ
  have hα0 : 0 < α := by rw [hα]; linarith
  have hβ0 : 0 < β := by rw [hβ]; linarith
  have hαβ : α + β = 1 := by rw [hα, hβ]; ring
  have hpq : (1 / α).HolderConjugate (1 / β) := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, by simpa only [one_div, inv_inv] using hαβ⟩
    rw [lt_one_div one_pos hα0, one_div_one]; linarith
  have hX : ∀ k, 0 ≤ ‖F k‖ ^ 2 := fun k => sq_nonneg _
  have hw : ∀ s k, 0 ≤ sobWeight s k * ‖F k‖ ^ 2 := fun s k =>
    mul_nonneg (sobWeight_nonneg s k) (hX k)
  have hpow : ∀ (t : ℝ) (ht : 0 < t) (s : ℝ) (k : Mode),
      ((sobWeight s k * ‖F k‖ ^ 2) ^ t) ^ (1 / t) = sobWeight s k * ‖F k‖ ^ 2 := fun t ht s k => by
    rw [← Real.rpow_mul (hw s k), mul_one_div_cancel ht.ne', Real.rpow_one]
  have hterm : ∀ k, sobWeight (1 + σ / 2) k * ‖F k‖ ^ 2 =
      (sobWeight 1 k * ‖F k‖ ^ 2) ^ α * (sobWeight 2 k * ‖F k‖ ^ 2) ^ β := fun k => by
    simp only [sobWeight]
    split_ifs with hk
    · simp [Real.zero_rpow hα0.ne']
    have hk0 : 0 < absk k := lt_of_lt_of_le one_pos (one_le_absk hk)
    rw [Real.mul_rpow (Real.rpow_nonneg hk0.le _) (hX k),
      Real.mul_rpow (Real.rpow_nonneg hk0.le _) (hX k), ← Real.rpow_mul hk0.le,
      ← Real.rpow_mul hk0.le]
    calc absk k ^ (2 * (1 + σ / 2)) * ‖F k‖ ^ 2
        = absk k ^ (2 * 1 * α + 2 * 2 * β) * (‖F k‖ ^ 2) ^ (α + β) := by
          rw [hαβ, Real.rpow_one]; congr 2; rw [hα, hβ]; ring
      _ = _ := by
          rw [Real.rpow_add hk0, Real.rpow_add' (hX k) (by rw [hαβ]; exact one_ne_zero)]; ring
  have hS1 : Summable fun k => ((sobWeight 1 k * ‖F k‖ ^ 2) ^ α) ^ (1 / α) := by
    simp only [hpow α hα0]; exact hF.mono (s := 1) (by norm_num)
  have hS2 : Summable fun k => ((sobWeight 2 k * ‖F k‖ ^ 2) ^ β) ^ (1 / β) := by
    simp only [hpow β hβ0]; exact hF
  have hH := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg hpq (fun k => Real.rpow_nonneg (hw 1 k) α)
    (fun k => Real.rpow_nonneg (hw 2 k) β) hS1 hS2
  simp only [hpow α hα0, hpow β hβ0, one_div_one_div, ← hterm] at hH
  have e1 : ∀ (s t : ℝ), (hnorm s F ^ 2) ^ t = hnorm s F ^ (2 * t) := fun s t => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hnorm_nonneg s F)]; norm_num
  rw [← hnorm_sq (hF.mono (s := 1 + σ / 2) (by linarith)),
    ← hnorm_sq (hF.mono (s := 1) (by norm_num)), ← hnorm_sq hF, e1, e1] at hH
  convert hH using 3 <;> simp only [hα, hβ] <;> ring

end OVNS.Quant
