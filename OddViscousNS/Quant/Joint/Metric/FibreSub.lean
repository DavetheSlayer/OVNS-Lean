import OddViscousNS.Quant.Joint.Metric.FibreForms

/-!
# The subcritical rules of the fibered layer (step J5, node N1)

The rules of LOCAL457, Body 33 (`ℓ^{16/15} ⋆ ℓ^{16/9}`, `S ∈ H^{5/4}`) and of Bodies 38, 39
(`ℓ^r ⋆ ℓ^p`, `1/r = 1 − η/2`, `1/p = (1 + η)/2`, `S ∈ H^{1+ε}`, `η = ε/2`).  All of them are one
family, with a parameter `ε > 0`, `ε = 1/4` for the first: a weighted leaf `|p| S` with
`S ∈ H^{1+ε}` is `|p|^{−ε}` times an `ℓ²` sequence, and the kernel sums are
`∑ |p|^{−2−2ε} ≤ 9 + 4/ε`.

* `pos2_sub`: Body 39: `h ∈ H¹`, `|p| S`, the inverse-square exterior: `C ε^{−1/2} ‖h‖₁ ‖S‖_{1+ε}`.
  At `ε = 1/4` this is LOCAL457's `ℓ^{16/15} ⋆ ℓ^{16/9}`.
* `pos2_single`: Body 38, "a single weighted leaf and an inverse-first-power exterior": the third
  leaf is `ℓ¹`: `C ε^{−1/2} ‖S‖_{1+ε} W`.
* `pos2_pair_sub`: Body 38, "a distinct weighted pair and two such exteriors": `(C/ε) ‖S‖_{1+ε}²`.

The constant `ε^{−1/2}` is the one of the sources ("`C η^{−1/2}`", Bodies 38, 39).

**Not here:** the mixed pair of Body 38 ("one weighted leaf in `ℓ²` and one in `ℓ^p`", two
inverse-first-power exteriors).  Neither grouping of `FibreForms.lean` reaches it: `cs_mid` would
need `V · (z/J) ∈ L²` for `V ∈ L²`, which fails; `cs_out` with the `ℓ²` leaf against the rest has a
kernel sum that diverges in the vertical.  It needs that last grouping on each vertical, with the
fibre norms of the two exteriors: node N10, where it is used.
-/

open Finset

noncomputable section

namespace OVNS.Quant.Metric

variable {α β f₁ f₂ : Mode → ℝ} {A B U₁ U₂ W : ℝ} {ε : ℝ}

/-! ### A. The sum `∑ n^{−1−δ}` -/

/-- `(x+1)^{−1−δ} ≤ (x^{−δ} − (x+1)^{−δ})/δ`. -/
lemma rpow_telescope {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ) :
    (x + 1) ^ (-1 - δ) ≤ (x ^ (-δ) - (x + 1) ^ (-δ)) / δ := by
  set y := x + 1 with hy
  have hy0 : 0 < y := by positivity
  have hlog : 1 / y ≤ Real.log (y / x) := by
    have h := Real.one_sub_inv_le_log_of_pos (x := y / x) (by positivity)
    have e : 1 - (y / x)⁻¹ = 1 / y := by
      field_simp
      simp [hy]
    rwa [e] at h
  have hexp : 1 + δ / y ≤ (y / x) ^ δ := by
    rw [Real.rpow_def_of_pos (by positivity)]
    have h1 := Real.add_one_le_exp (δ / y)
    have h2 : δ / y ≤ Real.log (y / x) * δ := by
      have := mul_le_mul_of_nonneg_right hlog hδ.le
      calc δ / y = 1 / y * δ := by ring
        _ ≤ _ := this
    have h3 := Real.exp_le_exp.2 h2
    linarith
  have e1 : y ^ (-1 - δ) = y ^ (-δ) * (1 / y) := by
    rw [show -1 - δ = -δ + -1 by ring, Real.rpow_add hy0, Real.rpow_neg_one, one_div]
  have e2 : x ^ (-δ) = y ^ (-δ) * (y / x) ^ δ := by
    rw [Real.div_rpow hy0.le hx.le, Real.rpow_neg hy0.le, Real.rpow_neg hx.le]
    have : y ^ δ ≠ 0 := (Real.rpow_pos_of_pos hy0 δ).ne'
    field_simp
  rw [le_div_iff₀ hδ, e1, e2]
  have hp : 0 ≤ y ^ (-δ) := Real.rpow_nonneg hy0.le _
  have h3 := mul_le_mul_of_nonneg_left hexp hp
  have e3 : y ^ (-δ) * (1 + δ / y) = y ^ (-δ) + y ^ (-δ) * (1 / y) * δ := by ring
  linarith

/-- `∑_{n<N} (n+1)^{−1−δ} ≤ 1 + 1/δ`. -/
lemma sum_rpow_le {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (-1 - δ) ≤ 1 + 1 / δ := by
  have key : ∀ m : ℕ, ∑ n ∈ Finset.range (m + 1), ((n : ℝ) + 1) ^ (-1 - δ) ≤
      1 + 1 / δ - ((m : ℝ) + 1) ^ (-δ) / δ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have h := rpow_telescope (x := (m : ℝ) + 1) (by positivity) hδ
      push_cast at ih ⊢
      have e : ((m : ℝ) + 1) ^ (-δ) / δ - ((m : ℝ) + 1 + 1) ^ (-δ) / δ =
          (((m : ℝ) + 1) ^ (-δ) - ((m : ℝ) + 1 + 1) ^ (-δ)) / δ := by ring
      linarith
  rcases N with _ | m
  · simp
    positivity
  · have h : 0 ≤ ((m : ℝ) + 1) ^ (-δ) / δ := by positivity
    linarith [key m]

/-! ### B. The fibre sum at the exponent `2 + δ` -/

/-- `|k|^{−σ}`, zero at the origin, for `σ ≠ 0`. -/
def wr (σ : ℝ) (k : Mode) : ℝ := (absk k)⁻¹ ^ σ

lemma wr_nonneg (σ : ℝ) (k : Mode) : 0 ≤ wr σ k :=
  Real.rpow_nonneg (inv_nonneg.2 (absk_nonneg k)) σ

lemma wr_neg (σ : ℝ) (k : Mode) : wr σ (-k) = wr σ k := by simp only [wr, absk_neg]

/-- **The inverse sum at the exponent `2 + δ`**: `∑ |j|^{−2−δ} ≤ 9 + 8/δ` (Body 39: "bounded by
`C/η` before the root"). -/
theorem fib_wr {δ : ℝ} (hδ : 0 < δ) : Fib (wr (2 + δ)) (9 + 8 / δ) := by
  have hσ : 0 ≤ 2 + δ := by linarith
  refine fib_of_shell (ψ₀ := 1) (ψ := fun n => ((n : ℝ) + 1) ^ (-(2 + δ))) (wr_nonneg _)
    (fun k => ?_) (fun n k h => ?_) fun N => ?_
  · exact Real.rpow_le_one (inv_nonneg.2 (absk_nonneg k)) (inv_absk_le_one k) hσ
  · have h1 := inv_absk_le_of_sq h
    have h2 := Real.rpow_le_rpow (inv_nonneg.2 (absk_nonneg k)) h1 hσ
    refine h2.trans (le_of_eq ?_)
    rw [Real.rpow_neg (by positivity), Real.inv_rpow (by positivity)]
  · have e : ∀ n ∈ Finset.range N, 8 * ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ (-(2 + δ)) =
        8 * ((n : ℝ) + 1) ^ (-1 - δ) := fun n _ => by
      have h0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [mul_assoc, ← Real.rpow_one_add' h0.le (by linarith)]
      congr 2
      ring
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
    have h := sum_rpow_le hδ N
    have e8 : 8 * (1 + 1 / δ) = 8 + 8 / δ := by ring
    linarith

/-- `x² y^{2ε} ≤ x^{2+2ε} + y^{2+2ε}`: the larger length is discarded. -/
lemma two_rpow_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hε : 0 < ε) :
    x ^ 2 * y ^ (2 * ε) ≤ x ^ (2 + 2 * ε) + y ^ (2 + 2 * ε) := by
  have h2 : (0 : ℝ) < 2 * ε := by positivity
  have hx' : x ^ (2 + 2 * ε) = x ^ 2 * x ^ (2 * ε) := by
    rw [Real.rpow_add' hx (by positivity), Real.rpow_two]
  have hy' : y ^ (2 + 2 * ε) = y ^ 2 * y ^ (2 * ε) := by
    rw [Real.rpow_add' hy (by positivity), Real.rpow_two]
  have p1 : 0 ≤ x ^ (2 * ε) := Real.rpow_nonneg hx _
  have p2 : 0 ≤ y ^ (2 * ε) := Real.rpow_nonneg hy _
  rw [hx', hy']
  rcases le_total x y with h | h
  · have := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx h 2) p2
    have h3 : 0 ≤ x ^ 2 * x ^ (2 * ε) := by positivity
    linarith
  · have := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hy h h2.le) (sq_nonneg x)
    have h3 : 0 ≤ y ^ 2 * y ^ (2 * ε) := by positivity
    linarith

/-- The inverse weight `|a|^{−ε}` on the slow modes. -/
def sw (ε : ℝ) (a : Mode) : ℝ := sl (fun k => (absk k)⁻¹ ^ ε) a

lemma sw_nonneg (ε : ℝ) (a : Mode) : 0 ≤ sw ε a :=
  sl_nonneg (fun k => Real.rpow_nonneg (inv_nonneg.2 (absk_nonneg k)) ε) a

/-- A nonnegative slow mean-zero sequence of `H^{1+ε}` norm at most `U`. -/
structure SlowHs (ε : ℝ) (f : Mode → ℝ) (U : ℝ) : Prop where
  nn : ∀ p, 0 ≤ f p
  slow : ∀ p, p 2 ≠ 0 → f p = 0
  mean : f 0 = 0
  grad : L2B (fun p => absk p ^ (1 + ε) * f p) U

lemma SlowHs.sw_mul (h : SlowHs ε f₁ U₁) (a : Mode) :
    sw ε a * (absk a ^ (1 + ε) * f₁ a) = absk a * f₁ a := by
  by_cases h2 : a 2 = 0
  · by_cases h0 : a = 0
    · simp [h0, h.mean]
    · have hp : 0 < absk a := lt_of_lt_of_le one_pos (one_le_absk h0)
      simp only [sw, sl, h2, ite_true]
      rw [Real.inv_rpow hp.le, Real.rpow_add hp, Real.rpow_one]
      have : absk a ^ ε ≠ 0 := (Real.rpow_pos_of_pos hp ε).ne'
      field_simp
  · simp [h.slow a h2]

/-- The sum of the two inverse weights at a fixed slow pair. -/
lemma kernel_two {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hε : 0 < ε) :
    x ^ 2 * (y ^ ε) ^ 2 ≤ x ^ (2 + 2 * ε) + y ^ (2 + 2 * ε) := by
  have e : (y ^ ε) ^ 2 = y ^ (2 * ε) := by
    rw [mul_comm, Real.rpow_mul hy, Real.rpow_two]
  rw [e]
  exact two_rpow_le hx hy hε

/-! ### C. The kernels -/

/-- The slow sum at the exponent `2 + 2ε`. -/
lemma fib_eps (hε : 0 < ε) : Fib (wr (2 + 2 * ε)) (9 + 4 / ε) := by
  have h := fib_wr (δ := 2 * ε) (by positivity)
  have e : (8 : ℝ) / (2 * ε) = 4 / ε := by
    field_simp
    ring
  rwa [e] at h

lemma wr_inv_eq (ε : ℝ) (a : Mode) : wr (2 + 2 * ε) a = (absk a)⁻¹ ^ (2 + 2 * ε) := rfl

/-- `∑_a |a|^{−2ε} |t − a|⁻² ≤ 2 (9 + 4/ε)`, for every `t`: the sum that replaces
`ℓ^r ⋆ ℓ^p ⊂ ℓ²` (Bodies 38, 39). -/
lemma kernel_eps (hε : 0 < ε) (t : Mode) :
    SB (fun a : Mode => (sw ε a * (absk (t - a))⁻¹) ^ 2) (2 * (9 + 4 / ε)) := by
  have h := ((fib_eps hε) t).add ((fib_eps hε).slow (wr_neg _))
  refine (h.mono_bd (le_of_eq (two_mul _).symm)).of_le (fun a => sq_nonneg _) fun a => ?_
  have hx := inv_nonneg.2 (absk_nonneg (t - a))
  have hy := inv_nonneg.2 (absk_nonneg a)
  have hk := kernel_two hx hy hε
  simp only [sw, sl, wr_inv_eq]
  by_cases ha : a 2 = 0
  · simp only [ha, ite_true]
    calc ((absk a)⁻¹ ^ ε * (absk (t - a))⁻¹) ^ 2 = (absk (t - a))⁻¹ ^ 2 * ((absk a)⁻¹ ^ ε) ^ 2 := by
          ring
      _ ≤ _ := hk
  · simp [ha]

/-- The same sum with `t + a`. -/
lemma kernel_eps' (hε : 0 < ε) (t : Mode) :
    SB (fun a : Mode => (sw ε a * (absk (t + a))⁻¹) ^ 2) (2 * (9 + 4 / ε)) := by
  refine SB.equiv' (Equiv.neg Mode) (kernel_eps hε t) fun a => ?_
  simp only [Equiv.neg_apply, sub_neg_eq_add, sw, sl, Pi.neg_apply, neg_eq_zero, absk_neg]

/-- The kernel of `pos2_sub`: `∑_{a,b} |a|⁻²|b|^{−2ε}|j|⁻⁴ ≤ 34 (9 + 4/ε)`. -/
lemma kernel_sub (hε : 0 < ε) (l : Mode) :
    SB (fun y : Mode × Mode => (sinv y.1 * sw ε y.2 * (absk (l - y.1 - y.2))⁻¹ ^ 2) ^ 2)
      (34 * (9 + 4 / ε)) := by
  have hZ : 0 ≤ 9 + 4 / ε := by positivity
  have hS := (fib_eps hε).slow (wr_neg _)
  have hS0 := sl_nonneg (wr_nonneg (2 + 2 * ε))
  have hF : ∀ t b, 0 ≤ (if b 2 = 0 then w4 (t - b) else 0 : ℝ) := fun t b => by
    split_ifs
    · exact pow_nonneg (inv_nonneg.2 (absk_nonneg _)) 4
    · exact le_rfl
  have t1 : ∀ l : Mode, SB (fun y : Mode × Mode =>
      sl (wr (2 + 2 * ε)) y.1 * (if y.2 2 = 0 then w4 (l - y.1 - y.2) else 0))
      ((9 + 4 / ε) * 17) := fun l =>
    SB.prod_mul (K := fun a b => if b 2 = 0 then w4 (l - a - b) else 0) hS hS0
      (fun i k => hF _ k) (fun i => fib_w4 (l - i)) (by norm_num)
  have t2 : SB (fun y : Mode × Mode =>
      sl (wr (2 + 2 * ε)) y.2 * (if y.1 2 = 0 then w4 (l - y.1 - y.2) else 0))
      ((9 + 4 / ε) * 17) :=
    SB.equiv' (Equiv.prodComm Mode Mode) (t1 l) fun y => by
      simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, sub_right_comm]
  have h := ((t1 l).add t2).mono_bd (show _ ≤ 34 * (9 + 4 / ε) by linarith)
  refine h.of_le (fun y => sq_nonneg _) fun y => ?_
  obtain ⟨a, b⟩ := y
  have hx := inv_nonneg.2 (absk_nonneg a)
  have hy := inv_nonneg.2 (absk_nonneg b)
  have hz : 0 ≤ (absk (l - a - b))⁻¹ := inv_nonneg.2 (absk_nonneg _)
  have hk := mul_le_mul_of_nonneg_right (kernel_two hx hy hε) (by positivity :
    0 ≤ (absk (l - a - b))⁻¹ ^ 4)
  simp only [sinv, sw, sl, w4, wr_inv_eq]
  by_cases ha : a 2 = 0 <;> by_cases hb : b 2 = 0
  · simp only [ha, hb, ite_true]
    calc _ = (absk a)⁻¹ ^ 2 * ((absk b)⁻¹ ^ ε) ^ 2 * (absk (l - a - b))⁻¹ ^ 4 := by ring
      _ ≤ _ := hk
      _ = _ := by ring
  · simp [hb]
  · simp [ha]
  · simp [ha]

/-! ### D. The rules -/

/-- **Body 39, LOCAL457, at `ε = 1/4`**: `h ∈ H¹`, `|p| S` with `S ∈ H^{1+ε}`, and the inverse
square exterior: `C ε^{−1/2} ‖α‖ ‖β‖ ‖h‖₁ ‖S‖_{1+ε}`. -/
theorem pos2_sub (hε : 0 < ε) (hα : L2B α A) (hβ : L2B β B) (h1 : SlowH1 f₁ U₁)
    (h2 : SlowHs ε f₂ U₂) :
    SB (Phi₂ α (in2 β) f₁ fun p => absk p * f₂ p)
      (Real.sqrt (34 * (9 + 4 / ε)) * (A * B * (U₁ * U₂))) := by
  have hZ : 0 ≤ 34 * (9 + 4 / ε) := by positivity
  set p : I3 → ℝ := fun x => sinv x.2.1 * sw ε x.2.2 * (absk (inJ₂ x))⁻¹ ^ 2 with hp
  have hp0 : ∀ x, 0 ≤ p x := fun x => mul_nonneg (mul_nonneg (sinv_nonneg _) (sw_nonneg _ _))
    (by have := absk_nonneg (inJ₂ x); positivity)
  have h := cs_out hp0 (fun l => kernel_sub hε l) hZ hα hβ h1.grad h2.grad
  have e : Phi₂ α (in2 β) f₁ (fun p => absk p * f₂ p) = fun x : I3 =>
      α x.1 * p x * (absk x.2.1 * f₁ x.2.1 * (absk x.2.2 ^ (1 + ε) * f₂ x.2.2) * β (inJ₂ x)) := by
    funext x
    have e1 := h1.sinv_mul x.2.1
    have e2 := h2.sw_mul x.2.2
    simp only [Phi₂, in2_eq, hp]
    calc _ = α x.1 * ((absk (inJ₂ x))⁻¹ ^ 2 * β (inJ₂ x)) *
          ((sinv x.2.1 * (absk x.2.1 * f₁ x.2.1)) *
            (sw ε x.2.2 * (absk x.2.2 ^ (1 + ε) * f₂ x.2.2))) := by
          rw [e1, e2]
      _ = _ := by ring
  rw [e]
  refine h.mono_bd (le_of_eq ?_)
  ring

/-- `pos2_sub` at `ε = 1/4`: LOCAL457's `ℓ^{16/15} ⋆ ℓ^{16/9}`, `‖h‖₁ ‖S‖_{5/4}`. -/
theorem pos2_H54 (hα : L2B α A) (hβ : L2B β B) (h1 : SlowH1 f₁ U₁) (h2 : SlowHs (1 / 4) f₂ U₂) :
    SB (Phi₂ α (in2 β) f₁ fun p => absk p * f₂ p) (30 * (A * B * (U₁ * U₂))) := by
  have hA := hα.bd_nonneg
  have hB := hβ.bd_nonneg
  have hU1 := h1.grad.bd_nonneg
  have hU2 := h2.grad.bd_nonneg
  refine (pos2_sub (by norm_num) hα hβ h1 h2).mono_bd ?_
  refine mul_le_mul_of_nonneg_right (Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩) (by positivity)

/-- **Body 38, a single weighted leaf and an inverse-first-power exterior**: the leaf `|p| S`,
`S ∈ H^{1+ε}`, against `z/J` in `ℓ²`, the third leaf in `ℓ¹`. -/
theorem pos2_single (hε : 0 < ε) (hα : L2B α A) (hβ : L2B β B) (h1 : SlowHs ε f₁ U₁)
    (h2 : L1B f₂ W) :
    SB (Phi₂ α (in1 β) (fun p => absk p * f₁ p) f₂)
      (Real.sqrt (2 * (9 + 4 / ε)) * (A * B * (U₁ * W))) := by
  have hZ : 0 ≤ 2 * (9 + 4 / ε) := by positivity
  have hA := hα.bd_nonneg
  have hB := hβ.bd_nonneg
  have hU := h1.grad.bd_nonneg
  have hW := h2.bd_nonneg
  have hf2 : SB f₂ W := ⟨h2.s, h2.le⟩
  set u : Mode → ℝ := fun p => absk p ^ (1 + ε) * f₁ p with hu
  set P : I3 → ℝ := fun x => α x.1 * Real.sqrt (f₂ x.2.2) *
    (sw ε x.2.1 * (absk (inJ₂ x))⁻¹) with hP
  set Q : I3 → ℝ := fun x => u x.2.1 * β (inJ₂ x) * Real.sqrt (f₂ x.2.2) with hQ
  have hP0 : ∀ x, 0 ≤ P x := fun x => mul_nonneg (mul_nonneg (hα.nn _) (Real.sqrt_nonneg _))
    (mul_nonneg (sw_nonneg _ _) (inv_nonneg.2 (absk_nonneg _)))
  have hQ0 : ∀ x, 0 ≤ Q x := fun x => mul_nonneg (mul_nonneg (h1.grad.nn _) (hβ.nn _))
    (Real.sqrt_nonneg _)
  have hsq : ∀ b, Real.sqrt (f₂ b) ^ 2 = f₂ b := fun b => Real.sq_sqrt (h2.nn b)
  have hP2 : SB (fun x => P x ^ 2) ((A * Real.sqrt W * Real.sqrt (2 * (9 + 4 / ε))) ^ 2) := by
    have ht := SB.tri hα.sq hf2 (fun k => sq_nonneg _) h2.nn
      (K := fun y => (sw ε y.2.2 * (absk (y.1 - y.2.1 - y.2.2))⁻¹) ^ 2) (fun y => sq_nonneg _)
      fun l b => kernel_eps hε (l - b)
    have e : (A * Real.sqrt W * Real.sqrt (2 * (9 + 4 / ε))) ^ 2 =
        A ^ 2 * W * (2 * (9 + 4 / ε)) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hW, Real.sq_sqrt hZ]
    rw [e]
    refine SB.equiv' swapL ht fun x => ?_
    simp only [hP, mul_pow, hsq, swapL_apply, inJ₂, sub_right_comm]
  have hQ2 : SB (fun x => Q x ^ 2) ((B * Real.sqrt W * U₁) ^ 2) := by
    have ht := SB.tri (Z := U₁ ^ 2) hβ.sq hf2 (fun k => sq_nonneg _) h2.nn
      (K := fun y => u y.2.2 ^ 2) (fun y => sq_nonneg _) fun _ _ => h1.grad.sq
    have e : (B * Real.sqrt W * U₁) ^ 2 = B ^ 2 * W * U₁ ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hW]
    rw [e]
    refine SB.equiv' miE ht fun x => ?_
    simp only [hQ, mul_pow, hsq, miE, Equiv.coe_fn_mk]
    ring
  have h := SB.cs hP0 hQ0 (by positivity) (by positivity) hP2 hQ2
  have e : Phi₂ α (in1 β) (fun p => absk p * f₁ p) f₂ = fun x => P x * Q x := by
    funext x
    have e1 := h1.sw_mul x.2.1
    have e2 := Real.mul_self_sqrt (h2.nn x.2.2)
    simp only [Phi₂, in1, hP, hQ, hu, div_eq_mul_inv]
    calc _ = α x.1 * β (inJ₂ x) * (absk (inJ₂ x))⁻¹ *
          (sw ε x.2.1 * (absk x.2.1 ^ (1 + ε) * f₁ x.2.1)) *
            (Real.sqrt (f₂ x.2.2) * Real.sqrt (f₂ x.2.2)) := by
          rw [e1, e2]
          ring
      _ = _ := by ring
  rw [e]
  refine h.mono_bd (le_of_eq ?_)
  have hs : Real.sqrt W * Real.sqrt W = W := Real.mul_self_sqrt hW
  calc _ = (Real.sqrt W * Real.sqrt W) * (Real.sqrt (2 * (9 + 4 / ε)) * (A * B * U₁)) := by ring
    _ = _ := by
        rw [hs]
        ring

/-- **Body 38, a distinct weighted pair and two inverse-first-power exteriors**: `(C/ε)`. -/
theorem pos2_pair_sub (hε : 0 < ε) (hα : L2B α A) (hβ : L2B β B) (h1 : SlowHs ε f₁ U₁)
    (h2 : SlowHs ε f₂ U₂) :
    SB (Phi₂ (in1 α) (in1 β) (fun p => absk p * f₁ p) fun p => absk p * f₂ p)
      (2 * (9 + 4 / ε) * (A * B * (U₁ * U₂))) := by
  have hZ : 0 ≤ 2 * (9 + 4 / ε) := by positivity
  set κ₁ : I3 → ℝ := fun x => sw ε x.2.2 * (absk (inJ₂ x))⁻¹ with hκ₁
  set κ₂ : I3 → ℝ := fun x => sw ε x.2.1 * (absk x.1)⁻¹ with hκ₂
  have h10 : ∀ x, 0 ≤ κ₁ x := fun x => mul_nonneg (sw_nonneg _ _) (inv_nonneg.2 (absk_nonneg _))
  have h20 : ∀ x, 0 ≤ κ₂ x := fun x => mul_nonneg (sw_nonneg _ _) (inv_nonneg.2 (absk_nonneg _))
  have h := cs_mid h10 h20 (fun l a => kernel_eps hε (l - a)) (fun j b => kernel_eps' hε (j + b))
    hZ hZ hα hβ h1.grad h2.grad
  have e : Phi₂ (in1 α) (in1 β) (fun p => absk p * f₁ p) (fun p => absk p * f₂ p) =
      fun x : I3 => (α x.1 * (absk x.2.1 ^ (1 + ε) * f₁ x.2.1) * κ₁ x) *
        (β (inJ₂ x) * (absk x.2.2 ^ (1 + ε) * f₂ x.2.2) * κ₂ x) := by
    funext x
    have e1 := h1.sw_mul x.2.1
    have e2 := h2.sw_mul x.2.2
    simp only [Phi₂, in1, hκ₁, hκ₂, div_eq_mul_inv]
    calc _ = α x.1 * (absk x.1)⁻¹ * (β (inJ₂ x) * (absk (inJ₂ x))⁻¹) *
          ((sw ε x.2.1 * (absk x.2.1 ^ (1 + ε) * f₁ x.2.1)) *
            (sw ε x.2.2 * (absk x.2.2 ^ (1 + ε) * f₂ x.2.2))) := by
          rw [e1, e2]
      _ = _ := by ring
  rw [e]
  refine h.mono_bd (le_of_eq ?_)
  have hs := Real.mul_self_sqrt hZ
  calc _ = (Real.sqrt (2 * (9 + 4 / ε)) * Real.sqrt (2 * (9 + 4 / ε))) *
        (A * B * (U₁ * U₂)) := by ring
    _ = _ := by rw [hs]

end OVNS.Quant.Metric

end
