import OddViscousNS.Closed.Row.LatticeFin

/-!
# The scalar reduction and high outputs `K ≥ 100`

`S_a(k) = ∑_p a(p) a(k-p)`.  The pair lemma gives `rowR k c ≤ 36 h_C |c|² S_a(k) / 4.64` for
`C ≥ 1936`.  For `C ≥ 10⁴`, with `t = ⌊K⌋/3 ≥ 33` (so `C ≥ 9t²`): pairs with a leg of length `≤ t`
cost `(9/2C) ψ(t)` since the other leg has `B ≥ 4C/9`, and pairs with both legs longer cost `S₄(t)`.
So `S_a(k) ≤ 15/t + 17·9 t/(2C) ≤ 23.5/t ≤ .7122 < 4.64 · .163043`.  No Feynman integral.
-/

open Finset
open scoped ENNReal

noncomputable section

namespace OVNS
namespace Row

/-- `S_a(k)`. -/
def Sa (k : Mode) : ℝ≥0∞ := ∑' p, ENNReal.ofReal (aa (nsq p) * aa (nsq (k - p)))

/-- The scalar bound on the row form. -/
theorem rowR_le_Sa (k : Mode) (c : R3) (hc : dR k c = 0) (hC : 1936 ≤ nsq k) :
    rowR k c ≤ ENNReal.ofReal (36 * hm k * nR c / (464 / 100)) * Sa k := by
  unfold rowR Sa
  rw [← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun p => ?_
  have h0 : 0 ≤ 36 * hm k * nR c / (464 / 100) := by
    have := hm_nonneg k
    have := nR_nonneg c
    positivity
  rw [← ENNReal.ofReal_mul h0]
  refine ENNReal.ofReal_le_ofReal ((pair_le k p c hc hC).trans (le_of_eq ?_))
  ring

/-- Both legs long: AM-GM. -/
lemma aa_mul_le {A B ρ : ℕ} (hρ : 120 ≤ ρ ^ 2) (hA : ρ ^ 2 < A) (hB : ρ ^ 2 < B) :
    aa A * aa B ≤ ((A : ℝ)⁻¹ ^ 2 + (B : ℝ)⁻¹ ^ 2) / 2 := by
  rw [aa_high (by omega), aa_high (by omega)]
  nlinarith [sq_nonneg ((A : ℝ)⁻¹ - (B : ℝ)⁻¹)]

/-- The far-field cut of `S₄`, as a function on the lattice. -/
def x2 (ρ : ℕ) (p : Mode) : ℝ := if ρ ^ 2 < nsq p then (absSq p)⁻¹ ^ 2 else 0

lemma x2_nonneg (ρ : ℕ) (p : Mode) : 0 ≤ x2 ρ p := by
  unfold x2
  have := absSq_nonneg' p
  split_ifs <;> positivity

/-- A pair of long legs, as a summand of `S₄`. -/
lemma far_le {k p : Mode} {ρ : ℕ} (hρ : 120 ≤ ρ ^ 2) (h1 : ρ ^ 2 < nsq p)
    (h2 : ρ ^ 2 < nsq (k - p)) :
    ENNReal.ofReal (aa (nsq p) * aa (nsq (k - p))) ≤
      ENNReal.ofReal (1 / 2) * (ENNReal.ofReal (x2 ρ p) + ENNReal.ofReal (x2 ρ (k - p))) := by
  rw [← ENNReal.ofReal_add (x2_nonneg _ _) (x2_nonneg _ _), ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ((aa_mul_le hρ h1 h2).trans (le_of_eq ?_))
  simp only [x2, h1, h2, ↓reduceIte, nsq_cast]
  ring

/-- The sum over `k-p` is the sum over `p`, and the two halves add up. -/
lemma far_sum (k : Mode) (ρ : ℕ) :
    ∑' p, ENNReal.ofReal (1 / 2) * (ENNReal.ofReal (x2 ρ p) + ENNReal.ofReal (x2 ρ (k - p))) =
      Sm 2 ρ := by
  rw [ENNReal.tsum_mul_left, tsum_add]
  have h : ∑' p, ENNReal.ofReal (x2 ρ (k - p)) = ∑' p, ENNReal.ofReal (x2 ρ p) :=
    (Equiv.subLeft k).tsum_eq fun p => ENNReal.ofReal (x2 ρ p)
  rw [h, ← two_mul, ← mul_assoc, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
  have : (1 / 2 * 2 : ℝ) = 1 := by norm_num
  rw [this, ENNReal.ofReal_one, one_mul]
  rfl

/-- `ψ` as a series. -/
lemma psi_tsum (t : ℕ) : ∑' p : Mode, ENNReal.ofReal (if nsq p ≤ t ^ 2 then aa (nsq p) else 0) =
    ENNReal.ofReal (psiF t) := by
  classical
  unfold psiF
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => aa_nonneg _),
    tsum_eq_sum (s := ballF t) (fun p hp => by
      have : ¬ nsq p ≤ t ^ 2 := fun h => hp (mem_ballF.2 h)
      simp [this])]
  exact sum_congr rfl fun p hp => by simp [mem_ballF.1 hp]

/-- The other leg of a short leg. -/
lemma long_leg {k p : Mode} {t : ℕ} (hC : 9 * t ^ 2 ≤ nsq k) (hp : nsq p ≤ t ^ 2) :
    4 * nsq k ≤ 9 * nsq (k - p) := by
  have h1 : absk k ≤ absk p + absk (k - p) := by
    have := absk_add_le p (k - p)
    rwa [show p + (k - p) = k by abel] at this
  have h2 : absk p ≤ t := nsq_le_iff.1 hp
  have h3 : 3 * (t : ℝ) ≤ absk k := by
    unfold absk
    rw [show absSq k = (nsq k : ℝ) from (nsq_cast k).symm]
    apply Real.le_sqrt_of_sq_le
    have : ((9 * t ^ 2 : ℕ) : ℝ) ≤ (nsq k : ℝ) := by exact_mod_cast hC
    push_cast at this
    linarith
  have h5 : 2 * absk k ≤ 3 * absk (k - p) := by
    have := absk_nonneg k
    linarith
  have h6 : (2 * absk k) ^ 2 ≤ (3 * absk (k - p)) ^ 2 :=
    pow_le_pow_left₀ (by have := absk_nonneg k; positivity) h5 2
  rw [mul_pow, mul_pow, absk_sq, absk_sq, ← nsq_cast, ← nsq_cast] at h6
  have : ((4 * nsq k : ℕ) : ℝ) ≤ ((9 * nsq (k - p) : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast this

/-- A short leg is small against the long one. -/
lemma short_le {k p : Mode} {t : ℕ} (ht : 33 ≤ t) (hC : 9 * t ^ 2 ≤ nsq k) (hp : nsq p ≤ t ^ 2) :
    aa (nsq p) * aa (nsq (k - p)) ≤ 9 / (4 * (nsq k : ℝ)) * aa (nsq p) := by
  have h1 := long_leg hC hp
  have h2 : 9 * 33 ^ 2 ≤ nsq k := by
    have : 33 ^ 2 ≤ t ^ 2 := Nat.pow_le_pow_left ht 2
    omega
  have h3 : 120 < nsq (k - p) := by omega
  rw [aa_high h3, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (aa_nonneg _)
  have hC0 : (0 : ℝ) < nsq k := by exact_mod_cast (show 0 < nsq k by omega)
  have hB0 : (0 : ℝ) < nsq (k - p) := by exact_mod_cast (show 0 < nsq (k - p) by omega)
  rw [inv_eq_one_div, div_le_div_iff₀ hB0 (by positivity)]
  have : ((4 * nsq k : ℕ) : ℝ) ≤ ((9 * nsq (k - p) : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at this
  linarith

/-- The high-output bound on `S_a`. -/
theorem Sa_high (k : Mode) (t : ℕ) (ht : 33 ≤ t) (hC : 9 * t ^ 2 ≤ nsq k) :
    Sa k ≤ ENNReal.ofReal (47 / 2 * (t : ℝ)⁻¹) := by
  classical
  have h120 : 120 ≤ t ^ 2 := by
    have : 33 ^ 2 ≤ t ^ 2 := Nat.pow_le_pow_left ht 2
    omega
  set u : Mode → ℝ := fun p => if nsq p ≤ t ^ 2 then aa (nsq p) else 0 with hu
  have hu0 : ∀ p, 0 ≤ u p := fun p => by
    simp only [hu]; split_ifs
    · exact aa_nonneg _
    · exact le_rfl
  have hC0 : (0 : ℝ) < nsq k := by
    have : 0 < nsq k := by nlinarith
    exact_mod_cast this
  have hc : 0 ≤ 9 / (4 * (nsq k : ℝ)) := by positivity
  set E := ENNReal.ofReal (9 / (4 * (nsq k : ℝ))) with hE
  have hpt : ∀ p, ENNReal.ofReal (aa (nsq p) * aa (nsq (k - p))) ≤
      E * (ENNReal.ofReal (u p) + ENNReal.ofReal (u (k - p)))
        + ENNReal.ofReal (1 / 2) * (ENNReal.ofReal (x2 t p) + ENNReal.ofReal (x2 t (k - p))) := by
    intro p
    by_cases h1 : nsq p ≤ t ^ 2
    · refine le_add_right ?_
      rw [← ENNReal.ofReal_add (hu0 _) (hu0 _), ← ENNReal.ofReal_mul hc]
      refine ENNReal.ofReal_le_ofReal ((short_le ht hC h1).trans ?_)
      refine mul_le_mul_of_nonneg_left ?_ hc
      have : u p = aa (nsq p) := by simp only [hu, h1, ↓reduceIte]
      rw [this]
      have := hu0 (k - p)
      linarith
    · by_cases h2 : nsq (k - p) ≤ t ^ 2
      · refine le_add_right ?_
        rw [← ENNReal.ofReal_add (hu0 _) (hu0 _), ← ENNReal.ofReal_mul hc]
        have h3 := short_le (k := k) (p := k - p) ht hC h2
        rw [sub_sub_self', mul_comm] at h3
        refine ENNReal.ofReal_le_ofReal (h3.trans ?_)
        refine mul_le_mul_of_nonneg_left ?_ hc
        have : u (k - p) = aa (nsq (k - p)) := by simp only [hu, h2, ↓reduceIte]
        rw [this]
        have := hu0 p
        linarith
      · exact le_add_left (far_le h120 (by omega) (by omega))
  refine (tsum_le_tsum hpt).trans ?_
  rw [tsum_add, ENNReal.tsum_mul_left, far_sum, tsum_add]
  have hs1 : ∑' p, ENNReal.ofReal (u p) = ENNReal.ofReal (psiF t) := psi_tsum t
  have hs2 : ∑' p, ENNReal.ofReal (u (k - p)) = ENNReal.ofReal (psiF t) := by
    rw [← hs1]
    exact (Equiv.subLeft k).tsum_eq fun p => ENNReal.ofReal (u p)
  rw [hs1, hs2]
  have hψ0 : 0 ≤ psiF t := sum_nonneg fun _ _ => aa_nonneg _
  have hψ := psi_le t ht
  have hS := S4_le t (by omega)
  have ht0 : (0 : ℝ) < t := by
    have : 0 < t := by omega
    exact_mod_cast this
  have hC' : 9 * (t : ℝ) ^ 2 ≤ (nsq k : ℝ) := by
    have : ((9 * t ^ 2 : ℕ) : ℝ) ≤ (nsq k : ℝ) := by exact_mod_cast hC
    push_cast at this
    linarith
  have hb : 9 / (4 * (nsq k : ℝ)) * (psiF t + psiF t) ≤ 17 / 2 * (t : ℝ)⁻¹ := by
    have h1 : 9 / (4 * (nsq k : ℝ)) ≤ 9 / (4 * (9 * (t : ℝ) ^ 2)) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
    calc 9 / (4 * (nsq k : ℝ)) * (psiF t + psiF t)
        ≤ 9 / (4 * (9 * (t : ℝ) ^ 2)) * (17 * t + 17 * t) :=
          mul_le_mul h1 (by linarith) (by positivity) (by positivity)
      _ = _ := by field_simp; ring
  rw [← ENNReal.ofReal_add hψ0 hψ0, hE, ← ENNReal.ofReal_mul hc]
  refine (add_le_add (ENNReal.ofReal_le_ofReal hb) hS).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

/-- **High outputs**: the row bound for `C ≥ 10⁴`. -/
theorem rowR_high (k : Mode) (hk : 10000 ≤ nsq k) (c : R3) (hc : dR k c = 0) :
    rowR k c ≤ ENNReal.ofReal (36 * gOVNS (nsq k) * hm k * nR c) := by
  set t := Nat.sqrt (nsq k) / 3 with ht
  have h1 : Nat.sqrt (nsq k) * Nat.sqrt (nsq k) ≤ nsq k := Nat.sqrt_le (nsq k)
  have h100 : 100 ≤ Nat.sqrt (nsq k) := Nat.le_sqrt.2 (by omega)
  have ht33 : 33 ≤ t := by omega
  have hC : 9 * t ^ 2 ≤ nsq k := by
    have h2 : 3 * t ≤ Nat.sqrt (nsq k) := by omega
    nlinarith
  have hb := Sa_high k t ht33 hC
  have hr := rowR_le_Sa k c hc (by omega)
  have h0 : 0 ≤ 36 * hm k * nR c / (464 / 100) := by
    have := hm_nonneg k
    have := nR_nonneg c
    positivity
  refine hr.trans ((mul_le_mul_right hb _).trans ?_)
  rw [← ENNReal.ofReal_mul h0]
  refine ENNReal.ofReal_le_ofReal ?_
  have hg : gOVNS (nsq k) = 163043 / 1000000 := by
    unfold gOVNS
    simp only [show ¬ nsq k < 1024 by omega, show ¬ nsq k < 3600 by omega, ↓reduceIte]
  rw [hg]
  have ht0 : (33 : ℝ) ≤ t := by exact_mod_cast ht33
  have h3 : (t : ℝ)⁻¹ ≤ 33⁻¹ := inv_anti₀ (by norm_num) ht0
  have h4 : 47 / 2 * (t : ℝ)⁻¹ ≤ 464 / 100 * (163043 / 1000000) := by
    have : (47 : ℝ) / 2 * (33 : ℝ)⁻¹ ≤ 464 / 100 * (163043 / 1000000) := by norm_num
    linarith
  have h5 : 0 ≤ 36 * hm k * nR c := by
    have := hm_nonneg k
    have := nR_nonneg c
    positivity
  calc 36 * hm k * nR c / (464 / 100) * (47 / 2 * (t : ℝ)⁻¹)
      ≤ 36 * hm k * nR c / (464 / 100) * (464 / 100 * (163043 / 1000000)) :=
        mul_le_mul_of_nonneg_left h4 h0
    _ = _ := by ring

end Row
end OVNS
