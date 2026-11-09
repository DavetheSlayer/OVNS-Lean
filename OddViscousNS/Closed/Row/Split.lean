import OddViscousNS.Closed.Row.Tail
import OddViscousNS.Closed.Row.Count

/-!
# Splitting the row form: lens + tail, and the lens into high pairs + direct low zone
-/

open Finset
open scoped ENNReal

noncomputable section

namespace OVNS
namespace Row

set_option maxRecDepth 20000
set_option linter.constructorNameAsVariable false

/-- The lens: both legs of length `≤ R`. -/
def lensF (k : Mode) (R : ℕ) : Finset Mode :=
  (boxM R).filter fun p => nsq p ≤ R ^ 2 ∧ nsq (k - p) ≤ R ^ 2

/-- The row form is the lens sum plus the part off the lens. -/
theorem rowR_split (k : Mode) (c : R3) (R : ℕ) :
    rowR k c = ENNReal.ofReal (∑ p ∈ lensF k R, pterm k c p) + offSum k c R := by
  classical
  have h1 : ENNReal.ofReal (∑ p ∈ lensF k R, pterm k c p) =
      ∑' p, if p ∈ lensF k R then ENNReal.ofReal (pterm k c p) else 0 := by
    rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => pterm_nonneg _ _ _,
      tsum_eq_sum (s := lensF k R) (fun p hp => by simp [hp])]
    exact sum_congr rfl fun p hp => by simp [hp]
  unfold rowR offSum
  rw [h1, ← tsum_add]
  refine tsum_congr fun p => ?_
  have hmem : p ∈ lensF k R ↔ ¬ Off k R p := by
    simp only [lensF, mem_filter, Off, not_or, not_lt]
    exact ⟨fun h => h.2, fun h => ⟨mem_box_of_nsq h.1, h⟩⟩
  by_cases h : Off k R p
  · simp [hmem, h]
  · simp [hmem, h]

/-- The high pairs of a lens. -/
def hhF (k : Mode) : Finset Mode :=
  (boxM 78).filter fun p => 120 < nsq p ∧ nsq p ≤ 6084 ∧ 120 < nsq (k - p) ∧ nsq (k - p) ≤ 6084

/-- The low points. -/
def loF : Finset Mode := (boxM 10).filter fun p => nsq p ≤ 120

/-- The weight of a low point. -/
def wtL (k p : Mode) : ℝ := if nsq (k - p) ≤ 120 then 1 else 2

lemma mem_loF {p : Mode} : p ∈ loF ↔ nsq p ≤ 120 := by
  simp only [loF, mem_filter, and_iff_right_iff_imp]
  intro h
  rw [mem_boxM]
  intro i
  have h1 := coord_sq_le p i
  have h2 : (p i).natAbs ≤ 10 := by
    by_contra h3
    have h4 : 11 ≤ (p i).natAbs := by omega
    have h5 := Nat.pow_le_pow_left h4 2
    omega
  omega

lemma nsq_78 : (78 : ℕ) ^ 2 = 6084 := by norm_num

lemma mem_lens78 {k p : Mode} : p ∈ lensF k 78 ↔ nsq p ≤ 6084 ∧ nsq (k - p) ≤ 6084 := by
  simp only [lensF, mem_filter, nsq_78, and_iff_right_iff_imp]
  exact fun h => mem_box_of_nsq (t := 78) (by rw [nsq_78]; exact h.1)

/-- A low point keeps its partner in the lens. -/
lemma low_partner {k p : Mode} (hk : nsq k < 1936) (hp : nsq p ≤ 120) : nsq (k - p) ≤ 6084 := by
  have h1 := absk_sub_le k p
  have h2 : absk k ≤ ((44 : ℕ) : ℝ) := nsq_le_iff.1 (by norm_num; omega)
  have h3 : absk p ≤ ((11 : ℕ) : ℝ) := nsq_le_iff.1 (by norm_num; omega)
  have h4 : absk (k - p) ≤ ((78 : ℕ) : ℝ) := by
    push_cast at h2 h3 ⊢
    linarith
  have := nsq_le_iff.2 h4
  rwa [nsq_78] at this

/-- **The lens splits into the high pairs and the weighted low zone.** -/
theorem lens_split (k : Mode) (c : R3) (hc : dR k c = 0) (hk : nsq k < 1936) :
    ∑ p ∈ lensF k 78, pterm k c p =
      ∑ p ∈ hhF k, pterm k c p + ∑ p ∈ loF, wtL k p * pterm k c p := by
  classical
  set f := pterm k c with hf
  set L := lensF k 78 with hL
  -- split by `A ≤ 120`
  have h1 : ∑ p ∈ L, f p = ∑ p ∈ L.filter (fun p => nsq p ≤ 120), f p
      + ∑ p ∈ L.filter (fun p => ¬ nsq p ≤ 120), f p := (sum_filter_add_sum_filter_not _ _ _).symm
  have h2 : ∑ p ∈ L.filter (fun p => ¬ nsq p ≤ 120), f p =
      ∑ p ∈ (L.filter (fun p => ¬ nsq p ≤ 120)).filter (fun p => nsq (k - p) ≤ 120), f p
      + ∑ p ∈ (L.filter (fun p => ¬ nsq p ≤ 120)).filter (fun p => ¬ nsq (k - p) ≤ 120), f p :=
    (sum_filter_add_sum_filter_not _ _ _).symm
  have h3 : (L.filter (fun p => ¬ nsq p ≤ 120)).filter (fun p => ¬ nsq (k - p) ≤ 120) = hhF k := by
    ext p
    simp only [mem_filter, hL, mem_lens78, hhF]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      exact ⟨mem_box_of_nsq (t := 78) (by rw [nsq_78]; exact h1), by omega, h1, by omega, h2⟩
    · rintro ⟨_, h1, h2, h3, h4⟩
      exact ⟨⟨⟨h2, h4⟩, by omega⟩, by omega⟩
  set Lf := L.filter (fun p => nsq p ≤ 120) with hLf
  set La := Lf.filter (fun p => ¬ nsq (k - p) ≤ 120) with hLa
  set Lb := Lf.filter (fun p => nsq (k - p) ≤ 120) with hLb
  -- the reflection `p ↦ k - p`
  have h4 : ∑ p ∈ (L.filter (fun p => ¬ nsq p ≤ 120)).filter (fun p => nsq (k - p) ≤ 120), f p =
      ∑ p ∈ La, f p := by
    refine sum_nbij' (fun p => k - p) (fun p => k - p) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [hLa, hLf, mem_filter, hL, mem_lens78, sub_sub_self'] at hp ⊢
      exact ⟨⟨⟨hp.1.1.2, hp.1.1.1⟩, hp.2⟩, hp.1.2⟩
    · intro p hp
      simp only [hLa, hLf, mem_filter, hL, mem_lens78, sub_sub_self'] at hp ⊢
      exact ⟨⟨⟨hp.1.1.2, hp.1.1.1⟩, hp.2⟩, hp.1.2⟩
    · intro p _; exact sub_sub_self' k p
    · intro p _; exact sub_sub_self' k p
    · intro p _; exact (pterm_symm k p c hc).symm
  -- the low side
  have e1 : loF = Lf := by
    ext p
    simp only [hLf, mem_filter, hL, mem_lens78, mem_loF]
    constructor
    · intro h; exact ⟨⟨by omega, low_partner hk h⟩, h⟩
    · intro h; exact h.2
  have e3 := sum_filter_add_sum_filter_not Lf (fun p => nsq (k - p) ≤ 120) (fun p => wtL k p * f p)
  have e4 : ∑ p ∈ Lb, wtL k p * f p = ∑ p ∈ Lb, f p :=
    sum_congr rfl fun p hp => by
      have := (mem_filter.1 hp).2
      simp only [wtL, this, ↓reduceIte, one_mul]
  have e5 : ∑ p ∈ La, wtL k p * f p = 2 * ∑ p ∈ La, f p := by
    rw [mul_sum]
    exact sum_congr rfl fun p hp => by
      have := (mem_filter.1 hp).2
      simp only [wtL, this, ↓reduceIte]
  have e6 := sum_filter_add_sum_filter_not Lf (fun p => nsq (k - p) ≤ 120) f
  rw [h1, h2, h3, h4, e1]
  linarith

end Row
end OVNS
