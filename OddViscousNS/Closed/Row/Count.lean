import OddViscousNS.Closed.Row.Radial
import OddViscousNS.Closed.Row.Data.Seed

/-!
# Two-sided lattice counts by doubling

`p = 2q + e`, `e ∈ {0,1}³`, gives `N(t) ≤ 8 N(t')` when `t + 2 ≤ 2t'`, and `8 N(t) ≤ N(t')` when
`2t + 2 ≤ t'`.  So `N(t)/(t-3)³` and `N(t)/(t+3)³` are monotone along doubling and the kernel table
`seedChk` on `128 ≤ t ≤ 258` gives, for all `t ≥ 128`,
`39/10 (t+3)³ ≤ N(t) ≤ 9/2 (t-3)³`.  No measure theory.
-/

open Finset

noncomputable section

namespace OVNS
namespace Row

/-- The residues. -/
def Esq : Finset Mode := Fintype.piFinset fun _ => ({0, 1} : Finset ℤ)

lemma card_Esq : Esq.card = 8 := by
  simp [Esq, Fintype.card_piFinset]

lemma mem_Esq {e : Mode} : e ∈ Esq ↔ ∀ i, e i = 0 ∨ e i = 1 := by
  simp [Esq, Fintype.mem_piFinset]

lemma absSq_le_three {e : Mode} (he : e ∈ Esq) : absSq e ≤ 3 := by
  rw [mem_Esq] at he
  simp only [absSq, Fin.sum_univ_three]
  rcases he 0 with h0 | h0 <;> rcases he 1 with h1 | h1 <;> rcases he 2 with h2 | h2 <;>
    rw [h0, h1, h2] <;> norm_num

lemma absk_le_two {e : Mode} (he : e ∈ Esq) : absk e ≤ 2 := by
  unfold absk
  apply Real.sqrt_le_iff.2
  have := absSq_le_three he
  constructor <;> linarith

lemma nsq_le_iff {t : ℕ} {p : Mode} : nsq p ≤ t ^ 2 ↔ absk p ≤ t := by
  unfold absk
  rw [show absSq p = (nsq p : ℝ) from (nsq_cast p).symm, Real.sqrt_le_iff]
  constructor
  · intro h
    exact ⟨by positivity, by exact_mod_cast h⟩
  · intro h
    exact_mod_cast h.2

lemma absk_two_smul (q : Mode) : absk (2 • q) = 2 * absk q := by
  unfold absk
  have : absSq (2 • q) = 2 ^ 2 * absSq q := by
    simp only [absSq, Fin.sum_univ_three, Pi.smul_apply, nsmul_eq_mul]
    push_cast
    ring
  rw [this, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

/-- The upper doubling inequality. -/
theorem ball_double_le {t t' : ℕ} (h : t + 2 ≤ 2 * t') : ballC t ≤ 8 * ballC t' := by
  have : (ballF t).card ≤ (ballF t' ×ˢ Esq).card := by
    refine card_le_card_of_injOn (fun p => (fun i => p i / 2, fun i => p i % 2)) ?_ ?_
    · intro p hp
      have hp' := nsq_le_iff.1 (mem_ballF.1 hp)
      simp only [coe_product, Set.mem_prod, mem_coe]
      have he : (fun i => p i % 2 : Mode) ∈ Esq := by
        rw [mem_Esq]; intro i; omega
      refine ⟨mem_ballF.2 (nsq_le_iff.2 ?_), he⟩
      have e1 : 2 • (fun i => p i / 2 : Mode) = p - (fun i => p i % 2) := by
        funext i
        simp only [Pi.smul_apply, Pi.sub_apply, nsmul_eq_mul]
        push_cast
        omega
      have h1 := absk_sub_le p (fun i => p i % 2)
      have h2 := absk_two_smul (fun i => p i / 2 : Mode)
      rw [e1] at h2
      have h3 := absk_le_two he
      have h4 : ((t + 2 : ℕ) : ℝ) ≤ ((2 * t' : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at h4
      linarith
    · intro p _ q _ h
      have h1 := congrFun (Prod.ext_iff.1 h).1
      have h2 := congrFun (Prod.ext_iff.1 h).2
      funext i
      have := h1 i
      have := h2 i
      simp only at *
      omega
  rw [card_product, card_Esq] at this
  unfold ballC
  omega

/-- The lower doubling inequality. -/
theorem double_le_ball {t t' : ℕ} (h : 2 * t + 2 ≤ t') : 8 * ballC t ≤ ballC t' := by
  have : (ballF t ×ˢ Esq).card ≤ (ballF t').card := by
    refine card_le_card_of_injOn (fun x => 2 • x.1 + x.2) ?_ ?_
    · intro x hx
      simp only [coe_product, Set.mem_prod, mem_coe] at hx
      have hp' := nsq_le_iff.1 (mem_ballF.1 hx.1)
      refine mem_ballF.2 (nsq_le_iff.2 ?_)
      have h1 := absk_add_le (2 • x.1) x.2
      have h2 := absk_two_smul x.1
      have h3 := absk_le_two hx.2
      have h4 : ((2 * t + 2 : ℕ) : ℝ) ≤ (t' : ℝ) := by exact_mod_cast h
      push_cast at h4
      simp only at *
      linarith
    · intro x hx y hy h
      simp only [coe_product, Set.mem_prod, mem_coe] at hx hy
      have h1 := mem_Esq.1 hx.2
      have h2 := mem_Esq.1 hy.2
      have h3 : ∀ i, 2 * x.1 i + x.2 i = 2 * y.1 i + y.2 i := fun i => by
        have := congrFun h i
        simpa [Pi.smul_apply, nsmul_eq_mul] using this
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
      · have := h3 i; have := h1 i; have := h2 i; omega
      · have := h3 i; have := h1 i; have := h2 i; omega
  rw [card_product, card_Esq] at this
  unfold ballC
  omega

set_option linter.constructorNameAsVariable false in
/-- The seeds. -/
lemma seed_spec {t : ℕ} (h1 : 128 ≤ t) (h2 : t ≤ 258) :
    2 * ballC t ≤ 9 * (t - 3) ^ 3 ∧ 39 * (t + 3) ^ 3 ≤ 10 * ballC t := by
  have hs := seed_ok
  unfold seedChk at hs
  simp only [litB_eq] at hs
  have hi := allN_spec _ _ hs (t - 128) (by omega)
  simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at hi
  rw [show 128 + (t - 128) = t by omega, Bool.and_eq_true] at hi
  have hd : rd 32 (t * t) (th4 32 258 517 10 66565 17) = ballC t := by
    rw [rd_eq, ← pow_two]
    exact dig_th4_ball (R := 258) (by norm_num) (by norm_num) (by norm_num) h2 (by nlinarith)
      (3 * 258 ^ 2 + 1) (fun q hq => by
        simp only [Bx, mem_product, mem_range] at hq
        have hs : ∀ i, i < 2 * 258 + 1 → sq 258 i ≤ 258 ^ 2 := by
          intro i hi
          have e := sq_cast 258 i
          have : ((sq 258 i : ℕ) : ℤ) ≤ 258 ^ 2 := by
            rw [e]; push_cast; nlinarith
          exact_mod_cast this
        have h1 := hs _ hq.1
        have h2 := hs _ hq.2.1
        have h3 := hs _ hq.2.2
        simp only [sqs]
        omega)
  rw [hd] at hi
  have e1 := Nat.le_of_ble_eq_true hi.1
  have e2 := Nat.le_of_ble_eq_true hi.2
  constructor
  · calc 2 * ballC t ≤ _ := e1
      _ = _ := by ring
  · calc 39 * (t + 3) ^ 3 = _ := by ring
      _ ≤ _ := e2

/-- `N(t) ≤ 9/2 (t-3)³` for `t ≥ 128`. -/
theorem ball_upper (t : ℕ) (h : 128 ≤ t) : 2 * ballC t ≤ 9 * (t - 3) ^ 3 := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    rcases le_or_gt t 258 with h2 | h2
    · exact (seed_spec h h2).1
    · set t' := (t + 3) / 2 with ht'
      have h1 : t' < t := by omega
      have h3 : 128 ≤ t' := by omega
      have h4 := ih t' h1 h3
      have h5 := ball_double_le (t := t) (t' := t') (by omega)
      have h6 : 2 * (t' - 3) ≤ t - 3 := by omega
      have h7 : (2 * (t' - 3)) ^ 3 ≤ (t - 3) ^ 3 := Nat.pow_le_pow_left h6 3
      have h8 : (2 * (t' - 3)) ^ 3 = 8 * (t' - 3) ^ 3 := by ring
      nlinarith

/-- `N(t) ≥ 39/10 (t+3)³` for `t ≥ 128`. -/
theorem ball_lower (t : ℕ) (h : 128 ≤ t) : 39 * (t + 3) ^ 3 ≤ 10 * ballC t := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    rcases le_or_gt t 258 with h2 | h2
    · exact (seed_spec h h2).2
    · set t' := (t - 2) / 2 with ht'
      have h1 : t' < t := by omega
      have h3 : 128 ≤ t' := by omega
      have h4 := ih t' h1 h3
      have h5 := double_le_ball (t := t') (t' := t) (by omega)
      have h6 : t + 3 ≤ 2 * (t' + 3) := by omega
      have h7 : (t + 3) ^ 3 ≤ (2 * (t' + 3)) ^ 3 := Nat.pow_le_pow_left h6 3
      have h8 : (2 * (t' + 3)) ^ 3 = 8 * (t' + 3) ^ 3 := by ring
      nlinarith

end Row
end OVNS
