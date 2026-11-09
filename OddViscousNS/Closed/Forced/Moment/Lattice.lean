import OddViscousNS.Closed.Forced.Moment.PairSound
import OddViscousNS.Closed.Forced.Moment.Defs

/-!
# Lattice facts for pairs of modes

For nonzero non-collinear `p, ℓ` with `u = p + ℓ`, `v = p − ℓ`, `C_u = |u|²`, `C_v = |v|²`:
`C_u + C_v = 2(|p|² + |ℓ|²)` (parallelogram), `u ≠ 0 ≠ v`, `C_u ≡ C_v (mod 4)`
(`C_u − C_v = 4 p·ℓ`), `W(p,ℓ) = 4/(t(C_u + C_v))`, and the pair value is the symmetric
rational expression `rawR a bL C_u C_v (g C_u) (g C_v) W` (`Tpair_eq_rawR`), which is symmetric
in `(C_u, C_v)` (`rawR_symm`), so it may be evaluated at `(min, max)`.
-/

open Set

namespace OVNS

namespace Forced

namespace Mom

/-- `nsq` as an integer sum of squares. -/
private lemma nsq_intCast (k : Mode) : (nsq k : ℤ) = (k 0) ^ 2 + (k 1) ^ 2 + (k 2) ^ 2 := by
  simp only [nsq, Fin.sum_univ_three]
  push_cast
  simp only [sq_abs]

/-- The parallelogram identity for `absSq`. -/
private lemma absSq_parallelogram (p l : Mode) :
    absSq (p + l) + absSq (p - l) = 2 * (absSq p + absSq l) := by
  simp only [absSq, Fin.sum_univ_three, Pi.add_apply, Pi.sub_apply]
  push_cast
  ring

theorem nsq_add_nsq_sub (p l : Mode) : nsq (p + l) + nsq (p - l) = 2 * (nsq p + nsq l) := by
  have h := nsq_intCast (p + l)
  have h' := nsq_intCast (p - l)
  have hp := nsq_intCast p
  have hl := nsq_intCast l
  simp only [Pi.add_apply, Pi.sub_apply] at h h'
  have : ((nsq (p + l) + nsq (p - l) : ℕ) : ℤ) = ((2 * (nsq p + nsq l) : ℕ) : ℤ) := by
    push_cast
    rw [h, h', hp, hl]
    ring
  exact_mod_cast this

private lemma lat_modeVec_neg (l : Mode) : modeVec (-l) = -modeVec l := by
  ext i; simp [modeVec]

private lemma lat_cross_neg (a b : V3) : cross a (-b) = -cross a b := by
  ext i; fin_cases i <;> simp [cross] <;> ring

private lemma lat_cross_self (a : V3) : cross a a = 0 := by
  ext i; fin_cases i <;> simp [cross] <;> ring

theorem ne_zero_of_nonColl {p l : Mode} (h : NonColl p l) : p + l ≠ 0 ∧ p - l ≠ 0 := by
  constructor
  · intro h0
    have hl : l = -p := by rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact h0
    apply h
    rw [hl, lat_modeVec_neg, lat_cross_neg, lat_cross_self, neg_zero]
  · intro h0
    have hl : l = p := (sub_eq_zero.1 h0).symm
    apply h
    rw [hl, lat_cross_self]

theorem nsq_mod_four (p l : Mode) : nsq (p + l) % 4 = nsq (p - l) % 4 := by
  have h := nsq_intCast (p + l)
  have h' := nsq_intCast (p - l)
  simp only [Pi.add_apply, Pi.sub_apply] at h h'
  have key : (nsq (p + l) : ℤ) = nsq (p - l) + 4 * (p 0 * l 0 + p 1 * l 1 + p 2 * l 2) := by
    rw [h, h']
    ring
  omega

theorem Wpair_eq {t : ℝ} (ht : 0 < t) (p l : Mode) :
    Wpair t p l = 4 / (t * ((nsq (p + l) : ℝ) + nsq (p - l))) := by
  have _ := ht
  rw [Wpair, nsq_cast, nsq_cast, absSq_parallelogram, ← mul_assoc, mul_comm t 2, mul_assoc,
    show (4 : ℝ) = 2 * 2 by norm_num, mul_div_mul_left _ _ (two_ne_zero)]

theorem rawR_symm (a bL : ℝ) (Cl Ch : ℕ) (gl gh W : ℝ) :
    rawR a bL Cl Ch gl gh W = rawR a bL Ch Cl gh gl W := by
  unfold rawR
  rw [add_comm (Ch : ℝ) Cl]
  ring

/-- The pair value in terms of the output radii and `W`. -/
theorem Tpair_eq_rawR (g : ℕ → ℝ) {a bL t : ℝ} (ht : 0 < t) {p l : Mode} (hp : p ≠ 0) (hl : l ≠ 0)
    (hnc : NonColl p l) :
    Tpair g a bL t p l =
      rawR a bL (nsq (p + l)) (nsq (p - l)) (g (nsq (p + l))) (g (nsq (p - l))) (Wpair t p l) := by
  have _ := hp
  have _ := hl
  obtain ⟨hu, hv⟩ := ne_zero_of_nonColl hnc
  have hCu : (0 : ℝ) < nsq (p + l) := by
    exact_mod_cast Nat.pos_of_ne_zero fun h ↦ hu ((nsq_eq_zero_iff _).1 h)
  have hCv : (0 : ℝ) < nsq (p - l) := by
    exact_mod_cast Nat.pos_of_ne_zero fun h ↦ hv ((nsq_eq_zero_iff _).1 h)
  have hJ : (0 : ℝ) < (nsq (p + l) : ℝ) + nsq (p - l) := add_pos hCu hCv
  have hWe := Wpair_eq ht p l
  have hW : 0 < Wpair t p l := by rw [hWe]; positivity
  have term : ∀ (k : Mode) (x : ℝ),
      x / xiM a bL t k = x * Wpair t p l / ((1 + bL / hmet (nsq k)) * Wpair t p l +
        4 * a * (nsq k : ℝ) / ((nsq (p + l) : ℝ) + nsq (p - l))) := by
    intro k x
    rw [← mul_div_mul_right x _ hW.ne']
    congr 1
    rw [xiM, hm, ← nsq_cast, hWe]
    field_simp
    ring
  unfold Tpair rawR
  rw [term (p + l), term (p - l)]

/-- `1 ≤ nsq z` for `z ≠ 0`. -/
theorem one_le_nsq {z : Mode} (hz : z ≠ 0) : 1 ≤ nsq z :=
  Nat.one_le_iff_ne_zero.2 fun h ↦ hz ((nsq_eq_zero_iff z).1 h)

end Mom

end Forced

end OVNS
