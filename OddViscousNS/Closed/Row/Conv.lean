import OddViscousNS.Closed.Row.Radial

/-!
# From a slot of a product of index-box sums to a lattice convolution

`pair_sum_eq` turns the slot sum over index pairs into `∑_{p, k-p} Φ p (k-p)`, given that the slot
condition is exactly `p + l = k` (no aliasing).  `dig_conv` packages this for a pair of `z`-blocks of
the box of radius `R`.
-/

open Finset

noncomputable section

namespace OVNS
namespace Row

/-- Slot sums as convolutions. -/
lemma pair_sum_eq {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (I : Finset ι) (J : Finset κ)
    (a : ι → Mode) (b : κ → Mode) (ha : Set.InjOn a I) (hb : Set.InjOn b J) (Φ : Mode → Mode → ℕ)
    (k : Mode) (P : ι × κ → Prop) [DecidablePred P]
    (hP : ∀ i ∈ I, ∀ j ∈ J, P (i, j) ↔ a i + b j = k) :
    ∑ q ∈ (I ×ˢ J).filter P, Φ (a q.1) (b q.2) =
      ∑ p ∈ (I.image a).filter (fun p => k - p ∈ J.image b), Φ p (k - p) := by
  refine sum_bij (fun q _ => a q.1) ?_ ?_ ?_ ?_
  · intro q hq
    obtain ⟨h1, h2⟩ := mem_filter.1 hq
    obtain ⟨h3, h4⟩ := mem_product.1 h1
    have h5 := (hP q.1 h3 q.2 h4).1 (by simpa using h2)
    refine mem_filter.2 ⟨mem_image_of_mem _ h3, mem_image.2 ⟨q.2, h4, ?_⟩⟩
    rw [← h5]; abel
  · intro q hq q' hq' h
    obtain ⟨h1, h2⟩ := mem_filter.1 hq
    obtain ⟨h3, h4⟩ := mem_product.1 h1
    obtain ⟨h1', h2'⟩ := mem_filter.1 hq'
    obtain ⟨h3', h4'⟩ := mem_product.1 h1'
    have h5 := (hP q.1 h3 q.2 h4).1 (by simpa using h2)
    have h6 := (hP q'.1 h3' q'.2 h4').1 (by simpa using h2')
    have h7 : b q.2 = b q'.2 := by
      have e : a q.1 + b q.2 = a q.1 + b q'.2 := by rw [h5, h, h6]
      exact add_left_cancel e
    exact Prod.ext (ha h3 h3' h) (hb h4 h4' h7)
  · intro p hp
    obtain ⟨h1, h2⟩ := mem_filter.1 hp
    obtain ⟨i, hi, rfl⟩ := mem_image.1 h1
    obtain ⟨j, hj, h3⟩ := mem_image.1 h2
    refine ⟨(i, j), mem_filter.2 ⟨mem_product.2 ⟨hi, hj⟩, ?_⟩, rfl⟩
    rw [hP i hi j hj, h3]; abel
  · intro q hq
    obtain ⟨h1, h2⟩ := mem_filter.1 hq
    obtain ⟨h3, h4⟩ := mem_product.1 h1
    have h5 := (hP q.1 h3 q.2 h4).1 (by simpa using h2)
    rw [show k - a q.1 = b q.2 by rw [← h5]; abel]

/-- A block of `nz` layers from `z0`: its index set. -/
def Bl (n nz : ℕ) : Finset (ℕ × ℕ × ℕ) := range nz ×ˢ range n ×ˢ range n

/-- The lattice point of a block index. -/
def ptB (R z0 : ℕ) (q : ℕ × ℕ × ℕ) : Mode := ![(q.2.2 : ℤ) - R, (q.2.1 : ℤ) - R, (z0 + q.1 : ℕ) - R]

lemma ptB_inj (R z0 n nz : ℕ) : Set.InjOn (ptB R z0) (Bl n nz) := by
  intro q _ q' _ h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp [ptB] at h0 h1 h2
  obtain ⟨a, b, c⟩ := q
  obtain ⟨a', b', c'⟩ := q'
  simp only at h0 h1 h2
  ext <;> simp <;> omega

/-- The packing exponent. -/
def idxP (P : ℕ) (q : ℕ × ℕ × ℕ) : ℕ := q.2.2 + P * q.2.1 + P * P * q.1

/-- The packing exponent is injective on a block. -/
lemma idxP_inj {P n nz : ℕ} (hn : n ≤ P) : Set.InjOn (idxP P) (Bl n nz) := by
  rintro ⟨a, b, c⟩ h ⟨a', b', c'⟩ h' e
  simp only [Bl, coe_product, Set.mem_prod, mem_coe, mem_range] at h h'
  simp only [idxP] at e
  have hP : 0 < P := by omega
  have e1 : (c + P * b + P * P * a) % P = (c' + P * b' + P * P * a') % P := by rw [e]
  have r1 : ∀ c b a, (c + P * b + P * P * a) % P = c % P := fun c b a => by
    rw [show c + P * b + P * P * a = c + P * (b + P * a) by ring, Nat.add_mul_mod_self_left]
  rw [r1, r1, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at e1
  subst e1
  have e2 : b + P * a = b' + P * a' := by
    have : c + P * (b + P * a) = c + P * (b' + P * a') := by
      calc _ = c + P * b + P * P * a := by ring
        _ = c + P * b' + P * P * a' := e
        _ = _ := by ring
    exact Nat.eq_of_mul_eq_mul_left hP (Nat.add_left_cancel this)
  have e3 : (b + P * a) % P = (b' + P * a') % P := by rw [e2]
  rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)] at e3
  subst e3
  have e4 : a = a' := Nat.eq_of_mul_eq_mul_left hP (Nat.add_left_cancel e2)
  subst e4
  rfl

/-- **Digits of a product of two blocks are convolutions.** -/
theorem dig_conv {w R n P nz nz' z0 z0' s M : ℕ} (hX : 0 < (2 : ℕ) ^ w) (hn : n ≤ P)
    (U V : Mode → ℕ) (k : Mode)
    (hM : ∀ q ∈ Bl n nz ×ˢ Bl n nz', idxP P q.1 + idxP P q.2 < M) (hs : s < M)
    (hal : ∀ q ∈ Bl n nz, ∀ q' ∈ Bl n nz',
      idxP P q + idxP P q' = s ↔ ptB R z0 q + ptB R z0' q' = k)
    (hnorm : (∑ q ∈ Bl n nz, U (ptB R z0 q) ^ 2) * (∑ q ∈ Bl n nz', V (ptB R z0' q) ^ 2) <
      (2 ^ w) ^ 2) :
    Dig (2 ^ w) ((∑ q ∈ Bl n nz, U (ptB R z0 q) * (2 ^ w) ^ idxP P q) *
        (∑ q ∈ Bl n nz', V (ptB R z0' q) * (2 ^ w) ^ idxP P q)) s =
      ∑ p ∈ ((Bl n nz).image (ptB R z0)).filter (fun p => k - p ∈ (Bl n nz').image (ptB R z0')),
        U p * V (k - p) := by
  classical
  rw [dig_mul hX (Bl n nz) (Bl n nz') (fun q => U (ptB R z0 q)) (fun q => V (ptB R z0' q))
    (idxP P) (idxP P) (idxP_inj hn) (idxP_inj hn) hM hnorm s hs]
  exact pair_sum_eq (Bl n nz) (Bl n nz') (ptB R z0) (ptB R z0') (ptB_inj _ _ _ _) (ptB_inj _ _ _ _)
    (fun p l => U p * V l) k _ (fun i hi j hj => hal i hi j hj)

end Row
end OVNS
