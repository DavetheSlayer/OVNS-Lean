import OddViscousNS.Closed.Row.Arrays
import OddViscousNS.Closed.Row.RadK
import OddViscousNS.Closed.Row.Form

/-!
# Radial sums: from the kernel digits to sums over the lattice box
-/

open Finset

noncomputable section

namespace OVNS
namespace Row

/-- The box `|pᵢ| ≤ R`. -/
def boxM (R : ℕ) : Finset Mode := Fintype.piFinset fun _ => Finset.Icc (-(R : ℤ)) R

lemma mem_boxM {R : ℕ} {p : Mode} : p ∈ boxM R ↔ ∀ i, -(R : ℤ) ≤ p i ∧ p i ≤ R := by
  simp [boxM, Fintype.mem_piFinset, Finset.mem_Icc]

/-- The index box `(iz, iy, ix)`. -/
def Bx (n : ℕ) : Finset (ℕ × ℕ × ℕ) := range n ×ˢ range n ×ˢ range n

/-- The lattice point of an index. -/
def pt (R : ℕ) (q : ℕ × ℕ × ℕ) : Mode := ![(q.2.2 : ℤ) - R, (q.2.1 : ℤ) - R, (q.1 : ℤ) - R]

/-- The index of a lattice point. -/
def ptInv (R : ℕ) (p : Mode) : ℕ × ℕ × ℕ :=
  ((p 2 + R).toNat, (p 1 + R).toNat, (p 0 + R).toNat)

lemma pt_mem {R : ℕ} {q : ℕ × ℕ × ℕ} (hq : q ∈ Bx (2 * R + 1)) : pt R q ∈ boxM R := by
  simp only [Bx, mem_product, mem_range] at hq
  obtain ⟨h1, h2, h3⟩ := hq
  rw [mem_boxM]
  intro i
  fin_cases i <;> simp [pt] <;> omega

lemma ptInv_mem {R : ℕ} {p : Mode} (hp : p ∈ boxM R) : ptInv R p ∈ Bx (2 * R + 1) := by
  rw [mem_boxM] at hp
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  simp only [Bx, ptInv, mem_product, mem_range]
  omega

lemma pt_ptInv {R : ℕ} {p : Mode} (hp : p ∈ boxM R) : pt R (ptInv R p) = p := by
  rw [mem_boxM] at hp
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  funext i
  fin_cases i <;> simp [pt, ptInv] <;> omega

lemma ptInv_pt {R : ℕ} {q : ℕ × ℕ × ℕ} (hq : q ∈ Bx (2 * R + 1)) : ptInv R (pt R q) = q := by
  obtain ⟨a, b, c⟩ := q
  simp [ptInv, pt]

/-- Sums over the box in the index coordinates. -/
lemma sum_box {β : Type*} [AddCommMonoid β] (R : ℕ) (f : Mode → β) :
    ∑ q ∈ Bx (2 * R + 1), f (pt R q) = ∑ p ∈ boxM R, f p := by
  refine sum_nbij' (pt R) (ptInv R) (fun _ h => pt_mem h) (fun _ h => ptInv_mem h)
    (fun _ h => ptInv_pt h) (fun _ h => pt_ptInv h) (fun _ _ => rfl)

lemma nsq_pt (R : ℕ) (q : ℕ × ℕ × ℕ) : nsq (pt R q) = sq R q.1 + sq R q.2.1 + sq R q.2.2 := by
  zify
  rw [sq_cast, sq_cast, sq_cast]
  simp [nsq, pt, Fin.sum_univ_three]
  ring

/-- The squared length in index coordinates. -/
def sqs (R : ℕ) (q : ℕ × ℕ × ℕ) : ℕ := sq R q.1 + sq R q.2.1 + sq R q.2.2

lemma theta_spec (w R n b : ℕ) (hb : n < 2 ^ b) :
    theta w R n b = ∑ i ∈ range n, (2 ^ w) ^ sq R i := by
  unfold theta
  rw [pkB_spec, Nat.mod_eq_of_lt hb]
  refine sum_congr rfl fun i _ => ?_
  simp only [zero_add, pow_zero, one_pow, mul_one, Nat.mul_eq, shl_eq, one_mul, pow_mul]

lemma th3_spec (w R n b : ℕ) (hb : n < 2 ^ b) :
    th3 w R n b = ∑ q ∈ Bx n, 1 * (2 ^ w) ^ sqs R q := by
  unfold th3
  rw [lit_eq]
  simp only [Nat.mul_eq]
  rw [theta_spec w R n b hb, Bx, sum_product, mul_assoc, sum_mul]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_product, sum_mul_sum, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun l _ => ?_
  simp only [sqs, one_mul, pow_add]
  ring

lemma card_Bx (n : ℕ) : (Bx n).card = n ^ 3 := by
  simp [Bx, card_product]; ring

/-- The digits of `th3` are the representation numbers of the box. -/
theorem dig_th3 {w R n b : ℕ} (hb : n < 2 ^ b) (hX : n ^ 3 < 2 ^ w) (s : ℕ) (M : ℕ)
    (hM : ∀ q ∈ Bx n, sqs R q < M) (hs : s < M) :
    Dig (2 ^ w) (th3 w R n b) s = ((Bx n).filter (fun q => sqs R q = s)).card := by
  rw [th3_spec w R n b hb, dig_fiber (by positivity) (Bx n) (fun _ => 1) (sqs R) hM ?_ s hs]
  · simp
  · intro t _
    simp only [sum_const, smul_eq_mul, mul_one]
    calc _ ≤ (Bx n).card := card_filter_le _ _
      _ = n ^ 3 := card_Bx n
      _ < _ := hX

/-- Specification of `dsum`. -/
lemma dsum_spec (w : ℕ) (φ : ℕ → ℕ) (m : ℕ) (N lo : ℕ) :
    dsum w φ m N lo = ∑ i ∈ range (2 ^ m), φ (lo + i) * Dig (2 ^ w) N i := by
  induction m generalizing N lo with
  | zero =>
    show Nat.mul (φ lo) (Nat.mod N (Nat.shiftLeft 1 w)) = _
    have e : Nat.mod N (Nat.shiftLeft 1 w) = N % 2 ^ w := by
      show N % _ = _
      rw [shl_eq, one_mul]
    rw [e]
    simp [Dig]
  | succ m ih =>
    show lit N (fun N' => Nat.add
      (dsum w φ m (Nat.mod N' (Nat.shiftLeft 1 (Nat.mul w (Nat.shiftLeft 1 m)))) lo)
      (dsum w φ m (Nat.shiftRight N' (Nat.mul w (Nat.shiftLeft 1 m)))
        (Nat.add lo (Nat.shiftLeft 1 m)))) = _
    rw [lit_eq]
    have e1 : Nat.mod N (Nat.shiftLeft 1 (Nat.mul w (Nat.shiftLeft 1 m))) = N % (2 ^ w) ^ (2 ^ m) := by
      show N % _ = _
      simp only [shl_eq, Nat.mul_eq, one_mul, pow_mul]
    have e2 : Nat.shiftRight N (Nat.mul w (Nat.shiftLeft 1 m)) = N / (2 ^ w) ^ (2 ^ m) := by
      show N >>> _ = _
      simp only [Nat.shiftRight_eq_div_pow, shl_eq, Nat.mul_eq, one_mul, pow_mul]
    rw [e1, e2]
    simp only [Nat.add_eq, shl_eq, one_mul]
    rw [ih, ih, pow_succ, mul_two, sum_range_add]
    congr 1
    · refine sum_congr rfl fun i hi => ?_
      rw [dig_mod _ _ _ (mem_range.1 hi)]
    · refine sum_congr rfl fun i _ => ?_
      rw [dig_div, add_assoc]

/-- A radial sum over the index box is a `dsum`. -/
theorem radial_sum {w R n b m : ℕ} (hb : n < 2 ^ b) (hX : n ^ 3 < 2 ^ w) (φ : ℕ → ℕ)
    (hφ : ∀ s, 2 ^ m ≤ s → φ s = 0) :
    ∑ q ∈ Bx n, φ (sqs R q) = dsum w φ m (th3 w R n b) 0 := by
  classical
  set U := (Bx n).sup (sqs R) + 1 with hU
  have hUq : ∀ q ∈ Bx n, sqs R q < U := fun q hq =>
    Nat.lt_succ_of_le (le_sup (f := sqs R) hq)
  set M := U + 2 ^ m with hM
  have h1 : ∑ q ∈ Bx n, φ (sqs R q) =
      ∑ s ∈ range M, ∑ q ∈ (Bx n).filter (fun q => sqs R q = s), φ (sqs R q) := by
    rw [sum_fiberwise_of_maps_to (fun q hq => mem_range.2
      (lt_of_lt_of_le (hUq q hq) (Nat.le_add_right _ _)))]
  have h2 : ∀ s, ∑ q ∈ (Bx n).filter (fun q => sqs R q = s), φ (sqs R q) =
      φ s * ((Bx n).filter (fun q => sqs R q = s)).card := by
    intro s
    rw [sum_congr rfl (fun q hq => by rw [(mem_filter.1 hq).2]), sum_const, smul_eq_mul, mul_comm]
  rw [h1, dsum_spec]
  simp only [h2, zero_add]
  have hsub : range (2 ^ m) ⊆ range M := range_subset_range.2 (Nat.le_add_left _ _)
  rw [← sum_subset hsub]
  · refine sum_congr rfl fun s hs => ?_
    rw [dig_th3 hb hX s M (fun q hq => lt_of_lt_of_le (hUq q hq) (Nat.le_add_right _ _))
      (mem_range.1 (hsub hs))]
  · intro s hs hs'
    rw [hφ s (by simpa using hs'), zero_mul]

/-- `sqs` on the box index is `nsq`. -/
lemma sqs_eq_nsq (R : ℕ) (q : ℕ × ℕ × ℕ) : sqs R q = nsq (pt R q) := (nsq_pt R q).symm

/-- A radial sum over the lattice box is a `dsum`. -/
theorem radial_box {w R b m : ℕ} (hb : 2 * R + 1 < 2 ^ b) (hX : (2 * R + 1) ^ 3 < 2 ^ w)
    (φ : ℕ → ℕ) (hφ : ∀ s, 2 ^ m ≤ s → φ s = 0) :
    ∑ p ∈ boxM R, φ (nsq p) = dsum w φ m (th3 w R (2 * R + 1) b) 0 := by
  rw [← radial_sum hb hX φ hφ, ← sum_box R (fun p => φ (nsq p))]
  exact sum_congr rfl fun q _ => by rw [sqs_eq_nsq]

/-- The ball of radius `t`, as a finite set. -/
def ballF (t : ℕ) : Finset Mode := (boxM t).filter fun p => nsq p ≤ t ^ 2

/-- The lattice count `N(t) = #{|p| ≤ t}`. -/
def ballC (t : ℕ) : ℕ := (ballF t).card

lemma coord_sq_le (p : Mode) (i : Fin 3) : (p i).natAbs ^ 2 ≤ nsq p :=
  Finset.single_le_sum (f := fun j => (p j).natAbs ^ 2) (fun _ _ => Nat.zero_le _) (mem_univ i)

/-- A point of squared length `≤ t²` lies in the box of radius `t`. -/
lemma mem_box_of_nsq {t : ℕ} {p : Mode} (h : nsq p ≤ t ^ 2) : p ∈ boxM t := by
  rw [mem_boxM]
  intro i
  have h1 := coord_sq_le p i
  have h2 : (p i).natAbs ≤ t := by
    by_contra h3
    have : t + 1 ≤ (p i).natAbs := by omega
    have := Nat.pow_le_pow_left this 2
    nlinarith
  omega

lemma mem_ballF {t : ℕ} {p : Mode} : p ∈ ballF t ↔ nsq p ≤ t ^ 2 := by
  simp only [ballF, mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_box_of_nsq h, h⟩⟩

lemma ballF_mono {s t : ℕ} (h : s ≤ t) : ballF s ⊆ ballF t := by
  intro p hp
  rw [mem_ballF] at hp ⊢
  exact hp.trans (Nat.pow_le_pow_left h 2)

/-- The digits of `th4` are prefix counts. -/
theorem dig_th4 {w R n b M bM : ℕ} (hb : n < 2 ^ b) (hbM : M < 2 ^ bM) (hX : n ^ 3 < 2 ^ w)
    (s : ℕ) (hs : s < M) (U : ℕ) (hU : ∀ q ∈ Bx n, sqs R q < U) :
    Dig (2 ^ w) (th4 w R n b M bM) s = ((Bx n).filter (fun q => sqs R q ≤ s)).card := by
  classical
  have e1 : pkB w (fun _ => 1) M bM 0 = ∑ j ∈ range M, 1 * (2 ^ w) ^ j := by
    rw [pkB_spec, Nat.mod_eq_of_lt hbM]
  unfold th4
  simp only [Nat.mul_eq]
  rw [th3_spec w R n b hb, e1, pack_mul]
  have hfib : ∀ t, ∑ q ∈ (Bx n ×ˢ range M).filter (fun q => sqs R q.1 + q.2 = t), 1 * 1 ≤
      ((Bx n).filter (fun q => sqs R q ≤ t)).card := by
    intro t
    simp only [mul_one, sum_const, smul_eq_mul]
    refine card_le_card_of_injOn Prod.fst ?_ ?_
    · intro q hq
      simp only [coe_filter, Set.mem_ofPred_eq, mem_product] at hq ⊢
      exact ⟨hq.1.1, by omega⟩
    · intro q hq q' hq' h
      simp only [coe_filter, Set.mem_ofPred_eq, mem_product] at hq hq'
      have h2 : sqs R q.1 = sqs R q'.1 := by rw [h]
      exact Prod.ext h (by omega)
  have hle : ∀ t, ((Bx n).filter (fun q => sqs R q ≤ t)).card < 2 ^ w := fun t =>
    calc _ ≤ (Bx n).card := card_filter_le _ _
      _ = n ^ 3 := card_Bx n
      _ < _ := hX
  rw [dig_fiber (M := U + M) (by positivity) (Bx n ×ˢ range M) (fun q => 1 * 1)
    (fun q => sqs R q.1 + q.2) ?_ (fun t _ => lt_of_le_of_lt (hfib t) (hle t)) s (by omega)]
  · refine le_antisymm (hfib s) ?_
    simp only [mul_one, sum_const, smul_eq_mul]
    refine card_le_card_of_injOn (fun q => (q, s - sqs R q)) ?_ ?_
    · intro q hq
      simp only [coe_filter, Set.mem_ofPred_eq, mem_product, mem_range] at hq ⊢
      exact ⟨⟨hq.1, by omega⟩, by omega⟩
    · intro q _ q' _ h
      exact (Prod.ext_iff.1 h).1
  · intro q hq
    have h1 := hU q.1 (mem_product.1 hq).1
    have h2 := mem_range.1 (mem_product.1 hq).2
    omega

/-- The prefix digit at `t²` is the ball count, for `t ≤ R`. -/
theorem dig_th4_ball {w R b M bM t : ℕ} (hb : 2 * R + 1 < 2 ^ b) (hbM : M < 2 ^ bM)
    (hX : (2 * R + 1) ^ 3 < 2 ^ w) (ht : t ≤ R) (hM : t ^ 2 < M) (U : ℕ)
    (hU : ∀ q ∈ Bx (2 * R + 1), sqs R q < U) :
    Dig (2 ^ w) (th4 w R (2 * R + 1) b M bM) (t ^ 2) = ballC t := by
  rw [dig_th4 hb hbM hX _ hM U hU, ballC]
  refine card_nbij' (pt R) (ptInv R) ?_ ?_ ?_ ?_
  · intro q hq
    simp only [coe_filter, Set.mem_ofPred_eq] at hq
    exact mem_ballF.2 (by rw [← sqs_eq_nsq]; exact hq.2)
  · intro p hp
    have hp' := mem_ballF.1 hp
    have hbox : p ∈ boxM R := mem_box_of_nsq (hp'.trans (Nat.pow_le_pow_left ht 2))
    simp only [coe_filter, Set.mem_ofPred_eq]
    exact ⟨ptInv_mem hbox, by rw [sqs_eq_nsq, pt_ptInv hbox]; exact hp'⟩
  · intro q hq
    exact ptInv_pt (mem_filter.1 hq).1
  · intro p hp
    have hp' := mem_ballF.1 hp
    exact pt_ptInv (mem_box_of_nsq (hp'.trans (Nat.pow_le_pow_left ht 2)))

lemma cut_eq (lo hi n x : ℕ) : cut lo hi n x = if lo < n ∧ n ≤ hi then x else 0 := by
  unfold cut
  by_cases h1 : n ≤ hi
  · by_cases h2 : n ≤ lo
    · have e1 := Nat.ble_eq_true_of_le h1
      have e2 := Nat.ble_eq_true_of_le h2
      rw [e1, e2]; simp [show ¬ (lo < n) by omega]
    · have e1 := Nat.ble_eq_true_of_le h1
      have e2 : Nat.ble n lo = false := by
        rw [← Bool.not_eq_true]; intro h; exact h2 (Nat.le_of_ble_eq_true h)
      rw [e1, e2]; simp [show lo < n by omega, h1]
  · have e1 : Nat.ble n hi = false := by
      rw [← Bool.not_eq_true]; intro h; exact h1 (Nat.le_of_ble_eq_true h)
    rw [e1]; simp [h1]

/-- `rad128` is a radial sum over the box of radius `128`, for `φ` supported below `2¹⁵`. -/
lemma rad128_eq (φ : ℕ → ℕ) (hφ : ∀ s, 2 ^ 15 ≤ s → φ s = 0) :
    rad128 φ = ∑ p ∈ boxM 128, φ (nsq p) := by
  unfold rad128
  rw [lit_eq]
  exact (radial_box (R := 128) (w := 32) (b := 9) (m := 15) (by norm_num) (by norm_num) φ hφ).symm

/-- `rad78` is a radial sum over the box of radius `78`, for `φ` supported below `2¹³`. -/
lemma rad78_eq (φ : ℕ → ℕ) (hφ : ∀ s, 2 ^ 13 ≤ s → φ s = 0) :
    rad78 φ = ∑ p ∈ boxM 78, φ (nsq p) := by
  unfold rad78
  rw [lit_eq]
  exact (radial_box (R := 78) (w := 32) (b := 8) (m := 13) (by norm_num) (by norm_num) φ hφ).symm

end Row
end OVNS
