import OddViscousNS.Closed.Row.High
import OddViscousNS.Closed.Row.HHread
import OddViscousNS.Closed.Row.NormK

/-!
# Soundness of the scalar band `44 ≤ K < 100`
-/

open Finset
open scoped ENNReal

noncomputable section

namespace OVNS
namespace Row

set_option maxRecDepth 20000
set_option linter.constructorNameAsVariable false

lemma FA_ball : Ball 16384 FA := fun a h => by
  unfold FA
  rw [cut_eq]
  simp [show ¬ a ≤ 16384 by omega]

/-- Specification of the block arrays. -/
lemma arrS_spec (nz z0 : ℕ) (hnz : nz < 2 ^ 7) :
    arrS nz z0 = ∑ q ∈ Bl 257 nz, FA (nsq (ptB 128 z0 q)) * (2 ^ 50) ^ idxP 357 q := by
  have hb : 257 < 2 ^ 9 := by norm_num
  have := arr_spec (w := 50) (P := 357) (wP := 17850) (wPP := 6372450) (R := 128) (n := 257)
    (b := 9) (nz := nz) (z0 := z0) (bz := 7) (by norm_num) (by norm_num) hb hnz
    (fun _ => row0 50 128 16384 257 9 FA) (fun _ s i => FA (s + sq 128 i))
    (fun _ s => row0_spec FA_ball hb s)
  unfold arrS
  rw [this]
  refine sum_congr rfl fun q _ => ?_
  rw [nsq_ptB']
  rfl

/-- The image of a block. -/
lemma mem_block {n nz z0 R : ℕ} (hn : n = 2 * R + 1) (hz : z0 + nz ≤ n) {p : Mode}
    (hp : p ∈ (Bl n nz).image (ptB R z0)) : p ∈ boxM R := by
  obtain ⟨q, hq, rfl⟩ := mem_image.1 hp
  simp only [Bl, mem_product, mem_range] at hq
  obtain ⟨h1, h2, h3⟩ := hq
  rw [mem_boxM]
  intro i
  fin_cases i <;> simp [ptB] <;> omega

/-- Membership in a block image. -/
lemma mem_block_iff {n nz z0 R : ℕ} (hn : n = 2 * R + 1) (hz : z0 + nz ≤ n) {p : Mode} :
    p ∈ (Bl n nz).image (ptB R z0) ↔
      p ∈ boxM R ∧ (z0 : ℤ) ≤ p 2 + R ∧ p 2 + R < z0 + nz := by
  constructor
  · intro hp
    refine ⟨mem_block hn hz hp, ?_⟩
    obtain ⟨q, hq, rfl⟩ := mem_image.1 hp
    simp only [Bl, mem_product, mem_range] at hq
    obtain ⟨h1, h2, h3⟩ := hq
    constructor
    · simp [ptB]
    · simp [ptB]; omega
  · rintro ⟨h1, h2, h3⟩
    have h1' := mem_boxM.1 h1
    have h0 := h1' 0
    have h4 := h1' 1
    refine mem_image.2 ⟨((p 2 + R - z0).toNat, (p 1 + R).toNat, (p 0 + R).toNat), ?_, ?_⟩
    · simp only [Bl, mem_product, mem_range]
      omega
    · funext i
      fin_cases i <;> simp [ptB] <;> omega

/-- Sums over a block are below sums over the box. -/
lemma block_sum_le {n nz z0 R : ℕ} (hn : n = 2 * R + 1) (hz : z0 + nz ≤ n) (f : Mode → ℕ) :
    ∑ q ∈ Bl n nz, f (ptB R z0 q) ≤ ∑ p ∈ boxM R, f p := by
  classical
  rw [← sum_image (f := f) (g := ptB R z0) (s := Bl n nz) (ptB_inj R z0 n nz)]
  exact sum_le_sum_of_subset fun p hp => mem_block hn hz hp

lemma lt_of_succ_le' {a b : ℕ} (h : a + 1 ≤ b) : a < b := h

/-- The scalar norm bound, abstractly. -/
lemma norm_gen {r Z B : ℕ} (e : r = Z) (h : Nat.add r 1 ≤ B) : Z < B := by
  subst e
  exact lt_of_succ_le' h

lemma rad_phiR : rad128 (phiR FA) = ∑ p ∈ boxM 128, FA (nsq p) ^ 2 := by
  have h2 : rad128 (phiR FA) = ∑ p ∈ boxM 128, phiR FA (nsq p) :=
    rad128_eq _ fun s hs => by
      have hs' : 16384 < s := lt_of_lt_of_le (by norm_num) hs
      simp [phiR, FA_ball s hs']
  rw [h2]
  exact sum_congr rfl fun p _ => by simp [phiR, lit_eq, pow_two]

/-- The scalar norm bound, as a sum over the lattice box. -/
lemma normS_spec (h : normS = true) : ∑ p ∈ boxM 128, FA (nsq p) ^ 2 < 2 ^ 50 := by
  have h4 : (2 : ℕ) ^ 50 = 1125899906842624 := by norm_num
  rw [h4]
  exact norm_gen rad_phiR (Nat.le_of_ble_eq_true h)

/-- `k` at natural coordinates. -/
def kN (x y z : ℕ) : Mode := ![(x : ℤ), y, z]

lemma nsq_kN (x y z : ℕ) : nsq (kN x y z) = x * x + (y * y + z * z) := by
  simp [nsq, kN, Fin.sum_univ_three]
  ring

/-- A slot of a product of two blocks of the scalar band. -/
lemma scal_slot {nz nz' z0 z0' c x y z : ℕ} (hN : ∑ p ∈ boxM 128, FA (nsq p) ^ 2 < 2 ^ 50)
    (hz1 : nz < 2 ^ 7) (hz2 : nz' < 2 ^ 7)
    (hb1 : z0 + nz ≤ 257) (hb2 : z0' + nz' ≤ 257) (hx : x < 100) (hy : y < 71) (hz : z < 58)
    (hc : z0 + z0' + c = z + 256) :
    Dig (2 ^ 50) (arrS nz z0 * arrS nz' z0') (256 + x + 357 * (y + 256) + 127449 * c) =
      ∑ p ∈ ((Bl 257 nz).image (ptB 128 z0)).filter
          (fun p => kN x y z - p ∈ (Bl 257 nz').image (ptB 128 z0')),
        FA (nsq p) * FA (nsq (kN x y z - p)) := by
  rw [arrS_spec nz z0 hz1, arrS_spec nz' z0' hz2]
  refine dig_conv (w := 50) (R := 128) (n := 257) (P := 357) (M := 2 ^ 40) (by positivity)
    (by norm_num) (fun p => FA (nsq p)) (fun p => FA (nsq p)) _ ?_ ?_ ?_ ?_
  · intro q hq
    obtain ⟨h1, h2⟩ := mem_product.1 hq
    simp only [Bl, mem_product, mem_range] at h1 h2
    simp only [idxP]
    norm_num
    omega
  · norm_num
    omega
  · rintro ⟨a, b, e⟩ h ⟨a', b', e'⟩ h'
    simp only [Bl, mem_product, mem_range] at h h'
    simp only [idxP]
    constructor
    · intro hs
      have e1 : e + e' = 256 + x := by omega
      have e2 : b + b' = 256 + y := by omega
      have e3 : a + a' = c := by omega
      funext i
      fin_cases i <;> simp [ptB, kN] <;> omega
    · intro hs
      have h0 := congrFun hs 0
      have h1 := congrFun hs 1
      have h2 := congrFun hs 2
      simp [ptB, kN] at h0 h1 h2
      omega
  · have h1 := block_sum_le (n := 257) (nz := nz) (z0 := z0) (R := 128) rfl hb1
      (fun p => FA (nsq p) ^ 2)
    have h2 := block_sum_le (n := 257) (nz := nz') (z0 := z0') (R := 128) rfl hb2
      (fun p => FA (nsq p) ^ 2)
    rw [pow_two ((2 : ℕ) ^ 50)]
    exact Nat.mul_lt_mul'' (lt_of_le_of_lt h1 hN) (lt_of_le_of_lt h2 hN)

/-- Reading a digit through the two windows. -/
lemma rd_row {x y c N : ℕ} (hx : x < 100) (hy : y < 71) :
    rd 50 x (rowS y (layer c N)) = Dig (2 ^ 50) N (256 + x + 357 * (y + 256) + 127449 * c) := by
  have hX : ∀ m, (2 ^ 6372450 : ℕ) ^ m = (2 ^ 50) ^ (127449 * m) := fun m => by
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  rw [rd_eq]
  unfold rowS layer
  rw [win_eq, win_eq]
  simp only [hX, Nat.add_eq, Nat.mul_eq, mul_one]
  rw [dig_window _ _ _ _ hx, dig_window _ _ _ _ (by omega)]
  congr 1
  ring

/-- Unfolding the loops of the band check. -/
lemma scal_point {n1 n2 n3 n4 : ℕ} (h : allN (scalZ n1 n2 n3 n4) 58 = true) {x y z : ℕ}
    (hz : z < 58) (hy : y < 71) (hx : x < 100) (hzy : z ≤ y) (hyx : y ≤ x)
    (hC1 : 1936 ≤ x * x + (y * y + z * z)) (hC2 : x * x + (y * y + z * z) < 10000) :
    scalTest (x * x + (y * y + z * z))
      (Dig (2 ^ 50) n1 (256 + x + 357 * (y + 256) + 127449 * z)
        + 2 * (Dig (2 ^ 50) n2 (256 + x + 357 * (y + 256) + 127449 * (z + 64))
          + (Dig (2 ^ 50) n3 (256 + x + 357 * (y + 256) + 127449 * (z + 64))
            + Dig (2 ^ 50) n4 (256 + x + 357 * (y + 256) + 127449 * z)))) = true := by
  have h1 := allN_spec _ _ h z hz
  unfold scalZ at h1
  simp only [litB_eq] at h1
  have h2 := allN_spec _ _ h1 y hy
  unfold scalY at h2
  rw [Nat.ble_eq_true_of_le hzy] at h2
  simp only [litB_eq] at h2
  have h3 := allN_spec _ _ h2 x hx
  unfold scalPt at h3
  simp only [litB_eq, Nat.add_eq, Nat.mul_eq] at h3
  have e1 : Bool.and (Nat.ble y x) (Nat.ble 1936 (x * x + (y * y + z * z))) = true := by
    rw [Nat.ble_eq_true_of_le hyx, Nat.ble_eq_true_of_le hC1]; rfl
  have e2 : Nat.ble 10000 (x * x + (y * y + z * z)) = false := by
    rw [← Bool.not_eq_true]; intro h'; have := Nat.le_of_ble_eq_true h'; omega
  rw [e1, e2] at h3
  have h4 : scalTest (x * x + (y * y + z * z)) _ = true := h3
  rw [rd_row hx hy, rd_row hx hy, rd_row hx hy, rd_row hx hy] at h4
  exact h4

/-- What the test says. -/
lemma scalTest_spec {C S : ℕ} (h : scalTest C S = true) : ∃ cK, C ≤ cK * cK ∧ cK ≤ 100 ∧
    S * (128 - cK) * 100000000000 + 6597069766656000000000000 ≤
      464 * gN C * (128 - cK) * 4398046511104 := by
  unfold scalTest at h
  simp only [litB_eq] at h
  have h1 : Bool.and (Nat.ble C (Nat.mul (csq C) (csq C))) (Bool.and (Nat.ble (csq C) 100)
      (Nat.ble (Nat.add (Nat.mul (Nat.mul S (Nat.sub 128 (csq C))) 100000000000)
        6597069766656000000000000) (Nat.mul (Nat.mul (Nat.mul 464 (gN C))
          (Nat.sub 128 (csq C))) 4398046511104))) = true := h
  simp only [Bool.and_eq_true] at h1
  exact ⟨csq C, Nat.le_of_ble_eq_true h1.1, Nat.le_of_ble_eq_true h1.2.1,
    Nat.le_of_ble_eq_true h1.2.2⟩

/-- Exactly one of the seven block pairs holds. -/
lemma one_hot (u v z : ℤ) (n : ℕ) (hu : 0 ≤ u ∧ u ≤ 256) (hv : 0 ≤ v ∧ v ≤ 256)
    (huv : u + v = z + 256) (hz : 0 ≤ z ∧ z < 58) :
    (if 128 ≤ u ∧ u < 192 ∧ 128 ≤ v ∧ v < 192 then n else 0)
      + (if 64 ≤ u ∧ u < 128 ∧ 128 ≤ v ∧ v < 192 then n else 0)
      + (if 128 ≤ u ∧ u < 192 ∧ 64 ≤ v ∧ v < 128 then n else 0)
      + (if 0 ≤ u ∧ u < 64 ∧ 192 ≤ v ∧ v < 257 then n else 0)
      + (if 192 ≤ u ∧ u < 257 ∧ 0 ≤ v ∧ v < 64 then n else 0)
      + (if 64 ≤ u ∧ u < 128 ∧ 192 ≤ v ∧ v < 257 then n else 0)
      + (if 192 ≤ u ∧ u < 257 ∧ 64 ≤ v ∧ v < 128 then n else 0) = n := by
  split_ifs <;> omega

/-- The pairs with both legs in the box. -/
def boxT (k : Mode) : Finset Mode := (boxM 128).filter fun p => k - p ∈ boxM 128

/-- The convolution summand. -/
def fS (k p : Mode) : ℕ := FA (nsq p) * FA (nsq (k - p))

/-- A block sum as a cut of the sum over `boxT`. -/
lemma block_eq {k : Mode} {z0 nz z0' nz' : ℕ} {lo hi lo' hi' : ℤ} (h1 : z0 + nz ≤ 257)
    (h2 : z0' + nz' ≤ 257) (e1 : (z0 : ℤ) = lo) (e2 : (z0 : ℤ) + nz = hi) (e3 : (z0' : ℤ) = lo')
    (e4 : (z0' : ℤ) + nz' = hi') :
    ∑ p ∈ ((Bl 257 nz).image (ptB 128 z0)).filter
        (fun p => k - p ∈ (Bl 257 nz').image (ptB 128 z0')), FA (nsq p) * FA (nsq (k - p)) =
      ∑ p ∈ boxT k, if lo ≤ p 2 + 128 ∧ p 2 + 128 < hi ∧ lo' ≤ (k - p) 2 + 128 ∧
        (k - p) 2 + 128 < hi' then fS k p else 0 := by
  classical
  rw [← sum_filter]
  refine sum_congr ?_ fun _ _ => rfl
  ext p
  simp only [mem_filter, boxT]
  rw [mem_block_iff rfl h1, mem_block_iff rfl h2]
  push_cast
  rw [e2, e4, e1, e3]
  tauto

/-- The whole convolution is the sum of the seven block pairs. -/
lemma conv_seven {k : Mode} (hz : 0 ≤ k 2 ∧ k 2 < 58) :
    ∑ p ∈ boxM 128, fS k p =
      ∑ p ∈ boxT k, (if 128 ≤ p 2 + 128 ∧ p 2 + 128 < 192 ∧ 128 ≤ (k - p) 2 + 128 ∧
          (k - p) 2 + 128 < 192 then fS k p else 0)
      + ∑ p ∈ boxT k, (if 64 ≤ p 2 + 128 ∧ p 2 + 128 < 128 ∧ 128 ≤ (k - p) 2 + 128 ∧
          (k - p) 2 + 128 < 192 then fS k p else 0)
      + ∑ p ∈ boxT k, (if 128 ≤ p 2 + 128 ∧ p 2 + 128 < 192 ∧ 64 ≤ (k - p) 2 + 128 ∧
          (k - p) 2 + 128 < 128 then fS k p else 0)
      + ∑ p ∈ boxT k, (if 0 ≤ p 2 + 128 ∧ p 2 + 128 < 64 ∧ 192 ≤ (k - p) 2 + 128 ∧
          (k - p) 2 + 128 < 257 then fS k p else 0)
      + ∑ p ∈ boxT k, (if 192 ≤ p 2 + 128 ∧ p 2 + 128 < 257 ∧ 0 ≤ (k - p) 2 + 128 ∧
          (k - p) 2 + 128 < 64 then fS k p else 0)
      + ∑ p ∈ boxT k, (if 64 ≤ p 2 + 128 ∧ p 2 + 128 < 128 ∧ 192 ≤ (k - p) 2 + 128 ∧
          (k - p) 2 + 128 < 257 then fS k p else 0)
      + ∑ p ∈ boxT k, (if 192 ≤ p 2 + 128 ∧ p 2 + 128 < 257 ∧ 64 ≤ (k - p) 2 + 128 ∧
          (k - p) 2 + 128 < 128 then fS k p else 0) := by
  classical
  have h0 : ∑ p ∈ boxM 128, fS k p = ∑ p ∈ boxT k, fS k p := by
    rw [← sum_filter_add_sum_filter_not (boxM 128) (fun p => k - p ∈ boxM 128)]
    have : ∑ p ∈ (boxM 128).filter (fun p => ¬ k - p ∈ boxM 128), fS k p = 0 :=
      sum_eq_zero fun p hp => by
        unfold fS
        rw [ball_off_box (R := 128) (by norm_num) FA_ball (mem_filter.1 hp).2, mul_zero]
    rw [this, add_zero]
    rfl
  rw [h0]
  simp only [← sum_add_distrib]
  refine sum_congr rfl fun p hp => ?_
  obtain ⟨h1, h2⟩ := mem_filter.1 hp
  have h3 := (mem_boxM.1 h1) 2
  have h4 := (mem_boxM.1 h2) 2
  have e : (k - p) 2 = k 2 - p 2 := rfl
  rw [e] at h4 ⊢
  push_cast at h3 h4
  exact (one_hot (p 2 + 128) (k 2 - p 2 + 128) (k 2) (fS k p) (by omega) (by omega) (by omega)
    hz).symm

/-- The slot total of the four products is the whole convolution. -/
theorem conv_eq {x y z : ℕ} (hN : ∑ p ∈ boxM 128, FA (nsq p) ^ 2 < 2 ^ 50) (hx : x < 100)
    (hy : y < 71) (hz : z < 58) :
    Dig (2 ^ 50) (arrS 64 128 * arrS 64 128) (256 + x + 357 * (y + 256) + 127449 * z)
      + 2 * (Dig (2 ^ 50) (arrS 64 64 * arrS 64 128) (256 + x + 357 * (y + 256) + 127449 * (z + 64))
        + (Dig (2 ^ 50) (arrS 64 0 * arrS 65 192) (256 + x + 357 * (y + 256) + 127449 * (z + 64))
          + Dig (2 ^ 50) (arrS 64 64 * arrS 65 192) (256 + x + 357 * (y + 256) + 127449 * z))) =
      ∑ p ∈ boxM 128, fS (kN x y z) p := by
  have s22 := scal_slot (nz := 64) (nz' := 64) (z0 := 128) (z0' := 128) (c := z) hN (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hx hy hz (by omega)
  have s12 := scal_slot (nz := 64) (nz' := 64) (z0 := 64) (z0' := 128) (c := z + 64) hN (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hx hy hz (by omega)
  have s21 := scal_slot (nz := 64) (nz' := 64) (z0 := 128) (z0' := 64) (c := z + 64) hN (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hx hy hz (by omega)
  have s03 := scal_slot (nz := 64) (nz' := 65) (z0 := 0) (z0' := 192) (c := z + 64) hN (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hx hy hz (by omega)
  have s30 := scal_slot (nz := 65) (nz' := 64) (z0 := 192) (z0' := 0) (c := z + 64) hN (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hx hy hz (by omega)
  have s13 := scal_slot (nz := 64) (nz' := 65) (z0 := 64) (z0' := 192) (c := z) hN (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hx hy hz (by omega)
  have s31 := scal_slot (nz := 65) (nz' := 64) (z0 := 192) (z0' := 64) (c := z) hN (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hx hy hz (by omega)
  have hk : 0 ≤ (kN x y z) 2 ∧ (kN x y z) 2 < 58 := by
    simp only [kN]
    simp
    omega
  rw [conv_seven hk]
  rw [mul_comm (arrS 64 128) (arrS 64 64)] at s21
  rw [mul_comm (arrS 65 192) (arrS 64 0)] at s30
  rw [mul_comm (arrS 65 192) (arrS 64 64)] at s31
  rw [block_eq (lo := 128) (hi := 192) (lo' := 128) (hi' := 192) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)] at s22
  rw [block_eq (lo := 64) (hi := 128) (lo' := 128) (hi' := 192) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)] at s12
  rw [block_eq (lo := 128) (hi := 192) (lo' := 64) (hi' := 128) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)] at s21
  rw [block_eq (lo := 0) (hi := 64) (lo' := 192) (hi' := 257) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)] at s03
  rw [block_eq (lo := 192) (hi := 257) (lo' := 0) (hi' := 64) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)] at s30
  rw [block_eq (lo := 64) (hi := 128) (lo' := 192) (hi' := 257) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)] at s13
  rw [block_eq (lo := 192) (hi := 257) (lo' := 64) (hi' := 128) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)] at s31
  clear hN hx hy hz
  omega

/-- The rounded product bounds the true one. -/
lemma aa_mul_le_FA {A B : ℕ} (h1 : A ≤ 16384) (h2 : B ≤ 16384) :
    aa A * aa B ≤ ((FA A * FA B : ℕ) : ℝ) / 4398046511104 := by
  have hA : aa A ≤ (FA A : ℝ) / 2097152 := by
    rcases Nat.eq_zero_or_pos A with h | h
    · rw [h, aa_zero]; positivity
    · exact aa_le_FA h h1
  have hB : aa B ≤ (FA B : ℝ) / 2097152 := by
    rcases Nat.eq_zero_or_pos B with h | h
    · rw [h, aa_zero]; positivity
    · exact aa_le_FA h h2
  calc aa A * aa B ≤ (FA A : ℝ) / 2097152 * ((FA B : ℝ) / 2097152) :=
        mul_le_mul hA hB (aa_nonneg _) (by positivity)
    _ = _ := by push_cast; ring

lemma ite_t {α : Type*} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

/-- A point of the lens of radius `128`. -/
lemma lens128 {k p : Mode} (hO : ¬ Off k 128 p) :
    p ∈ boxM 128 ∧ nsq p ≤ 16384 ∧ nsq (k - p) ≤ 16384 := by
  have e : (128 : ℕ) ^ 2 = 16384 := by norm_num
  unfold Off at hO
  rw [e] at hO
  have h1 : nsq p ≤ 16384 := by
    by_contra h; exact hO (Or.inl (by omega))
  have h2 : nsq (k - p) ≤ 16384 := by
    by_contra h; exact hO (Or.inr (by omega))
  exact ⟨mem_box_of_nsq (t := 128) (by rw [e]; exact h1), h1, h2⟩

/-- `S_a(k)` is the lens part plus `S₄`. -/
theorem Sa_band {k : Mode} {ρ : ℕ} (hρ : ρ ≤ 128) (hk : nsq k ≤ (128 - ρ) ^ 2)
    (h120 : 120 ≤ ρ ^ 2) :
    Sa k ≤ ENNReal.ofReal (((∑ p ∈ boxM 128, fS k p : ℕ) : ℝ) / 4398046511104) + Sm 2 ρ := by
  classical
  have hpt : ∀ p, ENNReal.ofReal (aa (nsq p) * aa (nsq (k - p))) ≤
      (if p ∈ boxM 128 then ENNReal.ofReal (((fS k p : ℕ) : ℝ) / 4398046511104) else 0)
        + ENNReal.ofReal (1 / 2) * (ENNReal.ofReal (x2 ρ p) + ENNReal.ofReal (x2 ρ (k - p))) := by
    intro p
    by_cases hO : Off k 128 p
    · obtain ⟨h1, h2⟩ := off_legs hρ hk hO
      exact le_add_left (far_le h120 h1 h2)
    · refine le_add_right ?_
      obtain ⟨hp, h1, h2⟩ := lens128 hO
      rw [ite_t hp]
      exact ENNReal.ofReal_le_ofReal (aa_mul_le_FA h1 h2)
  have h1 : ∑' p : Mode, (if p ∈ boxM 128 then ENNReal.ofReal (((fS k p : ℕ) : ℝ) / 4398046511104)
      else 0) = ENNReal.ofReal (((∑ p ∈ boxM 128, fS k p : ℕ) : ℝ) / 4398046511104) := by
    rw [tsum_eq_sum (s := boxM 128) (fun p hp => by simp [hp])]
    push_cast
    rw [sum_div, ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity]
    refine sum_congr rfl fun p hp => ?_
    simp [hp]
  refine (tsum_le_tsum hpt).trans (le_of_eq ?_)
  rw [tsum_add, h1, far_sum]

/-- The real form of the band test. -/
lemma test_real {S G r : ℕ} (hr : 0 < r)
    (h : S * r * 100000000000 + 6597069766656000000000000 ≤ 464 * G * r * 4398046511104) :
    (S : ℝ) / 4398046511104 + 15 * (r : ℝ)⁻¹ ≤ 464 / 100 * ((G : ℝ) / 1000000000) := by
  have h1 : ((S * r * 100000000000 + 6597069766656000000000000 : ℕ) : ℝ) ≤
      ((464 * G * r * 4398046511104 : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h1
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have e : (S : ℝ) / 4398046511104 + 15 * (r : ℝ)⁻¹ =
      ((S : ℝ) * r * 100000000000 + 6597069766656000000000000) / (r * 439804651110400000000000) := by
    field_simp
    ring
  have e' : 464 / 100 * ((G : ℝ) / 1000000000) =
      (464 * (G : ℝ) * r * 4398046511104) / (r * 439804651110400000000000) := by
    field_simp
    ring
  rw [e, e']
  exact div_le_div_of_nonneg_right h1 (by positivity)

lemma rho_sq {ρ : ℕ} (h : 28 ≤ ρ) : 120 ≤ ρ ^ 2 := by nlinarith

lemma coords_band {x y z : ℕ} (hzy : z ≤ y) (hyx : y ≤ x) (hC2 : x * x + (y * y + z * z) < 10000) :
    x < 100 ∧ y < 71 ∧ z < 58 := by
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

/-- **The scalar band.** -/
theorem row_scal (hS : scalChk = true) (hN : normS = true) {x y z : ℕ} (hzy : z ≤ y) (hyx : y ≤ x)
    (hC1 : 1936 ≤ x * x + (y * y + z * z)) (hC2 : x * x + (y * y + z * z) < 10000)
    (c : R3) (hc : dR (kN x y z) c = 0) :
    rowR (kN x y z) c ≤
      ENNReal.ofReal (36 * gOVNS (nsq (kN x y z)) * hm (kN x y z) * nR c) := by
  obtain ⟨hx, hy, hz⟩ := coords_band hzy hyx hC2
  have hN' := normS_spec hN
  unfold scalChk at hS
  simp only [litB_eq, Nat.mul_eq] at hS
  have hp := scal_point hS hz hy hx hzy hyx hC1 hC2
  rw [conv_eq hN' hx hy hz, ← nsq_kN] at hp
  obtain ⟨cK, h1, h2, h3⟩ := scalTest_spec hp
  set k := kN x y z with hk
  set ρ := 128 - cK with hρ
  have hρ28 : 28 ≤ ρ := by omega
  have hb := Sa_band (k := k) (ρ := ρ) (by omega) (by
      have : 128 - ρ = cK := by omega
      rw [this, pow_two]; exact h1) (rho_sq hρ28)
  have hS4 := S4_le ρ hρ28
  have ht := test_real (by omega) h3
  have hg := gN_le (nsq k)
  have hr := rowR_le_Sa k c hc (by rw [hk, nsq_kN]; exact hC1)
  have h0 : 0 ≤ 36 * hm k * nR c / (464 / 100) := by
    have := hm_nonneg k
    have := nR_nonneg c
    positivity
  have hsum : Sa k ≤ ENNReal.ofReal (464 / 100 * gOVNS (nsq k)) := by
    refine hb.trans ((add_le_add le_rfl hS4).trans ?_)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal (ht.trans ?_)
    exact mul_le_mul_of_nonneg_left hg (by norm_num)
  refine hr.trans ((mul_le_mul_right hsum _).trans ?_)
  rw [← ENNReal.ofReal_mul h0]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  field_simp

end Row
end OVNS
