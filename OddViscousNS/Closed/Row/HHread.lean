import OddViscousNS.Closed.Row.Conv
import OddViscousNS.Closed.Row.NormK

/-!
# Reading the digit tables of the matrix band

A table checked by `hhChk` holds the convolutions `∑_p F(|p|²) w(p) G(|k-p|²)`, `w(p) = x²` or
`(x+y)²`, at the outputs `k ∈ [0,44)³`.
-/

open Finset

noncomputable section

namespace OVNS
namespace Row

set_option maxRecDepth 20000
set_option linter.constructorNameAsVariable false

/-- The weight `x²`. -/
def wx (p : Mode) : ℕ := (p 0).natAbs ^ 2

/-- The weight `(x+y)²`. -/
def wxy (p : Mode) : ℕ := (p 0 + p 1).natAbs ^ 2

/-- The convolution of the matrix band. -/
def DN (w : Mode → ℕ) (F G : ℕ → ℕ) (k : Mode) : ℕ :=
  ∑ p ∈ boxM 78, F (nsq p) * w p * G (nsq (k - p))

lemma sq_natAbs (R i : ℕ) : sq R i = (((i : ℤ) - R).natAbs) ^ 2 := by
  zify
  rw [sq_cast, sq_abs]

lemma nsq_ptB' (R z0 : ℕ) (q : ℕ × ℕ × ℕ) :
    nsq (ptB R z0 q) = sq R q.2.1 + sq R (z0 + q.1) + sq R q.2.2 := by
  zify
  rw [sq_cast, sq_cast, sq_cast]
  simp [nsq, ptB, Fin.sum_univ_three]
  ring

lemma image_block_full {R : ℕ} : (Bl (2 * R + 1) (2 * R + 1)).image (ptB R 0) = boxM R := by
  ext p
  constructor
  · intro hp
    obtain ⟨q, hq, rfl⟩ := mem_image.1 hp
    simp only [Bl, mem_product, mem_range] at hq
    obtain ⟨h1, h2, h3⟩ := hq
    rw [mem_boxM]
    intro i
    fin_cases i <;> simp [ptB] <;> omega
  · intro hp
    have h := mem_boxM.1 hp
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    refine mem_image.2 ⟨((p 2 + R).toNat, (p 1 + R).toNat, (p 0 + R).toNat), ?_, ?_⟩
    · simp only [Bl, mem_product, mem_range]
      omega
    · funext i
      fin_cases i <;> simp [ptB] <;> omega

/-- Sums over the full block are sums over the box. -/
lemma sum_block_full {R : ℕ} (f : Mode → ℕ) :
    ∑ q ∈ Bl (2 * R + 1) (2 * R + 1), f (ptB R 0 q) = ∑ p ∈ boxM R, f p := by
  classical
  rw [← image_block_full (R := R), sum_image (ptB_inj R 0 _ _)]

/-- Outside the box a ball-supported function vanishes. -/
lemma ball_off_box {R R2 : ℕ} {G : ℕ → ℕ} (hR : R ^ 2 = R2) (hG : Ball R2 G) {l : Mode}
    (hl : l ∉ boxM R) : G (nsq l) = 0 := by
  apply hG
  by_contra h
  exact hl (mem_box_of_nsq (by omega))

lemma idx_bound {n : ℕ} (hn : n = 157) : ∀ q ∈ Bl n n ×ˢ Bl n n, idxP 201 q.1 + idxP 201 q.2 < 2 ^ 40 := by
  subst hn
  rintro ⟨⟨a, b, e⟩, ⟨a', b', e'⟩⟩ hq
  simp only [Bl, mem_product, mem_range] at hq
  simp only [idxP]
  norm_num
  omega

lemma slot_bound {x y z : ℕ} (hx : x < 44) (hy : y < 44) (hz : z < 44) :
    156 + x + 201 * (y + 156) + 201 * 201 * (z + 156) < 2 ^ 40 := by
  norm_num
  omega

/-- **Reading a table.** -/
theorem hh_read_gen {T L R : ℕ} {U : Mode → ℕ} {G : ℕ → ℕ}
    (hL : L = ∑ q ∈ Bl 157 157, U (ptB 78 0 q) * (2 ^ 80) ^ idxP 201 q)
    (hR : R = ∑ q ∈ Bl 157 157, G (nsq (ptB 78 0 q)) * (2 ^ 80) ^ idxP 201 q)
    (hchk : hhChk T L R = true) (hG : Ball 6084 G)
    (hnorm : (∑ p ∈ boxM 78, U p ^ 2) * (∑ p ∈ boxM 78, G (nsq p) ^ 2) < (2 ^ 80) ^ 2)
    {x y z : ℕ} (hx : x < 44) (hy : y < 44) (hz : z < 44) :
    rdC T x y z = ∑ p ∈ boxM 78, U p * G (nsq ((![(x : ℤ), y, z] : Mode) - p)) := by
  classical
  have h1 := cubeChk_spec (w := 80) (P := 201) (wPP := 3232080) (off := 156) (Z := 44) (T := T)
    (N := Nat.mul L R) (by norm_num) (by norm_num) (by norm_num) hchk hx hy hz
  unfold rdC
  rw [rd_eq]
  simp only [Nat.add_eq, Nat.mul_eq]
  rw [h1]
  set k : Mode := ![(x : ℤ), y, z] with hk
  simp only [Nat.mul_eq]
  rw [hL, hR]
  have hn1 : (157 : ℕ) = 2 * 78 + 1 := by norm_num
  have hall := dig_conv (w := 80) (R := 78) (n := 157) (P := 201) (nz := 157) (nz' := 157) (z0 := 0)
    (z0' := 0) (s := 156 + x + 201 * (y + 156) + 201 * 201 * (z + 156)) (M := 2 ^ 40)
    (by positivity) (by norm_num) U (fun p => G (nsq p)) k ?_ ?_ ?_ ?_
  · rw [hall]
    have e1 : (Bl 157 157).image (ptB 78 0) = boxM 78 := image_block_full (R := 78)
    rw [e1]
    rw [← sum_filter_add_sum_filter_not (boxM 78) (fun p => k - p ∈ boxM 78)
      (fun p => U p * G (nsq (k - p)))]
    have e2 : ∑ p ∈ (boxM 78).filter (fun p => ¬ k - p ∈ boxM 78), U p * G (nsq (k - p)) = 0 :=
      sum_eq_zero fun p hp => by
        rw [ball_off_box (R := 78) (by norm_num) hG (mem_filter.1 hp).2, mul_zero]
    rw [e2, add_zero]
  · exact idx_bound (by norm_num)
  · exact slot_bound hx hy hz
  · rintro ⟨a, b, e⟩ h ⟨a', b', e'⟩ h'
    simp only [Bl, mem_product, mem_range] at h h'
    simp only [idxP]
    constructor
    · intro hs
      have e1 : e + e' = 156 + x := by omega
      have e2 : b + b' = 156 + y := by omega
      have e3 : a + a' = 156 + z := by omega
      funext i
      fin_cases i <;> simp [ptB, k] <;> omega
    · intro hs
      have h0 := congrFun hs 0
      have h1 := congrFun hs 1
      have h2 := congrFun hs 2
      simp [ptB, k] at h0 h1 h2
      omega
  · rw [sum_block_full (R := 78) (fun p => U p ^ 2), sum_block_full (R := 78) (fun p => G (nsq p) ^ 2)]
    exact hnorm

/-! ### The arrays of a kernel, in index form -/

/-- A slot of a band row: a value below `2^64` times a weight at most `6084`. -/
lemma slot78 {G : ℕ → ℕ} (hGb : ∀ A, G A < 2 ^ 64) {c : ℕ} (hc : c ≤ 6084) (A : ℕ) :
    G A * c < 2 ^ 80 :=
  calc G A * c ≤ G A * 6084 := Nat.mul_le_mul_left _ hc
    _ < 2 ^ 64 * 6084 := Nat.mul_lt_mul_of_pos_right (hGb A) (by norm_num)
    _ ≤ 2 ^ 80 := by norm_num

lemma rowW78_spec {G wt : ℕ → ℕ} (hG : Ball 6084 G) (hGb : ∀ A, G A < 2 ^ 64)
    (hwt : ∀ t < 157, wt t ≤ 6084) (s : ℕ) :
    rowW 80 157 6084 (pr78 G wt) s = ∑ i ∈ range 157, (G (s + sq 78 i) * wt i) * (2 ^ 80) ^ i :=
  rowW_spec (by norm_num) (by norm_num) (by norm_num) hG
    (fun A _ t ht => slot78 hGb (hwt t ht) A) s

lemma sq78_le {t : ℕ} (ht : t < 157) : sq 78 t ≤ 6084 := sq_le 78 t (by omega)

lemma arrR78_spec {G : ℕ → ℕ} (hG : Ball 6084 G) (hGb : ∀ A, G A < 2 ^ 64) :
    arrR78 G = ∑ q ∈ Bl 157 157, G (nsq (ptB 78 0 q)) * (2 ^ 80) ^ idxP 201 q := by
  have := arr_specT (w := 80) (P := 201) (wP := 16080) (wPP := 3232080) (R := 78) (n := 157)
    (b := 8) (nz := 157) (z0 := 0) (bz := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun _ => rowWS 80 157 6084 (pr78 G (fun _ => 1))) (fun _ s i => G (s + sq 78 i) * 1)
    (fun _ _ s => by rw [← rowW78_spec hG hGb (fun _ _ => by norm_num) s]; rfl)
  unfold arrR78
  rw [this]
  refine sum_congr rfl fun q _ => ?_
  rw [nsq_ptB', mul_one]
  rfl

lemma arrLx_spec {F : ℕ → ℕ} (hF : Ball 6084 F) (hFb : ∀ A, F A < 2 ^ 64) :
    arrLx F = ∑ q ∈ Bl 157 157, (F (nsq (ptB 78 0 q)) * wx (ptB 78 0 q)) * (2 ^ 80) ^ idxP 201 q := by
  have := arr_specT (w := 80) (P := 201) (wP := 16080) (wPP := 3232080) (R := 78) (n := 157)
    (b := 8) (nz := 157) (z0 := 0) (bz := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun _ => rowWS 80 157 6084 (pr78 F (fun t => sq 78 t))) (fun _ s i => F (s + sq 78 i) * sq 78 i)
    (fun _ _ s => by rw [← rowW78_spec hF hFb (fun _ ht => sq78_le ht) s]; rfl)
  unfold arrLx
  rw [this]
  refine sum_congr rfl fun q _ => ?_
  rw [nsq_ptB']
  have : wx (ptB 78 0 q) = sq 78 q.2.2 := by
    rw [sq_natAbs]; simp [wx, ptB]
  rw [this]
  rfl

lemma arrLxy_spec {F : ℕ → ℕ} (hF : Ball 6084 F) (hFb : ∀ A, F A < 2 ^ 64) :
    arrLxy F = ∑ q ∈ Bl 157 157, (F (nsq (ptB 78 0 q)) * wxy (ptB 78 0 q)) * (2 ^ 80) ^ idxP 201 q := by
  have := arr_specT (w := 80) (P := 201) (wP := 16080) (wPP := 3232080) (R := 78) (n := 157)
    (b := 8) (nz := 157) (z0 := 0) (bz := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (rowXYg 80 157 78 6084 (pr78 F (fun _ => 1)) (pr78 F (fun t => t)) (pr78 F (fun t => sq 78 t)))
    (fun iy s i => F (s + sq 78 i) * sq (2 * 78) (i + iy))
    (fun iy hiy s => rowXYg_spec (by omega) (rowW78_spec hF hFb (fun _ _ => by norm_num) s)
      (rowW78_spec hF hFb (fun t ht => by omega) s) (rowW78_spec hF hFb (fun _ ht => sq78_le ht) s))
  unfold arrLxy
  rw [this]
  refine sum_congr rfl fun q _ => ?_
  rw [nsq_ptB']
  have : wxy (ptB 78 0 q) = sq (2 * 78) (q.2.2 + q.2.1) := by
    rw [sq_natAbs]
    simp only [wxy, ptB]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Nat.cast_add]
    have : ((q.2.2 : ℤ) - (78 : ℕ) + ((q.2.1 : ℤ) - (78 : ℕ))) =
        (q.2.2 : ℤ) + q.2.1 - ((2 * 78 : ℕ) : ℤ) := by push_cast; ring
    rw [this]
  rw [this]
  rfl

end Row
end OVNS
