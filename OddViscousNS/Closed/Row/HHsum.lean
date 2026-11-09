import OddViscousNS.Closed.Row.LowSpec

/-!
# The high pairs of the matrix band

On `hhF k` the metric is affine and `W = ω_C`, so the summand is a combination of the separated
kernels `A^i B^j / (A² B² h_A h_B)`.  Their sums `M i j` are compared with the integer convolutions:
floors from below, and from above up to the rounding constant `errS`.
-/

open Finset

noncomputable section

namespace OVNS
namespace Row

set_option maxRecDepth 20000
set_option linter.constructorNameAsVariable false

/-- `A^(i-2)/h_A`. -/
def fr (i A : ℕ) : ℝ := (A : ℝ) ^ i / ((A : ℝ) ^ 2 * hmet A)

/-- The real kernel sum over the high pairs. -/
def Mh (i j : ℕ) (k : Mode) (v : R3) : ℝ :=
  ∑ p ∈ hhF k, fr i (nsq p) * fr j (nsq (k - p)) * dR p v ^ 2

/-- The integer convolution, as a real form. -/
def MR (F G : ℕ → ℕ) (k : Mode) (v : R3) : ℝ :=
  ∑ p ∈ boxM 78, (F (nsq p) : ℝ) * (G (nsq (k - p)) : ℝ) * dR p v ^ 2

lemma mem_hhF {k p : Mode} : p ∈ hhF k ↔
    120 < nsq p ∧ nsq p ≤ 6084 ∧ 120 < nsq (k - p) ∧ nsq (k - p) ≤ 6084 := by
  simp only [hhF, mem_filter, and_iff_right_iff_imp]
  exact fun h => mem_box_of_nsq (t := 78) (by rw [nsq_78]; exact h.2.1)

/-- The reflection on the high pairs. -/
lemma hh_reflect {k : Mode} (f : Mode → ℝ) : ∑ p ∈ hhF k, f (k - p) = ∑ p ∈ hhF k, f p := by
  refine sum_nbij' (fun p => k - p) (fun p => k - p) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [mem_hhF] at hp ⊢
    rw [sub_sub_self']
    exact ⟨hp.2.2.1, hp.2.2.2, hp.1, hp.2.1⟩
  · intro p hp
    rw [mem_hhF] at hp ⊢
    rw [sub_sub_self']
    exact ⟨hp.2.2.1, hp.2.2.2, hp.1, hp.2.1⟩
  · intro p _; exact sub_sub_self' k p
  · intro p _; exact sub_sub_self' k p
  · intro p _; rfl

/-- The kernels commute on `v ⊥ k`. -/
lemma Mh_swap (i j : ℕ) (k : Mode) (v : R3) (hv : dR k v = 0) : Mh j i k v = Mh i j k v := by
  unfold Mh
  rw [← hh_reflect (k := k)]
  refine sum_congr rfl fun p _ => ?_
  rw [sub_sub_self', dR_symm_sq k p v hv]
  ring

/-- The separated form of the weights on a high pair. -/
lemma w_hh {k p : Mode} (hp : p ∈ hhF k) :
    let e := hm k - 117 / 500
    let δ := hm k - 29 / 100 * absSq k - 117 / 500
    let a : ℝ := 29 / 100
    let g := fun i j => fr i (nsq p) * fr j (nsq (k - p))
    w1 k p = om (nsq k) ^ 2 * (e ^ 2 * (g 1 0 + g 0 1) - 2 * a * e * (g 2 0 + g 0 2)
        + a ^ 2 * (g 3 0 + g 0 3)) ∧
      w2 k p = om (nsq k) ^ 2 * (δ ^ 2 * (g 2 0 + g 0 2 - 2 * g 1 1)
        + a ^ 2 * (g 3 1 + g 1 3 - 2 * g 2 2)) := by
  intro e δ a g
  obtain ⟨h1, h2, h3, h4⟩ := mem_hhF.1 hp
  have hA0 : (0 : ℝ) < nsq p := by exact_mod_cast (show 0 < nsq p by omega)
  have hB0 : (0 : ℝ) < nsq (k - p) := by exact_mod_cast (show 0 < nsq (k - p) by omega)
  have hhA : hmet (nsq p) = 29 / 100 * (nsq p : ℝ) + 117 / 500 := by
    rw [hmet_affine (by omega)]; ring
  have hhB : hmet (nsq (k - p)) = 29 / 100 * (nsq (k - p) : ℝ) + 117 / 500 := by
    rw [hmet_affine (by omega)]; ring
  have hL : Lst k p = ((nsq p : ℝ) - nsq (k - p)) * δ := by
    simp only [Lst, hm, hhA, hhB, δ, ← nsq_cast]
    ring
  have hW := Wk_high k p (by omega) (by omega)
  have hg : ∀ i j, g i j = (nsq p : ℝ) ^ i * (nsq (k - p) : ℝ) ^ j /
      ((nsq p : ℝ) ^ 2 * (nsq (k - p) : ℝ) ^ 2 * (hmet (nsq p) * hmet (nsq (k - p)))) := by
    intro i j
    simp only [g, fr]
    rw [div_mul_div_comm]
    congr 1
    · ring
  have hhe : hm k = e + 117 / 500 := by simp only [e]; ring
  constructor
  · unfold w1
    rw [hW]
    simp only [hg]
    simp only [hm, ← nsq_cast] at hhe ⊢
    simp only [hhA, hhB]
    set A := (nsq p : ℝ)
    set B := (nsq (k - p) : ℝ)
    set hC := hmet (nsq k)
    have hne1 : (29 / 100 * A + 117 / 500) ≠ 0 := by positivity
    have hne2 : (29 / 100 * B + 117 / 500) ≠ 0 := by positivity
    simp only [hhe, a]
    field_simp
    ring
  · unfold w2
    rw [hW, hL]
    simp only [hg]
    simp only [hm, ← nsq_cast]
    simp only [hhA, hhB]
    set A := (nsq p : ℝ)
    set B := (nsq (k - p) : ℝ)
    have hne1 : (29 / 100 * A + 117 / 500) ≠ 0 := by positivity
    have hne2 : (29 / 100 * B + 117 / 500) ≠ 0 := by positivity
    simp only [a]
    field_simp
    ring

/-- The two forms of the high-pair sum. -/
theorem hh_sum1 (k : Mode) (v : R3) (hv : dR k v = 0) :
    ∑ p ∈ hhF k, w1 k p * dR p v ^ 2 = om (nsq k) ^ 2 * (2 * (hm k - 117 / 500) ^ 2 * Mh 1 0 k v
      - 4 * (29 / 100) * (hm k - 117 / 500) * Mh 2 0 k v + 2 * (29 / 100) ^ 2 * Mh 3 0 k v) := by
  have e : 2 * (hm k - 117 / 500) ^ 2 * Mh 1 0 k v
      - 4 * (29 / 100) * (hm k - 117 / 500) * Mh 2 0 k v + 2 * (29 / 100) ^ 2 * Mh 3 0 k v =
      (hm k - 117 / 500) ^ 2 * (Mh 1 0 k v + Mh 0 1 k v)
      - 2 * (29 / 100) * (hm k - 117 / 500) * (Mh 2 0 k v + Mh 0 2 k v)
      + (29 / 100) ^ 2 * (Mh 3 0 k v + Mh 0 3 k v) := by
    rw [Mh_swap 1 0 k v hv, Mh_swap 2 0 k v hv, Mh_swap 3 0 k v hv]
    ring
  rw [e]
  unfold Mh
  simp only [← sum_add_distrib, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun p hp => ?_
  rw [(w_hh hp).1]
  ring

theorem hh_sum2 (k : Mode) (v : R3) (hv : dR k v = 0) :
    ∑ p ∈ hhF k, w2 k p * dR p v ^ 2 = om (nsq k) ^ 2 *
      (2 * (hm k - 29 / 100 * absSq k - 117 / 500) ^ 2 * (Mh 2 0 k v - Mh 1 1 k v)
        + 2 * (29 / 100) ^ 2 * (Mh 3 1 k v - Mh 2 2 k v)) := by
  have e : 2 * (hm k - 29 / 100 * absSq k - 117 / 500) ^ 2 * (Mh 2 0 k v - Mh 1 1 k v)
        + 2 * (29 / 100) ^ 2 * (Mh 3 1 k v - Mh 2 2 k v) =
      (hm k - 29 / 100 * absSq k - 117 / 500) ^ 2 * (Mh 2 0 k v + Mh 0 2 k v - 2 * Mh 1 1 k v)
        + (29 / 100) ^ 2 * (Mh 3 1 k v + Mh 1 3 k v - 2 * Mh 2 2 k v) := by
    rw [Mh_swap 2 0 k v hv, Mh_swap 3 1 k v hv]
    ring
  rw [e]
  unfold Mh
  simp only [← sum_add_distrib, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun p hp => ?_
  rw [(w_hh hp).2]
  ring

/-- An integer kernel rounding a real one from below, supported on the shell. -/
structure KerR (i : ℕ) (F : ℕ → ℕ) (s : ℝ) : Prop where
  pos : 0 < s
  lo : ∀ A, 120 < A → A ≤ 6084 → (F A : ℝ) / s ≤ fr i A
  hi : ∀ A, 120 < A → A ≤ 6084 → fr i A ≤ ((F A : ℝ) + 1) / s
  zero : ∀ A, ¬ (120 < A ∧ A ≤ 6084) → F A = 0

lemma KerR.ball {i F s} (h : KerR i F s) : Ball 6084 F := fun a ha => h.zero a (by omega)

lemma fr_nonneg (i A : ℕ) : 0 ≤ fr i A := by
  have h : 0 ≤ hmet A := by
    unfold hmet
    split_ifs
    · exact le_rfl
    · positivity
    · positivity
  unfold fr
  positivity

lemma dR_sq_le (p : Mode) (v : R3) : dR p v ^ 2 ≤ (nsq p : ℝ) * nR v := by
  rw [nsq_cast]
  simp only [dR, absSq, nR]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- `MR` only sees the high pairs. -/
lemma MR_hh {i j : ℕ} {F G : ℕ → ℕ} {s t : ℝ} (hF : KerR i F s) (hG : KerR j G t) (k : Mode)
    (v : R3) : MR F G k v = ∑ p ∈ hhF k, (F (nsq p) : ℝ) * (G (nsq (k - p)) : ℝ) * dR p v ^ 2 := by
  classical
  unfold MR
  symm
  refine sum_subset (filter_subset _ _) fun p hp hn => ?_
  have h : ¬ (120 < nsq p ∧ nsq p ≤ 6084 ∧ 120 < nsq (k - p) ∧ nsq (k - p) ≤ 6084) := fun h =>
    hn (mem_filter.2 ⟨hp, h⟩)
  by_cases h1 : 120 < nsq p ∧ nsq p ≤ 6084
  · have h2 : ¬ (120 < nsq (k - p) ∧ nsq (k - p) ≤ 6084) := fun h2 =>
      h ⟨h1.1, h1.2, h2.1, h2.2⟩
    rw [hG.zero _ h2]; simp
  · rw [hF.zero _ h1]; simp

/-- The floors are below the kernel. -/
theorem Mh_lo {i j : ℕ} {F G : ℕ → ℕ} {s t : ℝ} (hF : KerR i F s) (hG : KerR j G t) (k : Mode)
    (v : R3) : MR F G k v / (s * t) ≤ Mh i j k v := by
  rw [MR_hh hF hG, sum_div]
  refine sum_le_sum fun p hp => ?_
  obtain ⟨h1, h2, h3, h4⟩ := mem_hhF.1 hp
  have e1 := hF.lo _ h1 h2
  have e2 := hG.lo _ h3 h4
  have hs := hF.pos
  have ht := hG.pos
  calc (F (nsq p) : ℝ) * (G (nsq (k - p)) : ℝ) * dR p v ^ 2 / (s * t)
      = ((F (nsq p) : ℝ) / s) * ((G (nsq (k - p)) : ℝ) / t) * dR p v ^ 2 := by
        field_simp
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        exact mul_le_mul e1 e2 (by positivity) (fr_nonneg _ _)

/-- The rounding constant as lattice sums. -/
lemma errS_eq {F G : ℕ → ℕ} (hF : Ball 6084 F) (hG : Ball 6084 G) :
    errS F G = ∑ p ∈ boxM 78, F (nsq p) * nsq p + 6084 * (∑ p ∈ boxM 78, G (nsq p)
      + ∑ p ∈ boxM 78, shell 6084 (nsq p) 1) := by
  have e : (2 : ℕ) ^ 13 = 8192 := by norm_num
  unfold errS
  simp only [Nat.add_eq, Nat.mul_eq]
  rw [rad78_eq (fun n => F n * n) (fun s hs => by
      have : 6084 < s := by omega
      simp only [hF s this, zero_mul]),
    rad78_eq G (fun s hs => hG s (by omega)),
    rad78_eq (fun n => shell 6084 n 1) (fun s hs => shell_ball _ _ _ (by omega))]

/-- The rounding is below `errS`. -/
lemma round_le {i j : ℕ} {F G : ℕ → ℕ} {s t : ℝ} (hF : KerR i F s) (hG : KerR j G t) (k : Mode) :
    ∑ p ∈ hhF k, ((F (nsq p) : ℝ) + (G (nsq (k - p)) : ℝ) + 1) * (nsq p : ℝ) ≤ (errS F G : ℝ) := by
  rw [errS_eq hF.ball hG.ball]
  push_cast
  have h1 : ∑ p ∈ hhF k, (F (nsq p) : ℝ) * (nsq p : ℝ) ≤ ∑ p ∈ boxM 78, (F (nsq p) : ℝ) * (nsq p : ℝ) :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
  have h2 : ∑ p ∈ hhF k, (G (nsq (k - p)) : ℝ) * (nsq p : ℝ) ≤
      6084 * ∑ p ∈ boxM 78, (G (nsq p) : ℝ) := by
    calc ∑ p ∈ hhF k, (G (nsq (k - p)) : ℝ) * (nsq p : ℝ)
        ≤ ∑ p ∈ hhF k, (G (nsq (k - p)) : ℝ) * 6084 := by
          refine sum_le_sum fun p hp => ?_
          have h3 := (mem_hhF.1 hp).2.1
          have : (nsq p : ℝ) ≤ 6084 := by exact_mod_cast h3
          exact mul_le_mul_of_nonneg_left this (by positivity)
      _ = ∑ p ∈ hhF k, (G (nsq p) : ℝ) * 6084 :=
          hh_reflect (k := k) (fun p => (G (nsq p) : ℝ) * 6084)
      _ = 6084 * ∑ p ∈ hhF k, (G (nsq p) : ℝ) := by rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
  have h3 : ∑ p ∈ hhF k, (nsq p : ℝ) ≤ 6084 * ∑ p ∈ boxM 78, (shell 6084 (nsq p) 1 : ℝ) := by
    rw [mul_sum]
    refine (sum_le_sum fun p hp => ?_).trans
      (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity)
    obtain ⟨a1, a2, _, _⟩ := mem_hhF.1 hp
    rw [shell_eq]
    simp only [a1, a2, and_self, ↓reduceIte, Nat.cast_one, mul_one]
    exact_mod_cast a2
  have e : ∑ p ∈ hhF k, ((F (nsq p) : ℝ) + (G (nsq (k - p)) : ℝ) + 1) * (nsq p : ℝ) =
      ∑ p ∈ hhF k, (F (nsq p) : ℝ) * (nsq p : ℝ) + ∑ p ∈ hhF k, (G (nsq (k - p)) : ℝ) * (nsq p : ℝ)
        + ∑ p ∈ hhF k, (nsq p : ℝ) := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun _ _ => by ring
  rw [e]
  linarith

/-- The kernel is below the floors plus the rounding constant. -/
theorem Mh_hi {i j : ℕ} {F G : ℕ → ℕ} {s t : ℝ} (hF : KerR i F s) (hG : KerR j G t) (k : Mode)
    (v : R3) : Mh i j k v ≤ MR F G k v / (s * t) + (errS F G : ℝ) / (s * t) * nR v := by
  have hs := hF.pos
  have ht := hG.pos
  have hn := nR_nonneg v
  have hr := mul_le_mul_of_nonneg_right (round_le hF hG k) hn
  have hpt : ∀ p ∈ hhF k, fr i (nsq p) * fr j (nsq (k - p)) * dR p v ^ 2 ≤
      ((F (nsq p) : ℝ) * (G (nsq (k - p)) : ℝ) * dR p v ^ 2 +
        ((F (nsq p) : ℝ) + (G (nsq (k - p)) : ℝ) + 1) * (nsq p : ℝ) * nR v) / (s * t) := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := mem_hhF.1 hp
    have e1 := hF.hi _ h1 h2
    have e2 := hG.hi _ h3 h4
    have h5 : fr i (nsq p) * fr j (nsq (k - p)) ≤
        ((F (nsq p) : ℝ) + 1) / s * (((G (nsq (k - p)) : ℝ) + 1) / t) :=
      mul_le_mul e1 e2 (fr_nonneg _ _) (by positivity)
    have h6 := dR_sq_le p v
    have h7 := sq_nonneg (dR p v)
    rw [div_mul_div_comm] at h5
    calc fr i (nsq p) * fr j (nsq (k - p)) * dR p v ^ 2
        ≤ ((F (nsq p) : ℝ) + 1) * ((G (nsq (k - p)) : ℝ) + 1) / (s * t) * dR p v ^ 2 :=
          mul_le_mul_of_nonneg_right h5 h7
      _ = ((F (nsq p) : ℝ) * (G (nsq (k - p)) : ℝ) * dR p v ^ 2 +
          ((F (nsq p) : ℝ) + (G (nsq (k - p)) : ℝ) + 1) * dR p v ^ 2) / (s * t) := by
          field_simp
          ring
      _ ≤ _ := by
          refine div_le_div_of_nonneg_right ?_ (by positivity)
          have : ((F (nsq p) : ℝ) + (G (nsq (k - p)) : ℝ) + 1) * dR p v ^ 2 ≤
              ((F (nsq p) : ℝ) + (G (nsq (k - p)) : ℝ) + 1) * ((nsq p : ℝ) * nR v) :=
            mul_le_mul_of_nonneg_left h6 (by positivity)
          linarith
  unfold Mh
  refine (sum_le_sum hpt).trans ?_
  rw [← sum_div, sum_add_distrib, add_div, MR_hh hF hG, sum_div, ← sum_mul]
  have := div_le_div_of_nonneg_right hr (show 0 ≤ s * t by positivity)
  refine add_le_add le_rfl ?_
  calc (∑ p ∈ hhF k, ((F (nsq p) : ℝ) + (G (nsq (k - p)) : ℝ) + 1) * (nsq p : ℝ)) * nR v / (s * t)
      ≤ (errS F G : ℝ) * nR v / (s * t) := this
    _ = _ := by ring

/-- The floor of a quotient against the real quotient. -/
lemma floor_bd (n d : ℕ) (hd : 0 < d) (x s : ℝ) (hs : 0 < s) (hx : x = (n : ℝ) / d / s) :
    ((Nat.div n d : ℕ) : ℝ) / s ≤ x ∧ x ≤ (((Nat.div n d : ℕ) : ℝ) + 1) / s := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / d := Nat.cast_div_le
  have h2 : (n : ℝ) / d ≤ ((n / d : ℕ) : ℝ) + 1 := by
    rw [div_le_iff₀ hd0]
    have : n < d * (n / d + 1) := Nat.lt_mul_div_succ n hd
    have h3 : (n : ℝ) ≤ (d : ℝ) * (((n / d : ℕ) : ℝ) + 1) := by exact_mod_cast this.le
    linarith
  rw [hx]
  exact ⟨div_le_div_of_nonneg_right h1 hs.le, div_le_div_of_nonneg_right h2 hs.le⟩

/-- Building a `KerR` from a quotient. -/
lemma kerR_of {i : ℕ} {F : ℕ → ℕ} {s : ℝ} (hs : 0 < s) (n d : ℕ → ℕ)
    (hF : ∀ A, F A = shell 6084 A (Nat.div (n A) (d A))) (hd : ∀ A, 120 < A → 0 < d A)
    (hx : ∀ A, 120 < A → A ≤ 6084 → fr i A = (n A : ℝ) / (d A : ℝ) / s) : KerR i F s where
  pos := hs
  lo := fun A h1 h2 => by
    have := (floor_bd (n A) (d A) (hd A h1) _ s hs (hx A h1 h2)).1
    rw [hF, shell_eq]
    simpa only [h1, h2, and_self, ↓reduceIte] using this
  hi := fun A h1 h2 => by
    have := (floor_bd (n A) (d A) (hd A h1) _ s hs (hx A h1 h2)).2
    rw [hF, shell_eq]
    simpa only [h1, h2, and_self, ↓reduceIte] using this
  zero := fun A h => by
    rw [hF, shell_eq]
    simp only [h, ↓reduceIte]

lemma hm_shell {A : ℕ} (h : 120 < A) : hmet A = ((290 * A + 234 : ℕ) : ℝ) / 1000 := by
  rw [hmet_affine (by omega)]
  push_cast
  ring

lemma kerR3 (N : ℕ) (s : ℝ) (hs : 0 < s) (hN : (N : ℝ) = 1000 * s) : KerR 3 (F3 N 6084) s := by
  refine kerR_of hs (fun A => Nat.mul N A) (fun A => Nat.add (Nat.mul 290 A) 234)
    (fun A => rfl) (fun A _ => by simp) (fun A h1 _ => ?_)
  have hA : (A : ℝ) ≠ 0 := by exact_mod_cast (show A ≠ 0 by omega)
  have hd : ((290 : ℝ) * A + 234) ≠ 0 := by positivity
  simp only [fr, hm_shell h1, Nat.mul_eq, Nat.add_eq]
  push_cast
  rw [hN]
  field_simp

lemma kerR2 (N : ℕ) (s : ℝ) (hs : 0 < s) (hN : (N : ℝ) = 1000 * s) : KerR 2 (F2 N 6084) s := by
  refine kerR_of hs (fun _ => N) (fun A => Nat.add (Nat.mul 290 A) 234)
    (fun A => rfl) (fun A _ => by simp) (fun A h1 _ => ?_)
  have hA : (A : ℝ) ≠ 0 := by exact_mod_cast (show A ≠ 0 by omega)
  have hd : ((290 : ℝ) * A + 234) ≠ 0 := by positivity
  simp only [fr, hm_shell h1, Nat.mul_eq, Nat.add_eq]
  push_cast
  rw [hN]
  field_simp

lemma kerR1 (N : ℕ) (s : ℝ) (hs : 0 < s) (hN : (N : ℝ) = 1000 * s) : KerR 1 (F1 N 6084) s := by
  refine kerR_of hs (fun _ => N) (fun A => Nat.mul A (Nat.add (Nat.mul 290 A) 234))
    (fun A => rfl) (fun A h => ?_) (fun A h1 _ => ?_)
  · simp only [Nat.mul_eq, Nat.add_eq]; positivity
  have hA : (A : ℝ) ≠ 0 := by exact_mod_cast (show A ≠ 0 by omega)
  have hd : ((290 : ℝ) * A + 234) ≠ 0 := by positivity
  simp only [fr, hm_shell h1, Nat.mul_eq, Nat.add_eq]
  push_cast
  rw [hN]
  field_simp

lemma kerR0 (N : ℕ) (s : ℝ) (hs : 0 < s) (hN : (N : ℝ) = 1000 * s) : KerR 0 (F0 N 6084) s := by
  refine kerR_of hs (fun _ => N) (fun A => Nat.mul (Nat.mul A A) (Nat.add (Nat.mul 290 A) 234))
    (fun A => rfl) (fun A h => ?_) (fun A h1 _ => ?_)
  · simp only [Nat.mul_eq, Nat.add_eq]; positivity
  have hA : (A : ℝ) ≠ 0 := by exact_mod_cast (show A ≠ 0 by omega)
  have hd : ((290 : ℝ) * A + 234) ≠ 0 := by positivity
  simp only [fr, hm_shell h1, Nat.mul_eq, Nat.add_eq]
  push_cast
  rw [hN]
  field_simp

end Row
end OVNS
