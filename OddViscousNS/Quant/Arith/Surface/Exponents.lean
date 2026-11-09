import Mathlib

/-!
# The L-shaped exponent set (route L7)

`expSet l Y = {e ∈ ℕ³ : e·l ≤ Y, e₀ < 4 ∨ e₁ < 2}`, `expA l = (2l₀+l₁)/(l₀l₁l₂)`.
The set is a union of six right triangles of lattice points; every sum is computed along the rows of
a triangle and estimated by telescoping (`h(s) = Z²s/2 − s³/6`), so no integrals are needed.

Main results: `expSet_card_ge`, `expSet_weight_le`.
-/

open Finset

namespace OVNS.Quant.Surf

/-! ## triangles of lattice points -/

/-- `{v : v b ≤ X}`. -/
noncomputable def rowS (b X : ℝ) : Finset ℕ := range (⌊X / b⌋₊ + 1)

lemma mem_rowS {b X : ℝ} (hb : 0 < b) (hX : 0 ≤ X) {v : ℕ} : v ∈ rowS b X ↔ (v : ℝ) * b ≤ X := by
  rw [rowS, mem_range, Nat.lt_succ_iff, Nat.le_floor_iff (div_nonneg hX hb.le), le_div_iff₀ hb]

lemma card_rowS_bounds {b X : ℝ} (hb : 0 < b) (hX : 0 ≤ X) :
    X / b ≤ ((rowS b X).card : ℝ) ∧ ((rowS b X).card : ℝ) ≤ X / b + 1 ∧
      (((rowS b X).card : ℝ) - 1) * b ≤ X := by
  have h0 : 0 ≤ X / b := div_nonneg hX hb.le
  have h1 := Nat.floor_le h0
  have h2 := Nat.lt_floor_add_one (X / b)
  have e : ((rowS b X).card : ℝ) = (⌊X / b⌋₊ : ℝ) + 1 := by simp [rowS]
  rw [e]
  refine ⟨h2.le, by linarith, ?_⟩
  rw [add_sub_cancel_right]
  exact (le_div_iff₀ hb).1 h1

/-- `{(u, v) : u a + v b ≤ X}`. -/
noncomputable def tri (a b X : ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact (range (⌊X / a⌋₊ + 1) ×ˢ range (⌊X / b⌋₊ + 1)).filter fun p =>
    (p.1 : ℝ) * a + (p.2 : ℝ) * b ≤ X

lemma mem_tri {a b X : ℝ} (ha : 0 < a) (hb : 0 < b) {p : ℕ × ℕ} :
    p ∈ tri a b X ↔ (p.1 : ℝ) * a + (p.2 : ℝ) * b ≤ X := by
  classical
  simp only [tri, mem_filter, mem_product, mem_range, Nat.lt_succ_iff]
  refine ⟨fun h => h.2, fun h => ⟨⟨?_, ?_⟩, h⟩⟩
  · have h1 : (p.1 : ℝ) * a ≤ X := by
      have : 0 ≤ (p.2 : ℝ) * b := by positivity
      linarith
    exact Nat.le_floor ((le_div_iff₀ ha).2 h1)
  · have h1 : (p.2 : ℝ) * b ≤ X := by
      have : 0 ≤ (p.1 : ℝ) * a := by positivity
      linarith
    exact Nat.le_floor ((le_div_iff₀ hb).2 h1)

/-- Sum over a triangle by rows. -/
lemma sum_triangle {a b X : ℝ} (ha : 0 < a) (hb : 0 < b) (hX : 0 ≤ X) (f : ℕ → ℕ → ℝ) :
    ∑ p ∈ tri a b X, f p.1 p.2 =
      ∑ u ∈ rowS a X, ∑ v ∈ rowS b (X - u * a), f u v := by
  classical
  rw [Finset.sum_sigma']
  refine Finset.sum_bij' (fun p _ => ⟨p.1, p.2⟩) (fun p _ => (p.1, p.2)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨u, v⟩ hp
    rw [mem_tri ha hb] at hp
    simp only at hp
    have h1 : (u : ℝ) * a ≤ X := by
      have : 0 ≤ (v : ℝ) * b := by positivity
      linarith
    simp only [mem_sigma]
    exact ⟨(mem_rowS ha hX).2 h1, (mem_rowS hb (by linarith)).2 (by linarith)⟩
  · rintro ⟨u, v⟩ hp
    simp only [mem_sigma] at hp
    have h1 := (mem_rowS ha hX).1 hp.1
    have h2 := (mem_rowS hb (by linarith)).1 hp.2
    rw [mem_tri ha hb]
    simp only
    linarith
  · rintro ⟨u, v⟩ _; rfl
  · rintro ⟨u, v⟩ _; rfl
  · rintro ⟨u, v⟩ _; rfl

/-- A row of a triangle stays inside the triangle. -/
lemma rowS_le {a X : ℝ} (ha : 0 < a) (hX : 0 ≤ X) {u : ℕ} (hu : u ∈ rowS a X) :
    (u : ℝ) * a ≤ X := (mem_rowS ha hX).1 hu

lemma gauss_real (n : ℕ) : ∑ i ∈ range n, (i : ℝ) = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- Telescoping along the rows. -/
lemma sum_rows_le {a X : ℝ} (f : ℕ → ℝ) (G : ℕ → ℝ) (h : ∀ u ∈ rowS a X, f u ≤ G (u + 1) - G u) :
    ∑ u ∈ rowS a X, f u ≤ G (rowS a X).card - G 0 := by
  have e : (rowS a X).card = ⌊X / a⌋₊ + 1 := by simp [rowS]
  rw [e, ← Finset.sum_range_sub G]
  exact Finset.sum_le_sum h

lemma le_sum_rows {a X : ℝ} (f : ℕ → ℝ) (G : ℕ → ℝ) (h : ∀ u ∈ rowS a X, G (u + 1) - G u ≤ f u) :
    G (rowS a X).card - G 0 ≤ ∑ u ∈ rowS a X, f u := by
  have e : (rowS a X).card = ⌊X / a⌋₊ + 1 := by simp [rowS]
  rw [e, ← Finset.sum_range_sub G]
  exact Finset.sum_le_sum h

/-- The upper bound for the number of points of a triangle. -/
theorem tri_card_le {a b X : ℝ} (ha : 0 < a) (hb : 0 < b) (hX : 0 ≤ X) :
    ((tri a b X).card : ℝ) ≤ (X + a + b) ^ 2 / (2 * a * b) := by
  have hc := sum_triangle ha hb hX (fun _ _ => 1)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  rw [hc]
  set Z := X + a + b with hZ
  set M := (rowS a X).card with hM
  set G : ℕ → ℝ := fun s => (Z * s - a * (s : ℝ) ^ 2 / 2) / b with hG
  have hterm : ∀ u ∈ rowS a X, ((rowS b (X - u * a)).card : ℝ) ≤ G (u + 1) - G u := by
    intro u hu
    have h1 := rowS_le ha hX hu
    have h2 := (card_rowS_bounds hb (by linarith : 0 ≤ X - u * a)).2.1
    have e : G (u + 1) - G u = (X - u * a) / b + 1 + (a / 2) / b := by
      simp only [hG, hZ]
      push_cast
      field_simp
      ring
    have : 0 ≤ (a / 2) / b := by positivity
    linarith
  refine (sum_rows_le _ G hterm).trans ?_
  have hG0 : G 0 = 0 := by simp [hG]
  rw [hG0, sub_zero]
  simp only [hG]
  rw [div_le_div_iff₀ hb (by positivity)]
  nlinarith [sq_nonneg (Z - a * M), mul_pos ha hb, mul_nonneg hb.le (sq_nonneg (Z - a * M))]

/-- The lower bound for the number of points of a triangle. -/
theorem tri_card_ge {a b X : ℝ} (ha : 0 < a) (hb : 0 < b) (hX : 0 ≤ X) :
    X ^ 2 / (2 * a * b) ≤ ((tri a b X).card : ℝ) := by
  have hc := sum_triangle ha hb hX (fun _ _ => 1)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  rw [hc]
  set M := (rowS a X).card with hM
  have hr := card_rowS_bounds ha hX
  set G : ℕ → ℝ := fun s => ((s : ℝ) * X - a * s * (s - 1) / 2) / b with hG
  have hterm : ∀ u ∈ rowS a X, G (u + 1) - G u ≤ ((rowS b (X - u * a)).card : ℝ) := by
    intro u hu
    have h1 := rowS_le ha hX hu
    have h2 := (card_rowS_bounds hb (by linarith : 0 ≤ X - u * a)).1
    have e : G (u + 1) - G u = (X - u * a) / b := by
      simp only [hG]
      push_cast
      field_simp
      ring
    linarith
  refine le_trans ?_ (le_sum_rows _ G hterm)
  have hG0 : G 0 = 0 := by simp [hG]
  rw [hG0, sub_zero]
  simp only [hG]
  rw [div_le_div_iff₀ (by positivity) hb]
  set s := a * (M : ℝ) with hs
  have h1 : X ≤ s := by
    have := hr.1
    rw [div_le_iff₀ ha] at this
    linarith
  have h2 : s - a ≤ X := by
    have := hr.2.2
    nlinarith
  have key : X ^ 2 ≤ 2 * s * X - s * (s - a) := by nlinarith
  have e : ((M : ℝ) * X - a * M * (M - 1) / 2) * (2 * a * b) =
      b * (2 * s * X - s * (s - a)) := by
    rw [hs]; ring
  rw [e, mul_comm (X ^ 2)]
  exact mul_le_mul_of_nonneg_left key hb.le

/-- The weight of a triangle. -/
theorem tri_weight_le {a b X : ℝ} (ha : 0 < a) (hb : 0 < b) (hX : 0 ≤ X) :
    ∑ p ∈ tri a b X, ((p.1 : ℝ) * a + (p.2 : ℝ) * b) ≤ (X + a + b) ^ 3 / (3 * a * b) := by
  rw [sum_triangle ha hb hX fun u v => (u : ℝ) * a + (v : ℝ) * b]
  set Z := X + a + b with hZ
  set M := (rowS a X).card with hM
  have hr := card_rowS_bounds ha hX
  set G : ℕ → ℝ := fun s => (Z ^ 2 * s - a ^ 2 * (s : ℝ) ^ 3 / 3) / (2 * b) with hG
  have hterm : ∀ u ∈ rowS a X, ∑ v ∈ rowS b (X - u * a), ((u : ℝ) * a + (v : ℝ) * b) ≤
      G (u + 1) - G u := by
    intro u hu
    have h1 := rowS_le ha hX hu
    set s := (u : ℝ) * a with hs
    have hs0 : 0 ≤ s := by positivity
    obtain ⟨-, h2, h3⟩ := card_rowS_bounds hb (by linarith : 0 ≤ X - s)
    set n := (rowS b (X - s)).card with hn
    have hn1 : (1 : ℝ) ≤ n := by
      have : n = ⌊(X - s) / b⌋₊ + 1 := by simp [hn, rowS]
      rw [this]; push_cast; have : (0 : ℝ) ≤ ⌊(X - s) / b⌋₊ := by positivity
      linarith
    have hsum : ∑ v ∈ rowS b (X - s), (s + (v : ℝ) * b) = n * s + b * (n * (n - 1) / 2) := by
      have e : (rowS b (X - s)) = range n := by simp [hn, rowS]
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul, e,
        gauss_real, Finset.card_range]
      ring
    rw [hsum]
    have h4 : (n : ℝ) ≤ (X - s + b) / b := by
      have : (X - s) / b + 1 = (X - s + b) / b := by field_simp
      linarith
    have hb2 : n * s + b * (n * (n - 1) / 2) ≤ (X - s + b) * (X + s) / (2 * b) := by
      have h5 : n * s + b * (n * (n - 1) / 2) = n * (s + (n - 1) * b / 2) := by ring
      have h6 : s + ((n : ℝ) - 1) * b / 2 ≤ (X + s) / 2 := by linarith
      have h7 : 0 ≤ s + ((n : ℝ) - 1) * b / 2 := by
        have : 0 ≤ ((n : ℝ) - 1) * b := mul_nonneg (by linarith) hb.le
        linarith
      rw [h5]
      calc (n : ℝ) * (s + (n - 1) * b / 2) ≤ (X - s + b) / b * ((X + s) / 2) :=
            mul_le_mul h4 h6 h7 (by have : 0 ≤ X - s + b := by linarith
                                    positivity)
        _ = (X - s + b) * (X + s) / (2 * b) := by field_simp
    refine hb2.trans ?_
    have e : G (u + 1) - G u = (Z ^ 2 - a ^ 2 * ((u : ℝ) ^ 2 + u + 1 / 3)) / (2 * b) := by
      simp only [hG]
      push_cast
      field_simp
      ring
    rw [e, div_le_div_iff_of_pos_right (by positivity)]
    have hus : a ^ 2 * ((u : ℝ) ^ 2 + u + 1 / 3) = s ^ 2 + s * a + a ^ 2 / 3 := by
      rw [hs]; ring
    rw [hus, hZ]
    nlinarith [mul_nonneg ha.le (sub_nonneg.2 h1), mul_nonneg hb.le (sub_nonneg.2 h1),
      mul_nonneg ha.le hX, mul_nonneg ha.le hb.le, sq_nonneg a, sq_nonneg b]
  refine (sum_rows_le _ G hterm).trans ?_
  have hG0 : G 0 = 0 := by simp [hG]
  rw [hG0, sub_zero]
  simp only [hG]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  set s := a * (M : ℝ) with hs
  have hs0 : 0 ≤ s := by positivity
  have hZ0 : 0 ≤ Z := by positivity
  have key : 3 * Z ^ 2 * s - s ^ 3 ≤ 2 * Z ^ 3 := by
    have : 0 ≤ (Z - s) ^ 2 * (2 * Z + s) := by positivity
    nlinarith
  have e : (Z ^ 2 * (M : ℝ) - a ^ 2 * (M : ℝ) ^ 3 / 3) * (3 * a * b) =
      b * (3 * Z ^ 2 * s - s ^ 3) := by
    rw [hs]; ring
  have e2 : Z ^ 3 * (2 * b) = b * (2 * Z ^ 3) := by ring
  rw [e, e2]
  exact mul_le_mul_of_nonneg_left key hb.le

/-! ## the exponent set -/

/-- The weight `e·l`. -/
noncomputable def wt (l : Fin 3 → ℝ) (e : Fin 3 → ℕ) : ℝ := ∑ i, (e i : ℝ) * l i

lemma wt_eq (l : Fin 3 → ℝ) (e : Fin 3 → ℕ) :
    wt l e = (e 0 : ℝ) * l 0 + (e 1 : ℝ) * l 1 + (e 2 : ℝ) * l 2 := by
  simp [wt, Fin.sum_univ_three]

lemma wt_nonneg {l : Fin 3 → ℝ} (hl : ∀ i, 0 < l i) (e : Fin 3 → ℕ) : 0 ≤ wt l e :=
  Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hl i).le

/-- The L-shaped exponent set `{e : e·l ≤ Y, e₀ < 4 ∨ e₁ < 2}`. -/
noncomputable def expSet (l : Fin 3 → ℝ) (Y : ℝ) : Finset (Fin 3 → ℕ) := by
  classical
  exact (Fintype.piFinset fun i => range (⌊Y / l i⌋₊ + 1)).filter fun e =>
    (e 0 < 4 ∨ e 1 < 2) ∧ wt l e ≤ Y

lemma mem_expSet {l : Fin 3 → ℝ} (hl : ∀ i, 0 < l i) {Y : ℝ} {e : Fin 3 → ℕ} :
    e ∈ expSet l Y ↔ (e 0 < 4 ∨ e 1 < 2) ∧ wt l e ≤ Y := by
  classical
  simp only [expSet, mem_filter, Fintype.mem_piFinset, mem_range, Nat.lt_succ_iff]
  refine ⟨fun h => h.2, fun h => ⟨fun i => ?_, h⟩⟩
  refine Nat.le_floor ((le_div_iff₀ (hl i)).2 ?_)
  have : (e i : ℝ) * l i ≤ wt l e :=
    Finset.single_le_sum (f := fun i => (e i : ℝ) * l i)
      (fun j _ => mul_nonneg (Nat.cast_nonneg _) (hl j).le) (mem_univ i)
  exact this.trans h.2

/-- `A = (2l₀ + l₁)/(l₀l₁l₂)`. -/
noncomputable def expA (l : Fin 3 → ℝ) : ℝ := (2 * l 0 + l 1) / (l 0 * l 1 * l 2)

/-- The six sectors of the exponent set. -/
def sec (e : Fin 3 → ℕ) : ℕ := if e 0 < 4 then e 0 else 4 + e 1

lemma sec_lt {l : Fin 3 → ℝ} (hl : ∀ i, 0 < l i) {Y : ℝ} {e : Fin 3 → ℕ}
    (he : e ∈ expSet l Y) : sec e ∈ range 6 := by
  have := ((mem_expSet hl).1 he).1
  simp only [sec, mem_range]
  split_ifs <;> omega

lemma sec_of_lt {e : Fin 3 → ℕ} (h : e 0 < 4) : sec e = e 0 := by simp [sec, h]

lemma sec_of_ge {e : Fin 3 → ℕ} (h : ¬ e 0 < 4) : sec e = 4 + e 1 := by simp [sec, h]

lemma eq_of_sec_lt {e : Fin 3 → ℕ} {s : ℕ} (hs : s < 4) (h : sec e = s) : e 0 = s := by
  by_cases h0 : e 0 < 4
  · rwa [sec_of_lt h0] at h
  · rw [sec_of_ge h0] at h
    omega

lemma eq_of_sec_ge {e : Fin 3 → ℕ} {k : ℕ} (h : sec e = 4 + k) : 4 ≤ e 0 ∧ e 1 = k := by
  by_cases h0 : e 0 < 4
  · rw [sec_of_lt h0] at h
    omega
  · rw [sec_of_ge h0] at h
    omega

lemma sum_fib0 {l : Fin 3 → ℝ} (hl : ∀ i, 0 < l i) (Y : ℝ) (s : ℕ) (hs : s < 4)
    (f : (Fin 3 → ℕ) → ℝ) :
    ∑ e ∈ expSet l Y with sec e = s, f e =
      ∑ p ∈ tri (l 1) (l 2) (Y - s * l 0), f ![s, p.1, p.2] := by
  classical
  symm
  refine Finset.sum_bij' (fun p _ => ![s, p.1, p.2]) (fun e _ => (e 1, e 2)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [mem_tri (hl 1) (hl 2)] at hp
    rw [mem_filter, mem_expSet hl, wt_eq, sec_of_lt (by simpa using hs)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    exact ⟨⟨Or.inl hs, by linarith⟩, trivial⟩
  · intro e he
    rw [mem_filter, mem_expSet hl, wt_eq] at he
    obtain ⟨⟨-, hw⟩, hsec⟩ := he
    have h0 := eq_of_sec_lt hs hsec
    rw [mem_tri (hl 1) (hl 2)]
    rw [h0] at hw
    simp only
    linarith
  · intro p _
    rfl
  · intro e he
    have h0 := eq_of_sec_lt hs (mem_filter.1 he).2
    funext i
    fin_cases i
    · exact h0.symm
    · rfl
    · rfl
  · intro p _
    rfl

lemma sum_fib1 {l : Fin 3 → ℝ} (hl : ∀ i, 0 < l i) (Y : ℝ) (k : ℕ) (hk : k < 2)
    (f : (Fin 3 → ℕ) → ℝ) :
    ∑ e ∈ expSet l Y with sec e = 4 + k, f e =
      ∑ p ∈ tri (l 0) (l 2) (Y - 4 * l 0 - k * l 1), f ![4 + p.1, k, p.2] := by
  classical
  symm
  refine Finset.sum_bij' (fun p _ => ![4 + p.1, k, p.2]) (fun e _ => (e 0 - 4, e 2))
    ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [mem_tri (hl 0) (hl 2)] at hp
    rw [mem_filter, mem_expSet hl, wt_eq, sec_of_ge (by simp)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    refine ⟨⟨Or.inr hk, ?_⟩, trivial⟩
    push_cast
    linarith
  · intro e he
    rw [mem_filter, mem_expSet hl, wt_eq] at he
    obtain ⟨⟨-, hw⟩, hsec⟩ := he
    obtain ⟨h0, h1⟩ := eq_of_sec_ge hsec
    rw [mem_tri (hl 0) (hl 2)]
    rw [h1] at hw
    simp only
    rw [Nat.cast_sub h0]
    push_cast
    linarith
  · intro p _
    simp
  · intro e he
    obtain ⟨h0, h1⟩ := eq_of_sec_ge (mem_filter.1 he).2
    funext i
    fin_cases i
    · show 4 + (e 0 - 4) = e 0
      omega
    · exact h1.symm
    · rfl
  · intro p _
    rfl

/-- Decomposition of a sum over the exponent set into six triangles. -/
lemma sum_expSet {l : Fin 3 → ℝ} (hl : ∀ i, 0 < l i) (Y : ℝ) (f : (Fin 3 → ℕ) → ℝ) :
    ∑ e ∈ expSet l Y, f e =
      ∑ p ∈ tri (l 1) (l 2) (Y - (0 : ℕ) * l 0), f ![0, p.1, p.2]
      + ∑ p ∈ tri (l 1) (l 2) (Y - (1 : ℕ) * l 0), f ![1, p.1, p.2]
      + ∑ p ∈ tri (l 1) (l 2) (Y - (2 : ℕ) * l 0), f ![2, p.1, p.2]
      + ∑ p ∈ tri (l 1) (l 2) (Y - (3 : ℕ) * l 0), f ![3, p.1, p.2]
      + ∑ p ∈ tri (l 0) (l 2) (Y - 4 * l 0 - (0 : ℕ) * l 1), f ![4 + p.1, 0, p.2]
      + ∑ p ∈ tri (l 0) (l 2) (Y - 4 * l 0 - (1 : ℕ) * l 1), f ![4 + p.1, 1, p.2] := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := sec) (t := range 6)
    (fun e he => sec_lt hl he) f]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [sum_fib0 hl Y 0 (by norm_num), sum_fib0 hl Y 1 (by norm_num), sum_fib0 hl Y 2 (by norm_num),
    sum_fib0 hl Y 3 (by norm_num), sum_fib1 hl Y 0 (by norm_num) f, sum_fib1 hl Y 1 (by norm_num) f]

/-- Size of the exponent set. -/
theorem expSet_card_ge {l : Fin 3 → ℝ} (hl : ∀ i, 0 < l i) {L : ℝ} (hL : ∀ i, l i ≤ L) {Y : ℝ}
    (hY : 5 * L ≤ Y) : expA l * (Y - 5 * L) ^ 2 ≤ ((expSet l Y).card : ℝ) := by
  have h0 := hl 0
  have h1 := hl 1
  have h2 := hl 2
  have hL0 := hL 0
  have hL1 := hL 1
  have hc : ((expSet l Y).card : ℝ) = ∑ e ∈ expSet l Y, (1 : ℝ) := by simp
  rw [hc, sum_expSet hl Y]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  set W := Y - 5 * L with hW
  have hW0 : 0 ≤ W := by linarith
  have ht : ∀ a b X : ℝ, 0 < a → 0 < b → W ≤ X → W ^ 2 / (2 * a * b) ≤ ((tri a b X).card : ℝ) := by
    intro a b X ha hb hX
    refine le_trans ?_ (tri_card_ge ha hb (hW0.trans hX))
    gcongr
  have e0 := ht (l 1) (l 2) (Y - (0 : ℕ) * l 0) h1 h2 (by push_cast; linarith)
  have e1 := ht (l 1) (l 2) (Y - (1 : ℕ) * l 0) h1 h2 (by push_cast; linarith)
  have e2 := ht (l 1) (l 2) (Y - (2 : ℕ) * l 0) h1 h2 (by push_cast; linarith)
  have e3 := ht (l 1) (l 2) (Y - (3 : ℕ) * l 0) h1 h2 (by push_cast; linarith)
  have e4 := ht (l 0) (l 2) (Y - 4 * l 0 - (0 : ℕ) * l 1) h0 h2 (by push_cast; linarith)
  have e5 := ht (l 0) (l 2) (Y - 4 * l 0 - (1 : ℕ) * l 1) h0 h2 (by push_cast; linarith)
  have hA : expA l * W ^ 2 = 4 * (W ^ 2 / (2 * l 1 * l 2)) + 2 * (W ^ 2 / (2 * l 0 * l 2)) := by
    simp only [expA]
    field_simp
    ring
  rw [hA]
  linarith

/-- Total weight of the exponent set. -/
theorem expSet_weight_le {l : Fin 3 → ℝ} (hl : ∀ i, 0 < l i) {L : ℝ} (hL : ∀ i, l i ≤ L) {Y : ℝ}
    (hY : 5 * L ≤ Y) : ∑ e ∈ expSet l Y, wt l e ≤
      2 / 3 * expA l * (Y + 2 * L) ^ 3 + 10 * L * expA l * (Y + 2 * L) ^ 2 := by
  have h0 := hl 0
  have h1 := hl 1
  have h2 := hl 2
  have hL0 := hL 0
  have hL1 := hL 1
  have hL2 := hL 2
  rw [sum_expSet hl Y]
  set Z := Y + 2 * L with hZ
  have hZ0 : 0 < Z := by linarith
  set a := 1 / (l 1 * l 2) with ha
  set b := 1 / (l 0 * l 2) with hb
  have ha0 : 0 < a := by positivity
  have hb0 : 0 < b := by positivity
  have hLp : 0 < L := by linarith
  -- one triangle
  have ht : ∀ (u v X c : ℝ), 0 < u → 0 < v → 0 ≤ X → X + u + v ≤ Z → 0 ≤ c →
      ∑ p ∈ tri u v X, (c + ((p.1 : ℝ) * u + (p.2 : ℝ) * v)) ≤
        c * (Z ^ 2 * (1 / (u * v)) / 2) + Z ^ 3 * (1 / (u * v)) / 3 := by
    intro u v X c hu hv hX hXZ hc
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    have c1 := tri_card_le hu hv hX
    have c2 := tri_weight_le hu hv hX
    have hX0 : 0 ≤ X + u + v := by positivity
    have c3 : (X + u + v) ^ 2 / (2 * u * v) ≤ Z ^ 2 * (1 / (u * v)) / 2 := by
      have : (X + u + v) ^ 2 ≤ Z ^ 2 := pow_le_pow_left₀ hX0 hXZ 2
      rw [show Z ^ 2 * (1 / (u * v)) / 2 = Z ^ 2 / (2 * u * v) by field_simp]
      gcongr
    have c4 : (X + u + v) ^ 3 / (3 * u * v) ≤ Z ^ 3 * (1 / (u * v)) / 3 := by
      have : (X + u + v) ^ 3 ≤ Z ^ 3 := pow_le_pow_left₀ hX0 hXZ 3
      rw [show Z ^ 3 * (1 / (u * v)) / 3 = Z ^ 3 / (3 * u * v) by field_simp]
      gcongr
    have c5 : ((tri u v X).card : ℝ) * c ≤ c * (Z ^ 2 * (1 / (u * v)) / 2) := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (c1.trans c3) hc
    linarith [c2.trans c4]
  have hw0 : ∀ (s : ℕ) (p : ℕ × ℕ), wt l ![s, p.1, p.2] =
      (s : ℝ) * l 0 + ((p.1 : ℝ) * l 1 + (p.2 : ℝ) * l 2) := by
    intro s p
    simp only [wt_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    ring
  have hw1 : ∀ (k : ℕ) (p : ℕ × ℕ), wt l ![4 + p.1, k, p.2] =
      (4 * l 0 + (k : ℝ) * l 1) + ((p.1 : ℝ) * l 0 + (p.2 : ℝ) * l 2) := by
    intro k p
    simp only [wt_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    push_cast
    ring
  simp only [hw0, hw1]
  have T : ∀ s : ℕ, s < 4 → ∑ p ∈ tri (l 1) (l 2) (Y - (s : ℕ) * l 0),
      ((s : ℝ) * l 0 + ((p.1 : ℝ) * l 1 + (p.2 : ℝ) * l 2)) ≤
        (s : ℝ) * (L * Z ^ 2 * a / 2) + Z ^ 3 * a / 3 := by
    intro s hs
    have hs3 : (s : ℝ) ≤ 3 := by exact_mod_cast (by omega : s ≤ 3)
    have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
    have hle : (s : ℝ) * l 0 ≤ 3 * L := by nlinarith
    refine (ht _ _ _ _ h1 h2 (by linarith) (by nlinarith) (by positivity)).trans ?_
    have : (s : ℝ) * l 0 * (Z ^ 2 * a / 2) ≤ (s : ℝ) * (L * Z ^ 2 * a / 2) := by
      have : 0 ≤ (s : ℝ) * (Z ^ 2 * a / 2) := by positivity
      nlinarith
    linarith
  have U : ∀ k : ℕ, k < 2 → ∑ p ∈ tri (l 0) (l 2) (Y - 4 * l 0 - (k : ℕ) * l 1),
      ((4 * l 0 + (k : ℝ) * l 1) + ((p.1 : ℝ) * l 0 + (p.2 : ℝ) * l 2)) ≤
        2 * (L * Z ^ 2 * a) + (k : ℝ) * (L * Z ^ 2 * b / 2) + Z ^ 3 * b / 3 := by
    intro k hk
    have hk1 : (k : ℝ) ≤ 1 := by exact_mod_cast (by omega : k ≤ 1)
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have hle : (k : ℝ) * l 1 ≤ L := by nlinarith
    refine (ht _ _ _ _ h0 h2 (by linarith) (by nlinarith) (by positivity)).trans ?_
    have e1 : 4 * l 0 * (Z ^ 2 * b / 2) = 2 * (l 1 * Z ^ 2 * a) := by
      simp only [ha, hb]
      field_simp
      ring
    have e2 : l 1 * Z ^ 2 * a ≤ L * Z ^ 2 * a := by
      have : 0 ≤ Z ^ 2 * a := by positivity
      nlinarith
    have e3 : (k : ℝ) * l 1 * (Z ^ 2 * b / 2) ≤ (k : ℝ) * (L * Z ^ 2 * b / 2) := by
      have : 0 ≤ (k : ℝ) * (Z ^ 2 * b / 2) := by positivity
      nlinarith
    rw [add_mul]
    linarith
  have t0 := T 0 (by norm_num)
  have t1 := T 1 (by norm_num)
  have t2 := T 2 (by norm_num)
  have t3 := T 3 (by norm_num)
  have u0 := U 0 (by norm_num)
  have u1 := U 1 (by norm_num)
  have hA : expA l = 2 * a + b := by
    simp only [expA, ha, hb]
    field_simp
  rw [hA]
  push_cast at t0 t1 t2 t3 u0 u1
  have p1 : 0 ≤ L * Z ^ 2 * a := by positivity
  have p2 : 0 ≤ L * Z ^ 2 * b := by positivity
  nlinarith

end OVNS.Quant.Surf
