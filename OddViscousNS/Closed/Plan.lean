import OddViscousNS.Closed.Gram

/-!
# The 41-slope barrier plan `S̃` (certificate U785, §5–6 of the reconstruction)

The knots start at `(1,1)`; edge `i` (`0 ≤ i < 41`) has slope `m_i = slopes[i]/10⁶` and width
`min(1/500, (Y_i − Y_c)/m_i)`, so that the last knot is exactly `(X_c, Y_c)` with
`Y_c = (1 − 10⁻⁵)/(sκ₀)² = 399996000000000/407121861462121`, `s = 97/40`.  The barrier is
`S̃(X) = max(Y_c, max_i L_i(X))`, `L_i(X) = Y_i + m_i (X − X_i)`: convex, equal to `L_i` on the
closed edge `[X_{i+1}, X_i]`, equal to `Y_c` for `X ≤ X_c`, above the datum line `(2X+1)/3` on
`[0,1]`, and at most `1` on `(−∞, 1]`.
-/

open Set

namespace OVNS

/-- The 41 slopes, times `10⁶`. -/
def slopeN : List ℕ :=
  [494635, 468483, 446205, 425724, 406455, 388182, 370730, 354015, 337984, 322586, 307757,
   293490, 279756, 266530, 253789, 241514, 229673, 218262, 207265, 196667, 186452, 176608,
   167120, 157977, 149160, 140661, 132471, 124581, 116980, 109657, 102605, 95811, 89272,
   83055, 77151, 71501, 66036, 60850, 56021, 51322, 46835]

def slopeL : List ℚ := slopeN.map fun n => (n : ℚ) / 1000000

/-- `Y_c = (1 − 10⁻⁵)/(s κ₀)²`. -/
def Yc : ℚ := 399996000000000 / 407121861462121

/-- `X_c`, the abscissa of the last knot. -/
def Xc : ℚ := 302078577788605397457 / 328750903130662707500

/-- The knots `(X_0,Y_0) = (1,1), …, (X_41,Y_41) = (X_c,Y_c)`. -/
def knots : List (ℚ × ℚ) :=
  (slopeL.foldl (fun (acc : List (ℚ × ℚ)) m =>
    match acc with
    | [] => []
    | (X, Y) :: _ =>
      let w := min (1 / 500) ((Y - Yc) / m)
      (X - w, Y - m * w) :: acc) [(1, 1)]).reverse

def kX (i : ℕ) : ℚ := (knots.getD i (0, 0)).1
def kY (i : ℕ) : ℚ := (knots.getD i (0, 0)).2
def slope (i : ℕ) : ℚ := slopeL.getD i 0

/-- The affine piece of edge `i`. -/
noncomputable def piece (i : ℕ) (x : ℝ) : ℝ := (kY i : ℝ) + (slope i : ℝ) * (x - kX i)

/-- The barrier `S̃`. -/
noncomputable def Stilde (x : ℝ) : ℝ :=
  max (Yc : ℝ) ((Finset.range 41).sup' ⟨0, by simp⟩ fun i => piece i x)

/-! ### Rational facts (kernel-checked) -/

theorem knots_length : knots.length = 42 := by
  decide +kernel

theorem kX_zero : kX 0 = 1 := by
  decide +kernel

theorem kY_zero : kY 0 = 1 := by
  decide +kernel

theorem kX_last : kX 41 = Xc := by
  decide +kernel

theorem kY_last : kY 41 = Yc := by
  decide +kernel

theorem Yc_eq : Yc = (1 - 1 / 100000) / ((97 / 40 : ℚ) * (208013 / 500000)) ^ 2 := by
  decide +kernel

theorem slope_pos : ∀ i < 41, 0 < slope i := by
  decide +kernel

theorem slope_lt : ∀ i < 41, slope i < 2 / 3 := by
  decide +kernel

private theorem slope_anti_aux : ∀ j < 41, ∀ i < j, slope j < slope i := by
  decide +kernel

theorem slope_anti : ∀ i j, i < j → j < 41 → slope j < slope i := by
  intro i j hij hj
  exact slope_anti_aux j hj i hij

/-- Each knot lies on the previous edge: `Y_{i+1} = Y_i − m_i (X_i − X_{i+1})`. -/
theorem knot_step : ∀ i < 41, kY (i + 1) = kY i - slope i * (kX i - kX (i + 1)) := by
  decide +kernel

theorem kX_anti : ∀ i < 41, kX (i + 1) < kX i := by
  decide +kernel

theorem intercept_pos : ∀ i < 41, 0 < kY i - slope i * kX i := by
  decide +kernel

theorem knots_above_datum : ∀ i ≤ 41, 2 * kX i + 1 ≤ 3 * kY i := by
  decide +kernel

theorem Yc_le_kY : ∀ i ≤ 41, Yc ≤ kY i := by
  decide +kernel

theorem kX_le_one : ∀ i ≤ 41, kX i ≤ 1 := by
  decide +kernel

theorem Xc_pos : 0 < Xc := by
  decide +kernel

theorem Yc_pos : 0 < Yc := by
  decide +kernel

/-! ### Auxiliary rational facts, including the constant piece `41` -/

private theorem slope_41 : slope 41 = 0 := by
  decide +kernel

private theorem slope_succ_lt : ∀ k < 41, slope (k + 1) < slope k := by
  decide +kernel

private theorem slope_nonneg' : ∀ i ≤ 41, 0 ≤ slope i := by
  decide +kernel

private theorem slope_le' : ∀ i ≤ 41, slope i ≤ 2 / 3 := by
  decide +kernel

private theorem intercept_pos' : ∀ i ≤ 41, 0 < kY i - slope i * kX i := by
  decide +kernel

private theorem intercept_le_one : ∀ i ≤ 41, kY i - slope i * kX i ≤ 1 := by
  decide +kernel

private theorem kX_antitone_aux : ∀ b ≤ 41, ∀ a ≤ b, kX b ≤ kX a := by
  decide +kernel

/-! ### Real facts about `S̃` -/

private theorem piece_41 (x : ℝ) : piece 41 x = Yc := by
  simp [piece, slope_41, kY_last]

private theorem kX_antitone_real {a b : ℕ} (hab : a ≤ b) (hb : b ≤ 41) :
    (kX b : ℝ) ≤ kX a := by
  exact_mod_cast kX_antitone_aux b hb a hab

/-- Consecutive pieces cross at the knot between them. -/
private theorem piece_succ_sub {k : ℕ} (hk : k < 41) (x : ℝ) :
    piece (k + 1) x - piece k x = ((slope (k + 1) : ℝ) - slope k) * (x - kX (k + 1)) := by
  have h : (kY (k + 1) : ℝ) = kY k - slope k * (kX k - kX (k + 1)) := by
    exact_mod_cast knot_step k hk
  simp only [piece]
  linear_combination h

private theorem slope_succ_lt_real {k : ℕ} (hk : k < 41) : (slope (k + 1) : ℝ) < slope k := by
  exact_mod_cast slope_succ_lt k hk

private theorem piece_lt_succ {k : ℕ} (hk : k < 41) {x : ℝ} (hx : x < kX (k + 1)) :
    piece k x < piece (k + 1) x := by
  have h1 := piece_succ_sub hk x
  have h2 := slope_succ_lt_real hk
  nlinarith

private theorem piece_succ_lt {k : ℕ} (hk : k < 41) {x : ℝ} (hx : (kX (k + 1) : ℝ) < x) :
    piece (k + 1) x < piece k x := by
  have h1 := piece_succ_sub hk x
  have h2 := slope_succ_lt_real hk
  nlinarith

/-- Left of knot `i`, later pieces dominate earlier ones. -/
private theorem chain_left {j i : ℕ} (hji : j ≤ i) (hi : i ≤ 41) {x : ℝ} (hx : x ≤ kX i) :
    piece j x ≤ piece i x := by
  induction i, hji using Nat.le_induction with
  | base => exact le_rfl
  | succ n hjn ih =>
    have hn : n < 41 := by omega
    have h1 := ih (by omega) (hx.trans (kX_antitone_real (by omega) hi))
    have h2 := piece_succ_sub hn x
    have h3 := slope_succ_lt_real hn
    nlinarith

/-- Right of knot `i + 1`, earlier pieces dominate later ones. -/
private theorem chain_right {i j : ℕ} (hij : i < j) (hj : j ≤ 41) {x : ℝ}
    (hx : (kX (i + 1) : ℝ) ≤ x) : piece j x ≤ piece i x := by
  induction j, hij using Nat.le_induction with
  | base =>
    have h2 := piece_succ_sub (show i < 41 by omega) x
    have h3 := slope_succ_lt_real (show i < 41 by omega)
    nlinarith
  | succ n hin ih =>
    have hn : n < 41 := by omega
    have h1 := ih (by omega)
    have hx' : (kX (n + 1) : ℝ) ≤ x := (kX_antitone_real (by omega) (by omega)).trans hx
    have h2 := piece_succ_sub hn x
    have h3 := slope_succ_lt_real hn
    nlinarith

private theorem le_Stilde' {i : ℕ} (hi : i ≤ 41) (x : ℝ) : piece i x ≤ Stilde x := by
  rcases Nat.lt_or_ge i 41 with h | h
  · exact le_max_of_le_right (Finset.le_sup' (fun i => piece i x) (Finset.mem_range.2 h))
  · obtain rfl : i = 41 := by omega
    rw [piece_41]
    exact le_max_left _ _

private theorem Stilde_le' {x c : ℝ} (h : ∀ i ≤ 41, piece i x ≤ c) : Stilde x ≤ c := by
  refine max_le ?_ ?_
  · rw [← piece_41 x]
    exact h 41 le_rfl
  · exact Finset.sup'_le _ _ fun i hi => h i (by simp at hi; omega)

private theorem exists_Stilde_eq (x : ℝ) : ∃ i ≤ 41, Stilde x = piece i x := by
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' (⟨0, by simp⟩ : (Finset.range 41).Nonempty)
    (fun i => piece i x)
  rcases le_total (Yc : ℝ) ((Finset.range 41).sup' ⟨0, by simp⟩ fun i => piece i x) with h | h
  · refine ⟨i, by simp at hi; omega, ?_⟩
    rw [Stilde, max_eq_right h, he]
  · refine ⟨41, le_rfl, ?_⟩
    rw [Stilde, max_eq_left h, piece_41]

private theorem Stilde_eq_of_edge {i : ℕ} (hi : i ≤ 41) {x : ℝ} (hx : x ≤ kX i)
    (hx' : i < 41 → (kX (i + 1) : ℝ) ≤ x) : Stilde x = piece i x := by
  refine le_antisymm (Stilde_le' fun j hj => ?_) (le_Stilde' hi x)
  rcases le_or_gt j i with h | h
  · exact chain_left h hi hx
  · exact chain_right h hj (hx' (by omega))

theorem Stilde_convex : ConvexOn ℝ univ Stilde := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain ⟨i, hi, he⟩ := exists_Stilde_eq (a • x + b • y)
  rw [he]
  have h1 := le_Stilde' hi x
  have h2 := le_Stilde' hi y
  have e : piece i (a • x + b • y) = a * piece i x + b * piece i y := by
    simp only [piece, smul_eq_mul]
    linear_combination (↑(slope i) * ↑(kX i) - ↑(kY i)) * hab
  rw [e, smul_eq_mul, smul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

theorem piece_le_Stilde {i : ℕ} (hi : i < 41) (x : ℝ) : piece i x ≤ Stilde x :=
  le_Stilde' hi.le x

theorem Yc_le_Stilde (x : ℝ) : (Yc : ℝ) ≤ Stilde x :=
  le_max_left _ _

/-- On the closed edge `[X_{i+1}, X_i]` the barrier is the piece `L_i`. -/
theorem Stilde_eq_piece {i : ℕ} (hi : i < 41) {x : ℝ} (hx : x ∈ Icc (kX (i + 1) : ℝ) (kX i)) :
    Stilde x = piece i x :=
  Stilde_eq_of_edge hi.le hx.2 fun _ => hx.1

/-- The plateau. -/
theorem Stilde_eq_Yc {x : ℝ} (hx : x ≤ Xc) : Stilde x = Yc := by
  rw [Stilde_eq_of_edge le_rfl (by rw [kX_last]; exact hx) (fun h => absurd h (lt_irrefl _)),
    piece_41]

/-- Contact with `L_i` at some `x ≤ 1` happens only on the closed edge `i`. -/
theorem edge_of_contact {i : ℕ} (hi : i < 41) {x : ℝ} (hx : x ≤ 1) (h : piece i x = Stilde x) :
    x ∈ Icc (kX (i + 1) : ℝ) (kX i) := by
  constructor
  · by_contra hc
    have := piece_lt_succ hi (not_le.1 hc)
    have := le_Stilde' (show i + 1 ≤ 41 by omega) x
    linarith
  · by_contra hc
    rcases i with _ | k
    · have : (kX 0 : ℝ) = 1 := by exact_mod_cast kX_zero
      linarith [not_le.1 hc]
    · have := piece_succ_lt (show k < 41 by omega) (not_le.1 hc)
      have := le_Stilde' (show k ≤ 41 by omega) x
      linarith

/-- Contact with the plateau value at some `x ≤ 1` happens only for `x ≤ X_c`. -/
theorem plateau_of_contact {x : ℝ} (_hx : x ≤ 1) (h : Stilde x = Yc) : x ≤ Xc := by
  by_contra hc
  have hc' : (kX (40 + 1) : ℝ) < x := by
    rw [show 40 + 1 = 41 from rfl, kX_last]; exact not_le.1 hc
  have := piece_succ_lt (show 40 < 41 by omega) hc'
  have := le_Stilde' (show 40 ≤ 41 by omega) x
  rw [show 40 + 1 = 41 from rfl, piece_41] at *
  linarith

theorem Stilde_le_one {x : ℝ} (hx : x ≤ 1) : Stilde x ≤ 1 := by
  refine Stilde_le' fun j hj => ?_
  have h0 : piece 0 1 = 1 := by simp [piece, kX_zero, kY_zero]
  have hs : (0 : ℝ) ≤ slope j := by exact_mod_cast slope_nonneg' j hj
  have hmono : piece j x ≤ piece j 1 := by
    simp only [piece]; nlinarith
  rcases Nat.eq_zero_or_pos j with rfl | hpos
  · linarith
  · have : piece j 1 ≤ piece 0 1 := chain_right hpos hj (by exact_mod_cast kX_le_one 1 (by omega))
    linarith

/-- The datum line lies below the barrier on `[0,1]`. -/
theorem datum_le_Stilde {x : ℝ} (_hx0 : 0 ≤ x) (hx1 : x ≤ 1) : (2 * x + 1) / 3 ≤ Stilde x := by
  have hd : (2 * (Xc : ℝ) + 1) / 3 ≤ Yc := by
    have := knots_above_datum 41 le_rfl
    rw [kX_last, kY_last] at this
    have : (2 * (Xc : ℝ) + 1) ≤ 3 * Yc := by exact_mod_cast this
    linarith
  obtain ⟨i, hi, he⟩ := exists_Stilde_eq x
  rcases Nat.lt_or_ge i 41 with h | h
  · obtain ⟨ha, hb⟩ := edge_of_contact h hx1 he.symm
    rw [he]
    have hst : (kY (i + 1) : ℝ) = kY i - slope i * (kX i - kX (i + 1)) := by
      exact_mod_cast knot_step i h
    have d1 : 2 * (kX i : ℝ) + 1 ≤ 3 * kY i := by exact_mod_cast knots_above_datum i hi
    have d2 : 2 * (kX (i + 1) : ℝ) + 1 ≤ 3 * kY (i + 1) := by
      exact_mod_cast knots_above_datum (i + 1) (by omega)
    have hlt : (kX (i + 1) : ℝ) < kX i := by exact_mod_cast kX_anti i h
    have key : (piece i x - (2 * x + 1) / 3) * (kX i - kX (i + 1)) =
        (kY (i + 1) - (2 * kX (i + 1) + 1) / 3) * (kX i - x) +
          (kY i - (2 * kX i + 1) / 3) * (x - kX (i + 1)) := by
      simp only [piece]
      linear_combination (x - kX i) * hst
    have : 0 ≤ (piece i x - (2 * x + 1) / 3) * (kX i - kX (i + 1)) := by
      rw [key]
      have e1 : (0 : ℝ) ≤ kX i - x := by linarith
      have e2 : (0 : ℝ) ≤ x - kX (i + 1) := by linarith
      have e3 : (0 : ℝ) ≤ kY (i + 1) - (2 * kX (i + 1) + 1) / 3 := by linarith
      have e4 : (0 : ℝ) ≤ kY i - (2 * kX i + 1) / 3 := by linarith
      positivity
    have := nonneg_of_mul_nonneg_left this (by linarith)
    linarith
  · have hxc : x ≤ Xc := plateau_of_contact hx1 (by
      obtain rfl : i = 41 := by omega
      rw [he, piece_41])
    rw [Stilde_eq_Yc hxc]
    have : (x : ℝ) ≤ Xc := hxc
    linarith

/-- Star-shapedness: `λ S̃(x) ≤ S̃(λ x)` for `0 ≤ λ ≤ 1`. -/
theorem Stilde_ray {l x : ℝ} (_hl0 : 0 ≤ l) (hl1 : l ≤ 1) : l * Stilde x ≤ Stilde (l * x) := by
  obtain ⟨i, hi, he⟩ := exists_Stilde_eq x
  rw [he]
  refine le_trans ?_ (le_Stilde' hi (l * x))
  have hc : (0 : ℝ) < kY i - slope i * kX i := by exact_mod_cast intercept_pos' i hi
  simp only [piece]
  nlinarith

/-- Linear growth: `S̃(x) ≤ 1 + (2/3) x` for `x ≥ 0`. -/
theorem Stilde_le_lin {x : ℝ} (hx : 0 ≤ x) : Stilde x ≤ 1 + 2 / 3 * x := by
  refine Stilde_le' fun j hj => ?_
  have hc : (kY j : ℝ) - slope j * kX j ≤ 1 := by exact_mod_cast intercept_le_one j hj
  have hs : (slope j : ℝ) ≤ 2 / 3 := by
    have h := Rat.cast_le (K := ℝ) |>.mpr (slope_le' j hj)
    norm_num at h
    exact h
  simp only [piece]
  nlinarith

theorem Stilde_continuous : Continuous Stilde := by
  refine continuous_const.max ?_
  exact Continuous.finset_sup'_apply _ fun i _ => by unfold piece; fun_prop

end OVNS
