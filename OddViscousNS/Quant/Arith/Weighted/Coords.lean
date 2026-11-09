import OddViscousNS.Quant.Arith.Weighted.Defs

/-!
# Integer coordinates of a resonant sorted triad (Section A)

* `vertical_output_null`: a vertical largest output is a null face (`γ = 0`).
* `exists_coords`: squarefree rigidity gives `|k|² = Δx²`, `|m|² = Δy²`, `|n|² = Δz²` with
  `1 ≤ y ≤ x ≤ z` and the integer resonance.
* The exact identities (`x_id`, `L_id`, `J_id`), divisibility (`v ∣ tw`, `(v/g) ∣ w`), the ranges
  `0 ≤ t < 2z`, `t = 0 ⇒` equilateral, `t = z ⇒` collinear, the `s₂` branch, and the shell height
  bound `T |w| ≤ v (T + 2z)`.
-/

namespace OVNS.Quant

private theorem absk_eq_sqrt_nsqZ' (k : Mode) : absk k = Real.sqrt (nsqZ k) := by
  simp only [absk, absSq, nsqZ]
  push_cast
  rfl

private theorem absk_nonneg' (k : Mode) : 0 ≤ absk k := Real.sqrt_nonneg _

private theorem mem_sortedFibre {n m k : Mode} (hp : (m, k) ∈ sortedFibre n) :
    m + k + n = 0 ∧ nsqZ m ≤ nsqZ k ∧ nsqZ k ≤ nsqZ n ∧ m 2 ≠ 0 ∧ k 2 ≠ 0 ∧ n 2 ≠ 0 := by
  classical
  simp only [sortedFibre, Finset.mem_filter] at hp
  convert hp.2

/-- A1. The vertical largest output is a null face. -/
theorem vertical_output_null {n m k : Mode} {a b c : Sgn} (h0 : n 0 = 0) (h1 : n 1 = 0)
    (hp : (m, k) ∈ sortedFibre n) (hres : phase3 a b c m k n = 0) :
    gammaCoef a b c m k n = 0 := by
  obtain ⟨hsum, hmk, hkn, hm3, hk3, hn3⟩ := mem_sortedFibre hp
  have h2 : m 2 + k 2 + n 2 = 0 := by simpa using congrFun hsum 2
  have hnn : nsqZ n = n 2 ^ 2 := by simp [nsqZ, Fin.sum_univ_three, h0, h1]
  have hN : absk n = |(n 2 : ℝ)| := by
    rw [absk_eq_sqrt_nsqZ', hnn]; push_cast; exact Real.sqrt_sq_eq_abs _
  -- integer facts: `|m₃| + |k₃| = |n₃|`
  have hm2 : m 2 ^ 2 ≤ nsqZ m := by
    simp only [nsqZ, Fin.sum_univ_three]; nlinarith [sq_nonneg (m 0), sq_nonneg (m 1)]
  have hk2 : k 2 ^ 2 ≤ nsqZ k := by
    simp only [nsqZ, Fin.sum_univ_three]; nlinarith [sq_nonneg (k 0), sq_nonneg (k 1)]
  have hmn : |m 2| ≤ |n 2| := sq_le_sq.mp (by linarith)
  have hkn' : |k 2| ≤ |n 2| := sq_le_sq.mp (by linarith)
  have hsumabs : |m 2| + |k 2| = |n 2| := by
    rcases abs_cases (m 2) with ⟨ha, _⟩ | ⟨ha, _⟩ <;>
      rcases abs_cases (k 2) with ⟨hb, _⟩ | ⟨hb, _⟩ <;>
      rcases abs_cases (n 2) with ⟨hc, _⟩ | ⟨hc, _⟩ <;>
      simp only [ha, hb, hc] at hmn hkn' ⊢ <;> linarith
  -- real facts
  have hMr : |(m 2 : ℝ)| ≤ absk m := by
    rw [absk_eq_sqrt_nsqZ']; exact Real.abs_le_sqrt (by exact_mod_cast hm2)
  have hKr : |(k 2 : ℝ)| ≤ absk k := by
    rw [absk_eq_sqrt_nsqZ']; exact Real.abs_le_sqrt (by exact_mod_cast hk2)
  have hMK : absk m ≤ absk k := by
    rw [absk_eq_sqrt_nsqZ', absk_eq_sqrt_nsqZ']
    exact Real.sqrt_le_sqrt (by exact_mod_cast hmk)
  have hKN : absk k ≤ absk n := by
    rw [absk_eq_sqrt_nsqZ', absk_eq_sqrt_nsqZ']
    exact Real.sqrt_le_sqrt (by exact_mod_cast hkn)
  have hsr : |(m 2 : ℝ)| + |(k 2 : ℝ)| = absk n := by
    rw [hN]; exact_mod_cast hsumabs
  have hsg : ∀ s : Sgn, |sg s| = 1 := by intro s; cases s <;> simp [sg]
  have hres' : sg a * m 2 * absk m + sg b * k 2 * absk k = -(sg c * n 2 * absk n) := by
    simp only [phase3, lam] at hres; linarith
  have hlhs : |sg a * m 2 * absk m + sg b * k 2 * absk k| ≤
      |(m 2 : ℝ)| * absk m + |(k 2 : ℝ)| * absk k := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_mul, abs_mul, hsg, hsg, abs_of_nonneg (absk_nonneg' m),
      abs_of_nonneg (absk_nonneg' k), one_mul, one_mul]
  have hrhs : |-(sg c * n 2 * absk n)| = absk n ^ 2 := by
    rw [abs_neg, abs_mul, abs_mul, hsg, one_mul, ← hN, abs_of_nonneg (absk_nonneg' n), sq]
  rw [hres', hrhs] at hlhs
  have hm0 : 0 < |(m 2 : ℝ)| := abs_pos.mpr (by exact_mod_cast hm3)
  have hk0 : 0 < |(k 2 : ℝ)| := abs_pos.mpr (by exact_mod_cast hk3)
  have e1 : 0 ≤ |(m 2 : ℝ)| * (absk n - absk m) := mul_nonneg hm0.le (by linarith)
  have e2 : 0 ≤ |(k 2 : ℝ)| * (absk n - absk k) := mul_nonneg hk0.le (by linarith)
  have e3 : |(m 2 : ℝ)| * (absk n - absk m) + |(k 2 : ℝ)| * (absk n - absk k) ≤ 0 := by
    have : absk n ^ 2 = (|(m 2 : ℝ)| + |(k 2 : ℝ)|) * absk n := by rw [hsr, sq]
    nlinarith
  have hMeq : absk m = absk n := by
    have : |(m 2 : ℝ)| * (absk n - absk m) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h <;> [linarith; linarith]
  have hKeq : absk k = absk n := by
    have : |(k 2 : ℝ)| * (absk n - absk k) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h <;> [linarith; linarith]
  simp only [gammaCoef]
  rw [hMeq, hKeq]
  cases a <;> cases b <;> cases c <;> simp [sg]

/-- A3. Common squarefree part and the integer resonance. -/
theorem exists_coords {n m k : Mode} {a b c : Sgn} (hp : (m, k) ∈ sortedFibre n)
    (hres : phase3 a b c m k n = 0) :
    ∃ Δ x y z : ℕ, Squarefree Δ ∧ nsqZ k = Δ * x ^ 2 ∧ nsqZ m = Δ * y ^ 2 ∧ nsqZ n = Δ * z ^ 2 ∧
      1 ≤ y ∧ y ≤ x ∧ x ≤ z ∧
      k 2 * x + (sgZ a * sgZ b) * m 2 * y + (sgZ c * sgZ b) * n 2 * z = 0 := by
  obtain ⟨_, hmk, hkn, hm3, hk3, hn3⟩ := mem_sortedFibre hp
  have hpos : ∀ l : Mode, l 2 ≠ 0 → 0 < nsqZ l := by
    intro l hl
    simp only [nsqZ, Fin.sum_univ_three]
    nlinarith [sq_nonneg (l 0), sq_nonneg (l 1), pow_pos (abs_pos.mpr hl) 2, sq_abs (l 2)]
  have hcast : ∀ l : Mode, l 2 ≠ 0 → absk l = Real.sqrt (((nsqZ l).toNat : ℕ) : ℝ) := by
    intro l hl
    rw [absk_eq_sqrt_nsqZ']
    congr 1
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (hpos l hl).le]
  have hsgZ : ∀ s : Sgn, ((sgZ s : ℤ) : ℝ) = sg s := by intro s; cases s <;> simp [sg, sgZ]
  have hsgZ0 : ∀ s : Sgn, sgZ s ≠ 0 := by intro s; cases s <;> simp [sgZ]
  have hR : ((sgZ b * k 2 : ℤ) : ℝ) * Real.sqrt (((nsqZ k).toNat : ℕ) : ℝ) +
      ((sgZ a * m 2 : ℤ) : ℝ) * Real.sqrt (((nsqZ m).toNat : ℕ) : ℝ) +
      ((sgZ c * n 2 : ℤ) : ℝ) * Real.sqrt (((nsqZ n).toNat : ℕ) : ℝ) = 0 := by
    rw [← hcast k hk3, ← hcast m hm3, ← hcast n hn3]
    push_cast
    rw [hsgZ, hsgZ, hsgZ]
    simp only [phase3, lam] at hres
    linear_combination hres
  obtain ⟨Δ, x, y, z, hΔ, hA, hB, hC⟩ := squarefree_rigidity
    (Int.lt_toNat.mpr (hpos k hk3)) (Int.lt_toNat.mpr (hpos m hm3))
    (Int.lt_toNat.mpr (hpos n hn3)) (mul_ne_zero (hsgZ0 b) hk3) (mul_ne_zero (hsgZ0 a) hm3)
    (mul_ne_zero (hsgZ0 c) hn3) hR
  have hZ : ∀ (l : Mode) (u : ℕ), l 2 ≠ 0 → (nsqZ l).toNat = Δ * u ^ 2 →
      nsqZ l = Δ * u ^ 2 := by
    intro l u hl h
    rw [← Int.toNat_of_nonneg (hpos l hl).le, h]; push_cast; ring
  have hkZ := hZ k x hk3 hA
  have hmZ := hZ m y hm3 hB
  have hnZ := hZ n z hn3 hC
  have hΔ0 : 0 < Δ := Nat.pos_of_ne_zero hΔ.ne_zero
  have hΔZ : (0 : ℤ) < Δ := by exact_mod_cast hΔ0
  have hy0 : y ≠ 0 := by
    rintro rfl
    have := hpos m hm3
    rw [hmZ] at this; simp at this
  have hyx : y ≤ x := by
    have h : (Δ : ℤ) * y ^ 2 ≤ Δ * x ^ 2 := by rw [← hmZ, ← hkZ]; exact hmk
    have h' : ((y : ℤ)) ^ 2 ≤ (x : ℤ) ^ 2 := le_of_mul_le_mul_left h hΔZ
    have : (y : ℤ) ≤ x := by nlinarith [Int.natCast_nonneg x, Int.natCast_nonneg y]
    exact_mod_cast this
  have hxz : x ≤ z := by
    have h : (Δ : ℤ) * x ^ 2 ≤ Δ * z ^ 2 := by rw [← hkZ, ← hnZ]; exact hkn
    have h' : ((x : ℤ)) ^ 2 ≤ (z : ℤ) ^ 2 := le_of_mul_le_mul_left h hΔZ
    have : (x : ℤ) ≤ z := by nlinarith [Int.natCast_nonneg x, Int.natCast_nonneg z]
    exact_mod_cast this
  refine ⟨Δ, x, y, z, hΔ, hkZ, hmZ, hnZ, Nat.one_le_iff_ne_zero.mpr hy0, hyx, hxz, ?_⟩
  -- the integer resonance
  have hsq : ∀ u : ℕ, Real.sqrt ((Δ * u ^ 2 : ℕ) : ℝ) = Real.sqrt Δ * u := by
    intro u
    push_cast
    rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]
  rw [hA, hB, hC, hsq, hsq, hsq] at hR
  have hsΔ : 0 < Real.sqrt Δ := Real.sqrt_pos.mpr (by exact_mod_cast hΔ0)
  have hR' : ((sgZ b * k 2 : ℤ) : ℝ) * x + ((sgZ a * m 2 : ℤ) : ℝ) * y +
      ((sgZ c * n 2 : ℤ) : ℝ) * z = 0 := by
    have : Real.sqrt Δ * (((sgZ b * k 2 : ℤ) : ℝ) * x + ((sgZ a * m 2 : ℤ) : ℝ) * y +
      ((sgZ c * n 2 : ℤ) : ℝ) * z) = 0 := by linear_combination hR
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hsΔ.ne'
    · exact h
  have hI : sgZ b * k 2 * x + sgZ a * m 2 * y + sgZ c * n 2 * z = 0 := by
    exact_mod_cast hR'
  have hb2 : sgZ b * sgZ b = 1 := by cases b <;> simp [sgZ]
  linear_combination sgZ b * hI - k 2 * x * hb2

namespace Coords
variable {n k : Mode} (c : Coords n k)

private theorem hres' : k 2 * c.x + c.s2 * (-k 2 - n 2) * c.y + c.s3 * n 2 * c.z = 0 := by
  have h := c.hres
  simpa [Pi.sub_apply, Pi.neg_apply] using h

private theorem hm' : (k 0 + n 0) ^ 2 + (k 1 + n 1) ^ 2 + (k 2 + n 2) ^ 2 = c.Δ * c.y ^ 2 := by
  have h := c.hm
  simp only [nsqZ, Fin.sum_univ_three, Pi.sub_apply, Pi.neg_apply] at h
  linear_combination h

private theorem hk' : k 0 ^ 2 + k 1 ^ 2 + k 2 ^ 2 = c.Δ * c.x ^ 2 := by
  have h := c.hk
  simp only [nsqZ, Fin.sum_univ_three] at h
  linear_combination h

private theorem hn' : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = c.Δ * c.z ^ 2 := by
  have h := c.hn
  simp only [nsqZ, Fin.sum_univ_three] at h
  linear_combination h

/-- A4 (i)–(iii): the exact identities. -/
theorem x_id : n 2 * c.x = n 2 * (c.t + c.s3 * c.z) + c.t * c.w := by
  have h := c.hres'
  simp only [t, w]
  linear_combination -h

theorem L_id : 2 * n 2 * c.L =
    -c.Δ * n 2 * (c.t + c.s3 * c.z) ^ 2 - 2 * (n 2 ^ 2 + c.Δ * c.t ^ 2) * c.w := by
  have hx := c.x_id
  have hm := c.hm'
  have hk := c.hk'
  have hn := c.hn'
  simp only [t, w, L] at hx ⊢
  have e2 : c.s2 ^ 2 = 1 := by rcases c.hs2 with h | h <;> rw [h] <;> norm_num
  have e3 : c.s3 ^ 2 = 1 := by rcases c.hs3 with h | h <;> rw [h] <;> norm_num
  linear_combination n 2 * hm - n 2 * hk - n 2 * hn - 2 * c.Δ * (c.x - c.s2 * c.y) * hx
    - n 2 * c.Δ * c.y ^ 2 * e2 + n 2 * c.Δ * c.z ^ 2 * e3

theorem J_id : c.J ^ 2 = c.nh2 * (c.Δ * c.x ^ 2 - c.w ^ 2) - c.L ^ 2 := by
  have hk := c.hk'
  simp only [J, nh2, w, L]
  linear_combination (n 0 ^ 2 + n 1 ^ 2) * hk

/-- A4 (iv)–(v): divisibility. -/
theorem v_dvd_tw : n 2 ∣ c.t * c.w :=
  Dvd.intro (c.x - (c.t + c.s3 * c.z)) (by linear_combination c.x_id)

theorem vg_dvd_w : ((c.v / c.g : ℕ) : ℤ) ∣ c.w := by
  rw [Int.natCast_dvd]
  have hv0 : 0 < c.v := Int.natAbs_pos.mpr c.hn3
  have hg0 : 0 < c.g := Nat.gcd_pos_of_pos_left _ hv0
  have hdvd : c.v ∣ c.t.natAbs * c.w.natAbs := by
    rw [← Int.natAbs_mul]
    exact Int.natAbs_dvd_natAbs.mpr c.v_dvd_tw
  have hcop := Nat.coprime_div_gcd_div_gcd (m := c.v) (n := c.t.natAbs) hg0
  have hv : c.v = c.g * (c.v / c.g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
  have ht : c.t.natAbs = c.g * (c.t.natAbs / c.g) :=
    (Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)).symm
  have h2 : c.v / c.g ∣ c.w.natAbs * (c.t.natAbs / c.g) := by
    rw [hv, ht, mul_assoc] at hdvd
    rw [mul_comm]
    exact Nat.dvd_of_mul_dvd_mul_left hg0 hdvd
  exact hcop.dvd_of_dvd_mul_right h2

/-- A5: ranges. -/
theorem t_nonneg : 0 ≤ c.t := by
  have := c.hy; have := c.hyx
  simp only [t]
  rcases c.hs2 with h | h <;> rw [h] <;> linarith

theorem t_lt : c.t < 2 * c.z := by
  have := c.hy; have := c.hyx; have := c.hxz
  have hr := c.hres'
  have hk3 := c.hk3
  have hm3 : -k 2 - n 2 ≠ 0 := by simpa using c.hm3
  simp only [t]
  rcases c.hs2 with h | h <;> rw [h] at hr ⊢
  · linarith
  · by_contra hc
    have hx : c.x = c.y := by linarith
    have hz : c.z = c.y := by linarith
    rw [hx, hz] at hr
    have hy0 : c.y ≠ 0 := by omega
    rcases c.hs3 with h3 | h3 <;> rw [h3] at hr
    · apply hm3
      have : c.y * (2 * (k 2 + n 2)) = 0 := by linear_combination hr
      rcases mul_eq_zero.mp this with h' | h' <;> [exact absurd h' hy0; linarith]
    · apply hk3
      have : c.y * (2 * k 2) = 0 := by linear_combination hr
      rcases mul_eq_zero.mp this with h' | h' <;> [exact absurd h' hy0; linarith]

theorem t_eq_zero : c.t = 0 → c.x = c.y ∧ c.y = c.z := by
  intro h0
  have := c.hy; have := c.hyx; have := c.hxz
  have hr := c.hres'
  simp only [t] at h0
  rcases c.hs2 with h | h <;> rw [h] at hr h0
  · have hx : c.x = c.y := by linarith
    refine ⟨hx, ?_⟩
    rw [hx] at hr
    have : n 2 * (c.s3 * c.z - c.y) = 0 := by linear_combination hr
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' c.hn3
    · rcases c.hs3 with h3 | h3 <;> rw [h3] at h' <;> linarith
  · linarith

private theorem lagrange (m k : Mode) :
    nsqZ m * nsqZ k - dotZ m k ^ 2 =
      (m 1 * k 2 - m 2 * k 1) ^ 2 + (m 2 * k 0 - m 0 * k 2) ^ 2 + (m 0 * k 1 - m 1 * k 0) ^ 2 := by
  simp only [nsqZ, dotZ, Fin.sum_univ_three]
  ring

theorem t_eq_z : c.t = c.z → nsqZ (-k - n) * nsqZ k = dotZ (-k - n) k ^ 2 := by
  intro htz
  have hm := c.hm'
  have hk := c.hk'
  have hn := c.hn'
  simp only [t] at htz
  rcases c.hs2 with h | h <;> rw [h] at htz
  · -- `x = y + z`: `m ∥ n`
    have hlag : nsqZ (-k - n) * nsqZ k - dotZ (-k - n) k ^ 2 =
        nsqZ (-k - n) * nsqZ n - dotZ (-k - n) n ^ 2 := by
      simp only [nsqZ, dotZ, Fin.sum_univ_three, Pi.sub_apply, Pi.neg_apply]
      ring
    have hE : 2 * dotZ (-k - n) n = 2 * (c.Δ * c.y * c.z) := by
      simp only [dotZ, Fin.sum_univ_three, Pi.sub_apply, Pi.neg_apply]
      have hx : c.x = 1 * c.y + c.z := by linarith
      rw [hx] at hk
      linear_combination hk - hm - hn
    have hE' : dotZ (-k - n) n = c.Δ * c.y * c.z := by linarith
    have : nsqZ (-k - n) * nsqZ n - dotZ (-k - n) n ^ 2 = 0 := by
      rw [c.hm, c.hn, hE']; ring
    linarith
  · -- `z = x + y`: `m ∥ k`
    have hD : 2 * dotZ (-k - n) k = 2 * (c.Δ * c.x * c.y) := by
      simp only [dotZ, Fin.sum_univ_three, Pi.sub_apply, Pi.neg_apply]
      have hz : c.z = c.x + c.y := by linarith
      rw [hz] at hn
      linear_combination hn - hm - hk
    have hD' : dotZ (-k - n) k = c.Δ * c.x * c.y := by linarith
    rw [c.hm, c.hk, hD']; ring

theorem s2_branch : c.t ≠ c.z → (c.t < c.z ↔ c.s2 = 1) := by
  intro htz
  have := c.hy; have := c.hyx; have := c.hxz
  have hΔ := c.hΔ
  simp only [t] at htz ⊢
  rcases c.hs2 with h | h <;> rw [h] at htz ⊢
  · exact ⟨fun _ => rfl, fun _ => by linarith⟩
  · simp only [show (-1 : ℤ) ≠ 1 by norm_num, iff_false, not_lt]
    -- triangle inequality `z ≤ x + y`
    have hlag := lagrange (-k - n) k
    have hcs : dotZ (-k - n) k ^ 2 ≤ (c.Δ * c.x * c.y) ^ 2 := by
      have : nsqZ (-k - n) * nsqZ k = (c.Δ * c.x * c.y) ^ 2 := by rw [c.hm, c.hk]; ring
      nlinarith [sq_nonneg ((-k - n) 1 * k 2 - (-k - n) 2 * k 1),
        sq_nonneg ((-k - n) 2 * k 0 - (-k - n) 0 * k 2),
        sq_nonneg ((-k - n) 0 * k 1 - (-k - n) 1 * k 0)]
    have hpos : 0 ≤ c.Δ * c.x * c.y :=
      mul_nonneg (mul_nonneg hΔ.le (by linarith)) (by linarith)
    have hD : dotZ (-k - n) k ≤ c.Δ * c.x * c.y := by
      nlinarith
    have hN : nsqZ n = nsqZ (-k - n) + nsqZ k + 2 * dotZ (-k - n) k := by
      simp only [nsqZ, dotZ, Fin.sum_univ_three, Pi.sub_apply, Pi.neg_apply]
      ring
    rw [c.hn, c.hm, c.hk] at hN
    have hsq : c.Δ * c.z ^ 2 ≤ c.Δ * (c.x + c.y) ^ 2 := by nlinarith
    have hsq' : c.z ^ 2 ≤ (c.x + c.y) ^ 2 := le_of_mul_le_mul_left hsq hΔ
    nlinarith

/-- Shell bound on the height: `T |w| ≤ v (T + 2z)` for `T ≤ t`. -/
theorem w_shell {T : ℤ} (hT : 0 < T) (hTt : T ≤ c.t) :
    T * |c.w| ≤ (c.v : ℤ) * (T + 2 * c.z) := by
  have := c.hy; have := c.hyx; have := c.hxz
  have hx : c.t * c.w = n 2 * (c.x - c.t - c.s3 * c.z) := by linear_combination -c.x_id
  have habs : c.t * |c.w| = (c.v : ℤ) * |c.x - c.t - c.s3 * c.z| := by
    have := congrArg abs hx
    rw [abs_mul, abs_mul, abs_of_pos (lt_of_lt_of_le hT hTt)] at this
    rw [this, v, Int.natCast_natAbs]
  have hb : |c.x - c.t - c.s3 * c.z| ≤ 2 * c.z := by
    simp only [t]
    rcases c.hs2 with h | h <;> rcases c.hs3 with h3 | h3 <;> rw [h, h3] <;>
      exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hv : (0 : ℤ) ≤ c.v := Int.natCast_nonneg _
  have hw : 0 ≤ |c.w| := abs_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hTt hw, mul_le_mul_of_nonneg_left hb hv]

end Coords

end OVNS.Quant
