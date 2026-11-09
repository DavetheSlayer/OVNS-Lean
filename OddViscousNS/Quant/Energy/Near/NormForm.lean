import OddViscousNS.Quant.Energy.Near.Defs

/-!
# E9: the norm form `D` of a near triad

For the triad `(p, j = k − p, k)` put `A = p₃²|p|²`, `B = j₃²|j|²`, `C = k₃²|k|²` (integers) and
`D = A² + B² + C² − 2AB − 2BC − 2CA = (A − B + C)² − 4AC` (`normD`).  With `a = λ_{s₁}(p)`,
`b = λ_{s₂}(j)`, `c = λ₊(k)` (so `a² = A`, …) the four phases of the patterns `(±s₁, ±s₂)` are
`a + b − c`, `−a + b − c`, `a − b − c`, `−a − b − c`, and `D` is their product
(`normD_eq_prod_phases`; the sympy identity `D = ∏_{signs}(√A ± √B ± √C)` of the route report
§2.1 step 1 and of `near_moment.py`).  `Counting.lean`'s `resPoly`/`eval_resPoly` encode the
same form `(A + G − B)² − 4GA` for the exactly resonant count; here the integer `D` itself is the
object, so it is restated (the private `resPoly` is not reusable).

On a **near** triad (`0 < |Φ| < 1`, all legs with nonzero third coordinate):
* `D ≠ 0` (`normD_ne_zero_of_near`): a vanishing conjugate phase would force
  `|Φ| = 2|a|, 2|b|` or `2|c| ≥ 2` (route report §2.1 step 1; checked exhaustively up to `K = 32`
  in `near_moment.py`), hence `1 ≤ |D|`;
* `|D| ≤ 27 |Φ| m² K³ |k₃|` (`abs_normD_le_of_near`): the three conjugates are bounded by
  `1 + 2|a| ≤ 3|p|²`, `1 + 2|b| ≤ 3|j|²`, `1 + 2|c| ≤ 3|k₃|K`, and `|p|²|j|² ≤ m²K²`.  This is the
  report's `(459/32)|Φ| m² K³ |w|` (valid for `K ≥ 8`) with the cruder constant `27` valid for
  all `K ≥ 1`; only *some* constant is needed downstream;
* the window `|A − B| ≤ 4 |k₃| K³` (`abs_legA_sub_le_of_near`) used by the centred count.
-/

noncomputable section

namespace OVNS.Quant

/-- `A(p) = p₃² |p|²`, the integer value of `λ_±(p)²`. -/
def legA (p : Mode) : ℤ := p 2 ^ 2 * nsqZ p

/-- The norm form `D = A² + B² + C² − 2AB − 2BC − 2CA` of the triad `(p, k − p, k)`, with
`A = A(p)`, `B = A(k − p)`, `C = A(k)` (route report §1.5, §2.1). -/
def normD (p k : Mode) : ℤ :=
  legA p ^ 2 + legA (k - p) ^ 2 + legA k ^ 2 - 2 * legA p * legA (k - p)
    - 2 * legA (k - p) * legA k - 2 * legA k * legA p

/-- `D = y² − 4AC` with `y = A − B + C`; hence `y² ≡ D (mod 4C)` (route report §2.1 step 2). -/
theorem normD_eq_sq_sub (p k : Mode) :
    normD p k = (legA p - legA (k - p) + legA k) ^ 2 - 4 * legA p * legA k := by
  unfold normD
  ring

/-- `y² − D = 4AC`. -/
theorem sq_sub_normD (p k : Mode) :
    (legA p - legA (k - p) + legA k) ^ 2 - normD p k = 4 * legA p * legA k := by
  rw [normD_eq_sq_sub]
  ring

theorem legA_nonneg (p : Mode) : 0 ≤ legA p := mul_nonneg (sq_nonneg _) (nsqZ_nonneg p)

/-- `λ_s(p)² = A(p)`. -/
theorem lam_sq (s : Sgn) (p : Mode) : lam s p ^ 2 = (legA p : ℝ) := by
  have h : sg s ^ 2 = 1 := by cases s <;> simp [sg]
  simp only [lam, legA]
  push_cast
  rw [mul_pow, mul_pow, h, one_mul, absk_sq_eq_nsqZ]

/-- `|A(p)| ≤ |p|⁴`. -/
theorem legA_le (p : Mode) : (legA p : ℝ) ≤ absk p ^ 4 := by
  rw [← lam_sq true p, show absk p ^ 4 = (absk p ^ 2) ^ 2 by ring, ← sq_abs]
  gcongr
  rw [abs_lam, sq]
  exact mul_le_mul_of_nonneg_right (abs_coord_le_absk p 2) (absk_nonneg p)

/-- **Product identity.** The norm form is the product of the four phases of the patterns
`(±s₁, ±s₂)` (any base pattern `(s₁, s₂)`). -/
theorem normD_eq_prod_phases (s₁ s₂ : Sgn) (p k : Mode) :
    (normD p k : ℝ) = nearPhi s₁ s₂ p k * nearPhi (!s₁) s₂ p k * nearPhi s₁ (!s₂) p k *
      nearPhi (!s₁) (!s₂) p k := by
  simp only [normD, nearPhi, lam_not]
  push_cast
  rw [← lam_sq s₁ p, ← lam_sq s₂ (k - p), ← lam_sq true k]
  ring

/-- `D` as the product over all four patterns. -/
theorem normD_eq_prod (p k : Mode) :
    (normD p k : ℝ) = ∏ s : Sgn × Sgn, nearPhi s.1 s.2 p k := by
  rw [Fintype.prod_prod_type]
  simp only [Fintype.prod_bool]
  rw [normD_eq_prod_phases true true]
  simp only [Bool.not_true]
  ring

/-- The explicit form `D = (a + b − c)(−a + b − c)(a − b − c)(−a − b − c)` with
`a = λ_{s₁}(p)`, `b = λ_{s₂}(k − p)`, `c = λ₊(k)`. -/
theorem normD_eq_four (s₁ s₂ : Sgn) (p k : Mode) :
    (normD p k : ℝ) = (lam s₁ p + lam s₂ (k - p) - lam true k) *
      (-lam s₁ p + lam s₂ (k - p) - lam true k) * (lam s₁ p - lam s₂ (k - p) - lam true k) *
      (-lam s₁ p - lam s₂ (k - p) - lam true k) := by
  rw [normD_eq_prod_phases s₁ s₂]
  simp only [nearPhi, lam_not]
  ring

/-! ### Size of the signed lengths -/

/-- `1 ≤ |λ_s(p)|` for a fast leg. -/
theorem one_le_abs_lam (s : Sgn) {p : Mode} (hp : p 2 ≠ 0) : 1 ≤ |lam s p| := by
  rw [abs_lam]
  have h1 : (1 : ℝ) ≤ |(p 2 : ℝ)| := by exact_mod_cast Int.one_le_abs hp
  have h2 : 1 ≤ absk p := one_le_absk (by rintro rfl; simp at hp)
  nlinarith

/-- `|λ_s(p)| ≤ |p|²`. -/
theorem abs_lam_le_sq (s : Sgn) (p : Mode) : |lam s p| ≤ absk p ^ 2 := by
  rw [abs_lam, sq]
  exact mul_le_mul_of_nonneg_right (abs_coord_le_absk p 2) (absk_nonneg p)

private theorem sub_two_mul_ne_zero {x Φ : ℝ} (hx : 1 ≤ |x|) (hΦ : |Φ| < 1) :
    Φ - 2 * x ≠ 0 := by
  intro h
  have h1 : Φ = 2 * x := sub_eq_zero.1 h
  rw [h1, abs_mul, abs_two] at hΦ
  linarith

private theorem add_two_mul_ne_zero {x Φ : ℝ} (hx : 1 ≤ |x|) (hΦ : |Φ| < 1) :
    Φ + 2 * x ≠ 0 := by
  intro h
  have h1 : Φ = 2 * (-x) := by linarith
  rw [h1, abs_mul, abs_two, abs_neg] at hΦ
  linarith

/-- The three conjugate phases of a near pattern do not vanish. -/
private theorem four_phases_ne_zero {a b c : ℝ} (ha : 1 ≤ |a|) (hb : 1 ≤ |b|) (hc : 1 ≤ |c|)
    (h0 : 0 < |a + b - c|) (h1 : |a + b - c| < 1) :
    (a + b - c) * (-a + b - c) * (a - b - c) * (-a - b - c) ≠ 0 := by
  have e1 : -a + b - c = (a + b - c) - 2 * a := by ring
  have e2 : a - b - c = (a + b - c) - 2 * b := by ring
  have e3 : -a - b - c = -((a + b - c) + 2 * c) := by ring
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (abs_pos.1 h0) ?_) ?_) ?_
  · rw [e1]
    exact sub_two_mul_ne_zero ha h1
  · rw [e2]
    exact sub_two_mul_ne_zero hb h1
  · rw [e3]
    exact neg_ne_zero.2 (add_two_mul_ne_zero hc h1)

/-- The three conjugate phases of a near pattern are at most `1 + 2|a|`, `1 + 2|b|`, `1 + 2|c|`. -/
private theorem four_phases_abs_le {a b c : ℝ} (h1 : |a + b - c| < 1) :
    |(a + b - c) * (-a + b - c) * (a - b - c) * (-a - b - c)| ≤
      |a + b - c| * (1 + 2 * |a|) * (1 + 2 * |b|) * (1 + 2 * |c|) := by
  have e1 : -a + b - c = (a + b - c) - 2 * a := by ring
  have e2 : a - b - c = (a + b - c) - 2 * b := by ring
  have e3 : -a - b - c = -((a + b - c) + 2 * c) := by ring
  have b1 : |-a + b - c| ≤ 1 + 2 * |a| := by
    rw [e1]
    calc |(a + b - c) - 2 * a| ≤ |a + b - c| + |2 * a| := abs_sub _ _
      _ ≤ 1 + 2 * |a| := by rw [abs_mul, abs_two]; linarith
  have b2 : |a - b - c| ≤ 1 + 2 * |b| := by
    rw [e2]
    calc |(a + b - c) - 2 * b| ≤ |a + b - c| + |2 * b| := abs_sub _ _
      _ ≤ 1 + 2 * |b| := by rw [abs_mul, abs_two]; linarith
  have b3 : |-a - b - c| ≤ 1 + 2 * |c| := by
    rw [e3, abs_neg]
    calc |(a + b - c) + 2 * c| ≤ |a + b - c| + |2 * c| := abs_add_le _ _
      _ ≤ 1 + 2 * |c| := by rw [abs_mul, abs_two]; linarith
  rw [abs_mul, abs_mul, abs_mul]
  gcongr

/-! ### `D` on near triads -/

/-- **`D ≠ 0` on near triads** (route report §2.1 step 1): the near phase is nonzero and its three
conjugates have modulus `> 2 − 1`. -/
theorem normD_ne_zero_of_near {s₁ s₂ : Sgn} {p k : Mode} (hp : p ∈ nearBox k)
    (h : IsNear s₁ s₂ p k) : normD p k ≠ 0 := by
  obtain ⟨hk, hp3, hj3, -, -⟩ := mem_nearBox.1 hp
  have hcast : (normD p k : ℝ) ≠ 0 := by
    rw [normD_eq_four s₁ s₂]
    exact four_phases_ne_zero (one_le_abs_lam s₁ hp3) (one_le_abs_lam s₂ hj3)
      (one_le_abs_lam true hk) h.1 h.2
  exact_mod_cast hcast

/-- `1 ≤ |D|` on near triads (`D` is a nonzero integer). -/
theorem one_le_abs_normD_of_near {s₁ s₂ : Sgn} {p k : Mode} (hp : p ∈ nearBox k)
    (h : IsNear s₁ s₂ p k) : 1 ≤ |(normD p k : ℝ)| := by
  have := Int.one_le_abs (normD_ne_zero_of_near hp h)
  exact_mod_cast this

/-- `|p|² |j|² ≤ m² K²` on the box. -/
theorem sq_mul_sq_le_minLeg {p k : Mode} (hp : p ∈ nearBox k) :
    absk p ^ 2 * absk (k - p) ^ 2 ≤ minLeg p k ^ 2 * absk k ^ 2 := by
  obtain ⟨-, -, -, hpk, hjk⟩ := mem_nearBox.1 hp
  have h1 : absk p * absk (k - p) = minLeg p k * max (absk p) (absk (k - p)) :=
    (min_mul_max _ _).symm
  have h2 : max (absk p) (absk (k - p)) ≤ absk k := max_le hpk hjk
  have h3 : 0 ≤ minLeg p k := (minLeg_pos hp).le
  calc absk p ^ 2 * absk (k - p) ^ 2 = (absk p * absk (k - p)) ^ 2 := by ring
    _ = (minLeg p k * max (absk p) (absk (k - p))) ^ 2 := by rw [h1]
    _ ≤ (minLeg p k * absk k) ^ 2 := by
        have h4 : 0 ≤ max (absk p) (absk (k - p)) := le_trans (absk_nonneg p) (le_max_left _ _)
        exact pow_le_pow_left₀ (mul_nonneg h3 h4) (mul_le_mul_of_nonneg_left h2 h3) 2
    _ = minLeg p k ^ 2 * absk k ^ 2 := by ring

/-- **Size of `D` on near triads**: `|D| ≤ 27 |Φ| m² K³ |k₃|` (route report §2.1 step 1 with
`459/32` replaced by `27`, valid for all `K ≥ 1`). -/
theorem abs_normD_le_of_near {s₁ s₂ : Sgn} {p k : Mode} (hp : p ∈ nearBox k)
    (h : IsNear s₁ s₂ p k) :
    |(normD p k : ℝ)| ≤
      27 * |nearPhi s₁ s₂ p k| * minLeg p k ^ 2 * absk k ^ 3 * |(k 2 : ℝ)| := by
  obtain ⟨hk, hp3, hj3, hpk, hjk⟩ := mem_nearBox.1 hp
  obtain ⟨hK1, hp1, hj1⟩ := one_le_absk_of_mem_nearBox hp
  have hΦ : nearPhi s₁ s₂ p k = lam s₁ p + lam s₂ (k - p) - lam true k := rfl
  have ha : 1 + 2 * |lam s₁ p| ≤ 3 * absk p ^ 2 := by
    have := abs_lam_le_sq s₁ p
    nlinarith
  have hb : 1 + 2 * |lam s₂ (k - p)| ≤ 3 * absk (k - p) ^ 2 := by
    have := abs_lam_le_sq s₂ (k - p)
    nlinarith
  have hc : 1 + 2 * |lam true k| ≤ 3 * (|(k 2 : ℝ)| * absk k) := by
    rw [← abs_lam]
    linarith [one_le_abs_lam true hk]
  have hmm := sq_mul_sq_le_minLeg hp
  rw [normD_eq_four s₁ s₂]
  calc |(lam s₁ p + lam s₂ (k - p) - lam true k) * (-lam s₁ p + lam s₂ (k - p) - lam true k) *
        (lam s₁ p - lam s₂ (k - p) - lam true k) * (-lam s₁ p - lam s₂ (k - p) - lam true k)|
      ≤ |lam s₁ p + lam s₂ (k - p) - lam true k| * (1 + 2 * |lam s₁ p|) *
          (1 + 2 * |lam s₂ (k - p)|) * (1 + 2 * |lam true k|) := four_phases_abs_le (hΦ ▸ h.2)
    _ ≤ |lam s₁ p + lam s₂ (k - p) - lam true k| * (3 * absk p ^ 2) *
          (3 * absk (k - p) ^ 2) * (3 * (|(k 2 : ℝ)| * absk k)) := by gcongr
    _ = 27 * |nearPhi s₁ s₂ p k| * (absk p ^ 2 * absk (k - p) ^ 2) * absk k * |(k 2 : ℝ)| := by
        rw [hΦ]; ring
    _ ≤ 27 * |nearPhi s₁ s₂ p k| * (minLeg p k ^ 2 * absk k ^ 2) * absk k * |(k 2 : ℝ)| := by
        gcongr
    _ = 27 * |nearPhi s₁ s₂ p k| * minLeg p k ^ 2 * absk k ^ 3 * |(k 2 : ℝ)| := by ring

/-- The lower bound on the near phase: `|Φ| ≥ |D| / (27 m² K³ |k₃|)`. -/
theorem abs_normD_div_le_abs_nearPhi {s₁ s₂ : Sgn} {p k : Mode} (hp : p ∈ nearBox k)
    (h : IsNear s₁ s₂ p k) :
    |(normD p k : ℝ)| / (27 * minLeg p k ^ 2 * absk k ^ 3 * |(k 2 : ℝ)|) ≤
      |nearPhi s₁ s₂ p k| := by
  have hk : (k 2 : ℝ) ≠ 0 := by exact_mod_cast (mem_nearBox.1 hp).1
  have hw : 0 < |(k 2 : ℝ)| := abs_pos.2 hk
  have hm := minLeg_pos hp
  have hK : 0 < absk k := lt_of_lt_of_le one_pos (one_le_absk_of_mem_nearBox hp).1
  rw [div_le_iff₀ (by positivity)]
  linarith [abs_normD_le_of_near hp h]

/-- Crude size: `|D| ≤ 27 K⁶` on the near set (`|Φ| < 1`, `m ≤ K`, `|k₃| ≤ K`). -/
theorem abs_normD_le_pow_of_near {s₁ s₂ : Sgn} {p k : Mode} (hp : p ∈ nearBox k)
    (h : IsNear s₁ s₂ p k) : |(normD p k : ℝ)| ≤ 27 * absk k ^ 6 := by
  have hm := minLeg_le_absk hp
  have hm0 := (minLeg_pos hp).le
  have hw : |(k 2 : ℝ)| ≤ absk k := abs_coord_le_absk k 2
  have hΦ : |nearPhi s₁ s₂ p k| ≤ 1 := h.2.le
  have hK0 := absk_nonneg k
  calc |(normD p k : ℝ)| ≤ 27 * |nearPhi s₁ s₂ p k| * minLeg p k ^ 2 * absk k ^ 3 * |(k 2 : ℝ)| :=
        abs_normD_le_of_near hp h
    _ ≤ 27 * 1 * absk k ^ 2 * absk k ^ 3 * absk k := by gcongr
    _ = 27 * absk k ^ 6 := by ring

/-- **The window of `y = A − B + C`** on near triads: `|A − B| ≤ 4 |k₃| K³` (route report §2.1
step 2, "the window has length `O(|w|K³)`"), since `A − B = (a − b)(a + b)`, `a + b = Φ + c`. -/
theorem abs_legA_sub_le_of_near {s₁ s₂ : Sgn} {p k : Mode} (hp : p ∈ nearBox k)
    (h : IsNear s₁ s₂ p k) :
    |((legA p - legA (k - p) : ℤ) : ℝ)| ≤ 4 * |(k 2 : ℝ)| * absk k ^ 3 := by
  obtain ⟨hk, hp3, hj3, hpk, hjk⟩ := mem_nearBox.1 hp
  obtain ⟨hK1, hp1, hj1⟩ := one_le_absk_of_mem_nearBox hp
  set a := lam s₁ p
  set b := lam s₂ (k - p)
  set c := lam true k
  have hΦ : nearPhi s₁ s₂ p k = a + b - c := rfl
  have hc : |c| = |(k 2 : ℝ)| * absk k := abs_lam true k
  have hc1 : 1 ≤ |c| := one_le_abs_lam true hk
  have e : ((legA p - legA (k - p) : ℤ) : ℝ) = (a - b) * ((a + b - c) + c) := by
    push_cast
    rw [← lam_sq s₁ p, ← lam_sq s₂ (k - p)]
    ring
  have h1 : |a - b| ≤ 2 * absk k ^ 2 := by
    have := abs_lam_le_sq s₁ p
    have := abs_lam_le_sq s₂ (k - p)
    have hp2 : absk p ^ 2 ≤ absk k ^ 2 := by gcongr
    have hj2 : absk (k - p) ^ 2 ≤ absk k ^ 2 := by gcongr
    calc |a - b| ≤ |a| + |b| := abs_sub _ _
      _ ≤ 2 * absk k ^ 2 := by linarith
  have h2 : |(a + b - c) + c| ≤ 2 * |c| := by
    calc |(a + b - c) + c| ≤ |a + b - c| + |c| := abs_add_le _ _
      _ ≤ 2 * |c| := by rw [← hΦ]; linarith [h.2]
  rw [e, abs_mul]
  calc |a - b| * |(a + b - c) + c| ≤ (2 * absk k ^ 2) * (2 * |c|) := by gcongr
    _ = 4 * |(k 2 : ℝ)| * absk k ^ 3 := by rw [hc]; ring

end OVNS.Quant

end
