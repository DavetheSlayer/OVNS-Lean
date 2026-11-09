import OddViscousNS.Quant.Arith.Weighted.Surface

/-!
# The shell points on the joint surface (Section D, the point map)

For an output `n`, a squarefree part `Δ` with `|n|² = Δz²`, relative signs `(s₂, s₃)`, a divisor
`g ∣ v = |n₃|` and a dyadic shell `T ≤ t < 2T`, `shellPts` is the set of active middle legs `k`
with `gcd(v, t) = g`, `t` in the shell and `t` non-parabolic (`caOf ≠ 0`).  `ShellHyp` collects the
range hypotheses of the intermediate shells (`N^{p*−1/4} < g`, `T/g > N^{p*}`, `T ≤ 2z`).

* `tOf_eq_coords_t`: every active `k` carries integer coordinates `Coords n k` with the given
  `Δ, z, s₂, s₃` and `x = xOf Δ k`, `y = xOf Δ m`, `t = tOf Δ s₂ n k` (squarefree-part uniqueness:
  `Δz² = Δ'z'²` with both squarefree forces `Δ = Δ'`, `z = z'`).
* `surfPt_spec`: `X₁ = t/g`, `X₂ = g w / n₃` are exact integer quotients (`g ∣ t` from the gcd,
  `n₃ ∣ g w` from `vg_dvd_w`).
* `surface_points`: `X = (t/g, gw/n₃, k_i)` is an integer zero of `surfacePoly Δ z n₃ n_i n_j s₃ g`
  (`F = 4g²n_j²(|k|² − Δx²)` by `x_id`, `L_id`) in the box `(2T/g, 4gN/T, max 2 N)`
  (`|X₂| = g|w|/v ≤ g(T + 2z)/T ≤ 4gz/T` by `w_shell` and `T ≤ 2z`; `z ≤ N`; `|k_i| ≤ N`).
* `surface_points_two_to_one`: `X` determines `t, w, k_i`, hence `x` (by `x_id`) and `k_j²`, so a
  fibre has at most two elements.
* `proj_two_to_one`: `(X₁, X₂)` determines `t, w`, hence `L` (`L_id`) and `J²` (`J_id`), and
  `k_h` is determined by `(L, J)` since `|n_h|² ≠ 0`: at most two `k` per projected point.
-/

open MvPolynomial

noncomputable section

namespace OVNS.Quant

/-- The point `(t/g, g k₃/n₃, k_i)` of the joint surface. -/
def surfPt (Δ : ℕ) (s2 : ℤ) (g : ℕ) (i : Fin 3) (n k : Mode) : Fin 3 → ℤ :=
  ![tOf Δ s2 n k / g, g * k 2 / n 2, k i]

/-- Its projection `(t/g, g k₃/n₃)`. -/
def projPt (Δ : ℕ) (s2 : ℤ) (g : ℕ) (n k : Mode) : Fin 2 → ℤ :=
  ![tOf Δ s2 n k / g, g * k 2 / n 2]

/-- Active `k` with `gcd(v, t) = g`, `T ≤ t < 2T` and `t` non-parabolic. -/
def shellPts (n : Mode) (Δ z : ℕ) (s2 s3 : ℤ) (g T : ℕ) : Finset Mode := by
  classical
  exact ((activePts n s2 s3).filter fun k =>
      Nat.gcd (n 2).natAbs (tOf Δ s2 n k).natAbs = g).filter fun k =>
    (T : ℤ) ≤ tOf Δ s2 n k ∧ tOf Δ s2 n k < 2 * T ∧ caOf Δ z (n 2) (tOf Δ s2 n k) ≠ 0

/-- The shell box `(2T/g, 4gN/T, max 2 N)`. -/
def shellBox (g T : ℕ) (N : ℝ) : Fin 3 → ℝ := ![2 * T / g, 4 * g * N / T, max 2 N]

/-- The range hypotheses of an intermediate surface shell. -/
def ShellHyp (n : Mode) (Δ z g T : ℕ) : Prop :=
  Squarefree Δ ∧ nsqZ n = Δ * z ^ 2 ∧ g ∣ (n 2).natAbs ∧ 1 ≤ T ∧ T ≤ 2 * z ∧
    absk n ^ (pStar - 1 / 4) < g ∧ absk n ^ pStar < (T : ℝ) / g

private theorem mem_sortedFibre'' {n m k : Mode} (hp : (m, k) ∈ sortedFibre n) :
    m + k + n = 0 ∧ nsqZ m ≤ nsqZ k ∧ nsqZ k ≤ nsqZ n ∧ m 2 ≠ 0 ∧ k 2 ≠ 0 ∧ n 2 ≠ 0 := by
  classical
  simp only [sortedFibre, Finset.mem_filter] at hp
  convert hp.2

private lemma sqf_eq_of_mul_sq'' {a b m n : ℕ} (ha : Squarefree a) (hb : Squarefree b)
    (hm : m ≠ 0) (hn : n ≠ 0) (h : a * m ^ 2 = b * n ^ 2) : a = b := by
  refine Nat.eq_of_factorization_eq ha.ne_zero hb.ne_zero fun p ↦ ?_
  have h1 := ha.natFactorization_le_one p
  have h2 := hb.natFactorization_le_one p
  have := congrArg (fun k : ℕ ↦ k.factorization p) h
  rw [Nat.factorization_mul ha.ne_zero (pow_ne_zero 2 hm),
    Nat.factorization_mul hb.ne_zero (pow_ne_zero 2 hn), Nat.factorization_pow,
    Nat.factorization_pow] at this
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at this
  omega

private lemma xOf_eq' {Δ x : ℕ} {k : Mode} (hΔ : 0 < Δ) (h : nsqZ k = (Δ : ℤ) * (x : ℤ) ^ 2) :
    xOf Δ k = x := by
  simp only [xOf]
  rw [h, show (Δ : ℤ) * (x : ℤ) ^ 2 = ((Δ * x ^ 2 : ℕ) : ℤ) by push_cast; ring, Int.toNat_natCast,
    Nat.mul_div_cancel_left _ hΔ, Nat.sqrt_eq']

private lemma nsqZ_pos' {l : Mode} (hl : l 2 ≠ 0) : 0 < nsqZ l := by
  simp only [nsqZ, Fin.sum_univ_three]
  nlinarith [sq_nonneg (l 0), sq_nonneg (l 1), pow_pos (abs_pos.mpr hl) 2, sq_abs (l 2)]

/-- An active output is not vertical (`vertical_output_null`). -/
theorem active_nh {n k : Mode} {s2 s3 : ℤ} (hk : k ∈ activePts n s2 s3) :
    n 0 ^ 2 + n 1 ^ 2 ≠ 0 := by
  classical
  simp only [activePts, Finset.mem_filter] at hk
  obtain ⟨_, hp, a, b, c, _, _, hres, hγ⟩ := hk
  intro h0
  have e0 : n 0 = 0 := by nlinarith [sq_nonneg (n 0), sq_nonneg (n 1)]
  have e1 : n 1 = 0 := by nlinarith [sq_nonneg (n 0), sq_nonneg (n 1)]
  exact hγ (vertical_output_null e0 e1 hp hres)

/-- The integer coordinates of an active point, with the prescribed `Δ, z, s₂, s₃`. -/
theorem tOf_eq_coords_t {n k : Mode} {s2 s3 : ℤ} {Δ z : ℕ} (hk : k ∈ activePts n s2 s3)
    (hΔ : Squarefree Δ) (hn : nsqZ n = Δ * z ^ 2) :
    ∃ c : Coords n k, c.Δ = Δ ∧ c.z = z ∧ c.s2 = s2 ∧ c.s3 = s3 ∧ c.x = xOf Δ k ∧
      c.y = xOf Δ (-k - n) ∧ c.t = tOf Δ s2 n k := by
  classical
  simp only [activePts, Finset.mem_filter] at hk
  obtain ⟨_, hp, a, b, c', h2, h3, hres, _⟩ := hk
  obtain ⟨_, _, _, hm3, hk3, hn3⟩ := mem_sortedFibre'' hp
  obtain ⟨Δ', x, y, z', hΔ', hkx, hmy, hnz, hy, hyx, hxz, hr⟩ := exists_coords hp hres
  have hz'0 : z' ≠ 0 := by omega
  have hpos := nsqZ_pos' hn3
  have hz0 : z ≠ 0 := by
    rintro rfl; rw [hn] at hpos; simp at hpos
  have hE : Δ' * z' ^ 2 = Δ * z ^ 2 := by exact_mod_cast hnz.symm.trans hn
  have hΔe : Δ' = Δ := sqf_eq_of_mul_sq'' hΔ' hΔ hz'0 hz0 hE
  subst Δ'
  have hΔ0 : 0 < Δ := Nat.pos_of_ne_zero hΔ.ne_zero
  have hzz : z' = z := by
    have := Nat.eq_of_mul_eq_mul_left hΔ0 hE
    exact (Nat.pow_left_injective (by norm_num : 2 ≠ 0)) this
  subst z'
  have hsg : ∀ s : Sgn, sgZ s = 1 ∨ sgZ s = -1 := by intro s; cases s <;> simp [sgZ]
  have hpm : ∀ u v : Sgn, sgZ u * sgZ v = 1 ∨ sgZ u * sgZ v = -1 := by
    intro u v; rcases hsg u with h | h <;> rcases hsg v with h' | h' <;> simp [h, h']
  let C : Coords n k :=
    { Δ := Δ, x := x, y := y, z := z, s2 := s2, s3 := s3
      hΔ := by exact_mod_cast hΔ0
      hy := by exact_mod_cast hy
      hyx := by exact_mod_cast hyx
      hxz := by exact_mod_cast hxz
      hs2 := h2 ▸ hpm a b
      hs3 := h3 ▸ hpm c' b
      hk := hkx
      hm := hmy
      hn := hnz
      hres := by rw [← h2, ← h3]; exact hr
      hk3 := hk3
      hm3 := hm3
      hn3 := hn3 }
  refine ⟨C, rfl, rfl, rfl, rfl, (xOf_eq' hΔ0 hkx).symm, (xOf_eq' hΔ0 hmy).symm, ?_⟩
  simp only [Coords.t, tOf, C]
  rw [xOf_eq' hΔ0 hkx, xOf_eq' hΔ0 hmy]

private lemma mem_shellPts {n k : Mode} {Δ z : ℕ} {s2 s3 : ℤ} {g T : ℕ} :
    k ∈ shellPts n Δ z s2 s3 g T ↔ k ∈ activePts n s2 s3 ∧
      Nat.gcd (n 2).natAbs (tOf Δ s2 n k).natAbs = g ∧ (T : ℤ) ≤ tOf Δ s2 n k ∧
        tOf Δ s2 n k < 2 * T ∧ caOf Δ z (n 2) (tOf Δ s2 n k) ≠ 0 := by
  classical
  unfold shellPts
  simp only [Finset.mem_filter]
  tauto

/-- The normalised coordinates of a shell point. -/
private lemma shell_coords {n k : Mode} {s2 s3 : ℤ} {Δ z g T : ℕ} (hH : ShellHyp n Δ z g T)
    (hk : k ∈ shellPts n Δ z s2 s3 g T) :
    ∃ c : Coords n k, c.Δ = Δ ∧ c.z = z ∧ c.s3 = s3 ∧ c.t = tOf Δ s2 n k ∧ c.g = g ∧
      (T : ℤ) ≤ c.t ∧ c.t < 2 * T := by
  obtain ⟨hkA, hg, hT1, hT2, _⟩ := mem_shellPts.1 hk
  obtain ⟨c, hcΔ, hcz, -, hc3, -, -, hct⟩ := tOf_eq_coords_t hkA hH.1 hH.2.1
  refine ⟨c, hcΔ, hcz, hc3, hct, ?_, hct ▸ hT1, hct ▸ hT2⟩
  simp only [Coords.g]; rw [hct]; exact hg

private lemma g_pos {n : Mode} {Δ z g T : ℕ} (hH : ShellHyp n Δ z g T) (hn3 : n 2 ≠ 0) :
    0 < g :=
  Nat.pos_of_ne_zero fun h0 => by
    have := hH.2.2.1; rw [h0, zero_dvd_iff, Int.natAbs_eq_zero] at this; exact hn3 this

/-- The quotients defining `X₁, X₂` are exact. -/
theorem surfPt_spec {n k : Mode} {s2 s3 : ℤ} {Δ z g T : ℕ} (hH : ShellHyp n Δ z g T)
    (hk : k ∈ shellPts n Δ z s2 s3 g T) (i : Fin 3) :
    (g : ℤ) * surfPt Δ s2 g i n k 0 = tOf Δ s2 n k ∧
      n 2 * surfPt Δ s2 g i n k 1 = g * k 2 ∧ surfPt Δ s2 g i n k 2 = k i := by
  obtain ⟨-, hg, -, -, _⟩ := mem_shellPts.1 hk
  obtain ⟨c, -, -, -, -, hcg, -, -⟩ := shell_coords hH hk
  refine ⟨?_, ?_, rfl⟩
  · show (g : ℤ) * (tOf Δ s2 n k / g) = tOf Δ s2 n k
    refine Int.mul_ediv_cancel' (Int.natCast_dvd.2 ?_)
    rw [← hg]; exact Nat.gcd_dvd_right _ _
  · show n 2 * (g * k 2 / n 2) = g * k 2
    refine Int.mul_ediv_cancel' ?_
    obtain ⟨q, hq⟩ := c.vg_dvd_w
    rw [hcg] at hq
    have hv : g * ((n 2).natAbs / g) = (n 2).natAbs := Nat.mul_div_cancel' hH.2.2.1
    have hw : (g : ℤ) * k 2 = ((n 2).natAbs : ℤ) * q := by
      have : c.w = k 2 := rfl
      rw [← this, hq, ← hv]; simp only [Coords.v]; push_cast; ring
    rw [hw]
    exact (Int.dvd_natAbs.2 dvd_rfl).mul_right q

private lemma mem_Icc_floor {a : ℤ} {B : ℝ} (h : |(a : ℝ)| ≤ B) :
    a ∈ Finset.Icc (-⌊B⌋) ⌊B⌋ := by
  have : |a| ≤ ⌊B⌋ := Int.le_floor.2 (by rw [Int.cast_abs]; exact h)
  rw [Finset.mem_Icc]; exact abs_le.1 this

/-- The evaluation of the surface polynomial at a shell point is zero. -/
private lemma surface_eval {n k : Mode} {s2 s3 : ℤ} {Δ z g T : ℕ} (hH : ShellHyp n Δ z g T)
    (hk : k ∈ shellPts n Δ z s2 s3 g T) (i j : Fin 3) (hij : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) :
    eval (surfPt Δ s2 g i n k) (surfacePoly Δ z (n 2) (n i) (n j) s3 g) = 0 := by
  obtain ⟨h0, h1, h2⟩ := surfPt_spec hH hk i
  obtain ⟨c, hcΔ, hcz, hc3, hct, -, -, -⟩ := shell_coords hH hk
  generalize surfPt Δ s2 g i n k = P at h0 h1 h2 ⊢
  have hn3 := c.hn3
  have hev : eval P (surfacePoly Δ z (n 2) (n i) (n j) s3 g) =
      4 * g ^ 2 * n j ^ 2 * P 2 ^ 2 + ((-(2 * Δ * g ^ 2) * P 0 ^ 2 * P 1 - Δ * g ^ 3 * P 0 ^ 2
        - 2 * Δ * g ^ 2 * s3 * z * P 0 - Δ * g * z ^ 2 - 2 * n 2 ^ 2 * P 1)
        - 2 * g * n i * P 2) ^ 2 + 4 * n j ^ 2 * n 2 ^ 2 * P 1 ^ 2
        - 4 * g ^ 2 * n j ^ 2 * Δ * (g * P 0 + s3 * z + P 0 * P 1) ^ 2 := by
    simp only [surfacePoly, map_add, map_sub, map_mul, map_pow, map_neg, eval_X, eval_C]
  have e3 : s3 ^ 2 = 1 := by rcases c.hs3 with h | h <;> rw [← hc3, h] <;> norm_num
  have hL := c.L_id
  have hx := c.x_id
  simp only [hcΔ, hcz, hc3, hct, ← h0] at hL hx
  have hw : c.w = k 2 := rfl
  rw [hw] at hL hx
  have hA : (-(2 * Δ * g ^ 2) * P 0 ^ 2 * P 1 - Δ * g ^ 3 * P 0 ^ 2
        - 2 * Δ * g ^ 2 * s3 * z * P 0 - Δ * g * z ^ 2 - 2 * n 2 ^ 2 * P 1 : ℤ) =
      2 * g * (n 0 * k 0 + n 1 * k 1) := by
    have : n 2 * ((-(2 * Δ * g ^ 2) * P 0 ^ 2 * P 1 - Δ * g ^ 3 * P 0 ^ 2
        - 2 * Δ * g ^ 2 * s3 * z * P 0 - Δ * g * z ^ 2 - 2 * n 2 ^ 2 * P 1 : ℤ) -
        2 * g * (n 0 * k 0 + n 1 * k 1)) = 0 := by
      simp only [Coords.L] at hL
      linear_combination (-(g : ℤ)) * hL - 2 * (n 2 ^ 2 + Δ * g ^ 2 * P 0 ^ 2) * h1
        + Δ * g * n 2 * z ^ 2 * e3
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hn3
    · linarith
  have hX : (g * P 0 + s3 * z + P 0 * P 1 : ℤ) = c.x := by
    have : n 2 * ((g * P 0 + s3 * z + P 0 * P 1 : ℤ) - c.x) = 0 := by
      linear_combination -hx + P 0 * h1
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hn3
    · linarith
  have hk' : k 0 ^ 2 + k 1 ^ 2 + k 2 ^ 2 = Δ * c.x ^ 2 := by
    have := c.hk
    simp only [nsqZ, Fin.sum_univ_three] at this
    rw [hcΔ] at this; linear_combination this
  rw [hev, hA, hX, h2]
  rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · linear_combination 4 * (g : ℤ) ^ 2 * n 1 ^ 2 * hk' + 4 * n 1 ^ 2 * (n 2 * P 1 + g * k 2) * h1
  · linear_combination 4 * (g : ℤ) ^ 2 * n 0 ^ 2 * hk' + 4 * n 0 ^ 2 * (n 2 * P 1 + g * k 2) * h1

/-- D2: the shell points are integer zeros of the joint surface in the shell box. -/
theorem surface_points {n k : Mode} {s2 s3 : ℤ} {Δ z g T : ℕ} (hH : ShellHyp n Δ z g T)
    (hk : k ∈ shellPts n Δ z s2 s3 g T) (i j : Fin 3) (hij : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) :
    surfPt Δ s2 g i n k ∈
      boxZeros (surfacePoly Δ z (n 2) (n i) (n j) s3 g) (shellBox g T (absk n)) := by
  classical
  simp only [boxZeros, Finset.mem_filter]
  refine ⟨?_, surface_eval hH hk i j hij⟩
  obtain ⟨h0, h1, h2⟩ := surfPt_spec hH hk i
  obtain ⟨c, hcΔ, hcz, -, hct, -, hT1, hT2⟩ := shell_coords hH hk
  have hn3 := c.hn3
  have hg0 := g_pos hH hn3
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg0
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hH.2.2.2.1
  have hΔ1 : (1 : ℤ) ≤ Δ := by exact_mod_cast Nat.pos_of_ne_zero hH.1.ne_zero
  have hnn : 0 ≤ nsqZ n := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hzN : (z : ℝ) ≤ absk n := by
    rw [absk_eq_sqrt_nsqZ]
    calc (z : ℝ) = Real.sqrt ((z : ℝ) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (nsqZ n : ℝ) := Real.sqrt_le_sqrt (by
          have : ((z : ℤ)) ^ 2 ≤ nsqZ n := by
            rw [hH.2.1]; nlinarith [sq_nonneg (z : ℤ)]
          exact_mod_cast this)
  simp only [boxPts, Fintype.mem_piFinset]
  intro l
  fin_cases l
  · -- `X₁ = t/g`
    apply mem_Icc_floor
    simp only [shellBox, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [← hct] at h0
    have hX0 : 0 ≤ surfPt Δ s2 g i n k 0 := by
      have : (0 : ℤ) ≤ g * surfPt Δ s2 g i n k 0 := by rw [h0]; linarith
      by_contra hneg
      rw [not_le] at hneg
      have : (g : ℤ) * surfPt Δ s2 g i n k 0 < 0 :=
        mul_neg_of_pos_of_neg (by exact_mod_cast hg0) hneg
      linarith
    have hlt : (g : ℤ) * surfPt Δ s2 g i n k 0 < 2 * T := by rw [h0]; exact hT2
    rw [abs_of_nonneg (by exact_mod_cast hX0), le_div_iff₀ hgR]
    have : ((surfPt Δ s2 g i n k 0 * g : ℤ) : ℝ) ≤ ((2 * T : ℤ) : ℝ) := by
      exact_mod_cast (by linarith : surfPt Δ s2 g i n k 0 * g ≤ 2 * T)
    push_cast at this; linarith
  · -- `X₂ = g w / n₃`
    apply mem_Icc_floor
    simp only [shellBox, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    have hws := c.w_shell (T := T) (by exact_mod_cast hH.2.2.2.1) hT1
    have hv : ((c.v : ℕ) : ℤ) = |n 2| := by simp only [Coords.v, Int.natCast_natAbs]
    rw [hv] at hws
    have hw : c.w = k 2 := rfl
    rw [hw, hcz] at hws
    have habs : |n 2| * |surfPt Δ s2 g i n k 1| = g * |k 2| := by
      rw [← abs_mul, h1, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ g)]
    have hpos : 0 < |n 2| := abs_pos.mpr hn3
    have hTz : (T : ℤ) ≤ 2 * z := by exact_mod_cast hH.2.2.2.2.1
    have key : (T : ℤ) * |surfPt Δ s2 g i n k 1| ≤ 4 * g * z := by
      have : |n 2| * (T * |surfPt Δ s2 g i n k 1|) ≤ |n 2| * (g * (T + 2 * z)) := by
        have hg' : (0 : ℤ) ≤ g := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hws hg']
      have := le_of_mul_le_mul_left this hpos
      have hg' : (0 : ℤ) ≤ g := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hTz hg']
    have keyR : (T : ℝ) * |(surfPt Δ s2 g i n k 1 : ℝ)| ≤ 4 * g * z := by
      rw [← Int.cast_abs]; exact_mod_cast key
    rw [le_div_iff₀ hT0]
    nlinarith [mul_le_mul_of_nonneg_left hzN (by positivity : (0 : ℝ) ≤ 4 * g)]
  · -- `X₃ = k_i`
    apply mem_Icc_floor
    simp only [shellBox, Fin.reduceFinMk, Matrix.cons_val, h2]
    refine le_trans ?_ (le_max_right _ _)
    rw [absk_eq_sqrt_nsqZ]
    apply Real.abs_le_sqrt
    have hki : k i ^ 2 ≤ nsqZ k := by
      simp only [nsqZ, Fin.sum_univ_three]
      fin_cases i <;> simp <;> nlinarith [sq_nonneg (k 0), sq_nonneg (k 1), sq_nonneg (k 2)]
    have hkn : nsqZ k ≤ nsqZ n := by
      rw [c.hk, c.hn]
      have hx0 : 0 ≤ c.x := by linarith [c.hy, c.hyx]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 c.hxz 2) c.hΔ.le
    exact_mod_cast hki.trans hkn

/-- Two shell points with the same `t` and `k₃` have the same `|k_h|²` and the same `L`. -/
private lemma shell_determined {n k k' : Mode} {s2 s3 : ℤ} {Δ z g T : ℕ}
    (hH : ShellHyp n Δ z g T) (hk : k ∈ shellPts n Δ z s2 s3 g T)
    (hk' : k' ∈ shellPts n Δ z s2 s3 g T) (ht : tOf Δ s2 n k = tOf Δ s2 n k')
    (hw : k 2 = k' 2) :
    k 0 ^ 2 + k 1 ^ 2 = k' 0 ^ 2 + k' 1 ^ 2 ∧
      n 0 * k 0 + n 1 * k 1 = n 0 * k' 0 + n 1 * k' 1 := by
  obtain ⟨c, hcΔ, hcz, hc3, hct, -, -, -⟩ := shell_coords hH hk
  obtain ⟨c', hcΔ', hcz', hc3', hct', -, -, -⟩ := shell_coords hH hk'
  have hn3 := c.hn3
  have hx := c.x_id
  have hx' := c'.x_id
  have hL := c.L_id
  have hL' := c'.L_id
  simp only [Coords.w, Coords.L, hcΔ, hcz, hc3, hct] at hx hL
  simp only [Coords.w, Coords.L, hcΔ', hcz', hc3', hct', ← ht, ← hw] at hx' hL'
  have hxx : c.x = c'.x := by
    have : n 2 * (c.x - c'.x) = 0 := by linear_combination hx - hx'
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hn3
    · linarith
  have hkk := c.hk
  have hkk' := c'.hk
  simp only [nsqZ, Fin.sum_univ_three, hcΔ, hcΔ', hxx, ← hw] at hkk hkk'
  refine ⟨by linear_combination hkk - hkk', ?_⟩
  have : 2 * n 2 * ((n 0 * k 0 + n 1 * k 1) - (n 0 * k' 0 + n 1 * k' 1)) = 0 := by
    linear_combination hL - hL'
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h (mul_ne_zero two_ne_zero hn3)
  · linarith

/-- From `X₁, X₂` recover `t, k₃`. -/
private lemma recover_tw {n k k' : Mode} {s2 s3 : ℤ} {Δ z g T : ℕ}
    (hH : ShellHyp n Δ z g T) (hk : k ∈ shellPts n Δ z s2 s3 g T)
    (hk' : k' ∈ shellPts n Δ z s2 s3 g T)
    (h0 : surfPt Δ s2 g 0 n k 0 = surfPt Δ s2 g 0 n k' 0)
    (h1 : surfPt Δ s2 g 0 n k 1 = surfPt Δ s2 g 0 n k' 1) :
    tOf Δ s2 n k = tOf Δ s2 n k' ∧ k 2 = k' 2 := by
  obtain ⟨a0, a1, -⟩ := surfPt_spec hH hk 0
  obtain ⟨b0, b1, -⟩ := surfPt_spec hH hk' 0
  obtain ⟨c, -⟩ := shell_coords hH hk
  have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast (g_pos hH c.hn3).ne'
  refine ⟨by rw [← a0, ← b0, h0], ?_⟩
  have : (g : ℤ) * k 2 = g * k' 2 := by rw [← a1, ← b1, h1]
  exact mul_left_cancel₀ hg0 this

/-- The two-to-one bound, for the pair `(i, j)` of horizontal indices. -/
private lemma two_to_one_aux (n : Mode) (Δ z : ℕ) (s2 s3 : ℤ) (g T : ℕ)
    (hH : ShellHyp n Δ z g T) (i j : Fin 3) (hij : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0))
    (X : Fin 3 → ℤ) :
    ((shellPts n Δ z s2 s3 g T).filter fun k => surfPt Δ s2 g i n k = X).card ≤ 2 := by
  classical
  set S := (shellPts n Δ z s2 s3 g T).filter fun k => surfPt Δ s2 g i n k = X with hS
  have key : ∀ k ∈ S, ∀ k' ∈ S, k i = k' i ∧ k 2 = k' 2 ∧ k j ^ 2 = k' j ^ 2 := by
    intro k hk k' hk'
    rw [hS, Finset.mem_filter] at hk hk'
    have e : ∀ l, surfPt Δ s2 g i n k l = surfPt Δ s2 g i n k' l := fun l => by
      rw [hk.2, hk'.2]
    obtain ⟨ht, hw⟩ := recover_tw hH hk.1 hk'.1 (e 0) (e 1)
    obtain ⟨hsq, -⟩ := shell_determined hH hk.1 hk'.1 ht hw
    have hi : k i = k' i := e 2
    refine ⟨hi, hw, ?_⟩
    rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hi] at hsq; linarith
    · rw [hi] at hsq; linarith
  have ext : ∀ k k' : Mode, k i = k' i → k j = k' j → k 2 = k' 2 → k = k' := by
    intro k k' hi hj hw
    funext l
    rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> fin_cases l <;> assumption
  rcases S.eq_empty_or_nonempty with hS0 | ⟨k₀, hk₀⟩
  · rw [hS0, Finset.card_empty]; omega
  refine (Finset.card_le_card_of_injOn (fun k => k j) (t := {k₀ j, -k₀ j}) ?_ ?_).trans
    Finset.card_le_two
  · intro k hk
    have := (key k hk k₀ hk₀).2.2
    rw [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    exact sq_eq_sq_iff_eq_or_eq_neg.1 this
  · intro k hk k' hk' hkk
    obtain ⟨hi, hw, -⟩ := key k hk k' hk'
    exact ext k k' hi hkk hw

/-- The point map `k ↦ X` is at most two-to-one on a shell. -/
theorem surface_points_two_to_one (n : Mode) (Δ z : ℕ) (s2 s3 : ℤ) (g T : ℕ)
    (hH : ShellHyp n Δ z g T) (i : Fin 3) (hi : i = 0 ∨ i = 1) (X : Fin 3 → ℤ) :
    ((shellPts n Δ z s2 s3 g T).filter fun k => surfPt Δ s2 g i n k = X).card ≤ 2 := by
  rcases hi with rfl | rfl
  · exact two_to_one_aux n Δ z s2 s3 g T hH 0 1 (Or.inl ⟨rfl, rfl⟩) X
  · exact two_to_one_aux n Δ z s2 s3 g T hH 1 0 (Or.inr ⟨rfl, rfl⟩) X

/-- The projection `k ↦ (X₁, X₂)` is at most two-to-one on a shell (the norm equation). -/
theorem proj_two_to_one (n : Mode) (Δ z : ℕ) (s2 s3 : ℤ) (g T : ℕ)
    (hH : ShellHyp n Δ z g T) (X : Fin 2 → ℤ) :
    ((shellPts n Δ z s2 s3 g T).filter fun k => projPt Δ s2 g n k = X).card ≤ 2 := by
  classical
  set S := (shellPts n Δ z s2 s3 g T).filter fun k => projPt Δ s2 g n k = X with hS
  let J : Mode → ℤ := fun k => k 0 * n 1 - k 1 * n 0
  have key : ∀ k ∈ S, ∀ k' ∈ S, k 2 = k' 2 ∧
      n 0 * k 0 + n 1 * k 1 = n 0 * k' 0 + n 1 * k' 1 ∧ J k ^ 2 = J k' ^ 2 := by
    intro k hk k' hk'
    rw [hS, Finset.mem_filter] at hk hk'
    have e : ∀ l, projPt Δ s2 g n k l = projPt Δ s2 g n k' l := fun l => by
      rw [hk.2, hk'.2]
    obtain ⟨ht, hw⟩ := recover_tw hH hk.1 hk'.1 (e 0) (e 1)
    obtain ⟨hsq, hL⟩ := shell_determined hH hk.1 hk'.1 ht hw
    refine ⟨hw, hL, ?_⟩
    have i1 : J k ^ 2 = (n 0 ^ 2 + n 1 ^ 2) * (k 0 ^ 2 + k 1 ^ 2) -
        (n 0 * k 0 + n 1 * k 1) ^ 2 := by simp only [J]; ring
    have i2 : J k' ^ 2 = (n 0 ^ 2 + n 1 ^ 2) * (k' 0 ^ 2 + k' 1 ^ 2) -
        (n 0 * k' 0 + n 1 * k' 1) ^ 2 := by simp only [J]; ring
    rw [i1, i2, hsq, hL]
  rcases S.eq_empty_or_nonempty with hS0 | ⟨k₀, hk₀⟩
  · rw [hS0, Finset.card_empty]; omega
  have hnh : n 0 ^ 2 + n 1 ^ 2 ≠ 0 := by
    have h := hk₀
    rw [hS, Finset.mem_filter] at h
    exact active_nh (mem_shellPts.1 h.1).1
  refine (Finset.card_le_card_of_injOn J (t := {J k₀, -J k₀}) ?_ ?_).trans Finset.card_le_two
  · intro k hk
    have := (key k hk k₀ hk₀).2.2
    rw [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    exact sq_eq_sq_iff_eq_or_eq_neg.1 this
  · intro k hk k' hk' hJ
    obtain ⟨hw, hL, -⟩ := key k hk k' hk'
    have hJ' : k 0 * n 1 - k 1 * n 0 = k' 0 * n 1 - k' 1 * n 0 := hJ
    have e0 : (n 0 ^ 2 + n 1 ^ 2) * k 0 = (n 0 ^ 2 + n 1 ^ 2) * k' 0 := by
      linear_combination n 0 * hL + n 1 * hJ'
    have e1 : (n 0 ^ 2 + n 1 ^ 2) * k 1 = (n 0 ^ 2 + n 1 ^ 2) * k' 1 := by
      linear_combination n 1 * hL - n 0 * hJ'
    funext l
    fin_cases l
    · exact mul_left_cancel₀ hnh e0
    · exact mul_left_cancel₀ hnh e1
    · exact hw

end OVNS.Quant

end
