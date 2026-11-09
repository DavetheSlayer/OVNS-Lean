import OddViscousNS.Quant.Arith.Weighted.Coords

/-!
# The fixed-`t` conic (Section B)

`(2n₃J)² = ca w² + cb w + cc` with discriminant `cM = 16 n₃² |n_h|² (Δt² − N²)² (Δt² + 3n₃²)`
(independent of `s₃`), the norm form `(2 ca w + cb)² − ca (4n₃J)² = cM`, `cM ≠ 0` off the
collinear value `t = z`, polynomial sizes in `|n|²`, at most two parabolic `t` (`ca = 0`), and the
counts: non-parabolic fixed `t` by `QuadraticNormCount` (`C = 16`, base `|n|²`), parabolic `t` by
`PlaneCurveCount` (`d = 2`, exponent `1/2 + η`).
-/

namespace OVNS.Quant
namespace Coords
variable {n k : Mode} (c : Coords n k)

private theorem hn'' : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = c.Δ * c.z ^ 2 := by
  have h := c.hn
  simp only [nsqZ, Fin.sum_univ_three] at h
  linear_combination h

theorem conic_id : (2 * n 2 * c.J) ^ 2 = c.ca * c.w ^ 2 + c.cb * c.w + c.cc := by
  have hJ := c.J_id
  have hL := c.L_id
  have hx := c.x_id
  have hn := c.hn''
  simp only [ca, cb, cc, Bt, nh2] at hJ ⊢
  linear_combination (4 * n 2 ^ 2) * hJ
    + 4 * (n 0 ^ 2 + n 1 ^ 2) * c.Δ * (n 2 * c.x + (n 2 * (c.t + c.s3 * c.z) + c.t * c.w)) * hx
    - (2 * n 2 * c.L + (-c.Δ * n 2 * (c.t + c.s3 * c.z) ^ 2
        - 2 * (n 2 ^ 2 + c.Δ * c.t ^ 2) * c.w)) * hL
    + 4 * (c.Δ * c.t ^ 2 - n 2 ^ 2) * c.w ^ 2 * hn

theorem disc_id : c.cb ^ 2 - 4 * c.ca * c.cc = c.cM := by
  have e : c.nh2 = c.Δ * c.z ^ 2 - n 2 ^ 2 := by
    simp only [nh2]; linear_combination c.hn''
  simp only [ca, cb, cc, cM, Bt]
  rw [e]
  rcases c.hs3 with h | h <;> rw [h] <;> ring

theorem norm_form : (2 * c.ca * c.w + c.cb) ^ 2 - c.ca * (4 * n 2 * c.J) ^ 2 = c.cM := by
  linear_combination (-4 * c.ca) * c.conic_id + c.disc_id

private theorem one_le_y : 1 ≤ c.y := c.hy

private theorem one_le_z : 1 ≤ c.z := by
  have := c.hy; have := c.hyx; have := c.hxz; omega

theorem cM_ne_zero (hnh : c.nh2 ≠ 0) (htz : c.t ≠ c.z) : c.cM ≠ 0 := by
  have hz := c.one_le_z
  have ht := c.t_nonneg
  have hΔ := c.hΔ
  have h1 : c.Bt - c.Δ * c.z ^ 2 ≠ 0 := by
    have e : c.Bt - c.Δ * c.z ^ 2 = c.Δ * ((c.t - c.z) * (c.t + c.z)) := by
      simp only [Bt]; ring
    rw [e]
    refine mul_ne_zero hΔ.ne' (mul_ne_zero (sub_ne_zero.mpr htz) ?_)
    omega
  have h2 : c.Bt + 3 * n 2 ^ 2 ≠ 0 := by
    have : 0 < n 2 ^ 2 := by positivity [c.hn3]
    have : 0 ≤ c.Bt := by simp only [Bt]; positivity
    omega
  simp only [cM]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (pow_ne_zero 2 c.hn3)) hnh) (pow_ne_zero 2 h1)) h2

theorem sizes (hnh : c.nh2 ≠ 0) :
    |c.ca| ≤ nsqZ n ^ 16 ∧ |c.cM| ≤ nsqZ n ^ 16 ∧
    |2 * c.ca * c.w + c.cb| ≤ nsqZ n ^ 16 ∧ |4 * n 2 * c.J| ≤ nsqZ n ^ 16 := by
  set N := nsqZ n with hNdef
  have hN : N = c.Δ * c.z ^ 2 := c.hn
  have hsum : c.nh2 + n 2 ^ 2 = N := by
    simp only [nh2]; rw [hN]; linear_combination c.hn''
  have hnh0 : 0 ≤ c.nh2 := by simp only [nh2]; positivity
  have hnh1 : 1 ≤ c.nh2 := by omega
  have hm1 : 1 ≤ n 2 ^ 2 := by
    have : 0 < n 2 ^ 2 := by positivity [c.hn3]
    omega
  have hN2 : 2 ≤ N := by omega
  have hz := c.one_le_z
  have ht := c.t_nonneg
  have ht2 := c.t_lt
  have hΔ := c.hΔ
  have hB0 : 0 ≤ c.Bt := by simp only [Bt]; positivity
  have hB4 : c.Bt ≤ 4 * N := by
    simp only [Bt]; rw [hN]
    have : c.t ^ 2 ≤ 4 * c.z ^ 2 := by nlinarith
    nlinarith
  have hn3N : |n 2| ≤ N := by
    have : |n 2| ≤ n 2 ^ 2 := by
      rw [← sq_abs]; nlinarith [abs_pos.mpr c.hn3]
    omega
  have hJ : |c.J| ≤ N := by
    have hx1 : 1 ≤ c.x := le_trans c.hy c.hyx
    have hxz := c.hxz
    have hx : c.Δ * c.x ^ 2 ≤ N := by
      rw [hN]; exact mul_le_mul_of_nonneg_left (by nlinarith) hΔ.le
    have h := c.J_id
    have : c.J ^ 2 ≤ N ^ 2 := by
      have : c.nh2 * (c.Δ * c.x ^ 2) ≤ N * N :=
        mul_le_mul (by omega) hx (by positivity) (by omega)
      nlinarith [sq_nonneg c.L, sq_nonneg c.w]
    have := sq_le_sq.mp this
    rwa [abs_of_nonneg (by omega : (0 : ℤ) ≤ N)] at this
  -- the coefficient `ca`
  have hca : |c.ca| ≤ 132 * N ^ 2 := by
    have e : c.ca = 4 * (-(c.Bt * c.Bt) + N * c.Bt - 3 * (n 2 ^ 2 * c.Bt) - N * n 2 ^ 2) := by
      simp only [ca]; rw [hN]; ring
    have h1 : c.Bt * c.Bt ≤ 4 * N * (4 * N) := mul_le_mul hB4 hB4 hB0 (by omega)
    have h2 : N * c.Bt ≤ N * (4 * N) := mul_le_mul_of_nonneg_left hB4 (by omega)
    have h3 : n 2 ^ 2 * c.Bt ≤ N * (4 * N) := mul_le_mul (by omega) hB4 hB0 (by omega)
    have h4 : N * n 2 ^ 2 ≤ N * N := mul_le_mul_of_nonneg_left (by omega) (by omega)
    have h5 : 0 ≤ c.Bt * c.Bt := mul_nonneg hB0 hB0
    have h6 : 0 ≤ N * c.Bt := mul_nonneg (by omega) hB0
    have h7 : 0 ≤ n 2 ^ 2 * c.Bt := mul_nonneg (by omega) hB0
    have h8 : 0 ≤ N * n 2 ^ 2 := mul_nonneg (by omega) (by omega)
    rw [e, abs_le]; constructor <;> nlinarith
  have hcM : 0 ≤ c.cM ∧ c.cM ≤ 1008 * N ^ 5 := by
    have a1 : n 2 ^ 2 * c.nh2 ≤ N * N := mul_le_mul (by omega) (by omega) hnh0 (by omega)
    have a2 : (c.Bt - c.Δ * c.z ^ 2) ^ 2 ≤ 9 * N ^ 2 := by
      rw [← hN]; nlinarith
    have a3 : (c.Bt - c.Δ * c.z ^ 2) ^ 2 * (c.Bt + 3 * n 2 ^ 2) ≤ 9 * N ^ 2 * (7 * N) :=
      mul_le_mul a2 (by omega) (by positivity) (by positivity)
    have a4 : n 2 ^ 2 * c.nh2 * ((c.Bt - c.Δ * c.z ^ 2) ^ 2 * (c.Bt + 3 * n 2 ^ 2)) ≤
        N * N * (9 * N ^ 2 * (7 * N)) :=
      mul_le_mul a1 a3 (mul_nonneg (sq_nonneg _) (by omega)) (by positivity)
    have e : c.cM = 16 * (n 2 ^ 2 * c.nh2 * ((c.Bt - c.Δ * c.z ^ 2) ^ 2 *
        (c.Bt + 3 * n 2 ^ 2))) := by simp only [cM]; ring
    constructor
    · rw [e]; positivity
    · rw [e]; nlinarith
  have hY : |4 * n 2 * c.J| ≤ 4 * N ^ 2 := by
    rw [abs_mul, abs_mul]
    have : |n 2| * |c.J| ≤ N * N := mul_le_mul hn3N hJ (abs_nonneg _) (by omega)
    norm_num; nlinarith
  have hpow : ∀ a : ℕ, a ≤ 16 → (2 : ℤ) ^ (16 - a) * N ^ a ≤ N ^ 16 := by
    intro a ha
    have : (2 : ℤ) ^ (16 - a) ≤ N ^ (16 - a) := pow_le_pow_left₀ (by norm_num) hN2 _
    calc (2 : ℤ) ^ (16 - a) * N ^ a ≤ N ^ (16 - a) * N ^ a :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = N ^ 16 := by rw [← pow_add]; congr 1; omega
  have p2 := hpow 2 (by norm_num)
  have p5 := hpow 5 (by norm_num)
  have p6 := hpow 6 (by norm_num)
  norm_num at p2 p5 p6
  refine ⟨by linarith, by rw [abs_of_nonneg hcM.1]; linarith, ?_, by linarith⟩
  -- `X² = cM + ca Y²`
  have hX : (2 * c.ca * c.w + c.cb) ^ 2 = c.cM + c.ca * (4 * n 2 * c.J) ^ 2 := by
    linear_combination c.norm_form
  have hY2 : (4 * n 2 * c.J) ^ 2 ≤ 16 * N ^ 4 := by
    have := sq_le_sq' (abs_le.mp hY).1 (abs_le.mp hY).2; nlinarith
  have hcaY : c.ca * (4 * n 2 * c.J) ^ 2 ≤ 132 * N ^ 2 * (16 * N ^ 4) := by
    calc c.ca * (4 * n 2 * c.J) ^ 2 ≤ |c.ca| * (4 * n 2 * c.J) ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
      _ ≤ 132 * N ^ 2 * (16 * N ^ 4) := mul_le_mul hca hY2 (sq_nonneg _) (by positivity)
  have hX2 : (2 * c.ca * c.w + c.cb) ^ 2 ≤ (N ^ 16) ^ 2 := by
    have : N ^ 6 ≤ N ^ 16 := by linarith
    have h16 : (N ^ 16) ^ 2 ≥ N ^ 16 * N ^ 6 := by
      rw [sq]; exact mul_le_mul_of_nonneg_left this (by positivity)
    have : (N : ℤ) ^ 5 ≤ N ^ 6 := pow_le_pow_right₀ (by omega) (by norm_num)
    nlinarith
  have := sq_le_sq.mp hX2
  rwa [abs_of_nonneg (by positivity : (0 : ℤ) ≤ N ^ 16)] at this

end Coords

/-- B2: at most two parabolic `t` per output (depends only on `Δ, z, n₃`). -/
theorem parabolic_card (Δ z n3 : ℤ) (hΔ : 0 < Δ) :
    ((Finset.Icc (1 : ℤ) (2 * z)).filter fun t =>
      -(Δ * t ^ 2) ^ 2 + (Δ * z ^ 2 - 3 * n3 ^ 2) * (Δ * t ^ 2) - Δ * z ^ 2 * n3 ^ 2 = 0).card
      ≤ 2 := by
  classical
  set q : Polynomial ℤ := Polynomial.C (-1) * Polynomial.X ^ 2 +
    Polynomial.C (Δ * z ^ 2 - 3 * n3 ^ 2) * Polynomial.X + Polynomial.C (-(Δ * z ^ 2 * n3 ^ 2))
    with hq
  have hdeg : q.natDegree = 2 := Polynomial.natDegree_quadratic (by norm_num)
  have hq0 : q ≠ 0 := by
    intro h; rw [h] at hdeg; simp at hdeg
  calc _ ≤ q.roots.toFinset.card := by
        refine Finset.card_le_card_of_injOn (fun t => Δ * t ^ 2) (fun t ht => ?_) ?_
        · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at ht
          rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hq0,
            Polynomial.IsRoot.def, hq]
          simp only [Polynomial.eval_add, Polynomial.eval_mul,
            Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
          linear_combination ht.2
        · intro a ha b hb hab
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at ha hb
          have h : Δ * (a - b) * (a + b) = 0 := by
            have := hab; simp only at this; linear_combination this
          rcases mul_eq_zero.mp h with h | h
          · rcases mul_eq_zero.mp h with h | h
            · omega
            · omega
          · omega
    _ ≤ q.roots.card := Multiset.toFinset_card_le _
    _ ≤ 2 := hdeg ▸ Polynomial.card_roots' q

private theorem mem_sortedFibre' {n m k : Mode} (hp : (m, k) ∈ sortedFibre n) :
    m + k + n = 0 ∧ nsqZ m ≤ nsqZ k ∧ nsqZ k ≤ nsqZ n ∧ m 2 ≠ 0 ∧ k 2 ≠ 0 ∧ n 2 ≠ 0 := by
  classical
  simp only [sortedFibre, Finset.mem_filter] at hp
  convert hp.2

private lemma sqf_eq_of_mul_sq' {a b m n : ℕ} (ha : Squarefree a) (hb : Squarefree b)
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

private lemma xOf_eq {Δ x : ℕ} {k : Mode} (hΔ : 0 < Δ) (h : nsqZ k = (Δ : ℤ) * (x : ℤ) ^ 2) :
    xOf Δ k = x := by
  simp only [xOf]
  rw [h, show (Δ : ℤ) * (x : ℤ) ^ 2 = ((Δ * x ^ 2 : ℕ) : ℤ) by push_cast; ring, Int.toNat_natCast,
    Nat.mul_div_cancel_left _ hΔ, Nat.sqrt_eq']

private lemma nsqZ_pos {l : Mode} (hl : l 2 ≠ 0) : 0 < nsqZ l := by
  simp only [nsqZ, Fin.sum_univ_three]
  nlinarith [sq_nonneg (l 0), sq_nonneg (l 1), pow_pos (abs_pos.mpr hl) 2, sq_abs (l 2)]

/-- The coordinates of an active point of a fixed-`t` fibre, normalised to the given data. -/
private theorem fibre_coords {n k : Mode} {Δ : ℕ} {z t s2 s3 : ℤ} (hsq : Squarefree Δ)
    (hn : nsqZ n = Δ * z ^ 2) (hk : k ∈ activePts n s2 s3) (ht : tOf Δ s2 n k = t) :
    ∃ c : Coords n k, c.Δ = Δ ∧ c.z = |z| ∧ c.t = t ∧ c.s3 = s3 ∧ c.nh2 ≠ 0 ∧ c.t ≠ c.z := by
  classical
  simp only [activePts, Finset.mem_filter] at hk
  obtain ⟨_, hp, a, b, c', h2, h3, hres, hγ⟩ := hk
  obtain ⟨_, _, _, hm3, hk3, hn3⟩ := mem_sortedFibre' hp
  obtain ⟨Δ', x, y, z', hΔ', hkx, hmy, hnz, hy, hyx, hxz, hr⟩ := exists_coords hp hres
  have hz'0 : z' ≠ 0 := by omega
  have hpos := nsqZ_pos hn3
  have hz0 : z.natAbs ≠ 0 := by
    intro h0; rw [Int.natAbs_eq_zero] at h0; rw [hn, h0] at hpos; simp at hpos
  have hE : Δ' * z' ^ 2 = Δ * z.natAbs ^ 2 := by
    have : ((Δ' * z' ^ 2 : ℕ) : ℤ) = ((Δ * z.natAbs ^ 2 : ℕ) : ℤ) := by
      push_cast; rw [sq_abs, ← hn, hnz]
    exact_mod_cast this
  have hΔe : Δ' = Δ := sqf_eq_of_mul_sq' hΔ' hsq hz'0 hz0 hE
  subst Δ'
  have hΔ0 : 0 < Δ := Nat.pos_of_ne_zero hsq.ne_zero
  have hzz : z' = z.natAbs := by
    have := Nat.eq_of_mul_eq_mul_left hΔ0 hE
    exact (Nat.pow_left_injective (by norm_num : 2 ≠ 0)) this
  have hsg : ∀ s : Sgn, sgZ s = 1 ∨ sgZ s = -1 := by intro s; cases s <;> simp [sgZ]
  have hpm : ∀ u v : Sgn, sgZ u * sgZ v = 1 ∨ sgZ u * sgZ v = -1 := by
    intro u v; rcases hsg u with h | h <;> rcases hsg v with h' | h' <;> simp [h, h']
  let C : Coords n k :=
    { Δ := Δ, x := x, y := y, z := z', s2 := s2, s3 := s3
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
  have hCt : C.t = t := by
    rw [← ht]
    simp only [Coords.t, tOf, C]
    rw [xOf_eq hΔ0 hkx, xOf_eq hΔ0 hmy]
  refine ⟨C, rfl, by simp [C, hzz], hCt, rfl, ?_, ?_⟩
  · intro h0
    have h0' : n 0 ^ 2 + n 1 ^ 2 = 0 := h0
    have e0 : n 0 = 0 := by nlinarith [sq_nonneg (n 0), sq_nonneg (n 1)]
    have e1 : n 1 = 0 := by nlinarith [sq_nonneg (n 0), sq_nonneg (n 1)]
    exact hγ (vertical_output_null e0 e1 hp hres)
  · intro htz
    have h := C.t_eq_z htz
    apply hγ
    have : crossAbs (-k - n) k = 0 := by
      simp only [crossAbs, h, sub_self, Int.cast_zero, Real.sqrt_zero]
    simp only [gammaCoef, this, zero_mul, zero_div]

private theorem coef_eq {n k k' : Mode} (c : Coords n k) (c' : Coords n k') (hΔ : c.Δ = c'.Δ)
    (hz : c.z = c'.z) (ht : c.t = c'.t) (hs : c.s3 = c'.s3) :
    c.ca = c'.ca ∧ c.cb = c'.cb ∧ c.cc = c'.cc ∧ c.cM = c'.cM := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Coords.ca, Coords.cb, Coords.cc, Coords.cM, Coords.Bt, Coords.nh2, hΔ, hz, ht, hs]

/-- On a fixed-`t` fibre, `(w, J)` determines `k` (when `n_h ≠ 0`). -/
private theorem fibre_inj {n k k' : Mode} (c : Coords n k) (c' : Coords n k') (hΔ : c.Δ = c'.Δ)
    (hz : c.z = c'.z) (ht : c.t = c'.t) (hs : c.s3 = c'.s3) (hnh : c.nh2 ≠ 0)
    (hw : k 2 = k' 2) (hJ : c.J = c'.J) : k = k' := by
  have hL : c.L = c'.L := by
    have h1 := c.L_id
    have h2 := c'.L_id
    rw [hΔ, hz, ht, hs] at h1
    have hw' : c.w = c'.w := hw
    rw [hw'] at h1
    have : 2 * n 2 * (c.L - c'.L) = 0 := by linear_combination h1 - h2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (mul_ne_zero two_ne_zero c.hn3)
    · linarith
  simp only [Coords.L, Coords.J] at hL hJ
  have hnh' : n 0 ^ 2 + n 1 ^ 2 ≠ 0 := hnh
  have e0 : (n 0 ^ 2 + n 1 ^ 2) * k 0 = (n 0 ^ 2 + n 1 ^ 2) * k' 0 := by
    linear_combination n 0 * hL + n 1 * hJ
  have e1 : (n 0 ^ 2 + n 1 ^ 2) * k 1 = (n 0 ^ 2 + n 1 ^ 2) * k' 1 := by
    linear_combination n 1 * hL - n 0 * hJ
  have e0' := mul_left_cancel₀ hnh' e0
  have e1' := mul_left_cancel₀ hnh' e1
  funext i
  fin_cases i
  · exact e0'
  · exact e1'
  · exact hw

private theorem two_le_nsqZ {n k : Mode} (c : Coords n k) (hnh : c.nh2 ≠ 0) : 2 ≤ nsqZ n := by
  have h1 : nsqZ n = c.nh2 + n 2 ^ 2 := by simp only [Coords.nh2, nsqZ, Fin.sum_univ_three]
  have : 0 ≤ c.nh2 := by simp only [Coords.nh2]; positivity
  have : 0 < n 2 ^ 2 := by positivity [c.hn3]
  omega

/-- B5: non-parabolic fixed-`t` count (`QuadraticNormCount` with `C = 16`, base `|n|²`). -/
theorem fixed_t_count (hQ : QuadraticNormCount) : ∀ η : ℝ, 0 < η → ∃ K : ℝ, 0 ≤ K ∧
    ∀ (n : Mode) (Δ : ℕ) (z t s2 s3 : ℤ), Squarefree Δ → nsqZ n = Δ * z ^ 2 →
      caOf Δ z (n 2) t ≠ 0 →
      (((activePts n s2 s3).filter fun k => tOf Δ s2 n k = t).card : ℝ) ≤
        K * (nsqZ n : ℝ) ^ η := by
  intro η hη
  obtain ⟨K, hK⟩ := hQ 16 η hη
  refine ⟨max K 0, le_max_right _ _, ?_⟩
  intro n Δ z t s2 s3 hsq hn hca
  classical
  set S := (activePts n s2 s3).filter fun k => tOf Δ s2 n k = t with hS
  have hfib : ∀ k ∈ S, ∃ c : Coords n k, c.Δ = Δ ∧ c.z = |z| ∧ c.t = t ∧ c.s3 = s3 ∧
      c.nh2 ≠ 0 ∧ c.t ≠ c.z := fun k hk => by
    rw [hS, Finset.mem_filter] at hk; exact fibre_coords hsq hn hk.1 hk.2
  rcases S.eq_empty_or_nonempty with hS0 | ⟨k₀, hk₀⟩
  · rw [hS0, Finset.card_empty, Nat.cast_zero]
    have : (0 : ℝ) ≤ nsqZ n := by
      have : 0 ≤ nsqZ n := Finset.sum_nonneg fun i _ => sq_nonneg _
      exact_mod_cast this
    exact mul_nonneg (le_max_right _ _) (Real.rpow_nonneg this _)
  obtain ⟨c₀, h₀Δ, h₀z, h₀t, h₀s, h₀nh, h₀tz⟩ := hfib k₀ hk₀
  have hca0 : c₀.ca ≠ 0 := by
    have : c₀.ca = caOf Δ z (n 2) t := by
      simp only [Coords.ca, Coords.Bt, caOf, h₀Δ, h₀z, h₀t, sq_abs]
    rwa [this]
  have hM0 := c₀.cM_ne_zero h₀nh h₀tz
  have hN2 := two_le_nsqZ c₀ h₀nh
  have hB2 : (2 : ℝ) ≤ (nsqZ n : ℝ) := by exact_mod_cast hN2
  have hfl : ⌊(nsqZ n : ℝ) ^ 16⌋ = nsqZ n ^ 16 := by rw [← Int.cast_pow, Int.floor_intCast]
  have hsz₀ := c₀.sizes h₀nh
  have hcard := hK (nsqZ n : ℝ) hB2 c₀.ca c₀.cM hca0 hM0
    (by rw [← Int.cast_abs, ← Int.cast_pow]; exact_mod_cast hsz₀.1)
    (by rw [← Int.cast_abs, ← Int.cast_pow]; exact_mod_cast hsz₀.2.1)
  let f : Mode → (Fin 2 → ℤ) := fun k =>
    ![2 * c₀.ca * k 2 + c₀.cb, 4 * n 2 * (k 0 * n 1 - k 1 * n 0)]
  have hle : S.card ≤ ((boxPts 2 fun _ => (nsqZ n : ℝ) ^ 16).filter
      fun p => p 0 ^ 2 - c₀.ca * p 1 ^ 2 = c₀.cM).card := by
    refine Finset.card_le_card_of_injOn f (fun k hk => ?_) ?_
    · obtain ⟨c, hΔ, hz, ht, hs, hnh, _⟩ := hfib k hk
      obtain ⟨ea, eb, -, eM⟩ := coef_eq c c₀ (hΔ.trans h₀Δ.symm) (hz.trans h₀z.symm)
        (ht.trans h₀t.symm) (hs.trans h₀s.symm)
      have hfk : f k = ![2 * c.ca * c.w + c.cb, 4 * n 2 * c.J] := by
        simp only [f, ea, eb]; rfl
      have hsz := c.sizes hnh
      rw [Finset.mem_coe, Finset.mem_filter, hfk]
      refine ⟨?_, ?_⟩
      · simp only [boxPts, Fintype.mem_piFinset, Fin.forall_fin_two, hfl, Finset.mem_Icc,
          Matrix.cons_val_zero, Matrix.cons_val_one]
        exact ⟨abs_le.mp hsz.2.2.1, abs_le.mp hsz.2.2.2⟩
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [← ea, ← eM]; exact c.norm_form
    · intro k hk k' hk' hkk
      obtain ⟨c, hΔ, hz, ht, hs, hnh, _⟩ := hfib k hk
      obtain ⟨c', hΔ', hz', ht', hs', _, _⟩ := hfib k' hk'
      have h0 := congrFun hkk 0
      have h1 := congrFun hkk 1
      simp only [f, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
      have hw : k 2 = k' 2 := by
        have : 2 * c₀.ca * (k 2 - k' 2) = 0 := by linear_combination h0
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h (mul_ne_zero two_ne_zero hca0)
        · linarith
      have hJ : c.J = c'.J := by
        have : 4 * n 2 * (c.J - c'.J) = 0 := by
          simp only [Coords.J]; linear_combination h1
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h (mul_ne_zero (by norm_num) c.hn3)
        · linarith
      exact fibre_inj c c' (hΔ.trans hΔ'.symm) (hz.trans hz'.symm) (ht.trans ht'.symm)
        (hs.trans hs'.symm) hnh hw hJ
  calc (S.card : ℝ) ≤ _ := by exact_mod_cast hle
    _ ≤ K * (nsqZ n : ℝ) ^ η := hcard
    _ ≤ max K 0 * (nsqZ n : ℝ) ^ η :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)

open Polynomial in
/-- A square of degree `≤ 2` has vanishing discriminant. -/
private theorem sq_quad {K : Type*} [_root_.Field K] (a b c : K) (s : K[X])
    (h : s ^ 2 = C a * X ^ 2 + C b * X + C c) : b ^ 2 - 4 * a * c = 0 := by
  have hd : s.natDegree ≤ 1 := by
    have h1 : (s ^ 2).natDegree ≤ 2 := h ▸ natDegree_quadratic_le
    rw [natDegree_pow] at h1
    omega
  rw [eq_X_add_C_of_natDegree_le_one hd] at h
  set s1 := s.coeff 1
  set s0 := s.coeff 0
  have e : (C s1 * X + C s0) ^ 2 = C (s1 ^ 2) * X ^ 2 + C (2 * s0 * s1) * X + C (s0 ^ 2) := by
    simp only [map_pow, map_mul, map_ofNat]; ring
  rw [e] at h
  have h2 := congrArg (fun p => p.coeff 2) h
  have h1 := congrArg (fun p => p.coeff 1) h
  have h0 := congrArg (fun p => p.coeff 0) h
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C] at h0 h1 h2
  norm_num at h0 h1 h2
  rw [← h0, ← h1, ← h2]; ring

open MvPolynomial in
/-- `Y² − (a w² + b w + c)` is irreducible over a field when `b² − 4ac ≠ 0`. -/
private theorem irred_conic {K : Type*} [_root_.Field K] (a b c : K) (h : b ^ 2 - 4 * a * c ≠ 0) :
    Irreducible (X 1 ^ 2 - C a * X 0 ^ 2 - C b * X 0 - C c : MvPolynomial (Fin 2) K) := by
  let e : MvPolynomial (Fin 2) K ≃ₐ[K] Polynomial (MvPolynomial (Fin 1) K) :=
    (renameEquiv K (Equiv.swap 0 1)).trans (finSuccEquiv K 1)
  set q : MvPolynomial (Fin 1) K := C a * X 0 ^ 2 + C b * X 0 + C c with hq
  have he : e (X 1 ^ 2 - C a * X 0 ^ 2 - C b * X 0 - C c) =
      Polynomial.X ^ 2 - Polynomial.C q := by
    have h1 : (1 : Fin 2) = Fin.succ 0 := rfl
    have hC : ∀ x : K, finSuccEquiv K 1 (C x) = Polynomial.C (C x) := fun x => by
      simp [finSuccEquiv_apply]
    simp only [e, q, AlgEquiv.trans_apply, map_sub, map_mul, map_pow, renameEquiv_apply,
      rename_X, rename_C, Equiv.swap_apply_left, Equiv.swap_apply_right, hC, map_add]
    rw [h1, finSuccEquiv_X_zero, finSuccEquiv_X_succ]
    ring
  rw [← MulEquiv.irreducible_iff e.toMulEquiv]
  show Irreducible (e _)
  rw [he]
  have hmon : (Polynomial.X ^ 2 - Polynomial.C q).Monic :=
    Polynomial.monic_X_pow_sub_C q (by norm_num)
  have hdeg : (Polynomial.X ^ 2 - Polynomial.C q).natDegree = 2 :=
    Polynomial.natDegree_X_pow_sub_C q
  rw [hmon.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
  refine Multiset.eq_zero_of_forall_notMem fun r hr => ?_
  rw [Polynomial.mem_roots hmon.ne_zero, Polynomial.IsRoot.def] at hr
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hr
  let φ : MvPolynomial (Fin 1) K →ₐ[K] Polynomial K := aeval fun _ => Polynomial.X
  have := congrArg φ hr
  simp only [φ, q, map_sub, map_pow, map_add, map_mul, map_zero, aeval_C, aeval_X,
    Polynomial.algebraMap_eq] at this
  exact h (sq_quad a b c (φ r) (by linear_combination this))

private lemma abs_le_floor {u : ℤ} {r : ℝ} (h : |(u : ℝ)| ≤ r) : -⌊r⌋ ≤ u ∧ u ≤ ⌊r⌋ := by
  have h1 := (abs_le.mp h).1
  have h2 := (abs_le.mp h).2
  have a1 : -u ≤ ⌊r⌋ := Int.le_floor.mpr (by push_cast; linarith)
  have a2 : u ≤ ⌊r⌋ := Int.le_floor.mpr h2
  omega

private theorem wY_bounds {n k : Mode} (c : Coords n k) :
    k 2 ^ 2 ≤ nsqZ n ∧ (2 * n 2 * c.J) ^ 2 ≤ 4 * nsqZ n ^ 3 := by
  have hk := c.hk
  have hN := c.hn
  have hk2 : k 2 ^ 2 ≤ nsqZ k := by
    simp only [nsqZ, Fin.sum_univ_three]; nlinarith [sq_nonneg (k 0), sq_nonneg (k 1)]
  have hn2 : n 2 ^ 2 ≤ nsqZ n := by
    simp only [nsqZ, Fin.sum_univ_three]; nlinarith [sq_nonneg (n 0), sq_nonneg (n 1)]
  have hx1 : 1 ≤ c.x := le_trans c.hy c.hyx
  have hxz := c.hxz
  have hΔ := c.hΔ
  have hx : c.Δ * c.x ^ 2 ≤ nsqZ n := by
    rw [hN]; exact mul_le_mul_of_nonneg_left (by nlinarith) hΔ.le
  have hnh : c.nh2 ≤ nsqZ n := by
    simp only [Coords.nh2, nsqZ, Fin.sum_univ_three]; nlinarith [sq_nonneg (n 2)]
  have hnh0 : 0 ≤ c.nh2 := by simp only [Coords.nh2]; positivity
  have hJ : c.J ^ 2 ≤ nsqZ n ^ 2 := by
    have h := c.J_id
    have : c.nh2 * (c.Δ * c.x ^ 2) ≤ nsqZ n * nsqZ n :=
      mul_le_mul hnh hx (by positivity) (by linarith)
    nlinarith [sq_nonneg c.L, sq_nonneg c.w]
  refine ⟨by linarith, ?_⟩
  have : n 2 ^ 2 * c.J ^ 2 ≤ nsqZ n * nsqZ n ^ 2 :=
    mul_le_mul hn2 hJ (sq_nonneg _) (by linarith)
  nlinarith

/-- `|u| ≤ M` and `|v| ≤ 2M³` from `u² ≤ N`, `v² ≤ 4N³`, `√N ≤ M`. -/
private lemma real_bounds {N : ℝ} {M : ℝ} (hN : 0 ≤ N) (hM : Real.sqrt N ≤ M) {u v : ℝ}
    (hu : u ^ 2 ≤ N) (hv : v ^ 2 ≤ 4 * N ^ 3) : |u| ≤ M ∧ |v| ≤ 2 * M ^ 3 := by
  have hM0 : 0 ≤ M := le_trans (Real.sqrt_nonneg _) hM
  have hM2 : N ≤ M ^ 2 := by
    have := pow_le_pow_left₀ (Real.sqrt_nonneg N) hM 2
    rwa [Real.sq_sqrt hN] at this
  refine ⟨le_trans (Real.abs_le_sqrt hu) hM, ?_⟩
  have h3 : N ^ 3 ≤ (M ^ 2) ^ 3 := pow_le_pow_left₀ hN hM2 3
  have : v ^ 2 ≤ (2 * M ^ 3) ^ 2 := by nlinarith
  have := sq_le_sq.mp this
  rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * M ^ 3)] at this

section Conic
open MvPolynomial

/-- The affine conic `Y² − a w² − b w − c` in the variables `(w, Y) = (X 0, X 1)`. -/
private noncomputable def conicPoly (a b cc : ℤ) : MvPolynomial (Fin 2) ℤ :=
  MvPolynomial.X 1 ^ 2 - C a * X 0 ^ 2 - C b * X 0 - C cc

private lemma conicPoly_coeff (a b cc : ℤ) :
    (conicPoly a b cc).coeff (Finsupp.single 1 2) = 1 := by
  have h1 : (Finsupp.single (0 : Fin 2) 2) ≠ Finsupp.single 1 2 := by
    intro h; have := congrArg (fun f => f 0) h; simp at this
  have h2 : (Finsupp.single (0 : Fin 2) 1) ≠ Finsupp.single 1 2 := by
    intro h; have := congrArg (fun f => f 0) h; simp at this
  have h3 : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 2 := by
    intro h; have := congrArg (fun f => f 1) h; simp at this
  simp only [conicPoly, coeff_sub, coeff_C_mul, X_pow_eq_monomial, coeff_monomial, coeff_C,
    h1, h3, ite_true, ite_false]
  rw [show (X 0 : MvPolynomial (Fin 2) ℤ) = monomial (Finsupp.single 0 1) 1 from rfl,
    coeff_monomial]
  simp [h2]

private lemma conicPoly_totalDegree (a b cc : ℤ) : (conicPoly a b cc).totalDegree = 2 := by
  apply le_antisymm
  · refine (totalDegree_sub _ _).trans (max_le ((totalDegree_sub _ _).trans (max_le
      ((totalDegree_sub _ _).trans (max_le ?_ ?_)) ?_)) ?_)
    · exact (totalDegree_pow _ _).trans (by rw [totalDegree_X]) 
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      exact (totalDegree_pow _ _).trans (by rw [totalDegree_X])
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add, totalDegree_X]; norm_num
    · rw [totalDegree_C]; norm_num
  · have hmem : Finsupp.single 1 2 ∈ (conicPoly a b cc).support := by
      rw [mem_support_iff, conicPoly_coeff]; norm_num
    have := le_totalDegree hmem
    simpa using this

private lemma conicPoly_eval (a b cc : ℤ) (p : Fin 2 → ℤ) :
    eval p (conicPoly a b cc) = p 1 ^ 2 - a * p 0 ^ 2 - b * p 0 - cc := by
  simp [conicPoly]

private lemma conicPoly_boxSize (a b cc : ℤ) (B : Fin 2 → ℝ) :
    B 1 ^ 2 ≤ boxSize (conicPoly a b cc) B := by
  have hmem : Finsupp.single 1 2 ∈ (conicPoly a b cc).support := by
    rw [mem_support_iff, conicPoly_coeff]; norm_num
  have hbdd : BddAbove ((fun e : Fin 2 →₀ ℕ => ∏ i, B i ^ (e i)) ''
      ((conicPoly a b cc).support : Set (Fin 2 →₀ ℕ))) :=
    ((conicPoly a b cc).support.finite_toSet.image _).bddAbove
  have := le_csSup hbdd (Set.mem_image_of_mem _ (Finset.mem_coe.mpr hmem))
  simpa [boxSize, Fin.prod_univ_two] using this

private lemma conicPoly_absIrred (a b cc : ℤ) (h : b ^ 2 - 4 * a * cc ≠ 0) :
    AbsIrred (conicPoly a b cc) := by
  unfold AbsIrred
  have e : map (Int.castRingHom (AlgebraicClosure ℚ)) (conicPoly a b cc) =
      X 1 ^ 2 - C (a : AlgebraicClosure ℚ) * X 0 ^ 2 - C (b : AlgebraicClosure ℚ) * X 0 -
        C (cc : AlgebraicClosure ℚ) := by
    simp [conicPoly]
  rw [e]
  apply irred_conic
  exact_mod_cast h

end Conic

/-- B6: a parabolic `t` (`caOf = 0`) costs `N^{1/2+η}` (`PlaneCurveCount`, `d = 2`). -/
theorem parabolic_t_count (hP : PlaneCurveCount) : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (n : Mode) (Δ : ℕ) (z t s2 s3 : ℤ), Squarefree Δ → nsqZ n = Δ * z ^ 2 →
      (((activePts n s2 s3).filter fun k => tOf Δ s2 n k = t).card : ℝ) ≤
        C * max 2 (absk n) ^ ((1 : ℝ) / 2 + η) := by
  intro η hη
  obtain ⟨Cp, hCp⟩ := hP 2 (η / 3) (by norm_num) (by positivity)
  refine ⟨max Cp 0 * 2 ^ (η / 3), by positivity, ?_⟩
  intro n Δ z t s2 s3 hsq hn
  classical
  set M : ℝ := max 2 (absk n) with hMdef
  have hM2 : (2 : ℝ) ≤ M := le_max_left _ _
  set S := (activePts n s2 s3).filter fun k => tOf Δ s2 n k = t with hS
  have hfib : ∀ k ∈ S, ∃ c : Coords n k, c.Δ = Δ ∧ c.z = |z| ∧ c.t = t ∧ c.s3 = s3 ∧
      c.nh2 ≠ 0 ∧ c.t ≠ c.z := fun k hk => by
    rw [hS, Finset.mem_filter] at hk; exact fibre_coords hsq hn hk.1 hk.2
  rcases S.eq_empty_or_nonempty with hS0 | ⟨k₀, hk₀⟩
  · rw [hS0, Finset.card_empty, Nat.cast_zero]; positivity
  obtain ⟨c₀, h₀Δ, h₀z, h₀t, h₀s, h₀nh, h₀tz⟩ := hfib k₀ hk₀
  set F := conicPoly c₀.ca c₀.cb c₀.cc with hF
  have hdisc : c₀.cb ^ 2 - 4 * c₀.ca * c₀.cc ≠ 0 := by
    rw [c₀.disc_id]; exact c₀.cM_ne_zero h₀nh h₀tz
  set B : Fin 2 → ℝ := ![M, 2 * M ^ 3] with hB
  have hB0 : B 0 = M := rfl
  have hB1 : B 1 = 2 * M ^ 3 := rfl
  have hMM : M ≤ 2 * M ^ 3 := by
    have : M * 1 ≤ M * (2 * M ^ 2) := mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
    linarith [show M * (2 * M ^ 2) = 2 * M ^ 3 by ring]
  have hcard := hCp F (conicPoly_totalDegree _ _ _) (conicPoly_absIrred _ _ _ hdisc) B
    (by rw [hB0]; exact hM2) (by rw [hB0, hB1]; exact hMM)
  -- the box is large enough and the map `k ↦ (w, 2 n₃ J)` is injective
  have hN0 : (0 : ℝ) ≤ nsqZ n := by
    have : 0 ≤ nsqZ n := Finset.sum_nonneg fun i _ => sq_nonneg _
    exact_mod_cast this
  have hsM : Real.sqrt (nsqZ n : ℝ) ≤ M := by
    rw [← absk_eq_sqrt_nsqZ]; exact le_max_right _ _
  let g : Mode → (Fin 2 → ℤ) := fun k => ![k 2, 2 * n 2 * (k 0 * n 1 - k 1 * n 0)]
  have hle : S.card ≤ (boxZeros F B).card := by
    refine Finset.card_le_card_of_injOn g (fun k hk => ?_) ?_
    · obtain ⟨c, hΔ, hz, ht, hs, hnh, _⟩ := hfib k hk
      obtain ⟨ea, eb, ec, -⟩ := coef_eq c c₀ (hΔ.trans h₀Δ.symm) (hz.trans h₀z.symm)
        (ht.trans h₀t.symm) (hs.trans h₀s.symm)
      have hgk : g k = ![c.w, 2 * n 2 * c.J] := rfl
      obtain ⟨hw, hY⟩ := wY_bounds c
      obtain ⟨hw', hY'⟩ := real_bounds hN0 hsM (u := (k 2 : ℝ)) (v := ((2 * n 2 * c.J : ℤ) : ℝ))
        (by exact_mod_cast hw) (by exact_mod_cast hY)
      rw [Finset.mem_coe, boxZeros, Finset.mem_filter, hgk]
      refine ⟨?_, ?_⟩
      · simp only [boxPts, Fintype.mem_piFinset, Fin.forall_fin_two, Finset.mem_Icc,
          Matrix.cons_val_zero, Matrix.cons_val_one]
        exact ⟨abs_le_floor hw', abs_le_floor hY'⟩
      · rw [hF, conicPoly_eval]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [← ea, ← eb, ← ec, c.conic_id]; ring
    · intro k hk k' hk' hkk
      obtain ⟨c, hΔ, hz, ht, hs, hnh, _⟩ := hfib k hk
      obtain ⟨c', hΔ', hz', ht', hs', _, _⟩ := hfib k' hk'
      have h0 := congrFun hkk 0
      have h1 := congrFun hkk 1
      simp only [g, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
      have hJ : c.J = c'.J := by
        have : 2 * n 2 * (c.J - c'.J) = 0 := by
          simp only [Coords.J]; linear_combination h1
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h (mul_ne_zero two_ne_zero c.hn3)
        · linarith
      exact fibre_inj c c' (hΔ.trans hΔ'.symm) (hz.trans hz'.symm) (ht.trans ht'.symm)
        (hs.trans hs'.symm) hnh h0 hJ
  -- the exponent: `log B₀ log B₁ / log 𝔗 ≤ log B₀ / 2`
  have hT := conicPoly_boxSize c₀.ca c₀.cb c₀.cc B
  rw [← hF, hB1] at hT
  have hB1gt : 1 < 2 * M ^ 3 := by nlinarith
  have hl1 : 0 < Real.log (2 * M ^ 3) := Real.log_pos hB1gt
  have hl0 : 0 ≤ Real.log M := Real.log_nonneg (by linarith)
  have hlT : 2 * Real.log (2 * M ^ 3) ≤ Real.log (boxSize F B) := by
    rw [← Real.log_rpow (by positivity)]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hT)
  have hexp : Real.exp (Real.log (B 0) * Real.log (B 1) / Real.log (boxSize F B)) ≤
      M ^ ((1 : ℝ) / 2) := by
    rw [hB0, hB1, Real.rpow_def_of_pos (by linarith)]
    apply Real.exp_le_exp.mpr
    calc Real.log M * Real.log (2 * M ^ 3) / Real.log (boxSize F B)
        ≤ Real.log M * Real.log (2 * M ^ 3) / (2 * Real.log (2 * M ^ 3)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hlT
      _ = Real.log M * (1 / 2) := by field_simp
  have hpow : (B 1) ^ (η / 3) = 2 ^ (η / 3) * M ^ η := by
    rw [hB1, Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul (by linarith)]
    have : ((3 : ℕ) : ℝ) * (η / 3) = η := by push_cast; ring
    rw [this]
  calc (S.card : ℝ) ≤ (boxZeros F B).card := by exact_mod_cast hle
    _ ≤ Cp * B 1 ^ (η / 3) *
        Real.exp (Real.log (B 0) * Real.log (B 1) / Real.log (boxSize F B)) := hcard
    _ ≤ max Cp 0 * B 1 ^ (η / 3) * M ^ ((1 : ℝ) / 2) := by
        have hB1n : 0 ≤ B 1 ^ (η / 3) := Real.rpow_nonneg (by rw [hB1]; positivity) _
        exact mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) hB1n) hexp
          (by positivity) (mul_nonneg (le_max_right _ _) hB1n)
    _ = max Cp 0 * 2 ^ (η / 3) * M ^ ((1 : ℝ) / 2 + η) := by
        rw [hpow, Real.rpow_add (by linarith)]; ring

end OVNS.Quant
