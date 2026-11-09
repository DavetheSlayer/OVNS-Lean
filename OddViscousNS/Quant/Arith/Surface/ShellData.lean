import OddViscousNS.Quant.Arith.Surface.Tree
import OddViscousNS.Quant.Arith.Surface.SurfaceMod
import OddViscousNS.Quant.Arith.Weighted.SurfaceCover

/-!
# The surface data of a shell

The explicit `X₃`-coefficients `sF1`, `sF0` of the surface, the bound `|m| ≤ N²⁰` in the shell box, the
size of the box exponents `l i = log B i` (`shell_kappaHat_le`, `kappaHat_ge`), and the record
`shellD : SurfData` of a shell.
-/

open MvPolynomial

namespace OVNS.Quant.Surf

open private shell_facts shellBox_le shell_cover_ratio
  from OddViscousNS.Quant.Arith.Weighted.SurfaceCover

/-- The polynomial `2gL` in the plane variables. -/
noncomputable def sL (Δ z n3 s3 g : ℤ) : MvPolynomial (Fin 2) ℤ :=
  -C (2 * Δ * g ^ 2) * X 0 ^ 2 * X 1 - C (Δ * g ^ 3) * X 0 ^ 2 - C (2 * Δ * g ^ 2 * s3 * z) * X 0
    - C (Δ * g * z ^ 2) - C (2 * n3 ^ 2) * X 1

/-- The polynomial `x`. -/
noncomputable def sxs (z s3 g : ℤ) : MvPolynomial (Fin 2) ℤ := C g * X 0 + C (s3 * z) + X 0 * X 1

/-- The coefficient of `X₃`. -/
noncomputable def sF1 (Δ z n3 ni s3 g : ℤ) : MvPolynomial (Fin 2) ℤ :=
  -C (4 * g * ni) * sL Δ z n3 s3 g

/-- The coefficient of `1`. -/
noncomputable def sF0 (Δ z n3 nj s3 g : ℤ) : MvPolynomial (Fin 2) ℤ :=
  sL Δ z n3 s3 g ^ 2 + C (4 * nj ^ 2 * n3 ^ 2) * X 1 ^ 2
    - C (4 * g ^ 2 * nj ^ 2 * Δ) * sxs z s3 g ^ 2

/-- The leading coefficient `c = 4g²(nᵢ² + nⱼ²)`. -/
def sC (ni nj g : ℤ) : ℤ := 4 * g ^ 2 * (ni ^ 2 + nj ^ 2)

theorem surface_form (Δ z n3 ni nj s3 g : ℤ) :
    surfacePoly Δ z n3 ni nj s3 g = C (sC ni nj g) * X 2 ^ 2 +
      rename Fin.castSucc (sF1 Δ z n3 ni s3 g) * X 2 +
        rename Fin.castSucc (sF0 Δ z n3 nj s3 g) := by
  simp only [surfacePoly, sF1, sF0, sL, sxs, sC, map_add, map_sub, map_mul, map_neg, map_pow,
    rename_C, rename_X]
  have e0 : (Fin.castSucc (0 : Fin 2) : Fin 3) = 0 := rfl
  have e1 : (Fin.castSucc (1 : Fin 2) : Fin 3) = 1 := rfl
  simp only [e0, e1, map_ofNat]
  ring

lemma mVal_eq (Δ z n3 ni s3 g c : ℤ) (x : Fin 3 → ℤ) :
    mVal c (sF1 Δ z n3 ni s3 g) x = 2 * c * x 2 - 4 * g * ni *
      (-(2 * Δ * g ^ 2) * x 0 ^ 2 * x 1 - Δ * g ^ 3 * x 0 ^ 2 - 2 * Δ * g ^ 2 * s3 * z * x 0
        - Δ * g * z ^ 2 - 2 * n3 ^ 2 * x 1) := by
  have e0 : (Fin.castSucc (0 : Fin 2) : Fin 3) = 0 := rfl
  have e1 : (Fin.castSucc (1 : Fin 2) : Fin 3) = 1 := rfl
  simp only [mVal, sF1, sL, map_sub, map_mul, map_neg, map_pow, eval_C, eval_X, e0, e1]
  ring

/-- `|m| ≤ N²⁰` in the box. -/
lemma mVal_abs_le {N : ℝ} (hN : 2 ≤ N) {Δ z n3 ni nj s3 g : ℤ} {x : Fin 3 → ℤ}
    (hΔ : |(Δ : ℝ)| ≤ N ^ 2) (hz : |(z : ℝ)| ≤ N) (hn3 : |(n3 : ℝ)| ≤ N) (hni : |(ni : ℝ)| ≤ N)
    (hν : |((ni : ℝ) ^ 2 + (nj : ℝ) ^ 2)| ≤ N ^ 2) (hs3 : |(s3 : ℝ)| ≤ 1) (hg : |(g : ℝ)| ≤ N)
    (hx : ∀ i, |(x i : ℝ)| ≤ 4 * N) :
    |(mVal (sC ni nj g) (sF1 Δ z n3 ni s3 g) x : ℝ)| ≤ N ^ 20 := by
  have hN0 : 0 ≤ N := by linarith
  rw [mVal_eq]
  simp only [sC]
  push_cast
  set G := |(g : ℝ)|
  set D := |(Δ : ℝ)|
  set Z := |(z : ℝ)|
  set W := |(n3 : ℝ)|
  set I := |(ni : ℝ)|
  set S := |(s3 : ℝ)|
  set V := |((ni : ℝ) ^ 2 + (nj : ℝ) ^ 2)|
  set Y₀ := |(x 0 : ℝ)|
  set Y₁ := |(x 1 : ℝ)|
  set Y₂ := |(x 2 : ℝ)|
  have hG0 : 0 ≤ G := abs_nonneg _
  have hD0 : 0 ≤ D := abs_nonneg _
  have hZ0 : 0 ≤ Z := abs_nonneg _
  have hW0 : 0 ≤ W := abs_nonneg _
  have hI0 : 0 ≤ I := abs_nonneg _
  have hS0 : 0 ≤ S := abs_nonneg _
  have hV0 : 0 ≤ V := abs_nonneg _
  have hY0 : 0 ≤ Y₀ := abs_nonneg _
  have hY1 : 0 ≤ Y₁ := abs_nonneg _
  have hY2 : 0 ≤ Y₂ := abs_nonneg _
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  have hmain : |2 * (4 * (g : ℝ) ^ 2 * ((ni : ℝ) ^ 2 + (nj : ℝ) ^ 2)) * (x 2 : ℝ) -
      4 * (g : ℝ) * (ni : ℝ) * (-(2 * (Δ : ℝ) * (g : ℝ) ^ 2) * (x 0 : ℝ) ^ 2 * (x 1 : ℝ)
        - (Δ : ℝ) * (g : ℝ) ^ 3 * (x 0 : ℝ) ^ 2 - 2 * (Δ : ℝ) * (g : ℝ) ^ 2 * (s3 : ℝ) * (z : ℝ) * (x 0 : ℝ)
        - (Δ : ℝ) * (g : ℝ) * (z : ℝ) ^ 2 - 2 * (n3 : ℝ) ^ 2 * (x 1 : ℝ))| ≤
      8 * G ^ 2 * V * Y₂ + 4 * G * I * (2 * D * G ^ 2 * Y₀ ^ 2 * Y₁ + D * G ^ 3 * Y₀ ^ 2
        + 2 * D * G ^ 2 * S * Z * Y₀ + D * G * Z ^ 2 + 2 * W ^ 2 * Y₁) := by
    have e1 : |2 * (4 * (g : ℝ) ^ 2 * ((ni : ℝ) ^ 2 + (nj : ℝ) ^ 2)) * (x 2 : ℝ)| =
        8 * G ^ 2 * V * Y₂ := by
      simp only [abs_mul, abs_pow, abs_two, abs_of_pos (by norm_num : (0 : ℝ) < 4), G, V, Y₂]
      ring
    have e2 : |4 * (g : ℝ) * (ni : ℝ)| = 4 * G * I := by
      simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), G, I]
    have a1 : |(-(2 * (Δ : ℝ) * (g : ℝ) ^ 2) * (x 0 : ℝ) ^ 2 * (x 1 : ℝ))| =
        2 * D * G ^ 2 * Y₀ ^ 2 * Y₁ := by
      simp only [abs_mul, abs_neg, abs_pow, abs_two, D, G, Y₀, Y₁]
    have a2 : |(Δ : ℝ) * (g : ℝ) ^ 3 * (x 0 : ℝ) ^ 2| = D * G ^ 3 * Y₀ ^ 2 := by
      simp only [abs_mul, abs_pow, D, G, Y₀]
    have a3 : |2 * (Δ : ℝ) * (g : ℝ) ^ 2 * (s3 : ℝ) * (z : ℝ) * (x 0 : ℝ)| =
        2 * D * G ^ 2 * S * Z * Y₀ := by
      simp only [abs_mul, abs_pow, abs_two, D, G, S, Z, Y₀]
    have a4 : |(Δ : ℝ) * (g : ℝ) * (z : ℝ) ^ 2| = D * G * Z ^ 2 := by
      simp only [abs_mul, abs_pow, D, G, Z]
    have a5 : |2 * (n3 : ℝ) ^ 2 * (x 1 : ℝ)| = 2 * W ^ 2 * Y₁ := by
      simp only [abs_mul, abs_pow, abs_two, W, Y₁]
    refine (abs_sub _ _).trans ?_
    rw [e1, abs_mul, e2]
    gcongr
    refine (abs_sub _ _).trans ?_
    rw [a5]
    gcongr
    refine (abs_sub _ _).trans ?_
    rw [a4]
    gcongr
    refine (abs_sub _ _).trans ?_
    rw [a3]
    gcongr
    refine (abs_sub _ _).trans ?_
    rw [a1, a2]
  refine hmain.trans ?_
  have hb : 8 * G ^ 2 * V * Y₂ + 4 * G * I * (2 * D * G ^ 2 * Y₀ ^ 2 * Y₁ + D * G ^ 3 * Y₀ ^ 2
        + 2 * D * G ^ 2 * S * Z * Y₀ + D * G * Z ^ 2 + 2 * W ^ 2 * Y₁) ≤
      8 * N ^ 2 * N ^ 2 * (4 * N) + 4 * N * N * (2 * N ^ 2 * N ^ 2 * (4 * N) ^ 2 * (4 * N)
        + N ^ 2 * N ^ 3 * (4 * N) ^ 2 + 2 * N ^ 2 * N ^ 2 * 1 * N * (4 * N)
        + N ^ 2 * N * N ^ 2 + 2 * N ^ 2 * (4 * N)) := by
    gcongr
  refine hb.trans ?_
  have hN1 : 1 ≤ N := by linarith
  have p5 : N ^ 5 ≤ N ^ 9 := pow_le_pow_right₀ hN1 (by norm_num)
  have p7 : N ^ 7 ≤ N ^ 9 := pow_le_pow_right₀ hN1 (by norm_num)
  have p8 : N ^ 8 ≤ N ^ 9 := pow_le_pow_right₀ hN1 (by norm_num)
  have hN10 : (1024 : ℝ) ≤ N ^ 11 := by
    have : (2 : ℝ) ^ 11 ≤ N ^ 11 := pow_le_pow_left₀ (by norm_num) hN 11
    norm_num at this
    linarith
  have h9 : 0 ≤ N ^ 9 := by positivity
  have e : 8 * N ^ 2 * N ^ 2 * (4 * N) + 4 * N * N * (2 * N ^ 2 * N ^ 2 * (4 * N) ^ 2 * (4 * N)
        + N ^ 2 * N ^ 3 * (4 * N) ^ 2 + 2 * N ^ 2 * N ^ 2 * 1 * N * (4 * N)
        + N ^ 2 * N * N ^ 2 + 2 * N ^ 2 * (4 * N)) =
      32 * N ^ 5 + 576 * N ^ 9 + 32 * N ^ 8 + 4 * N ^ 7 + 32 * N ^ 5 := by ring
  have e2 : N ^ 20 = N ^ 11 * N ^ 9 := by ring
  rw [e, e2]
  nlinarith

lemma absk_sq (n : Mode) : absk n ^ 2 = (nsqZ n : ℝ) := by
  rw [absk_eq_sqrt_nsqZ, Real.sq_sqrt]
  have : 0 ≤ nsqZ n := Finset.sum_nonneg fun i _ => sq_nonneg _
  exact_mod_cast this

/-- Sizes on a shell. -/
lemma shell_size {n : Mode} {Δ z g T : ℕ} (hH : ShellHyp n Δ z g T) (hn3 : n 2 ≠ 0) :
    (Δ : ℝ) ≤ absk n ^ 2 ∧ (z : ℝ) ≤ absk n ∧ (g : ℝ) ≤ absk n ∧ ∀ i, |(n i : ℝ)| ≤ absk n := by
  obtain ⟨hΔ1, hzN, hg1, hN2, -, -, hz1⟩ := shell_facts hH
  have hN0 : 0 ≤ absk n := by linarith
  have hnq : absk n ^ 2 = (Δ : ℝ) * (z : ℝ) ^ 2 := by
    rw [absk_sq, hH.2.1]
    push_cast
    ring
  have hz1' : (1 : ℝ) ≤ z := by exact_mod_cast hz1
  have hni : ∀ i, |(n i : ℝ)| ≤ absk n := by
    intro i
    refine abs_le_of_sq_le_sq ?_ hN0
    rw [absk_sq]
    have : (n i) ^ 2 ≤ nsqZ n := by
      simp only [nsqZ]
      exact Finset.single_le_sum (f := fun i => n i ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    exact_mod_cast this
  refine ⟨?_, hzN, ?_, hni⟩
  · rw [hnq]
    have hΔ0 : (0 : ℝ) ≤ Δ := Nat.cast_nonneg _
    exact le_mul_of_one_le_right hΔ0 (one_le_pow₀ hz1')
  · have h1 := hni 2
    have h2 : g ≤ (n 2).natAbs := Nat.le_of_dvd (Int.natAbs_pos.2 hn3) hH.2.2.1
    have h3 : (g : ℝ) ≤ ((n 2).natAbs : ℝ) := by exact_mod_cast h2
    rw [Nat.cast_natAbs] at h3
    push_cast at h3
    linarith

lemma shell_norm {n : Mode} {Δ z g T : ℕ} (hH : ShellHyp n Δ z g T) {i j : Fin 3}
    (hij : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) :
    n i ^ 2 + n j ^ 2 + n 2 ^ 2 = (Δ : ℤ) * (z : ℤ) ^ 2 := by
  have hn := hH.2.1
  simp only [nsqZ, Fin.sum_univ_three] at hn
  rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith

/-- `L/36 ≤ κ̂`. -/
lemma kappaHat_ge {l : Fin 3 → ℝ} (hl : ∀ i, 0 < l i) {L : ℝ} (hL : ∀ i, l i ≤ L)
    (hL6 : ∀ i, L ≤ 6 * l i) : L / 36 ≤ kappaHat l := by
  have h0 := hl 0
  have h1 := hl 1
  have h2 := hl 2
  have hL0 : 0 < L := lt_of_lt_of_le h0 (hL 0)
  refine Real.le_sqrt_of_sq_le ?_
  rw [le_div_iff₀ (by positivity)]
  have a0 := hL6 0
  have a1 := hL6 1
  have a2 := hL6 2
  have b : L ^ 3 ≤ 216 * (l 0 * l 1 * l 2) := by
    have h3 : L ^ 2 ≤ 6 * l 0 * (6 * l 1) := by
      rw [sq]
      exact mul_le_mul a0 a1 hL0.le (by positivity)
    have h4 : L ^ 2 * L ≤ 6 * l 0 * (6 * l 1) * (6 * l 2) :=
      mul_le_mul h3 a2 hL0.le (by positivity)
    nlinarith
  have c : 4 * l 0 + 2 * l 1 ≤ 6 * L := by linarith [hL 0, hL 1]
  have d : (L / 36) ^ 2 * (4 * l 0 + 2 * l 1) ≤ (L / 36) ^ 2 * (6 * L) :=
    mul_le_mul_of_nonneg_left c (by positivity)
  nlinarith

/-- `κ̂ ≤ (p*/2) log N + 4` on a shell. -/
theorem shell_kappaHat_le {n : Mode} {Δ z g T : ℕ} (hH : ShellHyp n Δ z g T) (hN : 2 ≤ absk n) :
    kappaHat (fun i => Real.log (shellBox g T (absk n) i)) ≤
      pStar / 2 * Real.log (absk n) + 4 := by
  obtain ⟨hΔ1, -, hg1, -, hTN, hTg, -⟩ := shell_facts hH
  obtain ⟨-, -, -, -, -, hgN, hTgN⟩ := hH
  set N := absk n with hNdef
  have hp := pStar_bounds
  have hN0 : 0 < N := by linarith
  have hg0 : (0 : ℝ) < g := by linarith
  have hT0 : (0 : ℝ) < T := by
    have := (one_lt_div hg0).mp hTg
    linarith
  set lam := Real.log N with hlam
  set U := Real.log T - Real.log g with hU
  have hl2 : Real.log 2 ≤ lam := Real.log_le_log (by norm_num) hN
  have hB0 : Real.log (shellBox g T N 0) = Real.log 2 + U := by
    simp only [shellBox, Matrix.cons_val_zero]
    rw [Real.log_div (by positivity) hg0.ne', Real.log_mul (by norm_num) hT0.ne']
    ring
  have hB1 : Real.log (shellBox g T N 1) = Real.log 4 + lam - U := by
    simp only [shellBox, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [Real.log_div (by positivity) hT0.ne', Real.log_mul (by positivity) hN0.ne',
      Real.log_mul (by norm_num) hg0.ne']
    ring
  have hB2 : Real.log (shellBox g T N 2) = lam := by
    change Real.log (max 2 N) = lam
    rw [max_eq_right hN]
  have hU1 : pStar * lam < U := by
    have := Real.log_lt_log (by positivity) hTgN
    rwa [Real.log_rpow hN0, Real.log_div hT0.ne' hg0.ne'] at this
  have hU2 : U ≤ (5 / 4 - pStar) * lam + Real.log 2 := by
    have h1 := Real.log_lt_log (by positivity) hgN
    rw [Real.log_rpow hN0] at h1
    have h2 : Real.log T ≤ Real.log 2 + lam := by
      rw [← Real.log_mul (by norm_num) hN0.ne']
      exact Real.log_le_log hT0 hTN
    linarith
  refine le_trans (le_of_eq ?_) (kappa_bound hl2 hU1 hU2)
  simp only [kappaHat]
  rw [hB0, hB1, hB2]
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h256 : Real.log 256 = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num
  have e : 4 * (Real.log 2 + U) + 2 * (Real.log 4 + lam - U) = Real.log 256 + 2 * U + 2 * lam := by
    rw [h4, h256]
    ring
  rw [e]

/-- Points of the shell box have coordinates at most `4N`. -/
lemma abs_le_of_mem_box {B : Fin 3 → ℝ} {x : Fin 3 → ℤ}
    (hx : x ∈ boxPts 3 B) (i : Fin 3) : |(x i : ℝ)| ≤ B i := by
  have h := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hx i)
  have h1 : ((⌊B i⌋ : ℤ) : ℝ) ≤ B i := Int.floor_le _
  have h2 : (-(⌊B i⌋ : ℝ)) ≤ x i := by exact_mod_cast h.1
  have h3 : (x i : ℝ) ≤ (⌊B i⌋ : ℝ) := by exact_mod_cast h.2
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- The bound for `m` at a point of the shell box. -/
theorem shell_m_le {n : Mode} {Δ z g T : ℕ} {s3 : ℤ} (hH : ShellHyp n Δ z g T) (hn3 : n 2 ≠ 0)
    (hN : 2 ≤ absk n) {i j : Fin 3} (hij : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0))
    (hs3 : s3 = 1 ∨ s3 = -1) {x : Fin 3 → ℤ} (hx : ∀ l, |(x l : ℝ)| ≤ shellBox g T (absk n) l) :
    |(mVal (sC (n i) (n j) g) (sF1 Δ z (n 2) (n i) s3 g) x : ℝ)| ≤ absk n ^ 20 := by
  obtain ⟨h1, h2, h3, h4⟩ := shell_size hH hn3
  have hν : |((n i : ℝ) ^ 2 + (n j : ℝ) ^ 2)| ≤ absk n ^ 2 := by
    have hnorm := shell_norm hH hij
    have hnr : (n i : ℝ) ^ 2 + (n j : ℝ) ^ 2 + (n 2 : ℝ) ^ 2 = absk n ^ 2 := by
      rw [absk_sq, hH.2.1]
      exact_mod_cast hnorm
    rw [abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg (n 2 : ℝ)]
  have hzc : (z : ℝ) = |((z : ℤ) : ℝ)| := by simp
  refine mVal_abs_le hN (by simpa using h1) (by simpa using h2) (h4 2) (h4 i) hν ?_
    (by simpa using h3) (fun l => (hx l).trans (shellBox_le hH l))
  rcases hs3 with rfl | rfl <;> simp

lemma shell_hL {n : Mode} {Δ z g T : ℕ} (hH : ShellHyp n Δ z g T) (l : Fin 3) :
    Real.log (shellBox g T (absk n) l) ≤ Real.log (max (shellBox g T (absk n) 0)
      (max (shellBox g T (absk n) 1) (shellBox g T (absk n) 2))) := by
  have hb2 := fun l => shellBox_ge_two hH l
  refine Real.log_le_log (by linarith [hb2 l]) ?_
  fin_cases l
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

lemma shell_hL6 {n : Mode} {Δ z g T : ℕ} (hH : ShellHyp n Δ z g T) (hN : 2 ≤ absk n) (l : Fin 3) :
    Real.log (max (shellBox g T (absk n) 0)
      (max (shellBox g T (absk n) 1) (shellBox g T (absk n) 2))) ≤
      6 * Real.log (shellBox g T (absk n) l) := by
  obtain ⟨hr, -, -⟩ := shell_cover_ratio hH hN
  have hb2 := fun l => shellBox_ge_two hH l
  have hmin : min (shellBox g T (absk n) 0) (min (shellBox g T (absk n) 1)
      (shellBox g T (absk n) 2)) ≤ shellBox g T (absk n) l := by
    fin_cases l
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have hpos : 0 < min (shellBox g T (absk n) 0) (min (shellBox g T (absk n) 1)
      (shellBox g T (absk n) 2)) := lt_min (by linarith [hb2 0])
    (lt_min (by linarith [hb2 1]) (by linarith [hb2 2]))
  have := Real.log_le_log hpos hmin
  linarith

/-- The record of a shell. -/
noncomputable def shellD (n : Mode) (Δ z : ℕ) (s3 : ℤ) (g T : ℕ) (i j : Fin 3) (P₀ : ℕ)
    (hH : ShellHyp n Δ z g T) (hij : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) (hn3 : n 2 ≠ 0)
    (hnj : n j ≠ 0) (hs3 : s3 = 1 ∨ s3 = -1) (hN : 2 ≤ absk n)
    (hP1 : 20 * Real.log (absk n) ≤ P₀) (hP2 : 18 ≤ P₀)
    (hP3 : Real.log P₀ ≤ Real.log (absk n) / 36) : SurfData where
  Δ := Δ
  z := z
  n3 := n 2
  ni := n i
  nj := n j
  s3 := s3
  g := g
  c := sC (n i) (n j) g
  Bad := 2 * Δ * g * n j * (n i ^ 2 + n j ^ 2)
  F1 := sF1 Δ z (n 2) (n i) s3 g
  F0 := sF0 Δ z (n 2) (n j) s3 g
  B := shellBox g T (absk n)
  l := fun l => Real.log (shellBox g T (absk n) l)
  L := Real.log (max (shellBox g T (absk n) 0) (max (shellBox g T (absk n) 1)
    (shellBox g T (absk n) 2)))
  Mb := absk n ^ 20
  P₀ := P₀
  hΔ := by
    have := hH.1.ne_zero
    exact_mod_cast this
  hg := by
    have := (shell_facts hH).2.2.1
    have h : 1 ≤ g := by exact_mod_cast this
    exact_mod_cast (by omega : g ≠ 0)
  hc := by
    have hg1 := (shell_facts hH).2.2.1
    have h : 1 ≤ g := by exact_mod_cast hg1
    have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast (by omega : g ≠ 0)
    have hν : 0 < n i ^ 2 + n j ^ 2 := by positivity
    simp only [sC]
    positivity
  hF := surface_form _ _ _ _ _ _ _
  hirr := by
    have hg1 := (shell_facts hH).2.2.1
    have h : 1 ≤ g := by exact_mod_cast hg1
    have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast (by omega : g ≠ 0)
    have hz1 : (0 : ℤ) < z := by
      have := (shell_facts hH).2.2.2.2.2.2
      exact_mod_cast this
    have hΔ1 : (0 : ℤ) < Δ := by
      have := (shell_facts hH).1
      exact_mod_cast this
    exact surface_irreducible_rat _
      (surface_absIrred _ _ _ _ _ _ _ hΔ1 hz1 hn3 hnj hg0 hs3 (shell_norm hH hij))
  hPC := fun p _ hp => surface_card_mod_le _ _ _ _ _ _ _ (shell_norm hH hij) hs3 p hp
  hBad := by
    have hg1 := (shell_facts hH).2.2.1
    have h : 1 ≤ g := by exact_mod_cast hg1
    have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast (by omega : g ≠ 0)
    have hΔ1 : (Δ : ℤ) ≠ 0 := by
      have := hH.1.ne_zero
      exact_mod_cast this
    have hν : 0 < n i ^ 2 + n j ^ 2 := by positivity
    positivity
  hBadMb := by
    obtain ⟨h1, h2, h3, h4⟩ := shell_size hH hn3
    have hN0 : 0 ≤ absk n := by linarith
    have hν : (n i : ℝ) ^ 2 + (n j : ℝ) ^ 2 ≤ absk n ^ 2 := by
      have hnorm := shell_norm hH hij
      have hnr : (n i : ℝ) ^ 2 + (n j : ℝ) ^ 2 + (n 2 : ℝ) ^ 2 = absk n ^ 2 := by
        rw [absk_sq, hH.2.1]
        exact_mod_cast hnorm
      nlinarith [sq_nonneg (n 2 : ℝ)]
    push_cast
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_two, Nat.abs_cast, Nat.abs_cast,
      abs_of_nonneg (by positivity : 0 ≤ (n i : ℝ) ^ 2 + (n j : ℝ) ^ 2)]
    have hb : 2 * (Δ : ℝ) * g * |(n j : ℝ)| * ((n i : ℝ) ^ 2 + (n j : ℝ) ^ 2) ≤
        2 * absk n ^ 2 * absk n * absk n * absk n ^ 2 := by
      have := h4 j
      gcongr
    refine hb.trans ?_
    have hN1 : 1 ≤ absk n := by linarith
    have p6 : absk n ^ 6 ≤ absk n ^ 19 := pow_le_pow_right₀ hN1 (by norm_num)
    have e1 : absk n ^ 20 = absk n * absk n ^ 19 := by ring
    have e2 : 2 * absk n ^ 2 * absk n * absk n * absk n ^ 2 = 2 * absk n ^ 6 := by ring
    rw [e1, e2]
    have h19 : 0 ≤ absk n ^ 19 := by positivity
    nlinarith
  hB := fun l => by linarith [shellBox_ge_two hH l]
  hlB := fun _ => rfl
  hL := shell_hL hH
  hL6 := shell_hL6 hH hN
  hMb := by
    have hN0 : 0 < absk n := by linarith
    rw [Real.log_pow]
    push_cast
    exact hP1
  hP₀ := hP2
  hκ := by
    have hl : ∀ l : Fin 3, 0 < Real.log (shellBox g T (absk n) l) := fun l =>
      Real.log_pos (by linarith [shellBox_ge_two hH l])
    have h1 := kappaHat_ge hl (shell_hL hH) (shell_hL6 hH hN)
    have h2 : Real.log (absk n) ≤ Real.log (shellBox g T (absk n) 2) :=
      Real.log_le_log (by linarith) (le_max_right _ _)
    have h3 := (shell_hL hH 2)
    linarith

end OVNS.Quant.Surf
