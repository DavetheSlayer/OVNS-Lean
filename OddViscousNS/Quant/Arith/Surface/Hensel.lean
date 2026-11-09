import OddViscousNS.Quant.Arith.Surface.Blocks

/-!
# Truncated Hensel and the one-prime determinant divisibility (route L3, L4)

`hensel_poly` (no power series: iterate `w ↦ w - γ G(w)`), `local_expansion`, `pow_dvd_det`.
-/

open Finset

namespace OVNS.Quant.Surf

section H
open Polynomial



variable {R : Type*} [CommRing R]

/-- Evaluation at a point of `(π)²` agrees modulo `π` with evaluation at the origin. -/
lemma eval_sub_eval_zero_dvd (π u v : R) (hu : π ∣ u) (hv : π ∣ v)
    (a : MvPolynomial (Fin 2) R) :
    π ∣ MvPolynomial.eval ![u, v] a - MvPolynomial.eval ![0, 0] a := by
  induction a using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [map_add]
    have := dvd_add hp hq
    convert this using 1
    ring
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    obtain ⟨c, hc⟩ := hp
    have hi : π ∣ ![u, v] i := by
      fin_cases i
      · exact hu
      · exact hv
    obtain ⟨d, hd⟩ := hi
    have h00 : (![0, 0] : Fin 2 → R) i = 0 := by fin_cases i <;> rfl
    refine ⟨c * ![u, v] i + MvPolynomial.eval ![0, 0] p * d, ?_⟩
    rw [h00, mul_zero, sub_zero, sub_eq_iff_eq_add.1 hc]
    linear_combination (MvPolynomial.eval ![0, 0] p) * hd

/-- **Truncated Hensel.** -/
theorem hensel_poly (π : R) (k : ℕ) (hk : π ^ k = 0)
    (G : Polynomial (MvPolynomial (Fin 2) R)) (γ : R)
    (h0 : π ∣ MvPolynomial.eval ![0, 0] (G.coeff 0))
    (h1 : π ∣ 1 - γ * MvPolynomial.eval ![0, 0] (G.coeff 1)) :
    ∃ W : MvPolynomial (Fin 2) R, ∀ u v τ : R, π ∣ u → π ∣ v → π ∣ τ →
      (G.map (MvPolynomial.eval ![u, v])).eval τ = 0 → τ = MvPolynomial.eval ![u, v] W := by
  classical
  -- the Newton-like iteration in `R[U,V]`
  let w : ℕ → MvPolynomial (Fin 2) R := fun n =>
    Nat.rec 0 (fun _ wi => wi - MvPolynomial.C γ * G.eval wi) n
  have hw0 : w 0 = 0 := rfl
  have hws : ∀ n, w (n + 1) = w n - MvPolynomial.C γ * G.eval (w n) := fun _ => rfl
  refine ⟨w k, fun u v τ hu hv hτ hG => ?_⟩
  set φ := MvPolynomial.eval ![u, v] with hφ
  set g : R[X] := G.map φ with hg
  set y : ℕ → R := fun n => φ (w n) with hy
  have hy0 : y 0 = 0 := by simp [hy, hw0]
  have hys : ∀ n, y (n + 1) = y n - γ * g.eval (y n) := by
    intro n
    have e : φ (G.eval (w n)) = g.eval (φ (w n)) := by
      rw [hg, Polynomial.eval_map, Polynomial.eval₂_at_apply] 
    simp only [hy, hws, map_sub, map_mul]
    rw [e]
    simp [hφ]
  -- values at the origin
  have hg0 : π ∣ g.eval 0 := by
    have : g.eval 0 = φ (G.coeff 0) := by
      rw [← Polynomial.coeff_zero_eq_eval_zero, hg, Polynomial.coeff_map]
    rw [this]
    have h := eval_sub_eval_zero_dvd π u v hu hv (G.coeff 0)
    have e : φ (G.coeff 0) = MvPolynomial.eval ![0, 0] (G.coeff 0) +
        (φ (G.coeff 0) - MvPolynomial.eval ![0, 0] (G.coeff 0)) := by ring
    rw [e]
    exact dvd_add h0 h
  have hg1 : π ∣ 1 - γ * g.derivative.eval 0 := by
    have : g.derivative.eval 0 = φ (G.coeff 1) := by
      rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative, hg,
        Polynomial.coeff_map]
      simp
    rw [this]
    have h := eval_sub_eval_zero_dvd π u v hu hv (G.coeff 1)
    have e : 1 - γ * φ (G.coeff 1) = (1 - γ * MvPolynomial.eval ![0, 0] (G.coeff 1)) -
        γ * (φ (G.coeff 1) - MvPolynomial.eval ![0, 0] (G.coeff 1)) := by ring
    rw [e]
    exact dvd_sub h1 (h.mul_left γ)
  -- `y n` stays in `(π)`
  have hyp : ∀ n, π ∣ y n := by
    intro n
    induction n with
    | zero => simp [hy0]
    | succ n ih =>
      rw [hys]
      refine dvd_sub ih (Dvd.dvd.mul_left ?_ γ)
      have := Polynomial.sub_dvd_eval_sub (y n) 0 g
      rw [sub_zero] at this
      have h2 : π ∣ g.eval (y n) - g.eval 0 := ih.trans this
      have e : g.eval (y n) = (g.eval (y n) - g.eval 0) + g.eval 0 := by ring
      rw [e]
      exact dvd_add h2 hg0
  -- the error `τ - y n` is in `(π^n)`
  have herr : ∀ n, π ^ n ∣ τ - y n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      obtain ⟨κ, hκ⟩ := Polynomial.binomExpansion g (y n) (τ - y n)
      have hz : g.eval (y n + (τ - y n)) = 0 := by rw [add_sub_cancel]; exact hG
      rw [hz] at hκ
      set e := τ - y n with he
      -- `1 - γ g'(y)` is divisible by `π`
      have hd : π ∣ 1 - γ * g.derivative.eval (y n) := by
        have := Polynomial.sub_dvd_eval_sub (y n) 0 g.derivative
        rw [sub_zero] at this
        have h2 := (hyp n).trans this
        have e' : 1 - γ * g.derivative.eval (y n) = (1 - γ * g.derivative.eval 0) -
            γ * (g.derivative.eval (y n) - g.derivative.eval 0) := by ring
        rw [e']
        exact dvd_sub hg1 (h2.mul_left γ)
      have hnext : τ - y (n + 1) = e * (1 - γ * g.derivative.eval (y n)) - γ * (κ * e ^ 2) := by
        rw [hys]
        have : g.eval (y n) = -(g.derivative.eval (y n) * e + κ * e ^ 2) := by
          linear_combination -hκ
        rw [this, he]
        ring
      rw [hnext]
      have hee : π ∣ e := by
        rw [he]; exact dvd_sub hτ (hyp n)
      refine dvd_sub ?_ ?_
      · rw [pow_succ]; exact mul_dvd_mul ih hd
      · refine Dvd.dvd.mul_left (Dvd.dvd.mul_left ?_ _) _
        rw [pow_succ, sq]
        exact mul_dvd_mul ih hee
  have := herr k
  rw [hk, zero_dvd_iff] at this
  exact sub_eq_zero.1 this


end H


section L
open MvPolynomial



noncomputable def mVal (c : ℤ) (F1 : MvPolynomial (Fin 2) ℤ) (x : Fin 3 → ℤ) : ℤ :=
  2 * c * x 2 + eval (fun i : Fin 2 => x i.castSucc) F1

variable {R : Type*} [CommRing R]

/-- The shift `P ↦ P(b₀ + U, b₁ + V)` with coefficients cast to `R`. -/
noncomputable def shift (b : Fin 2 → ℤ) : MvPolynomial (Fin 2) ℤ →+* MvPolynomial (Fin 2) R :=
  eval₂Hom (C.comp (Int.castRingHom R)) fun i => C (b i : R) + X i

lemma shift_X (b : Fin 2 → ℤ) (i : Fin 2) : (shift b (X i) : MvPolynomial (Fin 2) R) =
    C (b i : R) + X i := by
  simp only [shift, coe_eval₂Hom, eval₂_X]

lemma eval_shift (b : Fin 2 → ℤ) (u : Fin 2 → R) (P : MvPolynomial (Fin 2) ℤ) :
    eval u (shift b P) = eval₂ (Int.castRingHom R) (fun i => (b i : R) + u i) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp only [shift, coe_eval₂Hom, eval₂_C, RingHom.comp_apply, eval_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq, eval₂_add]
  | mul_X p i hp =>
    rw [map_mul, shift_X, map_mul, hp, eval₂_mul, eval₂_X, map_add, eval_C, eval_X]

lemma cast_eval (x : Fin 2 → ℤ) (P : MvPolynomial (Fin 2) ℤ) :
    ((eval x P : ℤ) : R) = eval₂ (Int.castRingHom R) (fun i => (x i : R)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => rw [eval_C, eval₂_C]; rfl
  | add p q hp hq => rw [map_add, Int.cast_add, hp, hq, eval₂_add]
  | mul_X p i hp => rw [map_mul, Int.cast_mul, hp, eval₂_mul, eval₂_X, eval_X]

lemma quad_coeff0 {A : Type*} [CommRing A] (α β γ : A) :
    (Polynomial.C α * Polynomial.X ^ 2 + Polynomial.C β * Polynomial.X + Polynomial.C γ).coeff 0
      = γ := by
  simp [Polynomial.coeff_X]

lemma quad_coeff1 {A : Type*} [CommRing A] (α β γ : A) :
    (Polynomial.C α * Polynomial.X ^ 2 + Polynomial.C β * Polynomial.X + Polynomial.C γ).coeff 1
      = β := by
  simp [Polynomial.coeff_C, Polynomial.coeff_X_pow]

/-- `F(b₀ + U, b₁ + V, b₂ + T)` as a polynomial in `T`. -/
noncomputable def shiftQuad (c : ℤ) (F1 F0 : MvPolynomial (Fin 2) ℤ) (b : Fin 3 → ℤ) :
    Polynomial (MvPolynomial (Fin 2) R) :=
  let b' : Fin 2 → ℤ := fun i => b i.castSucc
  let f1 : MvPolynomial (Fin 2) R := shift b' F1
  let f0 : MvPolynomial (Fin 2) R := shift b' F0
  let α : MvPolynomial (Fin 2) R := C (c : R)
  let bb : MvPolynomial (Fin 2) R := C (b 2 : R)
  Polynomial.C α * Polynomial.X ^ 2 + Polynomial.C (2 * α * bb + f1) * Polynomial.X +
    Polynomial.C (α * bb ^ 2 + f1 * bb + f0)

lemma eval_F (c : ℤ) (F1 F0 : MvPolynomial (Fin 2) ℤ) (F : MvPolynomial (Fin 3) ℤ)
    (hF : F = C c * X 2 ^ 2 + rename Fin.castSucc F1 * X 2 + rename Fin.castSucc F0)
    (x : Fin 3 → ℤ) : eval x F = c * x 2 ^ 2 + eval (fun i : Fin 2 => x i.castSucc) F1 * x 2 +
      eval (fun i : Fin 2 => x i.castSucc) F0 := by
  subst hF
  simp [eval_rename, Function.comp_def]

/-- Truncated implicit function at an integer point of the surface. -/
theorem local_expansion (p k : ℕ) (hp : p.Prime) (c : ℤ) (F1 F0 : MvPolynomial (Fin 2) ℤ)
    (F : MvPolynomial (Fin 3) ℤ)
    (hF : F = C c * X 2 ^ 2 + rename Fin.castSucc F1 * X 2 + rename Fin.castSucc F0)
    (b : Fin 3 → ℤ) (hb : eval b F = 0) (hm : ¬ (p : ℤ) ∣ mVal c F1 b) :
    ∃ W : MvPolynomial (Fin 2) (ZMod (p ^ k)), ∀ x : Fin 3 → ℤ, eval x F = 0 →
      (p : ℤ) ∣ x 0 - b 0 → (p : ℤ) ∣ x 1 - b 1 → (p : ℤ) ∣ x 2 - b 2 →
      ((x 2 - b 2 : ℤ) : ZMod (p ^ k)) =
        eval ![((x 0 - b 0 : ℤ) : ZMod (p ^ k)), ((x 1 - b 1 : ℤ) : ZMod (p ^ k))] W := by
  set R := ZMod (p ^ k) with hR
  set π : R := (p : R) with hπ
  have hπk : π ^ k = 0 := by
    rw [hπ, ← Nat.cast_pow]; exact ZMod.natCast_self _
  set b' : Fin 2 → ℤ := fun i => b i.castSucc with hb'
  have hb0 : b' 0 = b 0 := rfl
  have hb1 : b' 1 = b 1 := rfl
  -- an inverse of `m(b)` modulo `p^k`
  have hcop : IsCoprime (mVal c F1 b) ((p : ℤ) ^ k) := by
    refine IsCoprime.pow_right ?_
    exact ((Nat.prime_iff_prime_int.1 hp).coprime_iff_not_dvd.2 hm).symm
  obtain ⟨u, w, huw⟩ := hcop
  set γ : R := (u : R) with hγ
  have hγm : γ * ((mVal c F1 b : ℤ) : R) = 1 := by
    have h := congrArg (fun z : ℤ => (z : R)) huw
    simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_one] at h
    rw [show (p : R) ^ k = 0 from hπk, mul_zero, add_zero] at h
    exact h
  set G : Polynomial (MvPolynomial (Fin 2) R) := shiftQuad c F1 F0 b with hG
  have hcoef0 : G.coeff 0 = C (c : R) * C (b 2 : R) ^ 2 + shift b' F1 * C (b 2 : R) +
      shift b' F0 := quad_coeff0 _ _ _
  have hcoef1 : G.coeff 1 = 2 * C (c : R) * C (b 2 : R) + shift b' F1 := quad_coeff1 _ _ _
  have hshift0 : ∀ P : MvPolynomial (Fin 2) ℤ,
      eval ![(0 : R), 0] (shift b' P) = ((eval b' P : ℤ) : R) := by
    intro P
    rw [eval_shift, cast_eval]
    congr 1
    funext i
    fin_cases i <;> simp
  have h0 : π ∣ eval ![(0 : R), 0] (G.coeff 0) := by
    have : eval ![(0 : R), 0] (G.coeff 0) = ((eval b F : ℤ) : R) := by
      rw [hcoef0, eval_F c F1 F0 F hF b]
      simp only [map_add, map_mul, map_pow, eval_C, hshift0]
      push_cast
      ring
    rw [this, hb]; simp
  have h1 : π ∣ 1 - γ * eval ![(0 : R), 0] (G.coeff 1) := by
    have : eval ![(0 : R), 0] (G.coeff 1) = ((mVal c F1 b : ℤ) : R) := by
      rw [hcoef1]
      simp only [map_add, map_mul, eval_C, hshift0, mVal]
      push_cast
      simp [hb']
    rw [this, hγm, sub_self]; exact dvd_zero _
  obtain ⟨W, hW⟩ := hensel_poly π k hπk G γ h0 h1
  refine ⟨W, fun x hx h0' h1' h2' => ?_⟩
  have hdv : ∀ z : ℤ, (p : ℤ) ∣ z → π ∣ (z : R) := by
    rintro z ⟨y, rfl⟩
    exact ⟨(y : R), by push_cast; rfl⟩
  refine hW _ _ _ (hdv _ h0') (hdv _ h1') (hdv _ h2') ?_
  set u0 : R := ((x 0 - b 0 : ℤ) : R)
  set v0 : R := ((x 1 - b 1 : ℤ) : R)
  have hshiftx : ∀ P : MvPolynomial (Fin 2) ℤ,
      eval ![u0, v0] (shift b' P) = ((eval (fun i : Fin 2 => x i.castSucc) P : ℤ) : R) := by
    intro P
    rw [eval_shift, cast_eval]
    congr 1
    funext i
    fin_cases i
    · simp [u0, hb']
    · simp [v0, hb']
  have hshiftx' : ∀ P : MvPolynomial (Fin 2) ℤ,
      eval ![u0, v0] (shift (fun i : Fin 2 => b i.castSucc) P) =
        ((eval (fun i : Fin 2 => x i.castSucc) P : ℤ) : R) := hshiftx
  have hxF := eval_F c F1 F0 F hF x
  rw [hx] at hxF
  have hcast := congrArg (fun z : ℤ => (z : R)) hxF
  simp only [Int.cast_zero, Int.cast_add, Int.cast_mul, Int.cast_pow] at hcast
  simp only [hG, shiftQuad, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, map_add, map_mul, map_pow, eval_C,
    hshiftx']
  push_cast
  simp only [map_ofNat]
  linear_combination -hcast

/-- The monomial matrix `(x_j^{e_i})`. -/
def monoMat {J : Type*} (pts : J → Fin 3 → ℤ) (es : J → Fin 3 → ℕ) : Matrix J J ℤ :=
  Matrix.of fun j i => ∏ l, pts j l ^ es i l

/-- D4: divisibility of a monomial determinant at one prime; classes given by representatives. -/
theorem pow_dvd_det {J : Type*} [Fintype J] [DecidableEq J]
    (c : ℤ) (F1 F0 : MvPolynomial (Fin 2) ℤ) (F : MvPolynomial (Fin 3) ℤ)
    (hF : F = C c * X 2 ^ 2 + rename Fin.castSucc F1 * X 2 + rename Fin.castSucc F0)
    (p a : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (pts : J → Fin 3 → ℤ) (es : J → Fin 3 → ℕ)
    (hz : ∀ j, eval (pts j) F = 0) (rep : J → J)
    (hrep : ∀ j, rep j = j ∨ ¬ (p : ℤ) ∣ mVal c F1 (pts (rep j)))
    (hcong : ∀ j, rep j ≠ j → ((p : ℤ) ^ a ∣ pts j 0 - pts (rep j) 0) ∧
      ((p : ℤ) ^ a ∣ pts j 1 - pts (rep j) 1) ∧ ((p : ℤ) ∣ pts j 2 - pts (rep j) 2)) :
    ((p : ℤ) ^ a) ^ (∑ ξ, Vs (univ.filter fun j => rep j = ξ).card) ∣ (monoMat pts es).det := by
  classical
  set ν := ∑ ξ, Vs (univ.filter fun j => rep j = ξ).card with hν
  set k := a * ν with hk
  set R := ZMod (p ^ k) with hR
  have hϖ0 : (((p : ℕ) : R) ^ a) ^ ν = 0 := by
    rw [← pow_mul, ← hk, ← Nat.cast_pow]; exact ZMod.natCast_self _
  -- the polynomial `W ξ` at a good base point
  have hex : ∀ ξ : J, ∃ W : MvPolynomial (Fin 2) R, ¬ (p : ℤ) ∣ mVal c F1 (pts ξ) →
      ∀ x : Fin 3 → ℤ, eval x F = 0 → (p : ℤ) ∣ x 0 - pts ξ 0 → (p : ℤ) ∣ x 1 - pts ξ 1 →
        (p : ℤ) ∣ x 2 - pts ξ 2 → ((x 2 - pts ξ 2 : ℤ) : R) =
          eval ![((x 0 - pts ξ 0 : ℤ) : R), ((x 1 - pts ξ 1 : ℤ) : R)] W := by
    intro ξ
    by_cases h : (p : ℤ) ∣ mVal c F1 (pts ξ)
    · exact ⟨0, fun h' => absurd h h'⟩
    · obtain ⟨W, hW⟩ := local_expansion p k hp c F1 F0 F hF (pts ξ) (hz ξ) h
      exact ⟨W, fun _ => hW⟩
  choose W hW using hex
  set M' : Matrix J J R := (monoMat pts es).map (Int.castRingHom R) with hM'
  set Q : J → J → MvPolynomial (Fin 2) R := fun ξ e =>
    if (p : ℤ) ∣ mVal c F1 (pts ξ) then C (M' ξ e) else
      (C (pts ξ 0 : R) + X 0) ^ es e 0 * (C (pts ξ 1 : R) + X 1) ^ es e 1 *
        (C (pts ξ 2 : R) + W ξ) ^ es e 2 with hQ
  set U : J → R := fun j => ((pts j 0 - pts (rep j) 0 : ℤ) : R) with hU
  set V : J → R := fun j => ((pts j 1 - pts (rep j) 1 : ℤ) : R) with hV
  have hdvdcast : ∀ z : ℤ, (p : ℤ) ^ a ∣ z → ((p : ℕ) : R) ^ a ∣ (z : R) := by
    rintro z ⟨y, rfl⟩
    exact ⟨(y : R), by push_cast; rfl⟩
  have hU' : ∀ j, ((p : ℕ) : R) ^ a ∣ U j := by
    intro j
    by_cases h : rep j = j
    · simp [hU, h]
    · exact hdvdcast _ (hcong j h).1
  have hV' : ∀ j, ((p : ℕ) : R) ^ a ∣ V j := by
    intro j
    by_cases h : rep j = j
    · simp [hV, h]
    · exact hdvdcast _ (hcong j h).2.1
  have hMQ : ∀ j e, M' j e = eval ![U j, V j] (Q (rep j) e) := by
    intro j e
    by_cases hg : (p : ℤ) ∣ mVal c F1 (pts (rep j))
    · have hrj : rep j = j := by
        rcases hrep j with h | h
        · exact h
        · exact absurd hg h
      have hU0 : U j = 0 := by simp [hU, hrj]
      simp only [hQ, hg, ite_true, eval_C]
      rw [hrj]
    · have hpa : (p : ℤ) ∣ (p : ℤ) ^ a := dvd_pow_self _ (by omega)
      have h1 : (p : ℤ) ∣ pts j 0 - pts (rep j) 0 := by
        by_cases h : rep j = j
        · simp [h]
        · exact hpa.trans (hcong j h).1
      have h2 : (p : ℤ) ∣ pts j 1 - pts (rep j) 1 := by
        by_cases h : rep j = j
        · simp [h]
        · exact hpa.trans (hcong j h).2.1
      have h3 : (p : ℤ) ∣ pts j 2 - pts (rep j) 2 := by
        by_cases h : rep j = j
        · simp [h]
        · exact (hcong j h).2.2
      have hw := hW (rep j) hg (pts j) (hz j) h1 h2 h3
      have e0 : eval ![U j, V j] (W (rep j)) = ((pts j 2 - pts (rep j) 2 : ℤ) : R) := hw.symm
      simp only [hQ, hg, ite_false, map_mul, map_pow, map_add, eval_C, eval_X, e0]
      simp only [hM', Matrix.map_apply, monoMat, Matrix.of_apply, Fin.prod_univ_three]
      simp [hU, hV]
  have hdvd := det_dvd_of_blocks M' rep (((p : ℕ) : R) ^ a) U V hU' hV' Q hMQ
  rw [← hν, hϖ0, zero_dvd_iff] at hdvd
  have hdet : (((monoMat pts es).det : ℤ) : R) = 0 := by
    have := Int.cast_det (R := R) (monoMat pts es)
    rw [this]
    exact hdvd
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ k)).1 hdet
  rw [← pow_mul]
  push_cast at this
  exact this


end L

end OVNS.Quant.Surf
