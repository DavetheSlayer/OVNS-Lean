import OddViscousNS.Quant.Arith.Weighted.Defs

/-!
# The point count of the surface modulo `p` (route L8)

`surface_card_mod_le`: the conic bundle `surfacePoly` has at most `p² + 18p` points over `𝔽_p`, off the
explicit bad integer `2Δg n_j(n_i² + n_j²)`.  This replaces Noether forms + Lang–Weil for the family.
-/

open Finset

namespace OVNS.Quant.Surf

theorem conic_card_le (p : ℕ) [Fact p.Prime] (a M : ZMod p) (ha : a ≠ 0) (hM : M ≠ 0)
    (hp2 : (2 : ZMod p) ≠ 0) :
    (univ.filter fun v : ZMod p × ZMod p => v.1 ^ 2 - a * v.2 ^ 2 = M).card ≤ p + 2 := by
  classical
  set S := univ.filter fun v : ZMod p × ZMod p => v.1 ^ 2 - a * v.2 ^ 2 = M with hS
  rcases S.eq_empty_or_nonempty with h0 | ⟨v₀, hv₀⟩
  · rw [h0]; simp
  obtain ⟨s₀, w₀⟩ := v₀
  have h₀ : s₀ ^ 2 - a * w₀ ^ 2 = M := by simpa [hS] using hv₀
  -- slope map on the remaining points
  set φ : ZMod p × ZMod p → Option (ZMod p) := fun v =>
    if v.1 = s₀ then none else some ((v.2 - w₀) / (v.1 - s₀)) with hφ
  have hinj : Set.InjOn φ ((S.erase (s₀, w₀) : Finset _) : Set (ZMod p × ZMod p)) := by
    rintro ⟨s, w⟩ hv ⟨s', w'⟩ hv' he
    simp only [hS, coe_erase, coe_filter, mem_univ, true_and, Set.mem_sdiff, Set.mem_ofPred_eq,
      Set.mem_singleton_iff, Prod.mk.injEq, not_and] at hv hv'
    obtain ⟨h1, hne⟩ := hv
    obtain ⟨h1', hne'⟩ := hv'
    simp only [hφ] at he
    by_cases hs : s = s₀
    · by_cases hs' : s' = s₀
      · -- vertical chord: `w, w'` both equal `-w₀`
        subst hs; subst hs'
        have hw : (w - w₀) * (w + w₀) = 0 := by
          have : a * ((w - w₀) * (w + w₀)) = 0 := by linear_combination h₀ - h1
          exact (mul_eq_zero.1 this).resolve_left ha
        have hw' : (w' - w₀) * (w' + w₀) = 0 := by
          have : a * ((w' - w₀) * (w' + w₀)) = 0 := by linear_combination h₀ - h1'
          exact (mul_eq_zero.1 this).resolve_left ha
        have e1 : w + w₀ = 0 := (mul_eq_zero.1 hw).resolve_left fun h =>
          hne rfl (sub_eq_zero.1 h)
        have e2 : w' + w₀ = 0 := (mul_eq_zero.1 hw').resolve_left fun h =>
          hne' rfl (sub_eq_zero.1 h)
        have : w = w' := by linear_combination e1 - e2
        rw [this]
      · simp [hs, hs'] at he
    · by_cases hs' : s' = s₀
      · simp [hs, hs'] at he
      · simp only [hs, hs', ite_false, Option.some.injEq] at he
        set l := (w - w₀) / (s - s₀) with hl
        have hd : s - s₀ ≠ 0 := sub_ne_zero.2 hs
        have hd' : s' - s₀ ≠ 0 := sub_ne_zero.2 hs'
        have e1 : w - w₀ = l * (s - s₀) := by rw [hl]; field_simp
        have e2 : w' - w₀ = l * (s' - s₀) := by rw [he]; field_simp
        -- both chords satisfy the same linear relation
        have k1 : (s - s₀) * ((s - s₀) * (1 - a * l ^ 2) + 2 * (s₀ - a * l * w₀)) = 0 := by
          have hw : w = w₀ + l * (s - s₀) := by linear_combination e1
          rw [hw] at h1
          linear_combination h1 - h₀
        have k2 : (s' - s₀) * ((s' - s₀) * (1 - a * l ^ 2) + 2 * (s₀ - a * l * w₀)) = 0 := by
          have hw : w' = w₀ + l * (s' - s₀) := by linear_combination e2
          rw [hw] at h1'
          linear_combination h1' - h₀
        have k1' := (mul_eq_zero.1 k1).resolve_left hd
        have k2' := (mul_eq_zero.1 k2).resolve_left hd'
        have k3 : (s - s') * (1 - a * l ^ 2) = 0 := by linear_combination k1' - k2'
        by_cases hss : s = s'
        · subst hss
          have : w = w' := by linear_combination e1 - e2
          rw [this]
        · have h1l : 1 - a * l ^ 2 = 0 := (mul_eq_zero.1 k3).resolve_left (sub_ne_zero.2 hss)
          have h2l : s₀ - a * l * w₀ = 0 := by
            have : 2 * (s₀ - a * l * w₀) = 0 := by
              rw [h1l, mul_zero, zero_add] at k1'
              exact k1'
            exact (mul_eq_zero.1 this).resolve_left hp2
          exfalso
          apply hM
          rw [← h₀]
          have es : s₀ = a * l * w₀ := sub_eq_zero.1 h2l
          have : s₀ ^ 2 - a * w₀ ^ 2 = a * w₀ ^ 2 * (a * l ^ 2 - 1) := by rw [es]; ring
          rw [this]
          have : a * l ^ 2 - 1 = 0 := by linear_combination -h1l
          rw [this, mul_zero]
  have hcard : (S.erase (s₀, w₀)).card ≤ Fintype.card (Option (ZMod p)) :=
    card_le_card_of_injOn φ (fun _ _ => by simp) hinj
  have h2 : Fintype.card (Option (ZMod p)) = p + 1 := by
    rw [Fintype.card_option, ZMod.card]
  have h3 := card_le_card_of_injOn (s := S) (t := insert (s₀, w₀) (S.erase (s₀, w₀))) id
    (fun x hx => by
      by_cases h : x = (s₀, w₀)
      · simp [h]
      · simp only [id, coe_insert, coe_erase, Set.mem_insert_iff, Set.mem_sdiff, mem_coe,
          Set.mem_singleton_iff]
        exact Or.inr ⟨hx, h⟩)
    (fun _ _ _ _ h => h)
  have h4 := card_insert_le (s₀, w₀) (S.erase (s₀, w₀))
  omega


section Field

variable {K : Type*} [_root_.Field K]

/-- The value of the surface polynomial. -/
def Fv (D z n i j s G x y w : K) : K :=
  4 * G ^ 2 * j ^ 2 * w ^ 2 +
    ((-(2 * D * G ^ 2) * x ^ 2 * y - D * G ^ 3 * x ^ 2 - 2 * D * G ^ 2 * s * z * x - D * G * z ^ 2
      - 2 * n ^ 2 * y) - 2 * G * i * w) ^ 2 + 4 * j ^ 2 * n ^ 2 * y ^ 2
    - 4 * G ^ 2 * j ^ 2 * D * (G * x + s * z + x * y) ^ 2

/-- `T(x,y)` (the polynomial `twoGL`). -/
def Tv (D z n s G x y : K) : K :=
  -(2 * D * G ^ 2) * x ^ 2 * y - D * G ^ 3 * x ^ 2 - 2 * D * G ^ 2 * s * z * x - D * G * z ^ 2
    - 2 * n ^ 2 * y

def aC (D n ν G x : K) : K :=
  -4 * (D ^ 2 * G ^ 4 * x ^ 4 + 2 * D * G ^ 2 * n ^ 2 * x ^ 2 - D * G ^ 2 * ν * x ^ 2 + n ^ 4
    + n ^ 2 * ν)

def bC (D z n ν s G x : K) : K :=
  -4 * D * G * (D * G ^ 4 * x ^ 4 + 2 * D * G ^ 3 * s * z * x ^ 3 + D * G ^ 2 * z ^ 2 * x ^ 2
    + G ^ 2 * n ^ 2 * x ^ 2 - 2 * G ^ 2 * ν * x ^ 2 + 2 * G * n ^ 2 * s * z * x
    - 2 * G * ν * s * z * x + n ^ 2 * z ^ 2)

def eC (D z ν s G x : K) : K :=
  -D * G ^ 2 * (D * G ^ 4 * x ^ 4 + 4 * D * G ^ 3 * s * z * x ^ 3
    + 4 * D * G ^ 2 * s ^ 2 * z ^ 2 * x ^ 2 + 2 * D * G ^ 2 * z ^ 2 * x ^ 2 + 4 * D * G * s * z ^ 3 * x
    + D * z ^ 4 - 4 * G ^ 2 * ν * x ^ 2 - 8 * G * ν * s * z * x - 4 * ν * s ^ 2 * z ^ 2)

/-- Completing the square in `X₃`. -/
lemma square_id (D z n i j s G x y w : K) :
    (2 * (4 * G ^ 2 * (i ^ 2 + j ^ 2)) * w - 4 * G * i * Tv D z n s G x y) ^ 2 =
      (4 * G * j) ^ 2 * (aC D n (i ^ 2 + j ^ 2) G x * y ^ 2 + bC D z n (i ^ 2 + j ^ 2) s G x * y
        + eC D z (i ^ 2 + j ^ 2) s G x)
      + 4 * (4 * G ^ 2 * (i ^ 2 + j ^ 2)) * Fv D z n i j s G x y w := by
  simp only [Fv, Tv, aC, bC, eC]
  ring

/-- The discriminant of the fibre conic. -/
lemma disc_id (D z n s G x : K) (hs : s ^ 2 = 1) :
    bC D z n (D * z ^ 2 - n ^ 2) s G x ^ 2
      - 4 * aC D n (D * z ^ 2 - n ^ 2) G x * eC D z (D * z ^ 2 - n ^ 2) s G x =
      16 * D ^ 2 * G ^ 2 * (D * z ^ 2 - n ^ 2) * (z - G * x) ^ 2 * (z + G * x) ^ 2 *
        (D * G ^ 2 * x ^ 2 + 3 * n ^ 2) := by
  simp only [aC, bC, eC]
  have h3 : s ^ 3 = s := by rw [pow_succ, hs, one_mul]
  have h4 : s ^ 4 = 1 := by rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hs, one_pow]
  ring_nf
  simp only [hs]
  ring

end Field

section Count

open Polynomial in
/-- The fibre over a good `x` injects into a nondegenerate conic. -/
lemma fibre_good (p : ℕ) [Fact p.Prime] (D z n i j s G x : ZMod p) (hG : G ≠ 0) (hj : j ≠ 0)
    (hν : i ^ 2 + j ^ 2 ≠ 0) (h2 : (2 : ZMod p) ≠ 0)
    (ha : aC D n (i ^ 2 + j ^ 2) G x ≠ 0)
    (hM : bC D z n (i ^ 2 + j ^ 2) s G x ^ 2 - 4 * aC D n (i ^ 2 + j ^ 2) G x *
      eC D z (i ^ 2 + j ^ 2) s G x ≠ 0) :
    (univ.filter fun v : ZMod p × ZMod p => Fv D z n i j s G x v.1 v.2 = 0).card ≤ p + 2 := by
  classical
  set ν := i ^ 2 + j ^ 2 with hνd
  set a := aC D n ν G x with hadef
  set b := bC D z n ν s G x with hbdef
  set e := eC D z ν s G x with hedef
  set c : ZMod p := 4 * G ^ 2 * ν with hc
  have h4 : (4 : ZMod p) ≠ 0 := by
    have : (4 : ZMod p) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hc0 : c ≠ 0 := mul_ne_zero (mul_ne_zero h4 (pow_ne_zero 2 hG)) hν
  have hd0 : 4 * G * j ≠ 0 := mul_ne_zero (mul_ne_zero h4 hG) hj
  set φ : ZMod p × ZMod p → ZMod p × ZMod p := fun v =>
    (2 * a * v.1 + b, (2 * c * v.2 - 4 * G * i * Tv D z n s G x v.1) / (4 * G * j)) with hφ
  have hmaps : ∀ v ∈ (univ.filter fun v : ZMod p × ZMod p => Fv D z n i j s G x v.1 v.2 = 0),
      φ v ∈ (univ.filter fun v : ZMod p × ZMod p => v.1 ^ 2 - (4 * a) * v.2 ^ 2 = b ^ 2 - 4 * a * e) := by
    rintro ⟨y, w⟩ hv
    have hF : Fv D z n i j s G x y w = 0 := by simpa using hv
    have hsq := square_id D z n i j s G x y w
    rw [hF, mul_zero, add_zero, ← hνd] at hsq
    simp only [mem_filter, mem_univ, true_and, hφ, div_pow]
    rw [hsq, mul_div_assoc, ← mul_div_assoc, mul_comm ((4 * G * j) ^ 2),
      mul_div_assoc, div_self (pow_ne_zero 2 hd0), mul_one]
    ring
  have hinj : Set.InjOn φ ((univ.filter fun v : ZMod p × ZMod p =>
      Fv D z n i j s G x v.1 v.2 = 0 : Finset _) : Set (ZMod p × ZMod p)) := by
    rintro ⟨y, w⟩ _ ⟨y', w'⟩ _ he
    simp only [hφ, Prod.mk.injEq] at he
    obtain ⟨h1, h2'⟩ := he
    have h2a : 2 * a ≠ 0 := mul_ne_zero h2 ha
    have hy : y = y' := by
      have : 2 * a * (y - y') = 0 := by linear_combination h1
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h2a)
    subst hy
    have h3 := (div_left_inj' hd0).1 h2'
    have : 2 * c * (w - w') = 0 := by linear_combination h3
    exact Prod.ext rfl (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (mul_ne_zero h2 hc0)))
  calc _ ≤ _ := card_le_card_of_injOn φ hmaps hinj
    _ ≤ p + 2 := conic_card_le p (4 * a) _ (mul_ne_zero h4 ha) hM h2

open Polynomial in
/-- Every fibre has at most `2p` points when `c ≠ 0`. -/
lemma fibre_any (p : ℕ) [Fact p.Prime] (D z n i j s G x : ZMod p) (hG : G ≠ 0)
    (hν : i ^ 2 + j ^ 2 ≠ 0) (h2 : (2 : ZMod p) ≠ 0) :
    (univ.filter fun v : ZMod p × ZMod p => Fv D z n i j s G x v.1 v.2 = 0).card ≤ 2 * p := by
  classical
  set c : ZMod p := 4 * G ^ 2 * (i ^ 2 + j ^ 2) with hc
  have h4 : (4 : ZMod p) ≠ 0 := by
    have : (4 : ZMod p) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hc0 : c ≠ 0 := mul_ne_zero (mul_ne_zero h4 (pow_ne_zero 2 hG)) hν
  -- for each `y` the polynomial in `w`
  set Q : ZMod p → (ZMod p)[X] := fun y =>
    C c * X ^ 2 + C (-(4 * G * i) * Tv D z n s G x y) * X +
      C (Tv D z n s G x y ^ 2 + 4 * j ^ 2 * n ^ 2 * y ^ 2
        - 4 * G ^ 2 * j ^ 2 * D * (G * x + s * z + x * y) ^ 2) with hQ
  have hquad : ∀ α β γ : ZMod p, (C α * X ^ 2 + C β * X + C γ : (ZMod p)[X]).coeff 2 = α := by
    intro α β γ
    simp [coeff_X_pow]
  have hQ0 : ∀ y, Q y ≠ 0 := by
    intro y h0
    have := congrArg (fun P => P.coeff 2) h0
    simp only [hQ, hquad, coeff_zero] at this
    exact hc0 this
  have hQd : ∀ y, (Q y).natDegree ≤ 2 := by
    intro y
    simp only [hQ]
    compute_degree
  have hFv : ∀ y w, Fv D z n i j s G x y w = (Q y).eval w := by
    intro y w
    simp only [hQ, eval_add, eval_mul, eval_C, eval_pow, eval_X, Fv, Tv, hc]
    ring
  have hle : (univ.filter fun v : ZMod p × ZMod p => Fv D z n i j s G x v.1 v.2 = 0).card ≤
      ((univ : Finset (ZMod p)).sigma fun y => (Q y).roots.toFinset).card := by
    refine card_le_card_of_injOn (fun v => (⟨v.1, v.2⟩ : Σ _ : ZMod p, ZMod p)) ?_ ?_
    · rintro ⟨y, w⟩ hv
      have hF : Fv D z n i j s G x y w = 0 := by simpa using hv
      simp only [coe_sigma, mem_coe, Set.mem_sigma_iff, Set.mem_univ, true_and,
        coe_univ, Multiset.mem_toFinset]
      exact (mem_roots (hQ0 y)).2 (by rw [IsRoot, ← hFv]; exact hF)
    · rintro ⟨y, w⟩ _ ⟨y', w'⟩ _ h
      simp only [Sigma.mk.injEq] at h
      obtain ⟨rfl, h⟩ := h
      simp only [heq_eq_eq] at h
      rw [h]
  refine hle.trans ?_
  rw [card_sigma]
  calc ∑ y : ZMod p, (Q y).roots.toFinset.card ≤ ∑ _y : ZMod p, 2 :=
        Finset.sum_le_sum fun y _ => (Multiset.toFinset_card_le _).trans
          ((card_roots' _).trans (hQd y))
    _ = 2 * p := by simp [ZMod.card, mul_comm]

open Polynomial in
/-- **Sharp point count** of the conic bundle. -/
theorem fv_card_le (p : ℕ) [Fact p.Prime] (D z n i j s G : ZMod p) (hD : D ≠ 0) (hG : G ≠ 0)
    (hj : j ≠ 0) (hν : i ^ 2 + j ^ 2 ≠ 0) (h2 : (2 : ZMod p) ≠ 0)
    (hrel : i ^ 2 + j ^ 2 = D * z ^ 2 - n ^ 2) (hs : s ^ 2 = 1) :
    (univ.filter fun ξ : Fin 3 → ZMod p =>
      Fv D z n i j s G (ξ 0) (ξ 1) (ξ 2) = 0).card ≤ p ^ 2 + 18 * p := by
  classical
  set ν := i ^ 2 + j ^ 2 with hνd
  have h4 : (4 : ZMod p) ≠ 0 := by
    have : (4 : ZMod p) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  set Pa : (ZMod p)[X] := C (-4 * D ^ 2 * G ^ 4) * X ^ 4 +
    C (-4 * (2 * D * G ^ 2 * n ^ 2 - D * G ^ 2 * ν)) * X ^ 2 + C (-4 * (n ^ 4 + n ^ 2 * ν)) with hPa
  set L1 : (ZMod p)[X] := C G * X - C z with hL1
  set L2 : (ZMod p)[X] := C G * X + C z with hL2
  set Q2 : (ZMod p)[X] := C (D * G ^ 2) * X ^ 2 + C (3 * n ^ 2) with hQ2
  have hPa0 : Pa ≠ 0 := by
    intro h0
    have := congrArg (fun P => P.coeff 4) h0
    have hq4 : ∀ α β γ : ZMod p, (C α * X ^ 4 + C β * X ^ 2 + C γ : (ZMod p)[X]).coeff 4 = α := by
      intro α β γ
      simp [coeff_X_pow]
    have e : Pa.coeff 4 = -4 * D ^ 2 * G ^ 4 := hq4 _ _ _
    simp only [e, coeff_zero] at this
    exact (mul_ne_zero (mul_ne_zero (neg_ne_zero.2 h4) (pow_ne_zero 2 hD)) (pow_ne_zero 4 hG)) this
  have hL10 : L1 ≠ 0 := by
    intro h0
    have := congrArg (fun P => P.coeff 1) h0
    simp [hL1, coeff_C] at this
    exact hG this
  have hL20 : L2 ≠ 0 := by
    intro h0
    have := congrArg (fun P => P.coeff 1) h0
    simp [hL2, coeff_C] at this
    exact hG this
  have hQ20 : Q2 ≠ 0 := by
    intro h0
    have := congrArg (fun P => P.coeff 2) h0
    have hq2 : ∀ α β : ZMod p, (C α * X ^ 2 + C β : (ZMod p)[X]).coeff 2 = α := by
      intro α β
      simp [coeff_X_pow]
    have e : Q2.coeff 2 = D * G ^ 2 := hq2 _ _
    simp only [e, coeff_zero] at this
    exact mul_ne_zero hD (pow_ne_zero 2 hG) this
  set Pol := Pa * L1 * L2 * Q2 with hPol
  have hPol0 : Pol ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero hPa0 hL10) hL20) hQ20
  have hdeg : Pol.natDegree ≤ 8 := by
    have hd1 : Pa.natDegree ≤ 4 := by simp only [hPa]; compute_degree
    have hd2 : L1.natDegree ≤ 1 := by simp only [hL1]; compute_degree
    have hd3 : L2.natDegree ≤ 1 := by simp only [hL2]; compute_degree
    have hd4 : Q2.natDegree ≤ 2 := by simp only [hQ2]; compute_degree
    calc Pol.natDegree ≤ (Pa * L1 * L2).natDegree + Q2.natDegree := natDegree_mul_le
      _ ≤ (Pa * L1).natDegree + L2.natDegree + Q2.natDegree := by
          gcongr; exact natDegree_mul_le
      _ ≤ Pa.natDegree + L1.natDegree + L2.natDegree + Q2.natDegree := by
          gcongr; exact natDegree_mul_le
      _ ≤ 8 := by omega
  set Zs : Finset (ZMod p) := Pol.roots.toFinset with hZs
  have hZcard : Zs.card ≤ 8 :=
    (Multiset.toFinset_card_le _).trans ((card_roots' _).trans hdeg)
  have hgood : ∀ x, x ∉ Zs →
      (univ.filter fun v : ZMod p × ZMod p => Fv D z n i j s G x v.1 v.2 = 0).card ≤ p + 2 := by
    intro x hx
    have hne : Pol.eval x ≠ 0 := by
      intro h0
      exact hx (Multiset.mem_toFinset.2 ((mem_roots hPol0).2 h0))
    simp only [hPol, eval_mul] at hne
    have e1 : Pa.eval x = aC D n ν G x := by
      simp only [hPa, eval_add, eval_mul, eval_C, eval_pow, eval_X, aC]
      ring
    have e2 : L1.eval x = G * x - z := by simp [hL1]
    have e3 : L2.eval x = G * x + z := by simp [hL2]
    have e4 : Q2.eval x = D * G ^ 2 * x ^ 2 + 3 * n ^ 2 := by simp [hQ2]
    rw [e1, e2, e3, e4] at hne
    have ha : aC D n ν G x ≠ 0 := fun h => hne (by rw [h]; ring)
    have hb1 : G * x - z ≠ 0 := fun h => hne (by rw [h]; ring)
    have hb2 : G * x + z ≠ 0 := fun h => hne (by rw [h]; ring)
    have hb3 : D * G ^ 2 * x ^ 2 + 3 * n ^ 2 ≠ 0 := fun h => hne (by rw [h]; ring)
    refine fibre_good p D z n i j s G x hG hj hν h2 ha ?_
    rw [← hνd, hrel, disc_id D z n s G x hs, ← hrel]
    have e16 : (16 : ZMod p) = 4 * 4 := by norm_num
    have hz1 : z - G * x ≠ 0 := fun h => hb1 (by linear_combination -h)
    have hz2 : z + G * x ≠ 0 := fun h => hb2 (by linear_combination h)
    rw [e16]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero h4 h4) (pow_ne_zero 2 hD)) (pow_ne_zero 2 hG)) hν) (pow_ne_zero 2 hz1))
      (pow_ne_zero 2 hz2)) hb3
  have hall : ∀ x, (univ.filter fun v : ZMod p × ZMod p =>
      Fv D z n i j s G x v.1 v.2 = 0).card ≤ (p + 2) + if x ∈ Zs then 2 * p else 0 := by
    intro x
    by_cases hx : x ∈ Zs
    · have := fibre_any p D z n i j s G x hG hν h2
      simp only [hx, ite_true]
      omega
    · simp only [hx, ite_false, add_zero]
      exact hgood x hx
  -- assemble over `x`
  have hle : (univ.filter fun ξ : Fin 3 → ZMod p =>
      Fv D z n i j s G (ξ 0) (ξ 1) (ξ 2) = 0).card ≤
      ((univ : Finset (ZMod p)).sigma fun x =>
        univ.filter fun v : ZMod p × ZMod p => Fv D z n i j s G x v.1 v.2 = 0).card := by
    refine card_le_card_of_injOn (fun ξ => (⟨ξ 0, (ξ 1, ξ 2)⟩ : Σ _ : ZMod p, ZMod p × ZMod p)) ?_ ?_
    · intro ξ hξ
      have hF : Fv D z n i j s G (ξ 0) (ξ 1) (ξ 2) = 0 := by simpa using hξ
      simpa using hF
    · intro ξ _ ξ' _ h
      simp only [Sigma.mk.injEq, Prod.mk.injEq, heq_eq_eq] at h
      obtain ⟨h0, h1, h2'⟩ := h
      funext l
      fin_cases l
      · exact h0
      · exact h1
      · exact h2'
  refine hle.trans ?_
  rw [card_sigma]
  calc ∑ x : ZMod p, (univ.filter fun v : ZMod p × ZMod p => Fv D z n i j s G x v.1 v.2 = 0).card
      ≤ ∑ x : ZMod p, ((p + 2) + if x ∈ Zs then 2 * p else 0) :=
        Finset.sum_le_sum fun x _ => hall x
    _ = p * (p + 2) + Zs.card * (2 * p) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, card_univ, ZMod.card, smul_eq_mul,
          Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul]
    _ ≤ p ^ 2 + 18 * p := by nlinarith

/-- The same statement for `surfacePoly`, off the bad integer `2Δg n_j(n_i² + n_j²)`. -/
theorem surface_card_mod_le (Δ z n3 ni nj s3 g : ℤ)
    (hnorm : ni ^ 2 + nj ^ 2 + n3 ^ 2 = Δ * z ^ 2) (hs3 : s3 = 1 ∨ s3 = -1) (p : ℕ) [Fact p.Prime]
    (hbad : ¬ (p : ℤ) ∣ 2 * Δ * g * nj * (ni ^ 2 + nj ^ 2)) :
    ((univ.filter fun ξ : Fin 3 → ZMod p =>
      MvPolynomial.eval ξ (MvPolynomial.map (Int.castRingHom (ZMod p))
        (OVNS.Quant.surfacePoly Δ z n3 ni nj s3 g)) = 0).card : ℕ) ≤ p ^ 2 + 18 * p := by
  classical
  have hcast : ∀ a : ℤ, (a : ZMod p) = 0 ↔ (p : ℤ) ∣ a := fun a =>
    ZMod.intCast_zmod_eq_zero_iff_dvd a p
  have hp : (p : ℤ) ∣ 2 * Δ * g * nj * (ni ^ 2 + nj ^ 2) ↔ False := by simpa using hbad
  have hne : ((2 * Δ * g * nj * (ni ^ 2 + nj ^ 2) : ℤ) : ZMod p) ≠ 0 :=
    fun h => hbad ((hcast _).1 h)
  push_cast at hne
  have h2 : (2 : ZMod p) ≠ 0 := fun h => hne (by rw [h]; ring)
  have hD : (Δ : ZMod p) ≠ 0 := fun h => hne (by rw [h]; ring)
  have hG : (g : ZMod p) ≠ 0 := fun h => hne (by rw [h]; ring)
  have hj : (nj : ZMod p) ≠ 0 := fun h => hne (by rw [h]; ring)
  have hν : (ni : ZMod p) ^ 2 + (nj : ZMod p) ^ 2 ≠ 0 := fun h => hne (by rw [h]; ring)
  have hrel : (ni : ZMod p) ^ 2 + (nj : ZMod p) ^ 2 = Δ * z ^ 2 - n3 ^ 2 := by
    have := congrArg (fun a : ℤ => (a : ZMod p)) hnorm
    push_cast at this
    linear_combination this
  have hs : (s3 : ZMod p) ^ 2 = 1 := by
    rcases hs3 with rfl | rfl <;> simp
  have key := fv_card_le p (Δ : ZMod p) z n3 ni nj s3 g hD hG hj hν h2 hrel hs
  refine le_trans (le_of_eq ?_) key
  congr 1
  refine Finset.filter_congr fun ξ _ => ?_
  have : MvPolynomial.eval ξ (MvPolynomial.map (Int.castRingHom (ZMod p))
      (OVNS.Quant.surfacePoly Δ z n3 ni nj s3 g)) =
      Fv (Δ : ZMod p) z n3 ni nj s3 g (ξ 0) (ξ 1) (ξ 2) := by
    simp only [OVNS.Quant.surfacePoly, Fv, map_add, map_sub, map_mul, map_neg, map_pow,
      MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.eval_C, MvPolynomial.eval_X, map_ofNat,
      Int.coe_castRingHom]
  rw [this]

end Count

end OVNS.Quant.Surf


