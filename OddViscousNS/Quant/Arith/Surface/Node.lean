import OddViscousNS.Quant.Arith.Surface.NodeWeight

/-!
# The vanishing of the determinants at a node (route L10)

`det_eq_zero`: at a node (points of a box on `F = 0`, `m ≠ 0`, `|m| ≤ Mb`, possibly all congruent
`(q^a, q^a, q)`) all `E × E` monomial determinants vanish, as soon as
`log ϑ + a log q (1 − 3/ϑ) > log P₀ + C₅ + (1 + 1199/ϑ) κ̂`.
-/

open Finset MvPolynomial

namespace OVNS.Quant.Surf

/-- The `𝔽_p`-point count, off `Bad`. -/
def PointCount (F : MvPolynomial (Fin 3) ℤ) (Bad : ℤ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ¬ (p : ℤ) ∣ Bad →
    ((univ.filter fun ξ : Fin 3 → ZMod p =>
      eval ξ (MvPolynomial.map (Int.castRingHom (ZMod p)) F) = 0).card : ℕ) ≤ p ^ 2 + 18 * p

/-- The data of a node. -/
structure NodeHyp (F : MvPolynomial (Fin 3) ℤ) (c : ℤ) (F1 : MvPolynomial (Fin 2) ℤ)
    (B : Fin 3 → ℝ) (Mb : ℝ) (P₀ q a : ℕ) (T : Finset (Fin 3 → ℤ)) : Prop where
  hT : ∀ x ∈ T, (∀ i, |(x i : ℝ)| ≤ B i) ∧ eval x F = 0 ∧ mVal c F1 x ≠ 0 ∧
    |(mVal c F1 x : ℝ)| ≤ Mb
  hq : q ≤ P₀
  ha : a = 0 ∨ q.Prime
  hcong : 1 ≤ a → ∀ x ∈ T, ¬ (q : ℤ) ∣ mVal c F1 x ∧ ∀ x' ∈ T,
    ((q : ℤ) ^ a ∣ x 0 - x' 0) ∧ ((q : ℤ) ^ a ∣ x 1 - x' 1) ∧ ((q : ℤ) ∣ x 2 - x' 2)

/-- `log E! ≤ 2 E^{3/2}`. -/
lemma log_factorial_le (E : ℕ) :
    Real.log (E.factorial : ℝ) ≤ 2 * (E : ℝ) ^ ((3 : ℝ) / 2) := by
  rcases Nat.eq_zero_or_pos E with rfl | hE
  · simp [Real.zero_rpow]
  have hE1 : (1 : ℝ) ≤ E := by exact_mod_cast hE
  have hE0 : (0 : ℝ) ≤ E := by linarith
  have h1 : Real.log (E.factorial : ℝ) ≤ E * Real.log E := by
    have : (E.factorial : ℝ) ≤ (E : ℝ) ^ E := by exact_mod_cast Nat.factorial_le_pow E
    have h := Real.log_le_log (by exact_mod_cast Nat.factorial_pos E) this
    rwa [Real.log_pow] at h
  have hs : 0 < Real.sqrt E := Real.sqrt_pos.2 (by linarith)
  have hs2 : Real.sqrt E ^ 2 = E := Real.sq_sqrt hE0
  have h2 : Real.log E ≤ 2 * Real.sqrt E := by
    have h3 := Real.log_le_sub_one_of_pos hs
    have h4 : Real.log E = 2 * Real.log (Real.sqrt E) := by
      conv_lhs => rw [← hs2]
      rw [Real.log_pow]
      norm_num
    linarith
  rw [rpow_three_halves hE0]
  calc _ ≤ (E : ℝ) * Real.log E := h1
    _ ≤ E * (2 * Real.sqrt E) := mul_le_mul_of_nonneg_left h2 hE0
    _ = 2 * Real.sqrt E ^ 2 * Real.sqrt E := by rw [hs2]; ring
    _ = _ := by ring

/-- The elementary estimate closing `det_eq_zero`. -/
lemma node_contradiction {R c₀ E κ ϑ logx logP C₄ a' S V F lq : ℝ} (hR : 0 < R) (hc : 2 / 3 ≤ c₀)
    (hϑ : 77 ≤ ϑ) (hE : ϑ * E ≤ R) (ha' : 0 ≤ a') (hlq : 0 ≤ lq)
    (h1 : c₀ * R * (logx - logP - C₄) + a' * V * lq ≤ F + S) (hF : F ≤ 2 * R)
    (hS : S ≤ c₀ * κ * R * (1 + 1199 / ϑ)) (hV : c₀ * R - 2 * E ≤ V) :
    logx + a' * lq * (1 - 3 / ϑ) ≤ logP + C₄ + 3 + (1 + 1199 / ϑ) * κ := by
  have hc0 : 0 < c₀ := by linarith
  have hϑ0 : 0 < ϑ := by linarith
  have hV2 : c₀ * R * (1 - 3 / ϑ) ≤ V := by
    refine le_trans ?_ hV
    have h2 : 2 * E ≤ 2 * R / ϑ := by
      rw [le_div_iff₀ hϑ0]
      linarith
    have h3 : c₀ * R * (3 / ϑ) = 3 * c₀ * R / ϑ := by ring
    have h4 : 2 * R / ϑ ≤ 3 * c₀ * R / ϑ := by
      apply div_le_div_of_nonneg_right _ hϑ0.le
      nlinarith
    have e : c₀ * R * (1 - 3 / ϑ) = c₀ * R - c₀ * R * (3 / ϑ) := by ring
    rw [e, h3]
    linarith
  have h5 : a' * lq * (c₀ * R * (1 - 3 / ϑ)) ≤ a' * V * lq := by
    have := mul_le_mul_of_nonneg_left hV2 (mul_nonneg ha' hlq)
    linarith
  have h6 : c₀ * R * (logx - logP - C₄ + a' * lq * (1 - 3 / ϑ)) ≤
      c₀ * R * (2 / c₀ + (1 + 1199 / ϑ) * κ) := by
    have e1 : c₀ * R * (2 / c₀ + (1 + 1199 / ϑ) * κ) = 2 * R + c₀ * κ * R * (1 + 1199 / ϑ) := by
      field_simp
    rw [e1]
    nlinarith
  have h7 := le_of_mul_le_mul_left h6 (by positivity)
  have h8 : 2 / c₀ ≤ 3 := by
    rw [div_le_iff₀ hc0]
    linarith
  linarith

set_option maxHeartbeats 1000000 in
/-- **Vanishing of the determinants at a node**: the core, for any exponent set of the right size
and weight. -/
theorem det_eq_zero_core : ∃ C₅ : ℝ, 0 ≤ C₅ ∧ ∀ (c : ℤ) (F1 F0 : MvPolynomial (Fin 2) ℤ)
    (F : MvPolynomial (Fin 3) ℤ) (Bad : ℤ) (B l : Fin 3 → ℝ) (κ Mb ϑ : ℝ) (P₀ q a : ℕ)
    (T : Finset (Fin 3 → ℤ)) (𝓔 : Finset (Fin 3 → ℕ)),
    F = C c * X 2 ^ 2 + rename Fin.castSucc F1 * X 2 + rename Fin.castSucc F0 →
    PointCount F Bad → Bad ≠ 0 → |(Bad : ℝ)| ≤ Mb → (∀ i, 1 ≤ B i) →
    (∀ i, l i = Real.log (B i)) → 0 ≤ κ →
    Real.log Mb ≤ P₀ → 18 ≤ P₀ → NodeHyp F c F1 B Mb P₀ q a T → 77 ≤ ϑ →
    ϑ ^ 2 ≤ (𝓔.card : ℝ) →
    ∑ e ∈ 𝓔, wt l e ≤ c0 * κ * ϑ ^ 3 * (1 + 1199 / ϑ) →
    Real.log P₀ + C₅ + (1 + 1199 / ϑ) * κ < Real.log ϑ + (a : ℝ) * Real.log q * (1 - 3 / ϑ) →
    ∀ pts : ↥𝓔 → Fin 3 → ℤ, (∀ j, pts j ∈ T) → (monoMat pts Subtype.val).det = 0 := by
  classical
  obtain ⟨C₄, hC₄, hPL⟩ := primes_lower
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C₄ + Real.log 2 + 3, by positivity, ?_⟩
  intro c F1 F0 F Bad B l κ Mb ϑ P₀ q a T 𝓔 hF hPC hBad hBadMb hB hlB hκ hMb hP₀ hN hϑ hE hS hnum
    pts hpts
  by_contra hdet
  have hϑ0 : 0 < ϑ := by linarith
  have hcard : Fintype.card ↥𝓔 = 𝓔.card := Fintype.card_coe _
  set E : ℕ := 𝓔.card with hEdef
  have hT := fun j => hN.hT (pts j) (hpts j)
  set x : ℕ := ⌊ϑ⌋₊ with hx
  have hx0 : (x : ℝ) ≤ ϑ := Nat.floor_le hϑ0.le
  have hx1 : 1 ≤ x := Nat.le_floor (by norm_num; linarith)
  have hxϑ : ϑ / 2 ≤ x := by
    have := Nat.lt_floor_add_one ϑ
    have h1 : (1 : ℝ) ≤ x := by exact_mod_cast hx1
    linarith
  have hxE : x ^ 2 ≤ E := by
    have : (x : ℝ) ^ 2 ≤ E := (pow_le_pow_left₀ (Nat.cast_nonneg _) hx0 2).trans hE
    exact_mod_cast this
  -- the primes
  have hex : ∀ p : ℕ, ∃ n : ℕ, p ∈ nodePrimes Bad P₀ x →
      ((p : ℤ) ^ n ∣ (monoMat pts Subtype.val).det ∧
        c0 * (((univ.filter fun j => ¬ (p : ℤ) ∣ mVal c F1 (pts j)).card : ℕ) : ℝ) ^
            ((3 : ℝ) / 2) / Real.sqrt ((p : ℝ) ^ 2 + 18 * p)
          - 2 * (((univ.filter fun j => ¬ (p : ℤ) ∣ mVal c F1 (pts j)).card : ℕ) : ℝ) ≤ n) := by
    intro p
    by_cases hp : p ∈ nodePrimes Bad P₀ x
    · obtain ⟨-, hpp, hpB⟩ := mem_nodePrimes.1 hp
      have : Fact p.Prime := ⟨hpp⟩
      obtain ⟨n, h1, h2⟩ := prime_val c F1 F0 F hF p pts Subtype.val (fun j => (hT j).2.1)
        (hPC p hpB)
      exact ⟨n, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose n hn using hex
  have hlow := hPL (J := ↥𝓔) (fun j => mVal c F1 (pts j)) Bad Mb P₀ x n (fun j => (hT j).2.2.1)
    (fun j => (hT j).2.2.2) hBad hBadMb hMb hP₀ hx1 (by rw [hcard]; exact hxE)
    (fun p hp => (hn p hp).2)
  rw [hcard] at hlow
  set D := (monoMat pts Subtype.val).det with hD
  set S := nodePrimes Bad P₀ x with hSdef
  have hSpr : ∀ p ∈ S, p.Prime := fun p hp => (mem_nodePrimes.1 hp).2.1
  -- the sum of all valuations
  have hcomb : (a : ℝ) * (Vs E : ℝ) * Real.log q + ∑ p ∈ S, (n p : ℝ) * Real.log p ≤
      Real.log |(D : ℝ)| := by
    by_cases ha0 : a = 0
    · subst ha0
      simpa using sum_log_le_log_abs D hdet S hSpr n fun p hp => (hn p hp).1
    have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.2 ha0
    have hqp : q.Prime := hN.ha.resolve_left ha0
    have hqS : q ∉ S := fun h => by
      have := (mem_nodePrimes.1 h).1.1
      have := hN.hq
      omega
    have hqD : (q : ℤ) ^ (a * Vs E) ∣ D := by
      have := q_val c F1 F0 F hF q a hqp ha1 pts Subtype.val (fun j => (hT j).2.1)
        (fun j => (hN.hcong ha1 _ (hpts j)).1) (fun j j' => (hN.hcong ha1 _ (hpts j)).2 _ (hpts j'))
      rwa [hcard] at this
    have h := sum_log_le_log_abs D hdet (insert q S)
      (fun p hp => (mem_insert.1 hp).elim (fun e => e ▸ hqp) (hSpr p))
      (Function.update n q (a * Vs E)) (fun p hp => by
        rcases mem_insert.1 hp with rfl | hp'
        · rw [Function.update_self]; exact hqD
        · have hne : p ≠ q := fun e => hqS (e ▸ hp')
          rw [Function.update_of_ne hne]
          exact (hn p hp').1)
    rw [Finset.sum_insert hqS, Function.update_self] at h
    have e2 : ∑ p ∈ S, (Function.update n q (a * Vs E) p : ℝ) * Real.log p =
        ∑ p ∈ S, (n p : ℝ) * Real.log p := by
      refine sum_congr rfl fun p hp => ?_
      have hne : p ≠ q := fun e => hqS (e ▸ hp)
      rw [Function.update_of_ne hne]
    rw [e2] at h
    push_cast at h
    exact h
  -- the upper bound
  have hup := log_abs_det_le pts (Subtype.val : ↥𝓔 → Fin 3 → ℕ) B hB
    (fun j i => (hT j).1 i) hdet
  have hll : (fun i => Real.log (B i)) = l := funext fun i => (hlB i).symm
  rw [hll, hcard, Finset.sum_coe_sort 𝓔 (fun e => wt l e)] at hup
  -- comparison
  have hEpos : (1 : ℝ) ≤ E := by
    have h1 : (1 : ℝ) ≤ ϑ ^ 2 := by nlinarith
    linarith
  have hE0 : (0 : ℝ) ≤ E := by linarith
  set R := (E : ℝ) ^ ((3 : ℝ) / 2) with hR
  have hsE : ϑ ≤ Real.sqrt E := Real.le_sqrt_of_sq_le hE
  have hsE2 : Real.sqrt E ^ 2 = E := Real.sq_sqrt hE0
  have hR3 : R = E * Real.sqrt E := by
    rw [hR, rpow_three_halves hE0]
    nlinarith
  have hR0 : 0 < R := by
    rw [hR3]
    have : 0 < Real.sqrt E := by linarith
    positivity
  have hϑ3 : ϑ ^ 3 ≤ R := by
    rw [hR, rpow_three_halves hE0]
    exact pow_le_pow_left₀ hϑ0.le hsE 3
  have hϑE : ϑ * E ≤ R := by
    rw [hR3, mul_comm]
    exact mul_le_mul_of_nonneg_left hsE hE0
  have hS' : ∑ e ∈ 𝓔, wt l e ≤ c0 * κ * R * (1 + 1199 / ϑ) := by
    refine hS.trans ?_
    have : 0 ≤ c0 * κ := mul_nonneg c0_pos.le hκ
    have h1 : c0 * κ * ϑ ^ 3 ≤ c0 * κ * R :=
      mul_le_mul_of_nonneg_left hϑ3 this
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hV : c0 * R - 2 * E ≤ Vs E := Vs_lower E
  have hF' : Real.log (E.factorial : ℝ) ≤ 2 * R := log_factorial_le E
  have hq0 : 0 ≤ Real.log (q : ℝ) := Real.log_natCast_nonneg q
  have hmain := node_contradiction (c₀ := c0) (E := (E : ℝ)) (κ := κ) (a' := (a : ℝ))
    (lq := Real.log (q : ℝ)) (logx := Real.log x) (logP := Real.log P₀) (C₄ := C₄)
    (F := Real.log (E.factorial : ℝ)) (S := ∑ e ∈ 𝓔, wt l e) (V := (Vs E : ℝ))
    hR0 two_thirds_le_c0 hϑ hϑE (Nat.cast_nonneg _) hq0
    (by linarith) hF' hS' hV
  have hlogx : Real.log ϑ - Real.log 2 ≤ Real.log x := by
    have h1 : Real.log (ϑ / 2) ≤ Real.log x := Real.log_le_log (by positivity) hxϑ
    rwa [Real.log_div hϑ0.ne' (by norm_num)] at h1
  linarith

end OVNS.Quant.Surf
