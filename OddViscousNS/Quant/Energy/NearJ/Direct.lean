import OddViscousNS.Quant.Energy.NearJ.Moments

/-!
# J1, part 3: the direct high-output count

`Near/Profiles.lean` bounds the outputs `K > q^{1/5}` by the trivial `208 K⁻⁵`, which only gives
`P ≲ q^{−3/10+δ}`.  The exponent `−1/3` needs the direct count of FULL_LOCAL_PROOF_210 §2
("Reconstructing205's height count, including its atom"), eqs. (2.1)–(2.3), closed as in its §5 and
TeX quantitative_energies l.348–352.  Everything below is proved; the steps, in order:

1. **Sublevel sets** (`card_sublevel_le`, `card_quartic_le`, `card_quadratic_le`): at most
   `d (2r + 1)` integers with `|P(x)| ≤ T ≤ |lc| r^d`, for `P` of degree `d`.  Complex and repeated
   roots are allowed: each root projects to the real axis.
2. **The norm form in `x = p₂`** at fixed `(p₁, p₃) = (u, a)`, `b = k₃ − a` (`normD_quartic`): a
   quartic with leading coefficient `(a² − b²)² = k₃²(2a − k₃)²`, nonzero off the degenerate slice
   `2a = k₃`.  On that slice (`normD_quadratic`) the quartic and cubic terms cancel and `D` is a
   genuine quadratic with leading coefficient `−4a⁴(4K² − k₂²)`, of modulus `≥ 12K²`.
3. **The count** (`card_boxSet_le`, eq. (2.1)): with `Y = 2R + 1`,
   `#{‖p‖_∞ ≤ R : |D(p)| ≤ t⁴} ≤ 4Y² + 40 t Y^{3/2} + (4/3)(Y/K) t²`.  The height sum
   `Σ_a |2a − k₃|^{−1/2} ≤ 5√Y` (`sum_inv_sqrt_le`) is what makes the exponent of `Y` equal `3/2`.
4. **The layers** (`layer_sum_le`, eq. (2.2)): `Σ [1 + (d/h)²]⁻¹ ≤ 4At + 3B + 6Et²` at `h = t⁴`
   from a count `Aτ + B + Eτ²`.
5. **The shell moment** (`sum_shell_le`, eq. (2.3)): on `M ≤ m < 2M`,
   `κ_N² ≤ (M²K⁶)⁻¹[1 + (D/h)²]⁻¹` with `h ≍ M²K⁶/q` (`nearW_le_lorentz`), and the power of `M`
   cancels:
   `Σ_shell κ_N² ≤ 19200 q^{−1/4}K^{−9/2} + 600 K⁻⁶ + 1344 q^{−1/2}K⁻⁴`.
6. **The high outputs** (`momP_high`, `momN_high`): sum over the `≲ log K` shells and four patterns;
   the logarithm is paid by the decay in `K` (`one_add_log_div_pow_le`).  For `K ≥ q^{1/6}`:
   `momP q k ≤ 253728 (1 + log q^{1/12}) q^{−2/3}` and `momN q k ≤ 253728 (1 + log q^{1/12})/q`.

## Departures from the source, none affecting the statement
* The count needs neither `D ≠ 0`, nor `p₃ (k − p)₃ ≠ 0`, nor the near condition: `|D| ≤ t⁴` on a
  box, for all `t ≥ 0`.  At `p₃ = 0` the quartic coefficient is `k₃⁴ ≠ 0`.
* The source's factor `|k₃|^{−1/2}` in (2.1) is dropped: `k₃² ≥ 1` is enough here.
* The parameter is `t = T^{1/4}`, so the count is polynomial in `t` and free of `rpow`.
* The source's exact layer-cake integral is replaced by the layers `16^J h < |d| ≤ 16^{J+1} h`.
  They start at height `h`, so the atom `B` is summed against `256^{−J}` and costs no logarithm.
* The height sum uses a threshold rather than the ordering of the integers `2a − k₃`.
* Nothing here uses the conditional leaf T44 (1.1) or the `12/29` interpolation of §§3–4.
* The norm-form bound has constant `27`, valid for all `K ≥ 1`, so there is no separate `K < 8`.
-/

noncomputable section

namespace OVNS.Quant.NearJ

open Finset

/-! ### Sublevel sets of polynomials (FULL_LOCAL_PROOF_210 §2)

In the docstrings of this file, as in `Near/` and in the source, indices are `1`-based: `p₁, p₂, p₃`
are `p 0, p 1, p 2`, and `k₃ = k 2` is the third coordinate. -/

/-- An interval of radius `r` carries at most `2r + 1` integers. -/
theorem card_int_le_of_abs_sub_le (S : Finset ℤ) (c : ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hS : ∀ x ∈ S, |(x : ℝ) - c| ≤ r) : (S.card : ℝ) ≤ 2 * r + 1 := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  have hsub : S ⊆ Finset.Icc ⌈c - r⌉ ⌊c + r⌋ := by
    intro x hx
    obtain ⟨h1, h2⟩ := abs_le.1 (hS x hx)
    rw [Finset.mem_Icc]
    exact ⟨Int.ceil_le.2 (by linarith), Int.le_floor.2 (by linarith)⟩
  have hc := Finset.card_le_card hsub
  rw [Int.card_Icc] at hc
  have hle : ⌈c - r⌉ ≤ ⌊c + r⌋ :=
    (Finset.mem_Icc.1 (hsub hx₀)).1.trans (Finset.mem_Icc.1 (hsub hx₀)).2
  have h1 : ((S.card : ℤ) : ℝ) ≤ ((⌊c + r⌋ + 1 - ⌈c - r⌉ : ℤ) : ℝ) := by
    have : (S.card : ℤ) ≤ ⌊c + r⌋ + 1 - ⌈c - r⌉ := by omega
    exact_mod_cast this
  push_cast at h1
  have h2 := Int.floor_le (c + r)
  have h3 := Int.le_ceil (c - r)
  linarith

/-- A product of numbers above `r ≥ 0` exceeds `r^{card}`. -/
theorem pow_card_lt_prod {r : ℝ} (hr : 0 ≤ r) : ∀ s : Multiset ℝ, s ≠ 0 → (∀ y ∈ s, r < y) →
    r ^ Multiset.card s < s.prod := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro h; exact absurd rfl h
  | cons a s ih =>
    intro _ hy
    have ha : r < a := hy a (Multiset.mem_cons_self a s)
    rw [Multiset.card_cons, Multiset.prod_cons, pow_succ, mul_comm]
    by_cases hs : s = 0
    · subst hs
      simpa using ha
    · have h1 := ih hs (fun y hy' => hy y (Multiset.mem_cons_of_mem hy'))
      exact mul_lt_mul'' ha h1 hr (by positivity)

/-- `|P(x)| ≤ T ≤ |lc| r^n` forces a complex root within `r` of `x` (`P = lc ∏ (X − z)`; complex
and repeated roots are permitted). -/
theorem exists_root_near (P : Polynomial ℂ) (hn : 0 < P.natDegree) {r T : ℝ} (hr : 0 ≤ r)
    (hT : T ≤ ‖P.leadingCoeff‖ * r ^ P.natDegree) {x : ℂ} (hx : ‖P.eval x‖ ≤ T) :
    ∃ z ∈ P.roots, ‖x - z‖ ≤ r := by
  by_contra hc
  push Not at hc
  have hsp := IsAlgClosed.splits P
  have hP0 : P ≠ 0 := by
    rintro rfl
    simp at hn
  have hlc : 0 < ‖P.leadingCoeff‖ := norm_pos_iff.2 (Polynomial.leadingCoeff_ne_zero.2 hP0)
  have hcard : Multiset.card P.roots = P.natDegree := hsp.natDegree_eq_card_roots.symm
  have heval : P.eval x = P.leadingCoeff * (P.roots.map fun z => x - z).prod := by
    conv_lhs => rw [hsp.eq_prod_roots]
    simp [Polynomial.eval_multiset_prod, Multiset.map_map]
  have hnorm : ‖P.eval x‖ = ‖P.leadingCoeff‖ * (P.roots.map fun z => ‖x - z‖).prod := by
    rw [heval, norm_mul]
    congr 1
    have := map_multiset_prod (normHom : ℂ →*₀ ℝ) (P.roots.map fun z => x - z)
    simp
  have hroots : P.roots ≠ 0 := by
    intro h
    rw [h] at hcard
    simp at hcard
    omega
  have hlt := pow_card_lt_prod hr (P.roots.map fun z => ‖x - z‖) (by simpa using hroots) (by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
    exact hc z hz)
  rw [Multiset.card_map, hcard] at hlt
  rw [hnorm] at hx
  have := mul_lt_mul_of_pos_left hlt hlc
  linarith

/-- **The sublevel count**: at most `deg P · (2r + 1)` integers with `|P(x)| ≤ T ≤ |lc| r^{deg P}`
(each complex root projects to the real axis; an interval of length `2r` carries `2r + 1`
integers). -/
theorem card_sublevel_le (P : Polynomial ℂ) (hn : 0 < P.natDegree) {r T : ℝ} (hr : 0 ≤ r)
    (hT : T ≤ ‖P.leadingCoeff‖ * r ^ P.natDegree) (S : Finset ℤ)
    (hS : ∀ x ∈ S, ‖P.eval (x : ℂ)‖ ≤ T) : (S.card : ℝ) ≤ P.natDegree * (2 * r + 1) := by
  classical
  obtain ⟨Z, hZ, hcard⟩ : ∃ Z : Finset ℂ, (∀ z, z ∈ Z ↔ z ∈ P.roots) ∧
      (Z.card : ℝ) ≤ P.natDegree :=
    ⟨P.roots.toFinset, fun z => Multiset.mem_toFinset, by
      exact_mod_cast (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' P)⟩
  have hsub : S ⊆ Z.biUnion fun z => S.filter fun x : ℤ => |(x : ℝ) - z.re| ≤ r := by
    intro x hx
    obtain ⟨z, hz, hxz⟩ := exists_root_near P hn hr hT (hS x hx)
    rw [Finset.mem_biUnion]
    refine ⟨z, (hZ z).2 hz, Finset.mem_filter.2 ⟨hx, ?_⟩⟩
    have h1 := Complex.abs_re_le_norm ((x : ℂ) - z)
    simp only [Complex.sub_re, Complex.intCast_re] at h1
    linarith
  have h1 : S.card ≤ ∑ z ∈ Z, (S.filter fun x : ℤ => |(x : ℝ) - z.re| ≤ r).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have h2 : (S.card : ℝ) ≤ ∑ z ∈ Z, ((S.filter fun x : ℤ => |(x : ℝ) - z.re| ≤ r).card : ℝ) := by
    rw [← Nat.cast_sum]
    exact Nat.cast_le.2 h1
  have h3 : ∑ z ∈ Z, ((S.filter fun x : ℤ => |(x : ℝ) - z.re| ≤ r).card : ℝ) ≤
      ∑ _z ∈ Z, (2 * r + 1) :=
    Finset.sum_le_sum fun z _ =>
      card_int_le_of_abs_sub_le _ z.re hr (fun x hx => (Finset.mem_filter.1 hx).2)
  rw [Finset.sum_const, nsmul_eq_mul] at h3
  have h4 : (Z.card : ℝ) * (2 * r + 1) ≤ P.natDegree * (2 * r + 1) :=
    mul_le_mul_of_nonneg_right hcard (by positivity)
  linarith

open Polynomial in
/-- **Quartic sublevel**: the degree-`4` interval bound. -/
theorem card_quartic_le {c₄ c₃ c₂ c₁ c₀ : ℝ} (h : c₄ ≠ 0) {r T : ℝ} (hr : 0 ≤ r)
    (hT : T ≤ |c₄| * r ^ 4) (S : Finset ℤ)
    (hS : ∀ x ∈ S, |c₄ * (x : ℝ) ^ 4 + c₃ * (x : ℝ) ^ 3 + c₂ * (x : ℝ) ^ 2 + c₁ * x + c₀| ≤ T) :
    (S.card : ℝ) ≤ 4 * (2 * r + 1) := by
  set P : ℂ[X] := C (c₄ : ℂ) * X ^ 4 + C (c₃ : ℂ) * X ^ 3 + C (c₂ : ℂ) * X ^ 2 + C (c₁ : ℂ) * X +
    C (c₀ : ℂ) with hP
  have hc : (c₄ : ℂ) ≠ 0 := by exact_mod_cast h
  have hdeg : P.natDegree = 4 := by
    rw [hP]
    compute_degree!
  have hlc : P.leadingCoeff = c₄ := by
    rw [Polynomial.leadingCoeff, hdeg, hP]
    simp
  have key := card_sublevel_le P (by omega) hr (T := T)
    (by rw [hlc, hdeg, Complex.norm_real, Real.norm_eq_abs]; exact hT) S (fun x hx => by
      have h1 := hS x hx
      have e : P.eval (x : ℂ) =
          ((c₄ * (x : ℝ) ^ 4 + c₃ * (x : ℝ) ^ 3 + c₂ * (x : ℝ) ^ 2 + c₁ * x + c₀ : ℝ) : ℂ) := by
        simp [hP]
      rw [e, Complex.norm_real, Real.norm_eq_abs]
      exact h1)
  rw [hdeg] at key
  exact_mod_cast key

open Polynomial in
/-- **Quadratic sublevel**: the degree-`2` interval bound. -/
theorem card_quadratic_le {c₂ c₁ c₀ : ℝ} (h : c₂ ≠ 0) {r T : ℝ} (hr : 0 ≤ r)
    (hT : T ≤ |c₂| * r ^ 2) (S : Finset ℤ)
    (hS : ∀ x ∈ S, |c₂ * (x : ℝ) ^ 2 + c₁ * x + c₀| ≤ T) :
    (S.card : ℝ) ≤ 2 * (2 * r + 1) := by
  set P : ℂ[X] := C (c₂ : ℂ) * X ^ 2 + C (c₁ : ℂ) * X + C (c₀ : ℂ) with hP
  have hc : (c₂ : ℂ) ≠ 0 := by exact_mod_cast h
  have hdeg : P.natDegree = 2 := by
    rw [hP]
    compute_degree!
  have hlc : P.leadingCoeff = c₂ := by
    rw [Polynomial.leadingCoeff, hdeg, hP]
    simp
  have key := card_sublevel_le P (by omega) hr (T := T)
    (by rw [hlc, hdeg, Complex.norm_real, Real.norm_eq_abs]; exact hT) S (fun x hx => by
      have h1 := hS x hx
      have e : P.eval (x : ℂ) = ((c₂ * (x : ℝ) ^ 2 + c₁ * x + c₀ : ℝ) : ℂ) := by
        simp [hP]
      rw [e, Complex.norm_real, Real.norm_eq_abs]
      exact h1)
  rw [hdeg] at key
  exact_mod_cast key

/-! ### The norm form as a polynomial in the second coordinate -/

theorem legA_eq (p : Mode) : legA p = p 2 ^ 2 * (p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2) := by
  rw [legA, nsqZ_eq]

/-- At fixed `p₁ = u`, `p₃ = a`, the norm form is a quartic in `x = p₂` with leading coefficient
`(a² − b²)²`, `b = k₃ − a`. -/
theorem normD_quartic (k : Mode) (u a : ℤ) : ∃ c₃ c₂ c₁ c₀ : ℤ, ∀ p : Mode, p 0 = u → p 2 = a →
    normD p k = (a ^ 2 - (k 2 - a) ^ 2) ^ 2 * p 1 ^ 4 + c₃ * p 1 ^ 3 + c₂ * p 1 ^ 2 + c₁ * p 1
      + c₀ := by
  obtain ⟨C, hC⟩ : ∃ C, C = legA k := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = k 2 - a := ⟨_, rfl⟩
  obtain ⟨α, hα⟩ : ∃ α, α = a ^ 2 * (u ^ 2 + a ^ 2) := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = b ^ 2 * ((k 0 - u) ^ 2 + k 1 ^ 2 + b ^ 2) := ⟨_, rfl⟩
  refine ⟨2 * (a ^ 2 - b ^ 2) * (2 * b ^ 2 * k 1),
    (2 * b ^ 2 * k 1) ^ 2 + 2 * (a ^ 2 - b ^ 2) * (α - β) - 2 * C * (a ^ 2 + b ^ 2),
    2 * (2 * b ^ 2 * k 1) * (α - β) - 2 * C * (-2 * b ^ 2 * k 1),
    (α - β) ^ 2 - 2 * C * (α + β) + C ^ 2, fun p hu ha => ?_⟩
  have hA : legA p = a ^ 2 * p 1 ^ 2 + α := by
    rw [legA_eq, hu, ha, hα]
    ring
  have hB : legA (k - p) = b ^ 2 * p 1 ^ 2 - 2 * b ^ 2 * k 1 * p 1 + β := by
    rw [legA_eq]
    simp only [Pi.sub_apply]
    rw [hu, ha, ← hb, hβ]
    ring
  rw [normD, hA, hB, ← hC, ← hb]
  ring

/-- On the degenerate slice `2a = k₃` (`a = b`) the quartic and cubic terms cancel, and the norm
form is a genuine quadratic in `x = p₂` with leading coefficient `−4a⁴(4K² − k₂²)`. -/
theorem normD_quadratic (k : Mode) (u a : ℤ) (h2 : 2 * a = k 2) :
    ∃ c₁ c₀ : ℤ, ∀ p : Mode, p 0 = u → p 2 = a →
      normD p k = -(4 * a ^ 4 * (4 * nsqZ k - k 1 ^ 2)) * p 1 ^ 2 + c₁ * p 1 + c₀ := by
  obtain ⟨C, hC⟩ : ∃ C, C = legA k := ⟨_, rfl⟩
  have hC' : C = 4 * a ^ 2 * nsqZ k := by
    rw [hC, legA, ← h2]
    ring
  obtain ⟨α, hα⟩ : ∃ α, α = a ^ 2 * (u ^ 2 + a ^ 2) := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = a ^ 2 * ((k 0 - u) ^ 2 + k 1 ^ 2 + a ^ 2) := ⟨_, rfl⟩
  refine ⟨4 * a ^ 2 * k 1 * (α - β) + 4 * C * a ^ 2 * k 1,
    (α - β) ^ 2 - 2 * C * (α + β) + C ^ 2, fun p hu ha => ?_⟩
  have hA : legA p = a ^ 2 * p 1 ^ 2 + α := by
    rw [legA_eq, hu, ha, hα]
    ring
  have hB : legA (k - p) = a ^ 2 * p 1 ^ 2 - 2 * a ^ 2 * k 1 * p 1 + β := by
    rw [legA_eq]
    simp only [Pi.sub_apply]
    rw [hu, ha, ← h2, hβ]
    ring
  rw [normD, hA, hB, ← hC, hC']
  ring

/-! ### The count on a box -/

/-- The points of the box `‖p‖_∞ ≤ R` with `|D(p)| ≤ t⁴`: no height, near or other-leg
restriction. -/
def boxSet (k : Mode) (R : ℕ) (t : ℝ) : Finset Mode :=
  (modeBox R).filter fun p => |(normD p k : ℝ)| ≤ t ^ 4

theorem mem_boxSet {k p : Mode} {R : ℕ} {t : ℝ} :
    p ∈ boxSet k R t ↔ p ∈ modeBox R ∧ |(normD p k : ℝ)| ≤ t ^ 4 := by
  simp [boxSet, Finset.mem_filter]

/-- A slice `(p₁, p₃) = (u, a)` injects into the integers by `p ↦ p₂`. -/
private theorem slice_injOn (F : Finset Mode) (u a : ℤ)
    (hF : ∀ p ∈ F, p 0 = u ∧ p 2 = a) : Set.InjOn (fun p : Mode => p 1) F := by
  intro p hp p' hp' h
  obtain ⟨h1, h2⟩ := hF p hp
  obtain ⟨h1', h2'⟩ := hF p' hp'
  simp only at h
  funext i
  fin_cases i
  · exact h1.trans h1'.symm
  · exact h
  · exact h2.trans h2'.symm

/-- **A nondegenerate slice** (`2a ≠ k₃`): at most `8 t/√|2a − k₃| + 4` points. -/
theorem card_slice_nondeg {k : Mode} (hk : k 2 ≠ 0) (R : ℕ) {t : ℝ} (ht : 0 ≤ t) (u a : ℤ)
    (ha : 2 * a ≠ k 2) :
    (((boxSet k R t).filter fun p => p 0 = u ∧ p 2 = a).card : ℝ) ≤
      4 * (2 * (t / Real.sqrt |((2 * a - k 2 : ℤ) : ℝ)|) + 1) := by
  classical
  obtain ⟨c₃, c₂, c₁, c₀, hD⟩ := normD_quartic k u a
  set F := (boxSet k R t).filter fun p => p 0 = u ∧ p 2 = a with hF
  have hFm : ∀ p ∈ F, (p 0 = u ∧ p 2 = a) ∧ |(normD p k : ℝ)| ≤ t ^ 4 := fun p hp => by
    rw [hF, Finset.mem_filter, mem_boxSet] at hp
    exact ⟨hp.2, hp.1.2⟩
  rw [← Finset.card_image_of_injOn (slice_injOn F u a fun p hp => (hFm p hp).1)]
  set n : ℝ := |((2 * a - k 2 : ℤ) : ℝ)| with hn
  have hn1 : 1 ≤ n := by
    have h1 : (2 * a - k 2) ≠ 0 := sub_ne_zero.2 ha
    have h2 := Int.one_le_abs h1
    rw [hn, ← Int.cast_abs]
    exact_mod_cast h2
  have hn0 : 0 < n := by linarith
  have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hss : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn0.le
  have hl1 : (1 : ℝ) ≤ (k 2 : ℝ) ^ 2 := by
    have h1 := Int.one_le_abs hk
    have h2 : (1 : ℝ) ≤ |(k 2 : ℝ)| := by exact_mod_cast h1
    rw [← sq_abs]
    nlinarith
  set c₄ : ℝ := (((a ^ 2 - (k 2 - a) ^ 2) ^ 2 : ℤ) : ℝ) with hc₄
  have hc₄e : c₄ = (k 2 : ℝ) ^ 2 * n ^ 2 := by
    rw [hc₄, hn, sq_abs]
    push_cast
    ring
  have hc₄pos : 0 < c₄ := by
    rw [hc₄e]
    positivity
  have hr0 : 0 ≤ t / Real.sqrt n := by positivity
  refine card_quartic_le (c₄ := c₄) (c₃ := c₃) (c₂ := c₂) (c₁ := c₁) (c₀ := c₀) hc₄pos.ne' hr0
    (T := t ^ 4) ?_ _ ?_
  · rw [abs_of_pos hc₄pos, hc₄e, div_pow]
    have e4 : Real.sqrt n ^ 4 = n ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hss]
    rw [e4]
    have hn2 : (0 : ℝ) < n ^ 2 := by positivity
    rw [show (k 2 : ℝ) ^ 2 * n ^ 2 * (t ^ 4 / n ^ 2) = (k 2 : ℝ) ^ 2 * t ^ 4 by field_simp]
    nlinarith [pow_nonneg ht 4]
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨⟨hu, ha'⟩, hle⟩ := hFm p hp
    rw [hD p hu ha'] at hle
    rw [hc₄]
    push_cast at hle ⊢
    exact hle

/-- **The degenerate slice** (`2a = k₃`): at most `4 t²/(3K) + 2` points; the leading coefficient
has magnitude at least `12 K²`. -/
theorem card_slice_deg {k : Mode} (hk : k 2 ≠ 0) (R : ℕ) (t : ℝ) (u a : ℤ)
    (ha : 2 * a = k 2) :
    (((boxSet k R t).filter fun p => p 0 = u ∧ p 2 = a).card : ℝ) ≤
      2 * (2 * (t ^ 2 / (3 * absk k)) + 1) := by
  classical
  obtain ⟨c₁, c₀, hD⟩ := normD_quadratic k u a ha
  set F := (boxSet k R t).filter fun p => p 0 = u ∧ p 2 = a with hF
  have hFm : ∀ p ∈ F, (p 0 = u ∧ p 2 = a) ∧ |(normD p k : ℝ)| ≤ t ^ 4 := fun p hp => by
    rw [hF, Finset.mem_filter, mem_boxSet] at hp
    exact ⟨hp.2, hp.1.2⟩
  rw [← Finset.card_image_of_injOn (slice_injOn F u a fun p hp => (hFm p hp).1)]
  have hK1 : 1 ≤ absk k := one_le_absk (by rintro rfl; simp at hk)
  have hK0 : 0 < absk k := by linarith
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hk (by simpa using ha.symm)
  have ha4 : (1 : ℝ) ≤ (a : ℝ) ^ 4 := by
    have h1 : (1 : ℤ) ≤ a ^ 2 := by
      have := Int.one_le_abs ha0
      nlinarith [sq_abs a, abs_nonneg a]
    have h2 : (1 : ℤ) ≤ a ^ 4 := by
      have : a ^ 4 = a ^ 2 * a ^ 2 := by ring
      nlinarith
    exact_mod_cast h2
  have hN : (nsqZ k : ℝ) = absk k ^ 2 := (absk_sq_eq_nsqZ k).symm
  have hk1 : (k 1 : ℝ) ^ 2 ≤ absk k ^ 2 := by
    rw [← hN]
    exact_mod_cast sq_coord_le_nsqZ k 1
  set c₂ : ℝ := ((-(4 * a ^ 4 * (4 * nsqZ k - k 1 ^ 2)) : ℤ) : ℝ) with hc₂
  have hc₂e : c₂ = -(4 * (a : ℝ) ^ 4 * (4 * absk k ^ 2 - (k 1 : ℝ) ^ 2)) := by
    rw [hc₂]
    push_cast
    rw [hN]
  have hbig : 12 * absk k ^ 2 ≤ |c₂| := by
    rw [hc₂e, abs_neg]
    have h3 : 3 * absk k ^ 2 ≤ 4 * absk k ^ 2 - (k 1 : ℝ) ^ 2 := by linarith
    have h4 : 0 ≤ absk k ^ 2 := by positivity
    calc 12 * absk k ^ 2 = 4 * 1 * (3 * absk k ^ 2) := by ring
      _ ≤ 4 * (a : ℝ) ^ 4 * (4 * absk k ^ 2 - (k 1 : ℝ) ^ 2) := by gcongr
      _ ≤ |4 * (a : ℝ) ^ 4 * (4 * absk k ^ 2 - (k 1 : ℝ) ^ 2)| := le_abs_self _
  have hc₂0 : c₂ ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hbig
    have : 0 < absk k ^ 2 := by positivity
    linarith
  have hr0 : 0 ≤ t ^ 2 / (3 * absk k) := by positivity
  refine card_quadratic_le (c₂ := c₂) (c₁ := c₁) (c₀ := c₀) hc₂0 hr0 (T := t ^ 4) ?_ _ ?_
  · have e : 12 * absk k ^ 2 * (t ^ 2 / (3 * absk k)) ^ 2 = 4 / 3 * t ^ 4 := by
      field_simp
      ring
    have h1 : 12 * absk k ^ 2 * (t ^ 2 / (3 * absk k)) ^ 2 ≤ |c₂| * (t ^ 2 / (3 * absk k)) ^ 2 := by
      gcongr
    have h2 : 0 ≤ t ^ 4 := by positivity
    linarith
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨⟨hu, ha'⟩, hle⟩ := hFm p hp
    rw [hD p hu ha'] at hle
    rw [hc₂]
    push_cast at hle ⊢
    exact hle

/-- `Σ_{m=1}^{N} 1/√m ≤ 2√N`. -/
theorem sum_inv_sqrt_Icc (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, (Real.sqrt (m : ℝ))⁻¹ ≤ 2 * Real.sqrt (N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    set y := Real.sqrt ((N + 1 : ℕ) : ℝ) with hy
    set x := Real.sqrt (N : ℝ) with hx
    have hy0 : 0 < y := Real.sqrt_pos.2 (by positivity)
    have hx0 : 0 ≤ x := Real.sqrt_nonneg _
    have hyy : y ^ 2 = (N : ℝ) + 1 := by
      rw [hy, Real.sq_sqrt (by positivity)]
      push_cast
      ring
    have hxx : x ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
    have h1 : y⁻¹ ≤ 2 * y - 2 * x := by
      rw [inv_le_iff_one_le_mul₀ hy0]
      nlinarith [sq_nonneg (y - x)]
    linarith

/-- **The height sum** (FULL_LOCAL_PROOF_210 §2): over a set of `Y` heights,
`Σ_{2a ≠ l} |2a − l|^{−1/2} ≤ 5 √Y`, whatever the position of `l`.  (The source orders the
distinct integers `2a − l`; here: heights with `|2a − l| ≥ Y` cost `√Y` in all, and the others are
counted by the at most two-to-one map `a ↦ |2a − l|` into `[1, Y]`.) -/
theorem sum_inv_sqrt_le (I : Finset ℤ) (l : ℤ) :
    ∑ a ∈ I, (if 2 * a = l then (0 : ℝ) else (Real.sqrt |((2 * a - l : ℤ) : ℝ)|)⁻¹) ≤
      5 * Real.sqrt (I.card : ℝ) := by
  classical
  rcases I.eq_empty_or_nonempty with rfl | hne
  · simp
  set Y := I.card with hY
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast Finset.card_pos.2 hne
  have hsY : 0 < Real.sqrt (Y : ℝ) := Real.sqrt_pos.2 hY0
  set n : ℤ → ℕ := fun a => (2 * a - l).natAbs with hn
  have hcast : ∀ a : ℤ, |((2 * a - l : ℤ) : ℝ)| = (n a : ℝ) := fun a => by
    rw [hn]
    simp only [Nat.cast_natAbs, Int.cast_abs]
  set Is := I.filter fun a => n a ∈ Finset.Icc 1 Y with hIs
  -- the pointwise split
  have hpt : ∀ a ∈ I, (if 2 * a = l then (0 : ℝ) else (Real.sqrt |((2 * a - l : ℤ) : ℝ)|)⁻¹) ≤
      (Real.sqrt (Y : ℝ))⁻¹ + (if n a ∈ Finset.Icc 1 Y then (Real.sqrt (n a : ℝ))⁻¹ else 0) := by
    intro a _
    have hinv : 0 ≤ (Real.sqrt (Y : ℝ))⁻¹ := by positivity
    split_ifs with h1 h2 h2
    · positivity
    · linarith
    · rw [hcast]
      have : 0 ≤ (Real.sqrt (n a : ℝ))⁻¹ := by positivity
      linarith
    · rw [hcast]
      have hn1 : 1 ≤ n a := by
        simp only [hn]
        have : 2 * a - l ≠ 0 := sub_ne_zero.2 h1
        omega
      have hge : Y ≤ n a := by
        rw [Finset.mem_Icc] at h2
        omega
      have : (Real.sqrt (n a : ℝ))⁻¹ ≤ (Real.sqrt (Y : ℝ))⁻¹ := by
        apply inv_anti₀ hsY
        apply Real.sqrt_le_sqrt
        exact_mod_cast hge
      linarith
  -- the small heights
  have hsmall : ∑ a ∈ Is, (Real.sqrt (n a : ℝ))⁻¹ ≤ 4 * Real.sqrt (Y : ℝ) := by
    have hmaps : ∀ a ∈ Is, n a ∈ Finset.Icc 1 Y := fun a ha => (Finset.mem_filter.1 ha).2
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    have hfib : ∀ m ∈ Finset.Icc 1 Y,
        ∑ a ∈ Is.filter (fun a => n a = m), (Real.sqrt (n a : ℝ))⁻¹ ≤
          2 * (Real.sqrt (m : ℝ))⁻¹ := by
      intro m _
      have hsub : Is.filter (fun a => n a = m) ⊆ {(l + m) / 2, (l - m) / 2} := by
        intro a ha
        have hna := (Finset.mem_filter.1 ha).2
        simp only [hn] at hna
        rw [Finset.mem_insert, Finset.mem_singleton]
        omega
      have hcard : ((Is.filter fun a => n a = m).card : ℝ) ≤ 2 := by
        exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_le_two
      calc ∑ a ∈ Is.filter (fun a => n a = m), (Real.sqrt (n a : ℝ))⁻¹
          = ∑ _a ∈ Is.filter (fun a => n a = m), (Real.sqrt (m : ℝ))⁻¹ :=
            Finset.sum_congr rfl fun a ha => by rw [(Finset.mem_filter.1 ha).2]
        _ = ((Is.filter fun a => n a = m).card : ℝ) * (Real.sqrt (m : ℝ))⁻¹ := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 2 * (Real.sqrt (m : ℝ))⁻¹ := by gcongr
    calc ∑ m ∈ Finset.Icc 1 Y, ∑ a ∈ Is.filter (fun a => n a = m), (Real.sqrt (n a : ℝ))⁻¹
        ≤ ∑ m ∈ Finset.Icc 1 Y, 2 * (Real.sqrt (m : ℝ))⁻¹ := Finset.sum_le_sum hfib
      _ = 2 * ∑ m ∈ Finset.Icc 1 Y, (Real.sqrt (m : ℝ))⁻¹ := by rw [Finset.mul_sum]
      _ ≤ 2 * (2 * Real.sqrt (Y : ℝ)) := by gcongr; exact sum_inv_sqrt_Icc Y
      _ = 4 * Real.sqrt (Y : ℝ) := by ring
  have hYs : (Y : ℝ) * (Real.sqrt (Y : ℝ))⁻¹ = Real.sqrt (Y : ℝ) := by
    have hss : Real.sqrt (Y : ℝ) * Real.sqrt (Y : ℝ) = Y := Real.mul_self_sqrt hY0.le
    field_simp
    nlinarith
  calc ∑ a ∈ I, (if 2 * a = l then (0 : ℝ) else (Real.sqrt |((2 * a - l : ℤ) : ℝ)|)⁻¹)
      ≤ ∑ a ∈ I, ((Real.sqrt (Y : ℝ))⁻¹ +
          (if n a ∈ Finset.Icc 1 Y then (Real.sqrt (n a : ℝ))⁻¹ else 0)) :=
        Finset.sum_le_sum hpt
    _ = (Y : ℝ) * (Real.sqrt (Y : ℝ))⁻¹ + ∑ a ∈ Is, (Real.sqrt (n a : ℝ))⁻¹ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hIs, Finset.sum_filter]
    _ ≤ 5 * Real.sqrt (Y : ℝ) := by
        rw [hYs]
        linarith

/-- **The box count** (FULL_LOCAL_PROOF_210 eq. (2.1)): for a fast output and `Y = 2R + 1`,
`#{‖p‖_∞ ≤ R : |D(p)| ≤ t⁴} ≤ 4Y² + 40 t Y^{3/2} + (4/3)(Y/K) t²`, including the `+4` atom of every
slice and the degenerate slice `2p₃ = k₃`.  No other restriction on `p`, and none on `k` or
`k − p`, so `R` may be far smaller than `K`.  (The source keeps a factor `|k₃|^{−1/2}` which is
not needed.) -/
theorem card_boxSet_le {k : Mode} (hk : k 2 ≠ 0) (R : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ((boxSet k R t).card : ℝ) ≤
      4 * (2 * R + 1 : ℝ) ^ 2 + 40 * t * ((2 * R + 1 : ℝ) * Real.sqrt (2 * R + 1)) +
        4 / 3 * ((2 * R + 1 : ℝ) / absk k) * t ^ 2 := by
  classical
  have hK1 : 1 ≤ absk k := one_le_absk (by rintro rfl; simp at hk)
  have hK0 : 0 < absk k := by linarith
  set I : Finset ℤ := Finset.Icc (-(R : ℤ)) R with hI
  set Y : ℝ := 2 * R + 1 with hY
  have hY0 : 0 ≤ Y := by positivity
  have hIY : (I.card : ℝ) = Y := by
    have h1 : I.card = 2 * R + 1 := by
      rw [hI, Int.card_Icc]
      omega
    rw [h1, hY]
    push_cast
    ring
  set r' := t ^ 2 / (3 * absk k) with hr'
  have hr'0 : 0 ≤ r' := by positivity
  set v : ℤ → ℝ := fun a => if 2 * a = k 2 then 0 else
    (Real.sqrt |((2 * a - k 2 : ℤ) : ℝ)|)⁻¹ with hv
  set e : ℤ → ℝ := fun a => if 2 * a = k 2 then 1 else 0 with he
  have hslice : ∀ u a : ℤ, (((boxSet k R t).filter fun p => p 0 = u ∧ p 2 = a).card : ℝ) ≤
      4 + 8 * t * v a + 4 * r' * e a := by
    intro u a
    by_cases h : 2 * a = k 2
    · have h1 := card_slice_deg hk R t u a h
      simp only [hv, he, h, ite_true]
      linarith
    · have h1 := card_slice_nondeg hk R ht u a h
      simp only [hv, he, h, ite_false]
      rw [div_eq_mul_inv] at h1
      linarith
  have hmaps : ∀ p ∈ boxSet k R t, (p 0, p 2) ∈ I ×ˢ I := by
    intro p hp
    have h := mem_modeBox.1 (mem_boxSet.1 hp).1
    rw [Finset.mem_product, hI, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨abs_le.1 (h 0), abs_le.1 (h 2)⟩
  have hcard : ((boxSet k R t).card : ℝ) = ∑ u ∈ I, ∑ a ∈ I,
      (((boxSet k R t).filter fun p => p 0 = u ∧ p 2 = a).card : ℝ) := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    push_cast
    rw [Finset.sum_product]
    simp only [Prod.mk.injEq]
  have hsumv : ∑ a ∈ I, v a ≤ 5 * Real.sqrt Y := by
    have := sum_inv_sqrt_le I (k 2)
    rw [hIY] at this
    exact this
  have hsume : ∑ a ∈ I, e a ≤ 1 := by
    have hle : (I.filter fun a => 2 * a = k 2).card ≤ 1 := by
      refine Finset.card_le_one.2 fun a ha b hb => ?_
      have h1 := (Finset.mem_filter.1 ha).2
      have h2 := (Finset.mem_filter.1 hb).2
      omega
    have h3 : ∑ a ∈ I, e a = ((I.filter fun a => 2 * a = k 2).card : ℝ) := by
      simp only [he]
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul, mul_one]
    rw [h3]
    exact_mod_cast hle
  have hinner : ∀ u ∈ I, ∑ a ∈ I, (((boxSet k R t).filter fun p => p 0 = u ∧ p 2 = a).card : ℝ) ≤
      4 * Y + 8 * t * (5 * Real.sqrt Y) + 4 * r' := by
    intro u _
    calc ∑ a ∈ I, (((boxSet k R t).filter fun p => p 0 = u ∧ p 2 = a).card : ℝ)
        ≤ ∑ a ∈ I, (4 + 8 * t * v a + 4 * r' * e a) := Finset.sum_le_sum fun a _ => hslice u a
      _ = 4 * Y + 8 * t * ∑ a ∈ I, v a + 4 * r' * ∑ a ∈ I, e a := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hIY,
            Finset.mul_sum, Finset.mul_sum]
          ring
      _ ≤ 4 * Y + 8 * t * (5 * Real.sqrt Y) + 4 * r' * 1 := by gcongr
      _ = 4 * Y + 8 * t * (5 * Real.sqrt Y) + 4 * r' := by ring
  rw [hcard]
  calc ∑ u ∈ I, ∑ a ∈ I, (((boxSet k R t).filter fun p => p 0 = u ∧ p 2 = a).card : ℝ)
      ≤ ∑ _u ∈ I, (4 * Y + 8 * t * (5 * Real.sqrt Y) + 4 * r') := Finset.sum_le_sum hinner
    _ = Y * (4 * Y + 8 * t * (5 * Real.sqrt Y) + 4 * r') := by
        rw [Finset.sum_const, nsmul_eq_mul, hIY]
    _ = 4 * Y ^ 2 + 40 * t * (Y * Real.sqrt Y) + 4 / 3 * (Y / absk k) * t ^ 2 := by
        rw [hr']
        field_simp
        ring

/-! ### The layer lemma (FULL_LOCAL_PROOF_210 eq. (2.2)) -/

/-- **The layers.**  If `#{|d| ≤ τ⁴} ≤ Aτ + B + Eτ²` for all `τ ≥ 0`, then
`Σ_s [1 + (d/h)²]⁻¹ ≤ 4At + 3B + 6Et²` at `h = t⁴`: the first layer `|d| ≤ h` costs the count at
`h`; the layers `16^J h < |d| ≤ 16^{J+1} h` carry the factor `256^{−J}`, which sums the counts
geometrically, the atom `B` included.  This replaces the source's exact integral identity for
`L(h)`, at the price of absolute constants only; the two minima of (2.2) are not needed, since
(2.3) drops them upward. -/
theorem layer_sum_le {α : Type*} (S : Finset α) (d : α → ℝ) {A B E t : ℝ} (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hE : 0 ≤ E) (ht : 0 < t)
    (hcount : ∀ τ : ℝ, 0 ≤ τ →
      ((S.filter fun s => |d s| ≤ τ ^ 4).card : ℝ) ≤ A * τ + B + E * τ ^ 2) :
    ∑ s ∈ S, (1 + (d s / t ^ 4) ^ 2)⁻¹ ≤ 4 * A * t + 3 * B + 6 * E * t ^ 2 := by
  classical
  set g : α → ℝ := fun s => (1 + (d s / t ^ 4) ^ 2)⁻¹ with hg
  have hg0 : ∀ s, 0 ≤ g s := fun s => by
    simp only [hg]
    positivity
  have hg1 : ∀ s, g s ≤ 1 := fun s => by
    simp only [hg]
    exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (d s / t ^ 4)])
  have ht4 : 0 < t ^ 4 := by positivity
  set T : ℕ → ℝ := fun J => (2 : ℝ) ^ J * t with hT
  have hT0 : ∀ J, 0 ≤ T J := fun J => by
    simp only [hT]
    positivity
  have hT4 : ∀ J, T J ^ 4 = (16 : ℝ) ^ J * t ^ 4 := fun J => by
    simp only [hT]
    rw [mul_pow, ← pow_mul, mul_comm J 4, pow_mul]
    norm_num
  set F : ℕ → ℝ := fun J => ∑ s ∈ S.filter (fun s => |d s| ≤ T J ^ 4), g s with hF
  have hAt : 0 ≤ A * t := by positivity
  have hEt : 0 ≤ E * t ^ 2 := by positivity
  have hinv : ∀ J, F J ≤ (4 - 3 * (1 / 128 : ℝ) ^ J) * (A * t) +
      (3 - 2 * (1 / 256 : ℝ) ^ J) * B + (6 - 5 * (1 / 64 : ℝ) ^ J) * (E * t ^ 2) := by
    intro J
    induction J with
    | zero =>
      have h0 := hcount (T 0) (hT0 0)
      have h1 : F 0 ≤ ((S.filter fun s => |d s| ≤ T 0 ^ 4).card : ℝ) := by
        calc F 0 ≤ ∑ _s ∈ S.filter (fun s => |d s| ≤ T 0 ^ 4), (1 : ℝ) :=
              Finset.sum_le_sum fun s _ => hg1 s
          _ = _ := by simp
      have e0 : T 0 = t := by simp [hT]
      rw [e0] at h0 h1
      have h2 := h1.trans h0
      simp only [pow_zero]
      linarith
    | succ J ih =>
      set X := S.filter fun s => |d s| ≤ T (J + 1) ^ 4 with hX
      have hmono : T J ^ 4 ≤ T (J + 1) ^ 4 := by
        have h1 : (16 : ℝ) ^ (J + 1) * t ^ 4 = 16 * ((16 : ℝ) ^ J * t ^ 4) := by ring
        rw [hT4, hT4, h1]
        have : 0 < (16 : ℝ) ^ J * t ^ 4 := by positivity
        linarith
      have hfilt : X.filter (fun s => |d s| ≤ T J ^ 4) =
          S.filter fun s => |d s| ≤ T J ^ 4 := by
        ext s
        simp only [hX, Finset.mem_filter]
        constructor
        · rintro ⟨⟨h1, -⟩, h3⟩
          exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩
          exact ⟨⟨h1, h3.trans hmono⟩, h3⟩
      have hb0 : 0 ≤ (1 / 256 : ℝ) ^ J := by positivity
      have hlayer : ∀ s ∈ X.filter (fun s => ¬ |d s| ≤ T J ^ 4), g s ≤ (1 / 256 : ℝ) ^ J := by
        intro s hs
        have h1 : T J ^ 4 < |d s| := not_le.1 (Finset.mem_filter.1 hs).2
        rw [hT4] at h1
        have h16 : 0 < (16 : ℝ) ^ J := by positivity
        have h2 : (16 : ℝ) ^ J < |d s / t ^ 4| := by
          rw [abs_div, abs_of_pos ht4, lt_div_iff₀ ht4]
          exact h1
        have h3 : ((16 : ℝ) ^ J) ^ 2 ≤ (d s / t ^ 4) ^ 2 := by
          rw [← sq_abs (d s / t ^ 4)]
          exact pow_le_pow_left₀ h16.le h2.le 2
        have h4 : ((16 : ℝ) ^ J) ^ 2 = (256 : ℝ) ^ J := by
          rw [← pow_mul, mul_comm J 2, pow_mul]
          norm_num
        have h5 : (1 / 256 : ℝ) ^ J = ((256 : ℝ) ^ J)⁻¹ := by
          rw [one_div, inv_pow]
        rw [h5]
        simp only [hg]
        apply inv_anti₀ (by positivity)
        rw [← h4]
        linarith
      have hsplit : F (J + 1) ≤ F J + (1 / 256 : ℝ) ^ J * (X.card : ℝ) := by
        have h1 : F (J + 1) = ∑ s ∈ X.filter (fun s => |d s| ≤ T J ^ 4), g s +
            ∑ s ∈ X.filter (fun s => ¬ |d s| ≤ T J ^ 4), g s :=
          (Finset.sum_filter_add_sum_filter_not X _ g).symm
        rw [hfilt] at h1
        have h2 : ∑ s ∈ X.filter (fun s => ¬ |d s| ≤ T J ^ 4), g s ≤
            ((X.filter fun s => ¬ |d s| ≤ T J ^ 4).card : ℝ) * (1 / 256 : ℝ) ^ J := by
          calc ∑ s ∈ X.filter (fun s => ¬ |d s| ≤ T J ^ 4), g s
              ≤ ∑ _s ∈ X.filter (fun s => ¬ |d s| ≤ T J ^ 4), (1 / 256 : ℝ) ^ J :=
                Finset.sum_le_sum hlayer
            _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
        have h3 : ((X.filter fun s => ¬ |d s| ≤ T J ^ 4).card : ℝ) ≤ X.card := by
          exact_mod_cast Finset.card_filter_le _ _
        have h4 : ((X.filter fun s => ¬ |d s| ≤ T J ^ 4).card : ℝ) * (1 / 256 : ℝ) ^ J ≤
            (X.card : ℝ) * (1 / 256 : ℝ) ^ J := mul_le_mul_of_nonneg_right h3 hb0
        linarith
      have hc := hcount (T (J + 1)) (hT0 _)
      have e1 : (1 / 256 : ℝ) ^ J * (2 : ℝ) ^ J = (1 / 128 : ℝ) ^ J := by
        rw [← mul_pow]
        norm_num
      have e2 : (1 / 256 : ℝ) ^ J * (4 : ℝ) ^ J = (1 / 64 : ℝ) ^ J := by
        rw [← mul_pow]
        norm_num
      have e3 : ((2 : ℝ) ^ J) ^ 2 = (4 : ℝ) ^ J := by
        rw [← pow_mul, mul_comm J 2, pow_mul]
        norm_num
      have hcb : (1 / 256 : ℝ) ^ J * (X.card : ℝ) ≤
          2 * (1 / 128 : ℝ) ^ J * (A * t) + (1 / 256 : ℝ) ^ J * B +
            4 * (1 / 64 : ℝ) ^ J * (E * t ^ 2) := by
        have h1 := mul_le_mul_of_nonneg_left hc hb0
        have e4 : (1 / 256 : ℝ) ^ J * (A * T (J + 1) + B + E * T (J + 1) ^ 2) =
            2 * ((1 / 256 : ℝ) ^ J * (2 : ℝ) ^ J) * (A * t) + (1 / 256 : ℝ) ^ J * B +
              4 * ((1 / 256 : ℝ) ^ J * ((2 : ℝ) ^ J) ^ 2) * (E * t ^ 2) := by
          simp only [hT]
          ring
        rw [e4, e1, e3, e2] at h1
        exact h1
      have ha0 : 0 ≤ (1 / 128 : ℝ) ^ J := by positivity
      have hc0 : 0 ≤ (1 / 64 : ℝ) ^ J := by positivity
      have hstep := mul_nonneg ha0 hAt
      have hstep2 := mul_nonneg hb0 hB
      have hstep3 := mul_nonneg hc0 hEt
      rw [pow_succ, pow_succ, pow_succ]
      nlinarith
  obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt ((∑ s ∈ S, |d s|) / t ^ 4)
    (show (1 : ℝ) < 16 by norm_num)
  have hall : ∀ s ∈ S, |d s| ≤ T J ^ 4 := by
    intro s hs
    have h1 : |d s| ≤ ∑ s ∈ S, |d s| :=
      Finset.single_le_sum (f := fun s => |d s|) (fun _ _ => abs_nonneg _) hs
    rw [div_lt_iff₀ ht4] at hJ
    rw [hT4]
    linarith
  have hFJ : F J = ∑ s ∈ S, g s := by
    simp only [hF]
    rw [Finset.filter_true_of_mem hall]
  have hfin := hinv J
  rw [hFJ] at hfin
  have ha0 : 0 ≤ (1 / 128 : ℝ) ^ J := by positivity
  have hb0 : 0 ≤ (1 / 256 : ℝ) ^ J := by positivity
  have hc0 : 0 ≤ (1 / 64 : ℝ) ^ J := by positivity
  have h1 := mul_nonneg ha0 hAt
  have h2 := mul_nonneg hb0 hB
  have h3 := mul_nonneg hc0 hEt
  nlinarith

/-! ### The dyadic shells of the shorter leg -/

/-- The dyadic index of the shorter leg: `2^i ≤ m < 2^{i+1}`. -/
def shellIdx (p k : Mode) : ℕ := Nat.log 2 ⌊minLeg p k⌋₊

theorem shellIdx_bounds {p k : Mode} (hp : p ∈ nearBox k) :
    (2 : ℝ) ^ shellIdx p k ≤ minLeg p k ∧ minLeg p k < 2 ^ (shellIdx p k + 1) := by
  have hm := one_le_minLeg hp
  set m := minLeg p k with hmdef
  have hf : ⌊m⌋₊ ≠ 0 := (Nat.floor_pos.2 hm).ne'
  have h1 : 2 ^ Nat.log 2 ⌊m⌋₊ ≤ ⌊m⌋₊ := Nat.pow_log_le_self 2 hf
  have h2 : ⌊m⌋₊ < 2 ^ (Nat.log 2 ⌊m⌋₊ + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  constructor
  · calc (2 : ℝ) ^ shellIdx p k ≤ (⌊m⌋₊ : ℝ) := by
          simp only [shellIdx, ← hmdef]
          exact_mod_cast h1
      _ ≤ m := Nat.floor_le (by linarith)
  · have h3 : (⌊m⌋₊ : ℝ) + 1 ≤ 2 ^ (shellIdx p k + 1) := by
      simp only [shellIdx, ← hmdef]
      exact_mod_cast h2
    have h4 := Nat.lt_floor_add_one m
    linarith

theorem shellIdx_le {p k : Mode} (hp : p ∈ nearBox k) :
    shellIdx p k ≤ Nat.log 2 ⌊absk k⌋₊ :=
  Nat.log_mono_right (Nat.floor_le_floor (minLeg_le_absk hp))

/-- The near triads of one pattern on the dyadic shell `i` of the shorter leg. -/
def shellSet (s₁ s₂ : Sgn) (k : Mode) (i : ℕ) : Finset Mode :=
  (nearBox k).filter fun p => IsNear s₁ s₂ p k ∧ shellIdx p k = i

theorem normD_sub (p k : Mode) : normD (k - p) k = normD p k := by
  unfold normD
  rw [sub_sub_cancel]
  ring

/-- `|p| < R` puts `p` in the box of side `R`. -/
theorem mem_modeBox_of_absk_lt {p : Mode} {R : ℕ} (h : absk p < R) : p ∈ modeBox R := by
  rw [mem_modeBox]
  intro i
  have h1 : |(p i : ℝ)| ≤ R := (abs_coord_le_absk p i).trans h.le
  have h2 : ((|p i| : ℤ) : ℝ) ≤ ((R : ℤ) : ℝ) := by
    rw [Int.cast_abs]
    exact_mod_cast h1
  exact_mod_cast h2

/-- **The shell count**: a shell point has a leg of length `< 2^{i+1}`; by the symmetry
`p ↔ k − p` of `D`, the shell count is at most twice the box count. -/
theorem card_shell_le (s₁ s₂ : Sgn) (k : Mode) (i : ℕ) (τ : ℝ) :
    (((shellSet s₁ s₂ k i).filter fun p => |(normD p k : ℝ)| ≤ τ ^ 4).card : ℝ) ≤
      2 * ((boxSet k (2 ^ (i + 1)) τ).card : ℝ) := by
  classical
  set R : ℕ := 2 ^ (i + 1) with hR
  have hsub : (shellSet s₁ s₂ k i).filter (fun p => |(normD p k : ℝ)| ≤ τ ^ 4) ⊆
      boxSet k R τ ∪ (boxSet k R τ).image fun p => k - p := by
    intro p hp
    rw [Finset.mem_filter, shellSet, Finset.mem_filter] at hp
    obtain ⟨⟨hbox, -, hi⟩, hle⟩ := hp
    have hlt := (shellIdx_bounds hbox).2
    rw [hi] at hlt
    have hRcast : (2 : ℝ) ^ (i + 1) = (R : ℝ) := by
      rw [hR]
      push_cast
      rfl
    rw [hRcast] at hlt
    rw [Finset.mem_union, Finset.mem_image]
    rcases min_lt_iff.1 hlt with h | h
    · exact Or.inl (mem_boxSet.2 ⟨mem_modeBox_of_absk_lt h, hle⟩)
    · refine Or.inr ⟨k - p, mem_boxSet.2 ⟨mem_modeBox_of_absk_lt h, ?_⟩, sub_sub_cancel k p⟩
      rw [normD_sub]
      exact hle
  have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h2 : ((boxSet k R τ).image fun p => k - p).card ≤ (boxSet k R τ).card :=
    Finset.card_image_le
  have h3 : ((shellSet s₁ s₂ k i).filter fun p => |(normD p k : ℝ)| ≤ τ ^ 4).card ≤
      2 * (boxSet k R τ).card := by omega
  exact_mod_cast h3

/-- **The Lorentzian on a shell** (FULL_LOCAL_PROOF_210 eq. (1.3)): for `M ≤ m < 2M` and
`h ≥ 108 M² K⁶/q`, `κ_N² ≤ (M²K⁶)⁻¹ [1 + (D/h)²]⁻¹`. -/
theorem nearW_le_lorentz {q : ℝ} (hq : 0 < q) {s₁ s₂ : Sgn} {p k : Mode} (hp : p ∈ nearBox k)
    (hn : IsNear s₁ s₂ p k) {M h : ℝ} (hM : 0 < M) (hmM : M ≤ minLeg p k)
    (hmM2 : minLeg p k < 2 * M) (hh : 108 * M ^ 2 * absk k ^ 6 / q ≤ h) :
    nearW q s₁ s₂ p k ≤ (M ^ 2 * absk k ^ 6)⁻¹ * (1 + ((normD p k : ℝ) / h) ^ 2)⁻¹ := by
  have hK1 := (one_le_absk_of_mem_nearBox hp).1
  have hK0 : 0 < absk k := by linarith
  have hm := minLeg_pos hp
  have hh0 : 0 < h := lt_of_lt_of_le (by positivity) hh
  have hhq : 108 * M ^ 2 * absk k ^ 6 ≤ h * q := (div_le_iff₀ hq).1 hh
  have hw : |(k 2 : ℝ)| ≤ absk k := abs_coord_le_absk k 2
  have hDle := abs_normD_le_of_near hp hn
  set Φ := nearPhi s₁ s₂ p k with hΦ
  set D : ℝ := (normD p k : ℝ) with hD
  have hΦ0 : 0 ≤ |Φ| := abs_nonneg Φ
  -- `|D| K² ≤ |Φ| h q`
  have h1 : |D| ≤ 108 * |Φ| * M ^ 2 * absk k ^ 4 := by
    have hm2 : minLeg p k ^ 2 ≤ (2 * M) ^ 2 := pow_le_pow_left₀ hm.le hmM2.le 2
    calc |D| ≤ 27 * |Φ| * minLeg p k ^ 2 * absk k ^ 3 * |(k 2 : ℝ)| := hDle
      _ ≤ 27 * |Φ| * (2 * M) ^ 2 * absk k ^ 3 * absk k := by gcongr
      _ = 108 * |Φ| * M ^ 2 * absk k ^ 4 := by ring
  have h2 : |D| * absk k ^ 2 ≤ |Φ| * (h * q) := by
    calc |D| * absk k ^ 2 ≤ (108 * |Φ| * M ^ 2 * absk k ^ 4) * absk k ^ 2 := by gcongr
      _ = |Φ| * (108 * M ^ 2 * absk k ^ 6) := by ring
      _ ≤ |Φ| * (h * q) := by gcongr
  -- `(D/h)² K⁴ ≤ q²Φ²`
  have h3 : (D / h) ^ 2 * absk k ^ 4 ≤ q ^ 2 * Φ ^ 2 := by
    have h4 : |D| / h * absk k ^ 2 ≤ |Φ| * q := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hh0]
      nlinarith
    have h5 : 0 ≤ |D| / h * absk k ^ 2 := by positivity
    have h6 := pow_le_pow_left₀ h5 h4 2
    have e1 : (|D| / h * absk k ^ 2) ^ 2 = (D / h) ^ 2 * absk k ^ 4 := by
      rw [mul_pow, div_pow, sq_abs, div_pow]
      ring
    have e2 : (|Φ| * q) ^ 2 = q ^ 2 * Φ ^ 2 := by
      rw [mul_pow, sq_abs]
      ring
    linarith
  have e : nearW q s₁ s₂ p k = nearKer q s₁ s₂ p k := by simp [nearW, hn]
  rw [e, nearKer, ← mul_inv, one_div]
  apply inv_anti₀ (by positivity)
  have hM2 : M ^ 2 ≤ minLeg p k ^ 2 := pow_le_pow_left₀ hM.le hmM 2
  calc M ^ 2 * absk k ^ 6 * (1 + (D / h) ^ 2)
      = M ^ 2 * absk k ^ 2 * (absk k ^ 4 + (D / h) ^ 2 * absk k ^ 4) := by ring
    _ ≤ minLeg p k ^ 2 * absk k ^ 2 * (absk k ^ 4 + q ^ 2 * Φ ^ 2) := by gcongr

/-- **The shell moment** (FULL_LOCAL_PROOF_210 eq. (2.3); without the factor `|k₃|^{−1/2}`), for
`K = z²`, `q = y⁴`: each dyadic shell of the shorter leg of one pattern contributes at most
`19200/(y z⁹) + 600/z¹² + 1344/(y²z⁸)`, i.e. `≲ q^{−1/4}K^{−9/2} + K^{−6} + q^{−1/2}K^{−4}`,
independently of the shell (the power of `M` cancels: `−2 + 3/2 + 1/2 = 0`). -/
theorem sum_shell_le {q y z : ℝ} (hy : 0 < y) (hq : q = y ^ 4) {k : Mode} (hk : k 2 ≠ 0)
    (hz : 0 < z) (hzK : z ^ 2 = absk k) (s₁ s₂ : Sgn) (i : ℕ) :
    ∑ p ∈ shellSet s₁ s₂ k i, nearW q s₁ s₂ p k ≤
      19200 / (y * z ^ 9) + 600 / z ^ 12 + 1344 / (y ^ 2 * z ^ 8) := by
  classical
  have hq0 : 0 < q := by rw [hq]; positivity
  have hK0 : 0 < absk k := by rw [← hzK]; positivity
  set M : ℝ := 2 ^ i with hM
  have hM1 : 1 ≤ M := one_le_pow₀ (by norm_num)
  have hM0 : 0 < M := by linarith
  set s := Real.sqrt M with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hM0
  have hss : s ^ 2 = M := Real.sq_sqrt hM0.le
  set t := 4 * s * z ^ 3 / y with ht
  have ht0 : 0 < t := by positivity
  have ht2 : t ^ 2 = 16 * M * z ^ 6 / y ^ 2 := by
    rw [ht, ← hss]
    field_simp
    ring
  have ht4 : t ^ 4 = 256 * M ^ 2 * absk k ^ 6 / q := by
    rw [hq, ← hzK, ht, ← hss]
    field_simp
    ring
  have hh : 108 * M ^ 2 * absk k ^ 6 / q ≤ t ^ 4 := by
    rw [ht4]
    gcongr
    norm_num
  -- the pointwise comparison
  have hpt : ∀ p ∈ shellSet s₁ s₂ k i, nearW q s₁ s₂ p k ≤
      (M ^ 2 * absk k ^ 6)⁻¹ * (1 + ((normD p k : ℝ) / t ^ 4) ^ 2)⁻¹ := by
    intro p hp
    rw [shellSet, Finset.mem_filter] at hp
    obtain ⟨hbox, hn, hi⟩ := hp
    obtain ⟨h1, h2⟩ := shellIdx_bounds hbox
    rw [hi] at h1 h2
    exact nearW_le_lorentz hq0 hbox hn hM0 h1 (by rw [pow_succ] at h2; linarith) hh
  -- the count
  have hcount : ∀ τ : ℝ, 0 ≤ τ →
      (((shellSet s₁ s₂ k i).filter fun p => |(normD p k : ℝ)| ≤ τ ^ 4).card : ℝ) ≤
        (1200 * M * s) * τ + 200 * M ^ 2 + (14 * M / absk k) * τ ^ 2 := by
    intro τ hτ
    have h1 := card_shell_le s₁ s₂ k i τ
    have h2 := card_boxSet_le hk (2 ^ (i + 1)) hτ
    set Y : ℝ := 2 * ((2 ^ (i + 1) : ℕ) : ℝ) + 1 with hY
    have hYe : Y = 4 * M + 1 := by
      rw [hY, hM]
      push_cast
      rw [pow_succ]
      ring
    have hY5 : Y ≤ 5 * M := by rw [hYe]; linarith
    have hY0 : 0 ≤ Y := by rw [hYe]; positivity
    have hsY : Real.sqrt Y ≤ 3 * s := by
      refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
      rw [mul_pow, hss]
      nlinarith
    have hY2 : Y ^ 2 ≤ 25 * M ^ 2 := by
      have := pow_le_pow_left₀ hY0 hY5 2
      nlinarith
    have hYs : Y * Real.sqrt Y ≤ 5 * M * (3 * s) :=
      mul_le_mul hY5 hsY (Real.sqrt_nonneg _) (by positivity)
    have hYK : Y / absk k ≤ 5 * M / absk k := by gcongr
    have h3 : 40 * τ * (Y * Real.sqrt Y) ≤ 40 * τ * (5 * M * (3 * s)) := by gcongr
    have h4 : 4 / 3 * (Y / absk k) * τ ^ 2 ≤ 4 / 3 * (5 * M / absk k) * τ ^ 2 := by gcongr
    have h5 : (M / absk k) * τ ^ 2 ≥ 0 := by positivity
    have e1 : 4 / 3 * (5 * M / absk k) * τ ^ 2 = 20 / 3 * ((M / absk k) * τ ^ 2) := by ring
    have e2 : (14 * M / absk k) * τ ^ 2 = 14 * ((M / absk k) * τ ^ 2) := by ring
    rw [e1] at h4
    rw [e2]
    nlinarith
  have hA : 0 ≤ 1200 * M * s := by positivity
  have hB : 0 ≤ 200 * M ^ 2 := by positivity
  have hE : 0 ≤ 14 * M / absk k := by positivity
  have hlayer := layer_sum_le (shellSet s₁ s₂ k i) (fun p => (normD p k : ℝ)) hA hB hE ht0 hcount
  have hinv0 : 0 ≤ (M ^ 2 * absk k ^ 6)⁻¹ := by positivity
  calc ∑ p ∈ shellSet s₁ s₂ k i, nearW q s₁ s₂ p k
      ≤ ∑ p ∈ shellSet s₁ s₂ k i,
          (M ^ 2 * absk k ^ 6)⁻¹ * (1 + ((normD p k : ℝ) / t ^ 4) ^ 2)⁻¹ :=
        Finset.sum_le_sum hpt
    _ = (M ^ 2 * absk k ^ 6)⁻¹ * ∑ p ∈ shellSet s₁ s₂ k i,
          (1 + ((normD p k : ℝ) / t ^ 4) ^ 2)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ (M ^ 2 * absk k ^ 6)⁻¹ * (4 * (1200 * M * s) * t + 3 * (200 * M ^ 2) +
          6 * (14 * M / absk k) * t ^ 2) := by gcongr
    _ = 19200 / (y * z ^ 9) + 600 / z ^ 12 + 1344 / (y ^ 2 * z ^ 8) := by
        rw [ht2, ht, ← hzK, ← hss]
        field_simp
        ring

/-! ### Summing the shells: the high outputs (FULL_LOCAL_PROOF_210 §5) -/

/-- The index of the top shell. -/
def shellTop (k : Mode) : ℕ := Nat.log 2 ⌊absk k⌋₊

/-- One pattern, all shells. -/
theorem sum_pattern_le {q y z : ℝ} (hy : 0 < y) (hq : q = y ^ 4) {k : Mode} (hk : k 2 ≠ 0)
    (hz : 0 < z) (hzK : z ^ 2 = absk k) (s₁ s₂ : Sgn) :
    ∑ p ∈ (nearBox k).filter (fun p => IsNear s₁ s₂ p k), nearW q s₁ s₂ p k ≤
      ((shellTop k : ℝ) + 1) *
        (19200 / (y * z ^ 9) + 600 / z ^ 12 + 1344 / (y ^ 2 * z ^ 8)) := by
  classical
  set N := (nearBox k).filter (fun p => IsNear s₁ s₂ p k) with hN
  have hmaps : ∀ p ∈ N, shellIdx p k ∈ Finset.range (shellTop k + 1) := fun p hp => by
    rw [Finset.mem_range]
    have := shellIdx_le (Finset.mem_filter.1 hp).1
    simp only [shellTop]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ i, N.filter (fun p => shellIdx p k = i) = shellSet s₁ s₂ k i := fun i => by
    ext p
    simp only [hN, shellSet, Finset.mem_filter, and_assoc]
  calc ∑ i ∈ Finset.range (shellTop k + 1), ∑ p ∈ N.filter (fun p => shellIdx p k = i),
        nearW q s₁ s₂ p k
      ≤ ∑ _i ∈ Finset.range (shellTop k + 1),
          (19200 / (y * z ^ 9) + 600 / z ^ 12 + 1344 / (y ^ 2 * z ^ 8)) :=
        Finset.sum_le_sum fun i _ => by
          rw [hfib]
          exact sum_shell_le hy hq hk hz hzK s₁ s₂ i
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- All patterns, all shells: `momN q k ≤ 4(I + 1)(q^{−1/4}K^{−9/2} + K^{−6} + q^{−1/2}K^{−4})`, up
to the constants of `sum_shell_le`.  Valid for every fast output and every `q > 0`. -/
theorem momN_le_direct {q y z : ℝ} (hy : 0 < y) (hq : q = y ^ 4) {k : Mode} (hk : k 2 ≠ 0)
    (hz : 0 < z) (hzK : z ^ 2 = absk k) :
    momN q k ≤ 4 * ((shellTop k : ℝ) + 1) *
      (19200 / (y * z ^ 9) + 600 / z ^ 12 + 1344 / (y ^ 2 * z ^ 8)) := by
  rw [momN_eq_sum_patterns]
  calc ∑ s : Sgn × Sgn,
        ∑ p ∈ (nearBox k).filter (fun p => IsNear s.1 s.2 p k), nearW q s.1 s.2 p k
      ≤ ∑ _s : Sgn × Sgn, ((shellTop k : ℝ) + 1) *
          (19200 / (y * z ^ 9) + 600 / z ^ 12 + 1344 / (y ^ 2 * z ^ 8)) :=
        Finset.sum_le_sum fun s _ => sum_pattern_le hy hq hk hz hzK s.1 s.2
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool,
          nsmul_eq_mul]
        push_cast
        ring

/-- The number of shells: `I + 1 ≤ 3(1 + log z)` for `K = z²`. -/
theorem shellTop_add_one_le {k : Mode} {z : ℝ} (hz : 1 ≤ z) (hzK : z ^ 2 = absk k) :
    (shellTop k : ℝ) + 1 ≤ 3 * (1 + Real.log z) := by
  have hz0 : 0 < z := by linarith
  have hK1 : 1 ≤ absk k := by
    rw [← hzK]
    exact one_le_pow₀ hz
  have hK0 : 0 < absk k := by linarith
  have hf : ⌊absk k⌋₊ ≠ 0 := (Nat.floor_pos.2 hK1).ne'
  have h1 : (2 : ℝ) ^ shellTop k ≤ absk k := by
    have h2 : 2 ^ shellTop k ≤ ⌊absk k⌋₊ := Nat.pow_log_le_self 2 hf
    calc (2 : ℝ) ^ shellTop k ≤ (⌊absk k⌋₊ : ℝ) := by exact_mod_cast h2
      _ ≤ absk k := Nat.floor_le hK0.le
  have h3 : (shellTop k : ℝ) * Real.log 2 ≤ 2 * Real.log z := by
    have h4 := Real.log_le_log (by positivity) h1
    rw [Real.log_pow, ← hzK, Real.log_pow] at h4
    push_cast at h4
    exact h4
  have hl2 : (2 / 3 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    norm_num at this ⊢
    linarith
  have hI : (0 : ℝ) ≤ (shellTop k : ℝ) := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.log z := Real.log_nonneg hz
  nlinarith

/-- `(1 + log z)/zⁿ` is decreasing for `z ≥ 1`, `n ≥ 1`: this pays the shell logarithm. -/
theorem one_add_log_div_pow_le {v z : ℝ} (hv : 1 ≤ v) (hz : v ≤ z) {n : ℕ} (hn : 1 ≤ n) :
    (1 + Real.log z) / z ^ n ≤ (1 + Real.log v) / v ^ n := by
  have hv0 : 0 < v := by linarith
  have hz0 : 0 < z := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  set x := z / v with hx
  have hx1 : 1 ≤ x := (one_le_div hv0).2 hz
  have hzx : z = v * x := by
    rw [hx]
    field_simp
  have hlz : Real.log z = Real.log v + Real.log x := by
    rw [hzx, Real.log_mul hv0.ne' (by positivity)]
  have hzn : z ^ n = v ^ n * x ^ n := by
    rw [hzx, mul_pow]
  rw [hlz, hzn]
  have hlx : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlv0 : 0 ≤ Real.log v := Real.log_nonneg hv
  have hxn : x ≤ x ^ n := le_self_pow₀ hx1 (by omega)
  have hvn : 0 < v ^ n := by positivity
  have key : 1 + Real.log v + Real.log x ≤ (1 + Real.log v) * x ^ n := by
    have h1 : (1 + Real.log v) * x ≤ (1 + Real.log v) * x ^ n := by gcongr
    nlinarith
  calc (1 + (Real.log v + Real.log x)) * v ^ n = (1 + Real.log v + Real.log x) * v ^ n := by ring
    _ ≤ ((1 + Real.log v) * x ^ n) * v ^ n := by gcongr
    _ = (1 + Real.log v) * (v ^ n * x ^ n) := by ring

/-- **The direct high-output bound, proper** (TeX quantitative_energies l.350–352; here `q = v¹²`):
for `K ≥ v² = q^{1/6}`, `momP q k ≤ 253728 (1 + log v) q^{−2/3}`.  All three terms of the shell
moment are exactly balanced or better at `K = q^{1/6}`:
`K²·q^{−1/4}K^{−9/2} = q^{−1/4}K^{−5/2} ≤ q^{−2/3}`, `K²·K^{−6} ≤ q^{−2/3}`,
`K²·q^{−1/2}K^{−4} ≤ q^{−5/6}`.  The number of shells is paid by `one_add_log_div_pow_le`. -/
theorem momP_high {v : ℝ} (hv : 1 ≤ v) {k : Mode} (hk : k 2 ≠ 0) (hK : v ^ 2 ≤ absk k) :
    momP (v ^ 12) k ≤ 253728 * (1 + Real.log v) / v ^ 8 := by
  have hv0 : 0 < v := by linarith
  have hK0 : 0 < absk k := lt_of_lt_of_le (by positivity) hK
  set z := Real.sqrt (absk k) with hz
  have hz0 : 0 < z := Real.sqrt_pos.2 hK0
  have hzK : z ^ 2 = absk k := Real.sq_sqrt hK0.le
  have hvz : v ≤ z := Real.le_sqrt_of_sq_le hK
  have hz1 : 1 ≤ z := hv.trans hvz
  have h := momN_le_direct (q := v ^ 12) (y := v ^ 3) (z := z) (by positivity) (by ring) hk hz0 hzK
  set L := (shellTop k : ℝ) + 1 with hL
  have hL3 : L ≤ 3 * (1 + Real.log z) := shellTop_add_one_le hz1 hzK
  have hL0 : 0 ≤ L := by positivity
  set X := 1 + Real.log v with hX
  have hX1 : 1 ≤ X := by
    have := Real.log_nonneg hv
    linarith
  have hLz : ∀ n : ℕ, 1 ≤ n → L / z ^ n ≤ 3 * (X / v ^ n) := by
    intro n hn
    calc L / z ^ n ≤ (3 * (1 + Real.log z)) / z ^ n := by gcongr
      _ = 3 * ((1 + Real.log z) / z ^ n) := by ring
      _ ≤ 3 * (X / v ^ n) :=
          mul_le_mul_of_nonneg_left (one_add_log_div_pow_le hv hvz hn) (by norm_num)
  have hKz : absk k ^ 2 = z ^ 4 := by
    rw [← hzK]
    ring
  have h10 : X / v ^ 10 ≤ X / v ^ 8 := by
    have h1 : v ^ 8 ≤ v ^ 10 := pow_le_pow_right₀ hv (by norm_num)
    gcongr
  unfold momP
  rw [hKz]
  calc z ^ 4 * momN (v ^ 12) k
      ≤ z ^ 4 * (4 * L * (19200 / (v ^ 3 * z ^ 9) + 600 / z ^ 12 +
          1344 / ((v ^ 3) ^ 2 * z ^ 8))) := by gcongr
    _ = 4 * (19200 / v ^ 3 * (L / z ^ 5) + 600 * (L / z ^ 8) + 1344 / v ^ 6 * (L / z ^ 4)) := by
        field_simp
    _ ≤ 4 * (19200 / v ^ 3 * (3 * (X / v ^ 5)) + 600 * (3 * (X / v ^ 8)) +
          1344 / v ^ 6 * (3 * (X / v ^ 4))) := by
        have h5 := hLz 5 (by norm_num)
        have h8 := hLz 8 (by norm_num)
        have h4 := hLz 4 (by norm_num)
        gcongr
    _ = 12 * (19800 * (X / v ^ 8) + 1344 * (X / v ^ 10)) := by
        field_simp
        ring
    _ ≤ 12 * (19800 * (X / v ^ 8) + 1344 * (X / v ^ 8)) := by gcongr
    _ = 253728 * X / v ^ 8 := by ring

/-- **The direct high-output bound, native**: for `K ≥ v² = q^{1/6}`,
`momN q k ≤ 253728 (1 + log v)/q` (divide `momP_high` by `K² ≥ q^{1/3}`). -/
theorem momN_high {v : ℝ} (hv : 1 ≤ v) {k : Mode} (hk : k 2 ≠ 0) (hK : v ^ 2 ≤ absk k) :
    momN (v ^ 12) k ≤ 253728 * (1 + Real.log v) / v ^ 12 := by
  have hv0 : 0 < v := by linarith
  have hP := momP_high hv hk hK
  have hN0 := momN_nonneg (v ^ 12) k
  have hK2 : v ^ 4 ≤ absk k ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hK 2
    calc v ^ 4 = (v ^ 2) ^ 2 := by ring
      _ ≤ absk k ^ 2 := this
  have h1 : v ^ 4 * momN (v ^ 12) k ≤ 253728 * (1 + Real.log v) / v ^ 8 :=
    (mul_le_mul_of_nonneg_right hK2 hN0).trans hP
  have e : 253728 * (1 + Real.log v) / v ^ 12 =
      (253728 * (1 + Real.log v) / v ^ 8) / v ^ 4 := by
    field_simp
  rw [e, le_div_iff₀ (by positivity)]
  linarith

end OVNS.Quant.NearJ

end
