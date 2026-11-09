import OddViscousNS.Quant.Energy.Native.TriadBound

/-!
# Theorem 1.2, fixed force — E5/E8 native layer: the assembled near bounds

The L6 assembly (LOCAL210 §6; report §2 Step 3).  The triad term of `nearD_eq_tsum_triad` is
bounded at each triad with its longest leg as output: the near kernel `kerB` is exactly
`13 m² K^{2j+1} √(nearKer)` (`kerB_le_nearKerSum`), the three possible positions of the longest
leg give the regions `A` (`Π_F h` on the longest leg) and `B`, `C` (an `F` on it), the helicities
give a factor `8`, the native weights a factor `4`.  Each region is a sum of the form
`Σ_k U_k Σ_{p ∈ nearBox k} κ_N(k,p) V_p W_{k−p}` (`boxTerm`), summed by `moment_cauchy`.

The constant is `nearC₀ = 26`: `8 · 13 · 4 = 416` per placement of the weights, with `3` regions
(`6` placements for `j = 2`, where `H³` goes on either `F` leg), and `2496 = 26 · 96`.

## Amendments to the scaffold statements
* `nearD1_le`/`nearD2_le` take `IsReal F`, `IsReal h`: the cyclic cancellation compares the three
  rootings on common amplitudes, which needs the reflected test amplitude (`inner_hel_real`).
* They conclude with `nearC₀ * nearN |r|`, and the roles carry `nearC₀` and the product-leaf
  constants.  The roles take `Adm` fields, which give the reality of the source.

## Reading choices
* Reality is what this proof uses; whether the bounds fail without it is not settled.
* The source `h = Π_F Q_τ(F, F)` uses the library's phased convection `Qphase` at an arbitrary
  phase `τ'` (TeX `Q_τ`); the mixed partner `2Π_F Q_τ(S, F)` (Body 19 §1) is not treated here.
-/

noncomputable section

namespace OVNS.Quant

open scoped Classical

/-- The constant of the near bounds relative to `nearN`. -/
def nearC₀ : ℝ := 26

theorem nearC₀_pos : 0 < nearC₀ := by norm_num [nearC₀]

/-! ### The box sums -/

/-- The summand `U_k κ_N(k, u) V_u W_{k−u}` of the near-box sum, on `u ∈ nearBox k`. -/
def boxTerm (q : ℝ) (U V W : Mode → ℝ) (y : Mode × Mode) : ℝ :=
  if y.2 ∈ nearBox y.1 then U y.1 * (nearKerSum q y.1 y.2 * (V y.2 * W (y.1 - y.2))) else 0

private lemma boxTerm_of_mem {q : ℝ} {U V W : Mode → ℝ} {k u : Mode} (hu : u ∈ nearBox k) :
    boxTerm q U V W (k, u) = U k * (nearKerSum q k u * (V u * W (k - u))) :=
  ite_eq_left hu

private lemma boxTerm_nonneg (q : ℝ) {U V W : Mode → ℝ} (hU : ∀ k, 0 ≤ U k) (hV : ∀ k, 0 ≤ V k)
    (hW : ∀ k, 0 ≤ W k) (y : Mode × Mode) : 0 ≤ boxTerm q U V W y := by
  unfold boxTerm
  split_ifs
  · exact mul_nonneg (hU _) (mul_nonneg (nearKerSum_nonneg _ _ _) (mul_nonneg (hV _) (hW _)))
  · exact le_rfl

/-- The box sum over the lattice square, by `moment_cauchy`. -/
theorem boxTerm_tsum_le (q : ℝ) {U V W : Mode → ℝ} (hU : ∀ k, 0 ≤ U k) (hV : ∀ k, 0 ≤ V k)
    (hW : ∀ k, 0 ≤ W k) (hU2 : Summable fun k => U k ^ 2) (hV2 : Summable fun k => V k ^ 2)
    (hW2 : Summable fun k => W k ^ 2) :
    Summable (boxTerm q U V W) ∧ ∑' y, boxTerm q U V W y ≤
      Real.sqrt (MomN q) *
        (Real.sqrt (∑' k, U k ^ 2) * Real.sqrt (∑' k, V k ^ 2) * Real.sqrt (∑' k, W k ^ 2)) := by
  obtain ⟨hs, hle⟩ := moment_cauchy (κ := nearKerSum q) (M := MomN q)
    (fun k p => nearKerSum_nonneg q k p)
    (fun k => by rw [sum_nearKerSum_sq]; exact momN_le_MomN q k) hU hV hW hU2 hV2 hW2
  have h0 : ∀ k, ∀ u ∉ nearBox k, boxTerm q U V W (k, u) = 0 := fun k u hu =>
    ite_eq_right hu
  have hfib : ∀ k, Summable fun u => boxTerm q U V W (k, u) := fun k =>
    summable_of_ne_finset_zero (h0 k)
  have hval : ∀ k, ∑' u, boxTerm q U V W (k, u) =
      U k * ∑ p ∈ nearBox k, nearKerSum q k p * (V p * W (k - p)) := fun k => by
    rw [tsum_eq_sum (h0 k), Finset.mul_sum]
    exact Finset.sum_congr rfl fun u hu => boxTerm_of_mem hu
  have hsum : Summable (boxTerm q U V W) :=
    (summable_prod_of_nonneg (boxTerm_nonneg q hU hV hW)).2
      ⟨hfib, by simpa only [Function.comp_def, hval] using hs⟩
  refine ⟨hsum, ?_⟩
  rw [hsum.tsum_prod]
  simpa only [hval] using hle

/-! ### The near kernel -/

/-- `kerB` at the near box is `13 m² K^{2j+1}` times the unit kernel, so at most
`13 m² K^{2j+1} κ_N`. -/
theorem kerB_le_nearKerSum (j : ℕ) (r Φ : ℝ) {k u : Mode} (hu : u ∈ nearBox k) {s₁ s₂ : Sgn}
    (hΦ : |Φ| = |nearPhi s₁ s₂ u k|) (h0 : 0 < |Φ|) (h1 : |Φ| < 1) :
    kerB j (r * Φ) (minLeg u k) (absk k) ≤
      13 * minLeg u k ^ 2 * absk k ^ (2 * j + 1) * nearKerSum |r| k u := by
  have hm : 0 < minLeg u k := minLeg_pos hu
  have hK : 0 < absk k := lt_of_lt_of_le one_pos (one_le_absk_of_mem_nearBox hu).1
  set m := minLeg u k
  set K := absk k
  have hsq : nearPhi s₁ s₂ u k ^ 2 = Φ ^ 2 := by rw [← sq_abs, ← hΦ, sq_abs]
  set D := K ^ 4 + (r * Φ) ^ 2 with hD
  have hD0 : 0 < D := by positivity
  have hsD : 0 < Real.sqrt D := Real.sqrt_pos.2 hD0
  have hNear : IsNear s₁ s₂ u k := ⟨hΦ ▸ h0, hΦ ▸ h1⟩
  have hker : nearKer |r| s₁ s₂ u k = (1 / (m * K * Real.sqrt D)) ^ 2 := by
    have e0 : absk k ^ 4 + r ^ 2 * Φ ^ 2 = D := by rw [hD, mul_pow]
    rw [nearKer, hsq, sq_abs, e0, div_pow, mul_pow, mul_pow, Real.sq_sqrt hD0.le]
    norm_num
    exact Or.inl rfl
  have hsqrt : 1 / (m * K * Real.sqrt D) ≤ nearKerSum |r| k u := by
    have h2 : nearW |r| s₁ s₂ u k = nearKer |r| s₁ s₂ u k := ite_eq_left hNear
    have h3 : nearW |r| s₁ s₂ u k ≤ ∑ s : Sgn × Sgn, nearW |r| s.1 s.2 u k := by
      have h5 := Finset.single_le_sum (s := Finset.univ) (a := (s₁, s₂))
        (f := fun s : Sgn × Sgn => nearW |r| s.1 s.2 u k)
        (fun s _ => nearW_nonneg |r| s.1 s.2 u k) (Finset.mem_univ _)
      exact h5
    have h4 : Real.sqrt (nearW |r| s₁ s₂ u k) ≤ nearKerSum |r| k u := Real.sqrt_le_sqrt h3
    have h6 : Real.sqrt (nearW |r| s₁ s₂ u k) = 1 / (m * K * Real.sqrt D) := by
      rw [h2, hker]
      exact Real.sqrt_sq (by positivity)
    exact h6 ▸ h4
  have e : kerB j (r * Φ) m K = 13 * m ^ 2 * K ^ (2 * j + 1) * (1 / (m * K * Real.sqrt D)) := by
    unfold kerB
    rw [← hD]
    field_simp
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_left hsqrt (by positivity)

/-- The eight helicities at a triad with output `k`, in the box of `k`. -/
private lemma sum_ker_le (j : ℕ) (r : ℝ) {p q k u : Mode} (hu : u ∈ nearBox k)
    (hpat : ∀ a b c, ∃ s₁ s₂, |Phi a b c p q| = |nearPhi s₁ s₂ u k|) :
    (∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn,
      if NearT a b c p q then kerB j (r * Phi a b c p q) (minLeg u k) (absk k) else 0) ≤
      8 * (13 * minLeg u k ^ 2 * absk k ^ (2 * j + 1) * nearKerSum |r| k u) := by
  set A := 13 * minLeg u k ^ 2 * absk k ^ (2 * j + 1) * nearKerSum |r| k u with hA
  have hA0 : 0 ≤ A := by
    have := absk_nonneg k
    have := nearKerSum_nonneg |r| k u
    positivity
  have hterm : ∀ a b c, (if NearT a b c p q then kerB j (r * Phi a b c p q) (minLeg u k) (absk k)
      else 0) ≤ A := by
    intro a b c
    split_ifs with hN
    · obtain ⟨s₁, s₂, hs⟩ := hpat a b c
      exact kerB_le_nearKerSum j r _ hu hs hN.2.1 hN.2.2
    · exact hA0
  calc _ ≤ ∑ _a : Sgn, ∑ _b : Sgn, ∑ _c : Sgn, A :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun c _ =>
          hterm a b c
    _ = 8 * A := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
        push_cast
        ring

/-- The helicity pattern of the near set: the phase of a triad with output `k`. -/
private lemma exists_pat (α β γ : Sgn) (u k : Mode) :
    ∃ s₁ s₂, |lam α u + lam β (k - u) + lam γ (-k)| = |nearPhi s₁ s₂ u k| := by
  cases γ
  · refine ⟨!α, !β, ?_⟩
    have e : lam false k = -lam true k := by simpa using lam_not true k
    simp only [nearPhi, lam_not, lam_neg, e]
    rw [← abs_neg]
    congr 1
    ring
  · refine ⟨α, β, ?_⟩
    simp only [nearPhi, lam_neg]
    congr 1

private lemma minLeg_cases (u k : Mode) :
    absk u ≤ minLeg u k ∨ absk (k - u) ≤ minLeg u k := by
  rcases min_choice (absk u) (absk (k - u)) with h | h
  · exact Or.inl (le_of_eq (by rw [minLeg, h]))
  · exact Or.inr (le_of_eq (by rw [minLeg, h]))

/-- The triad term against the kernel at the output `k`, for any placement of the output. -/
private lemma region_core {j : ℕ} (hj : j = 1 ∨ j = 2) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (r τ : ℝ)
    (F G : Field) {p q k u : Mode} (hu : u ∈ nearBox k)
    (hmn : absk p ≤ minLeg u k ∨ absk q ≤ minLeg u k ∨ absk (p + q) ≤ minLeg u k)
    (hmx : absk p ≤ absk k ∧ absk q ≤ absk k ∧ absk (p + q) ≤ absk k)
    (hpat : ∀ a b c, ∃ s₁ s₂, |Phi a b c p q| = |nearPhi s₁ s₂ u k|) :
    ‖nearTriadTerm j ε r τ F G (p, q)‖ ≤
      104 * (minLeg u k ^ 2 * absk k ^ (2 * j + 1)) *
        (nearKerSum |r| k u * (‖G p‖ * ‖F q‖ * ‖F (-(p + q))‖)) := by
  have hP : 0 ≤ ‖G p‖ * ‖F q‖ * ‖F (-(p + q))‖ := by positivity
  refine (abs_nearTriadTerm_le hj hε r τ F G p q hmn hmx).trans ?_
  refine (mul_le_mul_of_nonneg_right (sum_ker_le j r hu hpat) hP).trans (le_of_eq ?_)
  ring

/-! ### The three regions -/

private lemma leg_le_A (p q : Mode) : absk p ≤ absk q + absk (p + q) := by
  have h := absk_add_le (p + q) (-q)
  rw [show p + q + -q = p by abel, absk_neg] at h
  linarith

private lemma leg_le_B (p q : Mode) : absk q ≤ absk p + absk (p + q) := by
  have h := absk_add_le (p + q) (-p)
  rw [show p + q + -p = q by abel, absk_neg] at h
  linarith

private lemma sub_A (p q : Mode) : -p - q = -(p + q) := by abel

private lemma sub_B (p q : Mode) : -q - p = -(p + q) := by abel

private lemma regionA {j : ℕ} (hj : j = 1 ∨ j = 2) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (r τ : ℝ)
    (F G : Field) {p q : Mode} (hp3 : p 2 ≠ 0) (hq3 : q 2 ≠ 0) (hr3 : (-(p + q)) 2 ≠ 0)
    (h1 : absk q ≤ absk p) (h2 : absk (p + q) ≤ absk p) :
    q ∈ nearBox (-p) ∧ ‖nearTriadTerm j ε r τ F G (p, q)‖ ≤
      104 * (min (absk q) (absk (p + q)) ^ 2 * absk p ^ (2 * j + 1)) *
        (nearKerSum |r| (-p) q * (‖G p‖ * ‖F q‖ * ‖F (-(p + q))‖)) := by
  have hu : q ∈ nearBox (-p) := mem_nearBox.2 ⟨by simpa using hp3, hq3,
    by rw [sub_A]; exact hr3, by rwa [absk_neg], by rw [sub_A, absk_neg, absk_neg]; exact h2⟩
  refine ⟨hu, ?_⟩
  have hmin : minLeg q (-p) = min (absk q) (absk (p + q)) := by
    rw [minLeg, sub_A, absk_neg]
  have h := region_core hj hε r τ F G (p := p) (q := q) hu ?_ ?_ ?_
  · rwa [hmin, absk_neg] at h
  · rcases minLeg_cases q (-p) with h | h
    · exact Or.inr (Or.inl h)
    · rw [sub_A, absk_neg] at h
      exact Or.inr (Or.inr h)
  · rw [absk_neg]
    exact ⟨le_rfl, h1, h2⟩
  · intro a b c
    obtain ⟨s₁, s₂, h⟩ := exists_pat b c a q (-p)
    refine ⟨s₁, s₂, ?_⟩
    rw [← h, sub_A, neg_neg, lam_neg, Phi]
    congr 1
    ring

private lemma regionB {j : ℕ} (hj : j = 1 ∨ j = 2) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (r τ : ℝ)
    (F G : Field) {p q : Mode} (hp3 : p 2 ≠ 0) (hq3 : q 2 ≠ 0) (hr3 : (-(p + q)) 2 ≠ 0)
    (h1 : absk p ≤ absk q) (h2 : absk (p + q) ≤ absk q) :
    p ∈ nearBox (-q) ∧ ‖nearTriadTerm j ε r τ F G (p, q)‖ ≤
      104 * (min (absk p) (absk (p + q)) ^ 2 * absk q ^ (2 * j + 1)) *
        (nearKerSum |r| (-q) p * (‖G p‖ * ‖F q‖ * ‖F (-(p + q))‖)) := by
  have hu : p ∈ nearBox (-q) := mem_nearBox.2 ⟨by simpa using hq3, hp3,
    by rw [sub_B]; exact hr3, by rwa [absk_neg], by rw [sub_B, absk_neg, absk_neg]; exact h2⟩
  refine ⟨hu, ?_⟩
  have hmin : minLeg p (-q) = min (absk p) (absk (p + q)) := by
    rw [minLeg, sub_B, absk_neg]
  have h := region_core hj hε r τ F G (p := p) (q := q) hu ?_ ?_ ?_
  · rwa [hmin, absk_neg] at h
  · rcases minLeg_cases p (-q) with h | h
    · exact Or.inl h
    · rw [sub_B, absk_neg] at h
      exact Or.inr (Or.inr h)
  · rw [absk_neg]
    exact ⟨h1, le_rfl, h2⟩
  · intro a b c
    obtain ⟨s₁, s₂, h⟩ := exists_pat a c b p (-q)
    refine ⟨s₁, s₂, ?_⟩
    rw [← h, sub_B, neg_neg, lam_neg, Phi]
    congr 1
    ring

private lemma regionC {j : ℕ} (hj : j = 1 ∨ j = 2) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (r τ : ℝ)
    (F G : Field) {p q : Mode} (hp3 : p 2 ≠ 0) (hq3 : q 2 ≠ 0) (hr3 : (-(p + q)) 2 ≠ 0)
    (h1 : absk p ≤ absk (p + q)) (h2 : absk q ≤ absk (p + q)) :
    p ∈ nearBox (p + q) ∧ ‖nearTriadTerm j ε r τ F G (p, q)‖ ≤
      104 * (min (absk p) (absk q) ^ 2 * absk (p + q) ^ (2 * j + 1)) *
        (nearKerSum |r| (p + q) p * (‖G p‖ * ‖F q‖ * ‖F (-(p + q))‖)) := by
  have e : p + q - p = q := by abel
  have hk3 : (p + q) 2 ≠ 0 := fun h => hr3 (by simp only [Pi.neg_apply, h, neg_zero])
  have hu : p ∈ nearBox (p + q) := mem_nearBox.2 ⟨hk3, hp3, by rw [e]; exact hq3, h1,
    by rw [e]; exact h2⟩
  refine ⟨hu, ?_⟩
  have hmin : minLeg p (p + q) = min (absk p) (absk q) := by
    rw [minLeg, e]
  have h := region_core hj hε r τ F G (p := p) (q := q) hu ?_ ?_ ?_
  · rwa [hmin] at h
  · rcases minLeg_cases p (p + q) with h | h
    · exact Or.inl h
    · rw [e] at h
      exact Or.inr (Or.inl h)
  · exact ⟨h1, h2, le_rfl⟩
  · intro a b c
    obtain ⟨s₁, s₂, h⟩ := exists_pat a b c p (p + q)
    refine ⟨s₁, s₂, ?_⟩
    rw [← h, e, lam_neg, Phi]
    congr 1

/-! ### The native weights -/

private lemma wtA_one {K x y : ℝ} (hK : 0 ≤ K) (h : K ≤ x + y) :
    min x y ^ 2 * K ^ 3 ≤ 4 * (K * (x ^ 2 * y ^ 2)) := by
  rcases le_total x y with hxy | hxy
  · rw [min_eq_left hxy]
    have h1 : K ≤ 2 * y := by linarith
    have h2 : K ^ 2 ≤ (2 * y) ^ 2 := pow_le_pow_left₀ hK h1 2
    have h3 : 0 ≤ K * x ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 h3]
  · rw [min_eq_right hxy]
    have h1 : K ≤ 2 * x := by linarith
    have h2 : K ^ 2 ≤ (2 * x) ^ 2 := pow_le_pow_left₀ hK h1 2
    have h3 : 0 ≤ K * y ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 h3]

private lemma wtB_one {K g f : ℝ} (hK : 0 ≤ K) (hg : 0 ≤ g) (hf : 0 ≤ f) (h : K ≤ g + f) :
    min g f ^ 2 * K ^ 3 ≤ 4 * (K ^ 2 * (g * f ^ 2)) := by
  rcases le_total g f with hgf | hgf
  · rw [min_eq_left hgf]
    have h1 : g * K ≤ 2 * f ^ 2 := by nlinarith
    have h3 : 0 ≤ K ^ 2 * g := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 h3]
  · rw [min_eq_right hgf]
    have h1 : K ≤ 2 * g := by linarith
    have h3 : 0 ≤ K ^ 2 * f ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 h3]

private lemma wtA_two {K x y : ℝ} (hK : 0 ≤ K) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : K ≤ x + y) :
    min x y ^ 2 * K ^ 5 ≤ 4 * (K ^ 2 * (x ^ 2 * y ^ 3 + x ^ 3 * y ^ 2)) := by
  have key : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → a ≤ b → K ≤ a + b →
      a ^ 2 * K ^ 5 ≤ 4 * (K ^ 2 * (a ^ 2 * b ^ 3 + a ^ 3 * b ^ 2)) := by
    intro a b ha hb hab hK'
    have h1 : K ^ 3 ≤ (a + b) ^ 3 := pow_le_pow_left₀ hK hK' 3
    have h2 : (a + b) ^ 3 ≤ 4 * (b ^ 3 + a * b ^ 2) := by
      nlinarith [mul_nonneg ha hb, mul_nonneg (mul_nonneg ha hb) hb, mul_nonneg ha ha,
        mul_nonneg (mul_nonneg ha ha) (sub_nonneg.2 hab), mul_nonneg (mul_nonneg ha hb)
        (sub_nonneg.2 hab), mul_nonneg (mul_nonneg hb hb) (sub_nonneg.2 hab)]
    have h3 : 0 ≤ K ^ 2 * a ^ 2 := by positivity
    have h4 := mul_le_mul_of_nonneg_left (h1.trans h2) h3
    nlinarith [h4]
  rcases le_total x y with hxy | hxy
  · rw [min_eq_left hxy]
    exact key hx hy hxy h
  · rw [min_eq_right hxy]
    have := key hy hx hxy (by linarith)
    nlinarith [this]

private lemma wtB_two {K g f : ℝ} (hK : 0 ≤ K) (hf : 0 ≤ f) (h : K ≤ g + f) :
    min g f ^ 2 * K ^ 5 ≤ 4 * (K ^ 3 * (g ^ 2 * f ^ 2) + K ^ 2 * (g ^ 2 * f ^ 3)) := by
  have hp1 : 0 ≤ K ^ 2 * (g ^ 2 * f ^ 3) := by positivity
  have hp2 : 0 ≤ K ^ 3 * (g ^ 2 * f ^ 2) := by positivity
  rcases le_total g f with hgf | hgf
  · rw [min_eq_left hgf]
    have h1 : K ≤ 2 * f := by linarith
    have h2 : K ^ 2 ≤ (2 * f) ^ 2 := pow_le_pow_left₀ hK h1 2
    have h3 : 0 ≤ K ^ 3 * g ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 h3]
  · rw [min_eq_right hgf]
    have h1 : K ≤ 2 * g := by linarith
    have h2 : K ^ 2 ≤ (2 * g) ^ 2 := pow_le_pow_left₀ hK h1 2
    have h3 : 0 ≤ K ^ 3 * f ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 h3]

/-! ### The weighted sequences -/

/-- The weighted amplitude `|k|ⁿ ‖X_k‖`. -/
def wt (n : ℕ) (X : Field) (k : Mode) : ℝ := absk k ^ n * ‖X k‖

/-- The reflected weighted amplitude `|k|ⁿ ‖X_{−k}‖`. -/
def wtN (n : ℕ) (X : Field) (k : Mode) : ℝ := absk k ^ n * ‖X (-k)‖

private lemma wt_nonneg (n : ℕ) (X : Field) (k : Mode) : 0 ≤ wt n X k :=
  mul_nonneg (pow_nonneg (absk_nonneg k) n) (norm_nonneg _)

private lemma wtN_nonneg (n : ℕ) (X : Field) (k : Mode) : 0 ≤ wtN n X k :=
  mul_nonneg (pow_nonneg (absk_nonneg k) n) (norm_nonneg _)

private lemma wt_sq (n : ℕ) {X : Field} (hX : X 0 = 0) (k : Mode) :
    wt n X k ^ 2 = sobWeight n k * ‖X k‖ ^ 2 := by
  by_cases hk : k = 0
  · subst hk
    simp [wt, hX]
  · have e : (2 * (n : ℝ)) = ((2 * n : ℕ) : ℝ) := by push_cast; ring
    have hw : sobWeight n k = absk k ^ (2 * (n : ℝ)) := by simp [sobWeight, hk]
    rw [hw, e, Real.rpow_natCast, wt, mul_pow, ← pow_mul, mul_comm n 2]

private lemma wt_facts {n : ℕ} {s : ℝ} (hs : s = n) {X : Field} (hX : MZ s X) :
    (Summable fun k => wt n X k ^ 2) ∧ Real.sqrt (∑' k, wt n X k ^ 2) = hnorm s X := by
  subst hs
  have e : (fun k => wt n X k ^ 2) = fun k => sobWeight n k * ‖X k‖ ^ 2 :=
    funext (wt_sq n hX.mean)
  rw [e]
  exact ⟨hX.inH, rfl⟩

private lemma wtN_facts {n : ℕ} {s : ℝ} (hs : s = n) {X : Field} (hX : MZ s X) :
    (Summable fun k => wtN n X k ^ 2) ∧ Real.sqrt (∑' k, wtN n X k ^ 2) = hnorm s X := by
  obtain ⟨h1, h2⟩ := wt_facts hs hX
  have e : ∀ k, wtN n X k ^ 2 = wt n X (-k) ^ 2 := fun k => by simp only [wtN, wt, absk_neg]
  simp only [e]
  refine ⟨(Equiv.neg Mode).summable_iff.mpr h1, ?_⟩
  rw [← h2, ← (Equiv.neg Mode).tsum_eq fun k => wt n X k ^ 2]
  rfl

/-! ### Summing the regions -/

/-- A pointwise domination by box terms along permutations bounds the triad series. -/
private lemma tsum_regions {ι : Type*} [Fintype ι] {W : Mode × Mode → ℂ} {C B : ℝ} (hC : 0 ≤ C)
    (b : ι → Mode × Mode → ℝ) (e : ι → Equiv.Perm (Mode × Mode))
    (hb : ∀ i, Summable (b i)) (hB : ∀ i, ∑' x, b i x ≤ B)
    (hpt : ∀ x, ‖W x‖ ≤ C * ∑ i, b i (e i x)) :
    ‖∑' x, W x‖ ≤ C * (Fintype.card ι * B) := by
  have hs : ∀ i, Summable fun x => b i (e i x) := fun i => (e i).summable_iff.mpr (hb i)
  have hS : Summable fun x => C * ∑ i, b i (e i x) := (summable_sum fun i _ => hs i).mul_left C
  have hN : Summable fun x => ‖W x‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hS
  calc ‖∑' x, W x‖ ≤ ∑' x, ‖W x‖ := norm_tsum_le_tsum_norm hN
    _ ≤ ∑' x, C * ∑ i, b i (e i x) := hN.tsum_le_tsum hpt hS
    _ = C * ∑ i, ∑' x, b i (e i x) := by
        rw [tsum_mul_left, Summable.tsum_finsetSum fun i _ => hs i]
    _ ≤ C * ∑ _i : ι, B := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) hC
        rw [(e i).tsum_eq (b i)]
        exact hB i
    _ = C * (Fintype.card ι * B) := by simp [Finset.card_univ]

/-- `(p, q) ↦ (−p, q)`: the output of region `A`. -/
private def eA : Equiv.Perm (Mode × Mode) :=
  Function.Involutive.toPerm (fun x => (-x.1, x.2)) fun x => Prod.ext (by simp) rfl

/-- `(p, q) ↦ (−q, p)`: the output of region `B`. -/
private def eB : Equiv.Perm (Mode × Mode) where
  toFun x := (-x.2, x.1)
  invFun x := (x.2, -x.1)
  left_inv x := Prod.ext rfl (by simp)
  right_inv x := Prod.ext (by simp) rfl

/-- `(p, q) ↦ (p + q, p)`: the output of region `C`. -/
private def eC : Equiv.Perm (Mode × Mode) where
  toFun x := (x.1 + x.2, x.1)
  invFun x := (x.2, x.1 - x.2)
  left_inv x := Prod.ext rfl (by simp)
  right_inv x := Prod.ext (by simp) rfl

/-- At least one leg of a triad is the longest. -/
private lemma regions (p q : Mode) :
    (absk q ≤ absk p ∧ absk (p + q) ≤ absk p) ∨ (absk p ≤ absk q ∧ absk (p + q) ≤ absk q) ∨
      (absk p ≤ absk (p + q) ∧ absk q ≤ absk (p + q)) := by
  rcases le_total (absk p) (absk q) with h1 | h1 <;>
    rcases le_total (absk q) (absk (p + q)) with h2 | h2 <;>
    rcases le_total (absk p) (absk (p + q)) with h3 | h3
  · exact Or.inr (Or.inr ⟨h3, h2⟩)
  · exact Or.inr (Or.inr ⟨h1.trans h2, h2⟩)
  · exact Or.inr (Or.inl ⟨h1, h2⟩)
  · exact Or.inr (Or.inl ⟨h1, h2⟩)
  · exact Or.inr (Or.inr ⟨h3, h2⟩)
  · exact Or.inl ⟨h1, h3⟩
  · exact Or.inl ⟨h1, h2.trans h1⟩
  · exact Or.inl ⟨h1, h3⟩

/-- The fast legs of a triad with nonvanishing amplitudes, or the triad term vanishes. -/
private lemma triad_zero_or_fast {j : ℕ} (hj : j = 1 ∨ j = 2) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (r τ : ℝ) {F G : Field} (hF : PiF F = F) (hG : PiF G = G) (p q : Mode) :
    nearTriadTerm j ε r τ F G (p, q) = 0 ∨ (p 2 ≠ 0 ∧ q 2 ≠ 0 ∧ (-(p + q)) 2 ≠ 0) := by
  by_cases h : p 2 ≠ 0 ∧ q 2 ≠ 0 ∧ (-(p + q)) 2 ≠ 0
  · exact Or.inr h
  left
  have hP : ‖G p‖ * ‖F q‖ * ‖F (-(p + q))‖ = 0 := by
    by_cases h1 : p 2 = 0
    · rw [fast_zero hG h1]
      simp
    by_cases h2 : q 2 = 0
    · rw [fast_zero hF h2]
      simp
    have h3 : (-(p + q)) 2 = 0 := by
      by_contra h3
      exact h ⟨h1, h2, h3⟩
    rw [fast_zero hF h3]
    simp
  have hk := abs_nearTriadTerm_le hj hε r τ F G p q (mn := absk p)
    (mx := absk p + absk q + absk (p + q)) (Or.inl le_rfl)
    ⟨by linarith [absk_nonneg q, absk_nonneg (p + q)],
      by linarith [absk_nonneg p, absk_nonneg (p + q)],
      by linarith [absk_nonneg p, absk_nonneg q]⟩
  rw [hP, mul_zero] at hk
  exact norm_le_zero_iff.mp hk

private lemma finish {N A B P : ℝ} (h : N ≤ 104 * A * P) (hw : A ≤ 4 * B) (hP : 0 ≤ P) :
    N ≤ 416 * (B * P) := by
  nlinarith [mul_le_mul_of_nonneg_right hw hP]

/-! ### The pointwise domination -/

private lemma point_one {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (r τ : ℝ) {F G : Field}
    (hF : PiF F = F) (hG : PiF G = G) (p q : Mode) :
    ‖nearTriadTerm 1 ε r τ F G (p, q)‖ ≤ 416 *
      (boxTerm |r| (wtN 1 G) (wt 2 F) (wt 2 F) (-p, q) +
        boxTerm |r| (wtN 2 F) (wt 1 G) (wt 2 F) (-q, p) +
        boxTerm |r| (wtN 2 F) (wt 1 G) (wt 2 F) (p + q, p)) := by
  have b1 := boxTerm_nonneg |r| (wtN_nonneg 1 G) (wt_nonneg 2 F) (wt_nonneg 2 F) (-p, q)
  have b2 := boxTerm_nonneg |r| (wtN_nonneg 2 F) (wt_nonneg 1 G) (wt_nonneg 2 F) (-q, p)
  have b3 := boxTerm_nonneg |r| (wtN_nonneg 2 F) (wt_nonneg 1 G) (wt_nonneg 2 F) (p + q, p)
  rcases triad_zero_or_fast (Or.inl rfl) hε r τ hF hG p q with h0 | ⟨hp3, hq3, hr3⟩
  · rw [h0, norm_zero]
    positivity
  have hP : 0 ≤ ‖G p‖ * ‖F q‖ * ‖F (-(p + q))‖ := by positivity
  rcases regions p q with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨hu, hb⟩ := regionA (Or.inl rfl) hε r τ F G hp3 hq3 hr3 h1 h2
    have hw := wtA_one (absk_nonneg p) (leg_le_A p q)
    have := finish hb hw (mul_nonneg (nearKerSum_nonneg _ _ _) hP)
    have e : boxTerm |r| (wtN 1 G) (wt 2 F) (wt 2 F) (-p, q) =
        absk p * (absk q ^ 2 * absk (p + q) ^ 2) *
          (nearKerSum |r| (-p) q * (‖G p‖ * ‖F q‖ * ‖F (-(p + q))‖)) := by
      rw [boxTerm_of_mem hu]
      simp only [wtN, wt, neg_neg, absk_neg, sub_A]
      ring
    rw [← e] at this
    linarith
  · obtain ⟨hu, hb⟩ := regionB (Or.inl rfl) hε r τ F G hp3 hq3 hr3 h1 h2
    have hw := wtB_one (absk_nonneg q) (absk_nonneg p) (absk_nonneg (p + q)) (leg_le_B p q)
    have := finish hb hw (mul_nonneg (nearKerSum_nonneg _ _ _) hP)
    have e : boxTerm |r| (wtN 2 F) (wt 1 G) (wt 2 F) (-q, p) =
        absk q ^ 2 * (absk p * absk (p + q) ^ 2) *
          (nearKerSum |r| (-q) p * (‖G p‖ * ‖F q‖ * ‖F (-(p + q))‖)) := by
      rw [boxTerm_of_mem hu]
      simp only [wtN, wt, neg_neg, absk_neg, sub_B]
      ring
    rw [← e] at this
    linarith
  · obtain ⟨hu, hb⟩ := regionC (Or.inl rfl) hε r τ F G hp3 hq3 hr3 h1 h2
    have hw := wtB_one (absk_nonneg (p + q)) (absk_nonneg p) (absk_nonneg q) (absk_add_le p q)
    have := finish hb hw (mul_nonneg (nearKerSum_nonneg _ _ _) hP)
    have e : boxTerm |r| (wtN 2 F) (wt 1 G) (wt 2 F) (p + q, p) =
        absk (p + q) ^ 2 * (absk p * absk q ^ 2) *
          (nearKerSum |r| (p + q) p * (‖G p‖ * ‖F q‖ * ‖F (-(p + q))‖)) := by
      rw [boxTerm_of_mem hu]
      simp only [wtN, wt, add_sub_cancel_left]
      ring
    rw [← e] at this
    linarith

private lemma point_two {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (r τ : ℝ) {F G : Field}
    (hF : PiF F = F) (hG : PiF G = G) (p q : Mode) :
    ‖nearTriadTerm 2 ε r τ F G (p, q)‖ ≤ 416 *
      ((boxTerm |r| (wtN 2 G) (wt 2 F) (wt 3 F) (-p, q) +
          boxTerm |r| (wtN 2 G) (wt 3 F) (wt 2 F) (-p, q)) +
        (boxTerm |r| (wtN 3 F) (wt 2 G) (wt 2 F) (-q, p) +
          boxTerm |r| (wtN 2 F) (wt 2 G) (wt 3 F) (-q, p)) +
        (boxTerm |r| (wtN 3 F) (wt 2 G) (wt 2 F) (p + q, p) +
          boxTerm |r| (wtN 2 F) (wt 2 G) (wt 3 F) (p + q, p))) := by
  have b1 := boxTerm_nonneg |r| (wtN_nonneg 2 G) (wt_nonneg 2 F) (wt_nonneg 3 F) (-p, q)
  have b2 := boxTerm_nonneg |r| (wtN_nonneg 2 G) (wt_nonneg 3 F) (wt_nonneg 2 F) (-p, q)
  have b3 := boxTerm_nonneg |r| (wtN_nonneg 3 F) (wt_nonneg 2 G) (wt_nonneg 2 F) (-q, p)
  have b4 := boxTerm_nonneg |r| (wtN_nonneg 2 F) (wt_nonneg 2 G) (wt_nonneg 3 F) (-q, p)
  have b5 := boxTerm_nonneg |r| (wtN_nonneg 3 F) (wt_nonneg 2 G) (wt_nonneg 2 F) (p + q, p)
  have b6 := boxTerm_nonneg |r| (wtN_nonneg 2 F) (wt_nonneg 2 G) (wt_nonneg 3 F) (p + q, p)
  rcases triad_zero_or_fast (Or.inr rfl) hε r τ hF hG p q with h0 | ⟨hp3, hq3, hr3⟩
  · rw [h0, norm_zero]
    positivity
  have hP : 0 ≤ ‖G p‖ * ‖F q‖ * ‖F (-(p + q))‖ := by positivity
  rcases regions p q with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨hu, hb⟩ := regionA (Or.inr rfl) hε r τ F G hp3 hq3 hr3 h1 h2
    have hw := wtA_two (absk_nonneg p) (absk_nonneg q) (absk_nonneg (p + q)) (leg_le_A p q)
    have := finish hb hw (mul_nonneg (nearKerSum_nonneg _ _ _) hP)
    have e : boxTerm |r| (wtN 2 G) (wt 2 F) (wt 3 F) (-p, q) +
        boxTerm |r| (wtN 2 G) (wt 3 F) (wt 2 F) (-p, q) =
        absk p ^ 2 * (absk q ^ 2 * absk (p + q) ^ 3 + absk q ^ 3 * absk (p + q) ^ 2) *
          (nearKerSum |r| (-p) q * (‖G p‖ * ‖F q‖ * ‖F (-(p + q))‖)) := by
      rw [boxTerm_of_mem hu, boxTerm_of_mem hu]
      simp only [wtN, wt, neg_neg, absk_neg, sub_A]
      ring
    rw [← e] at this
    linarith
  · obtain ⟨hu, hb⟩ := regionB (Or.inr rfl) hε r τ F G hp3 hq3 hr3 h1 h2
    have hw := wtB_two (absk_nonneg q) (absk_nonneg (p + q)) (leg_le_B p q)
    have := finish hb hw (mul_nonneg (nearKerSum_nonneg _ _ _) hP)
    have e : boxTerm |r| (wtN 3 F) (wt 2 G) (wt 2 F) (-q, p) +
        boxTerm |r| (wtN 2 F) (wt 2 G) (wt 3 F) (-q, p) =
        (absk q ^ 3 * (absk p ^ 2 * absk (p + q) ^ 2) +
          absk q ^ 2 * (absk p ^ 2 * absk (p + q) ^ 3)) *
          (nearKerSum |r| (-q) p * (‖G p‖ * ‖F q‖ * ‖F (-(p + q))‖)) := by
      rw [boxTerm_of_mem hu, boxTerm_of_mem hu]
      simp only [wtN, wt, neg_neg, absk_neg, sub_B]
      ring
    rw [← e] at this
    linarith
  · obtain ⟨hu, hb⟩ := regionC (Or.inr rfl) hε r τ F G hp3 hq3 hr3 h1 h2
    have hw := wtB_two (absk_nonneg (p + q)) (absk_nonneg q) (absk_add_le p q)
    have := finish hb hw (mul_nonneg (nearKerSum_nonneg _ _ _) hP)
    have e : boxTerm |r| (wtN 3 F) (wt 2 G) (wt 2 F) (p + q, p) +
        boxTerm |r| (wtN 2 F) (wt 2 G) (wt 3 F) (p + q, p) =
        (absk (p + q) ^ 3 * (absk p ^ 2 * absk q ^ 2) +
          absk (p + q) ^ 2 * (absk p ^ 2 * absk q ^ 3)) *
          (nearKerSum |r| (p + q) p * (‖G p‖ * ‖F q‖ * ‖F (-(p + q))‖)) := by
      rw [boxTerm_of_mem hu, boxTerm_of_mem hu]
      simp only [wtN, wt, add_sub_cancel_left]
      ring
    rw [← e] at this
    linarith

/-! ### C. The native near bounds -/

/-- **E5, role 15 — the native `H¹` near differential** (LOCAL210 (6.1); report §1; Body 18 §2):
for real fast `F ∈ H²` and real `h ∈ H¹`, `|D_1^N(F; h)| ≤ C₀ N(q) ‖h‖₁ ‖F‖₂²` with
`N = nearN = 96 √𝔐_N`, `q = |r|`, `C₀ = nearC₀`.  The proof gives `1248 √𝔐_N`, i.e. `13 N`:
`416 = 8 · 13 · 4` per region, three regions. -/
theorem nearD1_le {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (r τ : ℝ) {F h : Field} (hF : MZ 2 F)
    (hFr : IsReal F) (hF' : PiF F = F) (hh : MZ 1 h) (hhr : IsReal h) :
    |nearD 1 ε r τ F h| ≤ nearC₀ * nearN |r| * hnorm 1 h * (hnorm 2 F * hnorm 2 F) := by
  have hG : MZ 1 (PiF h) := hh.PiF'
  have hGf : PiF (PiF h) = PiF h := by
    funext k
    by_cases hk : k 2 = 0 <;> simp [PiF, hk]
  obtain ⟨-, he⟩ := nearD_eq_tsum_triad (j := 1) (Or.inl rfl) hε r τ
    (by convert hF using 2; norm_num) hFr (by simpa using hh) hhr
  obtain ⟨u1, u1n⟩ := wtN_facts (n := 1) (s := 1) (by norm_num) hG
  obtain ⟨v1, v1n⟩ := wt_facts (n := 1) (s := 1) (by norm_num) hG
  obtain ⟨w2, w2n⟩ := wt_facts (n := 2) (s := 2) (by norm_num) hF
  obtain ⟨u2, u2n⟩ := wtN_facts (n := 2) (s := 2) (by norm_num) hF
  obtain ⟨sA, bA⟩ := boxTerm_tsum_le |r| (wtN_nonneg 1 (PiF h)) (wt_nonneg 2 F) (wt_nonneg 2 F)
    u1 w2 w2
  obtain ⟨sB, bB⟩ := boxTerm_tsum_le |r| (wtN_nonneg 2 F) (wt_nonneg 1 (PiF h)) (wt_nonneg 2 F)
    u2 v1 w2
  rw [u1n, w2n] at bA
  rw [u2n, v1n, w2n] at bB
  set M := Real.sqrt (MomN |r|)
  set g := hnorm 1 (PiF h)
  set b := hnorm 2 F
  have key := tsum_regions (ι := Fin 3) (C := 416) (B := M * (g * b * b)) (by norm_num)
    (W := nearTriadTerm 1 ε r τ F (PiF h))
    ![boxTerm |r| (wtN 1 (PiF h)) (wt 2 F) (wt 2 F),
      boxTerm |r| (wtN 2 F) (wt 1 (PiF h)) (wt 2 F),
      boxTerm |r| (wtN 2 F) (wt 1 (PiF h)) (wt 2 F)] ![eA, eB, eC]
    (fun i => by fin_cases i; exacts [sA, sB, sB])
    (fun i => by
      fin_cases i
      · exact bA
      · exact bB.trans_eq (by ring)
      · exact bB.trans_eq (by ring))
    (fun x => by
      rw [Fin.sum_univ_three]
      exact point_one hε r τ hF' hGf x.1 x.2)
  rw [he]
  refine (Complex.abs_re_le_norm _).trans (key.trans ?_)
  have hM : 0 ≤ M := Real.sqrt_nonneg _
  have hb : 0 ≤ b := hnorm_nonneg _ _
  have hg : g ≤ hnorm 1 h := hnorm_PiF_le hh.inH
  have h0 := hnorm_nonneg 1 h
  have hT : 0 ≤ M * (b * b) := by positivity
  simp only [Fintype.card_fin, nearC₀, nearN]
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hg hT, mul_nonneg hT h0]

/-- **E8, role 31 — the native `H²` near differential** (LOCAL210 (6.1); report §1): for real
fast `F ∈ H³` and real `h ∈ H²`, `|D_2^N(F; h)| ≤ C₀ N(q) ‖h‖₂ ‖F‖₂ ‖F‖₃`, slots
`(H²(h), H²(F), H³(F))`; both placements of `H³` on the `F` legs are used in each of the three
regions: `2496 √𝔐_N = 26 N`. -/
theorem nearD2_le {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (r τ : ℝ) {F h : Field} (hF : MZ 3 F)
    (hFr : IsReal F) (hF' : PiF F = F) (hh : MZ 2 h) (hhr : IsReal h) :
    |nearD 2 ε r τ F h| ≤ nearC₀ * nearN |r| * hnorm 2 h * (hnorm 2 F * hnorm 3 F) := by
  have hG : MZ 2 (PiF h) := hh.PiF'
  have hF2 : MZ 2 F := hF.mono' (by norm_num)
  have hGf : PiF (PiF h) = PiF h := by
    funext k
    by_cases hk : k 2 = 0 <;> simp [PiF, hk]
  obtain ⟨-, he⟩ := nearD_eq_tsum_triad (j := 2) (Or.inr rfl) hε r τ
    (by convert hF using 2; norm_num) hFr (by simpa using hh) hhr
  obtain ⟨uG, uGn⟩ := wtN_facts (n := 2) (s := 2) (by norm_num) hG
  obtain ⟨vG, vGn⟩ := wt_facts (n := 2) (s := 2) (by norm_num) hG
  obtain ⟨w2, w2n⟩ := wt_facts (n := 2) (s := 2) (by norm_num) hF2
  obtain ⟨w3, w3n⟩ := wt_facts (n := 3) (s := 3) (by norm_num) hF
  obtain ⟨u2, u2n⟩ := wtN_facts (n := 2) (s := 2) (by norm_num) hF2
  obtain ⟨u3, u3n⟩ := wtN_facts (n := 3) (s := 3) (by norm_num) hF
  obtain ⟨sA1, bA1⟩ := boxTerm_tsum_le |r| (wtN_nonneg 2 (PiF h)) (wt_nonneg 2 F) (wt_nonneg 3 F)
    uG w2 w3
  obtain ⟨sA2, bA2⟩ := boxTerm_tsum_le |r| (wtN_nonneg 2 (PiF h)) (wt_nonneg 3 F) (wt_nonneg 2 F)
    uG w3 w2
  obtain ⟨sB1, bB1⟩ := boxTerm_tsum_le |r| (wtN_nonneg 3 F) (wt_nonneg 2 (PiF h)) (wt_nonneg 2 F)
    u3 vG w2
  obtain ⟨sB2, bB2⟩ := boxTerm_tsum_le |r| (wtN_nonneg 2 F) (wt_nonneg 2 (PiF h)) (wt_nonneg 3 F)
    u2 vG w3
  rw [uGn, w2n, w3n] at bA1
  rw [uGn, w2n, w3n] at bA2
  rw [u3n, vGn, w2n] at bB1
  rw [u2n, vGn, w3n] at bB2
  set M := Real.sqrt (MomN |r|)
  set g := hnorm 2 (PiF h)
  set b := hnorm 2 F
  set c := hnorm 3 F
  have sA := sA1.add sA2
  have sB := sB1.add sB2
  have tA : ∑' x, (boxTerm |r| (wtN 2 (PiF h)) (wt 2 F) (wt 3 F) x +
      boxTerm |r| (wtN 2 (PiF h)) (wt 3 F) (wt 2 F) x) ≤ 2 * (M * (g * b * c)) := by
    rw [sA1.tsum_add sA2]
    linarith [bA1, bA2.trans_eq (by ring : M * (g * c * b) = M * (g * b * c))]
  have tB : ∑' x, (boxTerm |r| (wtN 3 F) (wt 2 (PiF h)) (wt 2 F) x +
      boxTerm |r| (wtN 2 F) (wt 2 (PiF h)) (wt 3 F) x) ≤ 2 * (M * (g * b * c)) := by
    rw [sB1.tsum_add sB2]
    linarith [bB1.trans_eq (by ring : M * (c * g * b) = M * (g * b * c)),
      bB2.trans_eq (by ring : M * (b * g * c) = M * (g * b * c))]
  have key := tsum_regions (ι := Fin 3) (C := 416) (B := 2 * (M * (g * b * c))) (by norm_num)
    (W := nearTriadTerm 2 ε r τ F (PiF h))
    ![fun x => boxTerm |r| (wtN 2 (PiF h)) (wt 2 F) (wt 3 F) x +
        boxTerm |r| (wtN 2 (PiF h)) (wt 3 F) (wt 2 F) x,
      fun x => boxTerm |r| (wtN 3 F) (wt 2 (PiF h)) (wt 2 F) x +
        boxTerm |r| (wtN 2 F) (wt 2 (PiF h)) (wt 3 F) x,
      fun x => boxTerm |r| (wtN 3 F) (wt 2 (PiF h)) (wt 2 F) x +
        boxTerm |r| (wtN 2 F) (wt 2 (PiF h)) (wt 3 F) x] ![eA, eB, eC]
    (fun i => by fin_cases i; exacts [sA, sB, sB])
    (fun i => by fin_cases i; exacts [tA, tB, tB])
    (fun x => by
      rw [Fin.sum_univ_three]
      exact point_two hε r τ hF' hGf x.1 x.2)
  rw [he]
  refine (Complex.abs_re_le_norm _).trans (key.trans ?_)
  have hM : 0 ≤ M := Real.sqrt_nonneg _
  have hb : 0 ≤ b := hnorm_nonneg _ _
  have hc : 0 ≤ c := hnorm_nonneg _ _
  have hg : g ≤ hnorm 2 h := hnorm_PiF_le hh.inH
  have hT : 0 ≤ M * (b * c) := by positivity
  simp only [Fintype.card_fin, nearC₀, nearN]
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hg hT]

/-! ### E. The roles 15/31 coefficient `√P_F y^{3/2} N(q)` -/

/-- `√(ab) · b = √a · b^{3/2}`. -/
private lemma sqrt_mul_eq_rpow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) * b = Real.sqrt a * b ^ (3 / 2 : ℝ) := by
  rw [Real.sqrt_mul ha, mul_assoc]
  congr 1
  rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
    Real.rpow_add' hb (by norm_num), Real.rpow_one]

/-- The elementary glue of report Step 5: `N (C √(ab) c) (b c) ≤ C √P_F y^{3/2} N c²` under
`a ≤ P_F`, `b ≤ y`. -/
private lemma glue {N C a b c PF yF : ℝ} (hN : 0 ≤ N) (hC : 0 ≤ C) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : a ≤ PF) (hb : b ≤ yF) :
    N * (C * Real.sqrt (a * b) * c) * (b * c) ≤
      C * Real.sqrt PF * yF ^ (3 / 2 : ℝ) * N * c ^ 2 := by
  have h2 : Real.sqrt a ≤ Real.sqrt PF := Real.sqrt_le_sqrt ha
  have h3 : b ^ (3 / 2 : ℝ) ≤ yF ^ (3 / 2 : ℝ) := Real.rpow_le_rpow hb0 hb (by norm_num)
  have h4 : 0 ≤ b ^ (3 / 2 : ℝ) := Real.rpow_nonneg hb0 _
  have h5 : 0 ≤ Real.sqrt a := Real.sqrt_nonneg _
  calc N * (C * Real.sqrt (a * b) * c) * (b * c)
      = C * (Real.sqrt (a * b) * b) * N * c ^ 2 := by ring
    _ = C * (Real.sqrt a * b ^ (3 / 2 : ℝ)) * N * c ^ 2 := by rw [sqrt_mul_eq_rpow ha0 hb0]
    _ ≤ C * (Real.sqrt PF * yF ^ (3 / 2 : ℝ)) * N * c ^ 2 := by gcongr
    _ = _ := by ring

/-- The phased source of a real solenoidal field is real. -/
private lemma isReal_Qphase (τ : ℝ) {F : Field} (hF : Adm 2 F) : IsReal (Qphase τ F F) :=
  (majorized_Qm (fun _ => phaseM τ) (fun _ => phaseM_bdd τ) (fun _ => phaseM_real τ)
    fun _ _ _ _ _ => continuous_const).real 0 F F hF hF

/-- **Role 31** (report Step 5; LOCAL210 §7, `W = P^{1/2} Y^{3/2}`): for admissible fast
`F ∈ H³` with `a_F ≤ P_F`, `b_F ≤ y`, the native `H²` near differential in the source direction
`h_ff = Π_F Q_τ(F, F)` is at most `32√5488 √P_F y^{3/2} C₀ N(q) c_F²`. -/
theorem role31_bound {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (r τ τ' : ℝ) {F : Field} (hF : Adm 3 F)
    (hF' : PiF F = F) {PF yF : ℝ} (ha : hnorm 1 F ≤ PF) (hb : hnorm 2 F ≤ yF) :
    |nearD 2 ε r τ F (Qphase τ' F F)| ≤
      32 * Real.sqrt 5488 * Real.sqrt PF * yF ^ (3 / 2 : ℝ) * (nearC₀ * nearN |r|) *
        hnorm 3 F ^ 2 := by
  have hF3 : MZ 3 F := ⟨hF.inH, hF.mean⟩
  have hF2 : MZ 2 F := hF3.mono' (by norm_num)
  have hA2 : Adm 2 F := ⟨hF.inH.mono (by norm_num), hF.real, hF.sol, hF.mean⟩
  obtain ⟨hI, -⟩ := hnorm_Qm_le (phaseM_bdd τ') (σ := 3) (by norm_num) hF3 hF3 hF2 hF2
  have e : (3 : ℝ) - 1 = 2 := by norm_num
  rw [e] at hI
  have hh : MZ 2 (PiF (Qphase τ' F F)) := ⟨hI.PiF, by simp [PiF]⟩
  have h1 := nearD2_le hε r τ hF3 hF.real hF' hh (isReal_PiF (isReal_Qphase τ' hA2))
  have h2 := hnorm_two_Qphase_le τ' hF3
  rw [← nearD_PiF]
  have hN : 0 ≤ nearC₀ * nearN |r| := mul_nonneg nearC₀_pos.le (nearN_nonneg |r|)
  have hbc : 0 ≤ hnorm 2 F * hnorm 3 F := mul_nonneg (hnorm_nonneg _ _) (hnorm_nonneg _ _)
  calc |nearD 2 ε r τ F (PiF (Qphase τ' F F))|
      ≤ nearC₀ * nearN |r| * hnorm 2 (PiF (Qphase τ' F F)) * (hnorm 2 F * hnorm 3 F) := h1
    _ ≤ nearC₀ * nearN |r| * (32 * Real.sqrt 5488 * Real.sqrt (hnorm 1 F * hnorm 2 F) *
        hnorm 3 F) * (hnorm 2 F * hnorm 3 F) := by gcongr
    _ ≤ _ := glue hN (by positivity) (hnorm_nonneg _ _) (hnorm_nonneg _ _) ha hb

/-- **Role 15** (report Step 5): for admissible fast `F ∈ H²` with `a_F ≤ P_F`, `b_F ≤ y`, the
native `H¹` near differential in the source direction `Π_F Q_τ(F, F)` is at most
`16√5488 √P_F y^{3/2} C₀ N(q) b_F²`. -/
theorem role15_bound {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (r τ τ' : ℝ) {F : Field} (hF : Adm 2 F)
    (hF' : PiF F = F) {PF yF : ℝ} (ha : hnorm 1 F ≤ PF) (hb : hnorm 2 F ≤ yF) :
    |nearD 1 ε r τ F (Qphase τ' F F)| ≤
      16 * Real.sqrt 5488 * Real.sqrt PF * yF ^ (3 / 2 : ℝ) * (nearC₀ * nearN |r|) *
        hnorm 2 F ^ 2 := by
  have hF2 : MZ 2 F := ⟨hF.inH, hF.mean⟩
  obtain ⟨hI, -⟩ := hnorm_Qm_le (phaseM_bdd τ') (σ := 2) (by norm_num) hF2 hF2 hF2 hF2
  have e : (2 : ℝ) - 1 = 1 := by norm_num
  rw [e] at hI
  have hh : MZ 1 (PiF (Qphase τ' F F)) := ⟨hI.PiF, by simp [PiF]⟩
  have h1 := nearD1_le hε r τ hF2 hF.real hF' hh (isReal_PiF (isReal_Qphase τ' hF))
  have h2 := hnorm_one_Qphase_le τ' hF2
  rw [← nearD_PiF]
  have hN : 0 ≤ nearC₀ * nearN |r| := mul_nonneg nearC₀_pos.le (nearN_nonneg |r|)
  have hbb : 0 ≤ hnorm 2 F * hnorm 2 F := mul_nonneg (hnorm_nonneg _ _) (hnorm_nonneg _ _)
  calc |nearD 1 ε r τ F (PiF (Qphase τ' F F))|
      ≤ nearC₀ * nearN |r| * hnorm 1 (PiF (Qphase τ' F F)) * (hnorm 2 F * hnorm 2 F) := h1
    _ ≤ nearC₀ * nearN |r| * (16 * Real.sqrt 5488 * Real.sqrt (hnorm 1 F * hnorm 2 F) *
        hnorm 2 F) * (hnorm 2 F * hnorm 2 F) := by gcongr
    _ ≤ _ := glue hN (by positivity) (hnorm_nonneg _ _) (hnorm_nonneg _ _) ha hb

/-- **Role 31, paid** (the `H2EnergyInterface` hypothesis with `K₂ = 32√5488`,
`N = C₀ nearN`; report §5 "Interface fix"): if `K₂ √P_F y^{3/2} C₀ N(q) ≤ 1` then
`|D_2^N(F; Π_F Q_τ(F,F))| ≤ c_F²` — a fixed share of the `H³` dissipation. -/
theorem role31_paid {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (r τ τ' : ℝ) {F : Field} (hF : Adm 3 F)
    (hF' : PiF F = F) {PF yF : ℝ} (ha : hnorm 1 F ≤ PF) (hb : hnorm 2 F ≤ yF)
    (hpaid : 32 * Real.sqrt 5488 * Real.sqrt PF * yF ^ (3 / 2 : ℝ) * (nearC₀ * nearN |r|) ≤ 1) :
    |nearD 2 ε r τ F (Qphase τ' F F)| ≤ hnorm 3 F ^ 2 :=
  calc |nearD 2 ε r τ F (Qphase τ' F F)|
      ≤ 32 * Real.sqrt 5488 * Real.sqrt PF * yF ^ (3 / 2 : ℝ) * (nearC₀ * nearN |r|) *
        hnorm 3 F ^ 2 := role31_bound hε r τ τ' hF hF' ha hb
    _ ≤ 1 * hnorm 3 F ^ 2 := mul_le_mul_of_nonneg_right hpaid (sq_nonneg _)
    _ = hnorm 3 F ^ 2 := one_mul _

/-- **Role 15, paid** (the `H1EnergyInterface` hypothesis with `K₁ = 16√5488`,
`N = C₀ nearN`): if `K₁ √P_F y^{3/2} C₀ N(q) ≤ 1` then `|D_1^N(F; Π_F Q_τ(F,F))| ≤ b_F²`. -/
theorem role15_paid {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (r τ τ' : ℝ) {F : Field} (hF : Adm 2 F)
    (hF' : PiF F = F) {PF yF : ℝ} (ha : hnorm 1 F ≤ PF) (hb : hnorm 2 F ≤ yF)
    (hpaid : 16 * Real.sqrt 5488 * Real.sqrt PF * yF ^ (3 / 2 : ℝ) * (nearC₀ * nearN |r|) ≤ 1) :
    |nearD 1 ε r τ F (Qphase τ' F F)| ≤ hnorm 2 F ^ 2 :=
  calc |nearD 1 ε r τ F (Qphase τ' F F)|
      ≤ 16 * Real.sqrt 5488 * Real.sqrt PF * yF ^ (3 / 2 : ℝ) * (nearC₀ * nearN |r|) *
        hnorm 2 F ^ 2 := role15_bound hε r τ τ' hF hF' ha hb
    _ ≤ 1 * hnorm 2 F ^ 2 := mul_le_mul_of_nonneg_right hpaid (sq_nonneg _)
    _ = hnorm 2 F ^ 2 := one_mul _

end OVNS.Quant

end
