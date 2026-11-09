import OddViscousNS.Quant.Energy.Native.NearAssembly
import OddViscousNS.Quant.Energy.Near.Profiles
import OddViscousNS.Quant.Energy.Kinetic.Identity

/-!
# Theorem 1.2, fixed force — E5, the corrected `H¹` energy: definitions

The objects of the `H¹` energy interface `H1EnergyInterface` (`Interfaces.lean`; TeX
`quantitative_energies.tex` eq. quant-h1-energy with `n = 3/4`, the "signed metric" paragraph
eq. quant-metric at `s = 1`, and the "purefast nonresonant cubic" paragraph; spec
`t12_energy_spec.md` §2.2 E5; survey `t12_energy_derivation.md` §2.2).

## The corrected energy (TeX: `E = e₁(M₁) + E⁰`, `e₁ = ½(‖F‖₁² + ⟨z₁, M₁ z₁⟩)`, `z₁ = A^{1/2}F`)
* `E⁰ = Re⟨R₋(F,F), AF⟩` is `cubicE 1 (−1) r τ F` of `Native/Defs.lean` (`cubicCorr` along the
  actual solution, phase `τ = r t`);
* the **signed metric**.  The TeX puts `M₁ = X₁ + X₂ + Z` (eq. quant-metric).  `X₁` "inverts the
  slow–fast vertex with denominator `−(|p|²+|k|²+|j|²) + irδ`": its multiplier is
  `metM r τ = 𝟏_{p slow, q fast, Φ ≠ 0} e^{iτΦ}/(−(|p|²+|q|²+|p+q|²) + irΦ)` (`metSym`; the
  resolvent `resolv (−1)` of `Native/Defs.lean`), and `⟨z₁, X₁ z₁⟩ = X1form = 4 pair 1 F (Qm metM S F)`.
  The normalization is fixed by the cancellation it must produce: the `H¹` law reads
  `½(a_F²)' + b_F² = −2⟨AF, Q_τ(S,F)⟩ − ⟨AF, Q_τ(F,F)⟩ − ⟨AF, H_ψ⟩` (both advective orders), and the
  frozen-amplitude-plus-heat derivative of the multiplier is `(irΦ − |p|² − |q|² − |k|²) metSym =
  e^{iτΦ}` (`metDM`), so `(½ X1form)' ∋ 2⟨AF, Q_nr(S,F)⟩`, which cancels the slow–fast term up to
  its resonant part, itself zero by catalytic neutrality (`cat_neutral`, `σ = 1`).  The Hermitian
  numerator "factors as `(v−u)[l(v+u)−uv]`" (TeX) is this vanishing at zero phase.
* `X₂` ("inverts both rootings `X₁𝓛 + 𝓛*X₁` using its two slow ancestor heats and two exterior
  fast heats") and `Z = −∫₀^∞ e^{−uA} X₁(τ+u; B_slow(e^{−uA}S, e^{−uA}S)) e^{−uA} du` are defined
  below **for reference** (`X2form`, `Zform`, as the heat integrals of Body 12 §7–8 and the TeX),
  but are **not** part of the fixed-force energy: the terms they would cancel,
  `−½⟨z,(X₁𝓛+𝓛*X₁)z⟩` and `−½⟨z, D_S X₁[B(S,S)] z⟩`, are `O((B_S² + W_S B_S)/q)·a_F²` and are paid
  by the timed multiplier `m` at a polynomial threshold of degree `< d` (TeX: "For fixed force one
  can instead pay this multiplier additively at its original stricter quota").  See
  `t12_h1_scaffold.md` §2 for the reading.  Hence here `M₁ = X₁` and
  `E = ½ a_F² + ½ X1form + E⁰` (`h1Energy`).

## The remainders and the sources
* `cubicHeat = Re⟨R₋(AF,F) + R₋(F,AF), AF⟩` is the TeX's `E_heat` ("both `−AF` input slots; the
  output heat cancels the test derivative").
* The nonresonant split `Q_τ = Q_res + Q_nr` (`Qnr`, `nonresM`) isolates the resonant slot
  `⟨AF, Q_res(F,F)⟩` paid by `ResH1`.
* `fastNL = −Π_F Q_{rt}(y,y)`, `slowNL = −Π_S Q_{rt}(y,y) + Π_S g` are the non-heat parts of the
  right-hand sides `fastRHS`, `slowRHS` of `Kinetic/Defs.lean` (`fastRHS = −A F + fastNL`).
* The sources `N_f`, `f_f`, `m` of eq. quant-h1-energy are constants on the piece, built from the
  caps (`nfConst`, `ffConst`, `mConst`); their budgets are paid by the thresholds.

## The role thresholds (TeX Table quant-roles; Body 17 §4; `t12_h1_scaffold.md` §3)
`h1Threshold Tp μ φ caps` is a sum of nonnegative role terms (a sum dominates the TeX's maximum):
roles 8 (`1`), 9 (FAR and genuine source, `role9`), 13 (static coercivity, `role13`), 14 (both
input heats, `role14`), the mixed near partner of role 15 (`role15mix`; the fast–fast near part is
the leading `K₁ √P_F y^{3/2} N(q) ≤ 1` hypothesis with `K₁ = h1K₁ = 32 cQ1`), 28 (metric:
operator `role28op`, metric–`Q` `role28Q`/`role28SF`, slow source `role28src`, timed quota
`role28timed`), and the force roles 11, 12, 18, 29, 30 (`roleForce`).  The proper profile
`P(q) = nearP q` (`Near/Defs.lean`) enters roles 13, 14 and the native profile `N(q) = nearN q`
the mixed role through `profC` (`nearProfilesEl` at `δ = 1/100`).  Caps enter through their
nonnegative parts `cp`.

## Reading choices (documented in `t12_h1_scaffold.md`)
1. `M₁ = X₁` (above).  2. The static and heat remainders are bounded by the proper profile
`nearP` with the allowances `cStat = cHeat = 2¹⁰` (TeX: "the two proper heat directions, static
coercivity … are separate estimates"; no body gives the constants).  3. `N̄ = π = 1` (the force
budgets are paid by `roleForce`, degree `v`; the TeX's `N̄ ≤ 9/512 + π/2²⁰`, `π ≍ μ` are upper
bounds we do not need).  4. The Wiener-interpolation and `H¹` product constants are the library's
(`cI`, `cQ1`: the constants of `exists_wiener_interp`, `exists_hnorm_one_Qphase_le`, i.e.
`2√5488`, `16√5488`), not the sources' `√42`, `7`.
-/

open scoped ENNReal ComplexConjugate
open MeasureTheory Set

noncomputable section

namespace OVNS

/-! ### A. The resonant / nonresonant split of the phase multiplier -/

open Classical in
/-- The nonresonant phase multiplier `𝟏_{Φ ≠ 0} e^{iτΦ}` (TeX `Q_nr`). -/
def nonresM (τ : ℝ) : Mult := fun a b c p q =>
  if Phi a b c p q = 0 then 0 else phaseM τ a b c p q

/-- `Q_nr,τ(f, g) = Q^♯_{nonresM τ}(f, g)`, the nonresonant part of the phased convection. -/
def Qnr (τ : ℝ) : Field → Field → Field := Qm (nonresM τ)

lemma nonresM_bdd (τ : ℝ) : (nonresM τ).Bdd := fun a b c p q => by
  unfold nonresM
  split_ifs
  · simp
  · exact phaseM_bdd τ a b c p q

lemma nonresM_real (τ : ℝ) : (nonresM τ).Real := fun a b c p q => by
  unfold nonresM
  by_cases h : Phi a b c p q = 0
  · have h' : Phi a b c (-p) (-q) = 0 := by rw [Phi_neg', h, neg_zero]
    simp [h, h']
  · have h' : Phi a b c (-p) (-q) ≠ 0 := by rw [Phi_neg', neg_ne_zero]; exact h
    simp only [h, h', ite_false]
    exact phaseM_real τ a b c p q

/-- `e^{iτΦ} = 𝟏_{Φ=0} + 𝟏_{Φ≠0} e^{iτΦ}` pointwise (the phase is `1` on the resonant set). -/
lemma phaseM_eq_resM_add_nonresM (τ : ℝ) (a b c : Sgn) (p q : Mode) :
    phaseM τ a b c p q = resM a b c p q + nonresM τ a b c p q := by
  unfold resM nonresM
  by_cases h : Phi a b c p q = 0
  · simp [h, phaseM]
  · simp [h]

/-- **The resonant / nonresonant split** `Q_τ(f,g) = Q_res(f,g) + Q_nr,τ(f,g)` on `H²` fields. -/
theorem Qphase_eq_Qres_add_Qnr (τ : ℝ) {f g : Field} (hf : MZ 2 f) (hg : MZ 2 g) :
    Qphase τ f g = Qres f g + Qnr τ f g :=
  Quant.Qm_add_mult' resM_bdd (nonresM_bdd τ) (phaseM_eq_resM_add_nonresM τ) hf hg

/-! ### B. The Laplacian and the heat semigroup on fields -/

/-- `A f`, `(Af)_k = |k|² f_k`. -/
def lapF (f : Field) : Field := fun k => (absSq k : ℂ) • f k

/-- The heat semigroup `e^{−uA}`. -/
def heatF (u : ℝ) (f : Field) : Field := fun k => (Real.exp (-(u * absSq k)) : ℂ) • f k

/-- `pair 1 F G = pair 0 (AF) G`: the `H¹` pairing is the `L²` pairing against `AF`. -/
lemma pair_one_eq_pair_zero_lap (F G : Field) : pair 1 F G = pair 0 (lapF F) G := by
  unfold pair
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0
  · simp [sobWeight, hk]
  · have h0 : sobWeight 0 k = 1 := by simp [sobWeight, hk]
    rw [sobWeight_one, h0, one_mul, lapF, inner_smul_left, Complex.conj_ofReal,
      Complex.re_ofReal_mul]

private lemma conjV_smul_real (c : ℝ) (v : V3) : conjV ((c : ℂ) • v) = (c : ℂ) • conjV v := by
  ext i
  simp [conjV, PiLp.smul_apply]

lemma IsReal.lapF {F : Field} (hF : IsReal F) : IsReal (lapF F) := fun k => by
  show (absSq (-k) : ℂ) • F (-k) = conjV ((absSq k : ℂ) • F k)
  rw [absSq_neg, hF k, conjV_smul_real]

/-- `(Af)_k` is `ℓ²` with norm `‖f‖₂`. -/
lemma lapF_l2 {f : Field} (hf : InH 2 f) :
    (Summable fun k => ‖lapF f k‖ ^ 2) ∧ Real.sqrt (∑' k, ‖lapF f k‖ ^ 2) = hnorm 2 f := by
  obtain ⟨h1, h2⟩ := tsum_norm_sq_absSq_smul hf
  have e : ∀ k, ‖lapF f k‖ = ‖(-(absSq k : ℝ) : ℂ) • f k‖ := fun k => by
    simp only [lapF, norm_smul, norm_neg]
  simp only [e]
  exact ⟨h1, h2⟩

lemma lapF_zero_mode (f : Field) : lapF f 0 = 0 := by simp [lapF, absSq]

lemma lapF_neg (f : Field) : lapF (-f) = -lapF f := by
  funext k; simp [lapF]

lemma lapF_add (f g : Field) : lapF (f + g) = lapF f + lapF g := by
  funext k; simp [lapF, smul_add]

lemma PiF_lapF (f : Field) : PiF (lapF f) = lapF (PiF f) := by
  funext k
  by_cases hk : k 2 = 0 <;> simp [PiF, lapF, hk]

/-! ### C. The slow–fast metric multiplier `X₁` (TeX, eq. quant-metric at `s = 1`) -/

/-- The slow–fast mask: slow first input, fast second input, nonzero exterior phase
(TeX: "its signed exterior phase is `δ = n(u − v)`, where the common fast vertical `n ≠ 0`"). -/
def SlowFast (a b c : Sgn) (p q : Mode) : Prop := p 2 = 0 ∧ q 2 ≠ 0 ∧ Phi a b c p q ≠ 0

/-- The three-leg heat `|p|² + |q|² + |p+q|²` of a triad (TeX: "denominator
`−(|p|²+|k|²+|j|²) + irδ`"). -/
def triHeat (p q : Mode) : ℝ := absSq p + absSq q + absSq (p + q)

/-- The `X₁` symbol `e^{iτΦ}/(−(|p|²+|q|²+|p+q|²) + irΦ)`. -/
def metSym (r τ : ℝ) (a b c : Sgn) (p q : Mode) : ℂ :=
  phaseM τ a b c p q * Quant.resolv (-1) (triHeat p q) (r * Phi a b c p q)

open Classical in
/-- The `X₁` multiplier `𝟏_{SlowFast} e^{iτΦ}/(−(|p|²+|q|²+|p+q|²) + irΦ)`. -/
def metM (r τ : ℝ) : Mult := fun a b c p q =>
  if SlowFast a b c p q then metSym r τ a b c p q else 0

open Classical in
/-- The frozen-amplitude-plus-heat derivative of `metM`: `𝟏_{SlowFast} e^{iτΦ}`
(`(irΦ − |p|² − |q|² − |p+q|²) metSym = e^{iτΦ}`). -/
def metDM (τ : ℝ) : Mult := fun a b c p q =>
  if SlowFast a b c p q then phaseM τ a b c p q else 0

lemma SlowFast.ne_zero {a b c : Sgn} {p q : Mode} (h : SlowFast a b c p q) : p + q ≠ 0 := by
  intro h0
  have := congrFun h0 2
  simp only [Pi.add_apply, h.1, zero_add, Pi.zero_apply] at this
  exact h.2.1 this

lemma one_le_triHeat {p q : Mode} (hk : p + q ≠ 0) : 1 ≤ triHeat p q := by
  unfold triHeat
  have := one_le_absSq hk
  have := absSq_nonneg p
  have := absSq_nonneg q
  linarith

lemma absSq_le_triHeat (p q : Mode) : absSq (p + q) ≤ triHeat p q := by
  unfold triHeat
  have := absSq_nonneg p
  have := absSq_nonneg q
  linarith

/-- `|metSym| ≤ 1/(|p|²+|q|²+|p+q|²)` (the modulus of the resolvent). -/
lemma norm_metSym_le (r τ : ℝ) (a b c : Sgn) {p q : Mode} (hk : p + q ≠ 0) :
    ‖metSym r τ a b c p q‖ ≤ 1 / triHeat p q := by
  have h1 := one_le_triHeat hk
  rw [metSym, norm_mul]
  calc ‖phaseM τ a b c p q‖ * ‖Quant.resolv (-1) (triHeat p q) (r * Phi a b c p q)‖
      ≤ 1 * (1 / triHeat p q) :=
        mul_le_mul (phaseM_bdd τ a b c p q)
          (Quant.norm_resolv_le (Or.inr rfl) (by linarith) _) (norm_nonneg _) zero_le_one
    _ = 1 / triHeat p q := one_mul _

/-- `|metSym| ≤ 1/|p+q|²` (the output-heat gain used by the summability controls). -/
lemma norm_metSym_le_absSq (r τ : ℝ) (a b c : Sgn) {p q : Mode} (hk : p + q ≠ 0) :
    ‖metSym r τ a b c p q‖ ≤ 1 / absSq (p + q) :=
  (norm_metSym_le r τ a b c hk).trans
    (one_div_le_one_div_of_le (by linarith [one_le_absSq hk]) (absSq_le_triHeat p q))

lemma norm_metM_le_absSq (r τ : ℝ) (a b c : Sgn) (p q : Mode) :
    ‖metM r τ a b c p q‖ ≤ 1 / absSq (p + q) := by
  unfold metM
  split_ifs with h
  · exact norm_metSym_le_absSq r τ a b c h.ne_zero
  · rw [norm_zero]
    exact div_nonneg zero_le_one (absSq_nonneg _)

lemma metM_bdd (r τ : ℝ) : (metM r τ).Bdd := fun a b c p q => by
  unfold metM
  split_ifs with h
  · exact (norm_metSym_le r τ a b c h.ne_zero).trans
      ((div_le_one (by linarith [one_le_triHeat h.ne_zero])).2 (one_le_triHeat h.ne_zero))
  · simp

lemma metDM_bdd (τ : ℝ) : (metDM τ).Bdd := fun a b c p q => by
  unfold metDM
  split_ifs
  · exact phaseM_bdd τ a b c p q
  · simp

lemma triHeat_neg (p q : Mode) : triHeat (-p) (-q) = triHeat p q := by
  have h : -p + -q = -(p + q) := by abel
  simp only [triHeat, h, absSq_neg]

lemma slowFast_neg (a b c : Sgn) (p q : Mode) : SlowFast a b c (-p) (-q) ↔ SlowFast a b c p q := by
  unfold SlowFast
  rw [Phi_neg', neg_ne_zero]
  simp

lemma metSym_neg (r τ : ℝ) (a b c : Sgn) (p q : Mode) :
    metSym r τ a b c (-p) (-q) = conj (metSym r τ a b c p q) := by
  rw [metSym, metSym, map_mul, ← phaseM_real τ a b c p q, Quant.conj_resolv, triHeat_neg,
    Phi_neg', mul_neg]

/-- Reality of the `X₁` multiplier. -/
lemma metM_real (r τ : ℝ) : (metM r τ).Real := fun a b c p q => by
  unfold metM
  rw [metSym_neg]
  by_cases h : SlowFast a b c p q
  · rw [ite_eq_left ((slowFast_neg a b c p q).2 h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h ((slowFast_neg a b c p q).1 h')), ite_eq_right h, map_zero]

lemma metDM_real (τ : ℝ) : (metDM τ).Real := fun a b c p q => by
  unfold metDM
  by_cases h : SlowFast a b c p q
  · rw [ite_eq_left ((slowFast_neg a b c p q).2 h), ite_eq_left h]
    exact phaseM_real τ a b c p q
  · rw [ite_eq_right (fun h' => h ((slowFast_neg a b c p q).1 h')), ite_eq_right h, map_zero]

/-- The `X₁` operator applied to `F`: `X₁(τ; S) F = Q^♯_{metM}(S, F)` (a fast field). -/
def X1op (r τ : ℝ) (S F : Field) : Field := Qm (metM r τ) S F

/-- `⟨z₁, X₁ z₁⟩ = 4 Re⟨AF, X₁(S)F⟩`, the `X₁` quadratic form on `z₁ = A^{1/2}F` (see the
module docstring for the normalization). -/
def X1form (r τ : ℝ) (S F : Field) : ℝ := 4 * pair 1 F (X1op r τ S F)

/-- The polarized form `⟨z_F, X₁ z_G⟩ = 2 Re⟨AG, X₁ F⟩ + 2 Re⟨AF, X₁ G⟩` (symmetric in
`F, G`; `X1form r τ S F = X1bil r τ S F F`). -/
def X1bil (r τ : ℝ) (S F G : Field) : ℝ :=
  2 * pair 1 G (X1op r τ S F) + 2 * pair 1 F (X1op r τ S G)

lemma X1form_eq_bil (r τ : ℝ) (S F : Field) : X1form r τ S F = X1bil r τ S F F := by
  unfold X1form X1bil
  ring

lemma X1bil_comm (r τ : ℝ) (S F G : Field) : X1bil r τ S F G = X1bil r τ S G F := by
  unfold X1bil
  ring

/-- The slow–fast linearization `𝓛_τ(S)F = 2Π_F Q_τ(S,F)` (TeX eq. quant-actual-system, "both
physical orders"). -/
def Lop (τ : ℝ) (S F : Field) : Field := (2 : ℂ) • PiF (Qphase τ S F)

/-- The phase-free slow convection `B_slow(S,S) = Π_S Q_res(S,S)` (on slow fields the phase is
identically `1`, `lam_slow`). -/
def Bslow (S : Field) : Field := PiS (Qres S S)

/-- **Reference only.** `⟨z₁, X₂ z₁⟩`, with `X₂ = −∫₀^∞ e^{−uA}[X₁(τ+u; S_u)𝓛(S_u) +
𝓛(S_u)*X₁(τ+u; S_u)] e^{−uA} du`, `S_u = e^{−uA}S` (Body 12 §7; TeX "inverts both rootings
`X₁𝓛 + 𝓛*X₁` using its two slow ancestor heats and two exterior fast heats"), written as the
heat integral of the polarized form `X1bil` at the advanced phase.  Not used in `h1Energy`. -/
def X2form (r t : ℝ) (S F : Field) : ℝ :=
  -∫ u in Ioi (0 : ℝ),
    X1bil r (r * (t + u)) (heatF u S) (heatF u F) (Lop (r * (t + u)) (heatF u S) (heatF u F))

/-- **Reference only.** `⟨z₁, Z z₁⟩`, with
`Z = −∫₀^∞ e^{−uA} X₁(τ+u; B_slow(e^{−uA}S, e^{−uA}S)) e^{−uA} du` (TeX; Body 12 §8).  Not used
in `h1Energy`. -/
def Zform (r t : ℝ) (S F : Field) : ℝ :=
  -∫ u in Ioi (0 : ℝ), X1form r (r * (t + u)) (Bslow (heatF u S)) (heatF u F)

/-! ### D. The cubic heat remainder -/

/-- `E_heat = Re⟨R₋(AF,F) + R₋(F,AF), AF⟩`: the two input heats of the purefast cubic (TeX:
"`E_heat` has both `−AF` input slots"). -/
def cubicHeat (r τ : ℝ) (F : Field) : ℝ :=
  pair 1 F (Quant.corr (-1) r τ (lapF F) F) + pair 1 F (Quant.corr (-1) r τ F (lapF F))

namespace Quant

variable {r : ℝ} {g : Field} {y : ℝ → Field}

/-! ### E. The energy along the actual solution -/

/-- The non-heat part `−Π_F Q_{rt}(y,y)` of the fast right-hand side (`fastRHS = −AF + fastNL`). -/
def fastNL (r : ℝ) (_g : Field) (y : ℝ → Field) (t : ℝ) : Field :=
  -PiF (Qphase (r * t) (y t) (y t))

/-- The non-heat part `−Π_S Q_{rt}(y,y) + Π_S g` of the slow right-hand side
(`slowRHS = −AS + slowNL`). -/
def slowNL (r : ℝ) (g : Field) (y : ℝ → Field) (t : ℝ) : Field :=
  -PiS (Qphase (r * t) (y t) (y t)) + PiS g

lemma fastRHS_eq_lap (t : ℝ) :
    fastRHS r g y t = -lapF (PiF (actual r g y t)) + fastNL r g y t := by
  funext k
  simp only [fastRHS, fastNL, lapF, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg, neg_smul]

lemma slowRHS_eq_lap (t : ℝ) :
    slowRHS r g y t = -lapF (PiS (actual r g y t)) + slowNL r g y t := by
  funext k
  simp only [slowRHS, slowNL, lapF, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg, neg_smul,
    add_assoc]

lemma PiF_fastNL (t : ℝ) : PiF (fastNL r g y t) = fastNL r g y t := by
  funext k
  by_cases hk : k 2 = 0 <;> simp [fastNL, PiF, hk]

lemma PiS_slowNL (t : ℝ) : PiS (slowNL r g y t) = slowNL r g y t := by
  funext k
  by_cases hk : k 2 = 0 <;> simp [slowNL, PiS, hk]

/-- `⟨z₁, X₁ z₁⟩` along the actual solution (`S = Π_S x`, `F = Π_F x`, phase `τ = r t`). -/
def metricCorr (r : ℝ) (g : Field) (y : ℝ → Field) (t : ℝ) : ℝ :=
  X1form r (r * t) (PiS (actual r g y t)) (PiF (actual r g y t))

/-- `E⁰ = Re⟨R₋(F,F), AF⟩` along the actual solution. -/
def cubicCorr (r : ℝ) (g : Field) (y : ℝ → Field) (t : ℝ) : ℝ :=
  cubicE 1 (-1) r (r * t) (PiF (actual r g y t))

/-- **The corrected `H¹` energy** `E = ½ a_F² + ½⟨z₁, X₁ z₁⟩ + E⁰` (TeX `E = e₁(M₁) + E⁰` with
`e₁ = ½(‖F‖₁² + ⟨z₁, M₁ z₁⟩)` and the fixed-force reading `M₁ = X₁`). -/
def h1Energy (r : ℝ) (g : Field) (y : ℝ → Field) (t : ℝ) : ℝ :=
  1 / 2 * fastNorm 1 r g y t ^ 2 + 1 / 2 * metricCorr r g y t + cubicCorr r g y t

/-! ### F. Constants, profiles, sources and thresholds -/

/-- The Wiener-interpolation constant `𝒜(u) ≤ c_I √(‖u‖₁‖u‖₂)` of `Lattice.lean`
(`exists_wiener_interp`; its proof gives `2√5488`, which that statement does not expose). -/
def cI : ℝ := max 1 (Classical.choose exists_wiener_interp)

/-- The `H¹` product constant `‖Π_F Q_τ(F,F)‖₁ ≤ c_{Q1} √(‖F‖₁‖F‖₂) ‖F‖₂` of `Native/Bound.lean`
(`exists_hnorm_one_Qphase_le`; the library's route gives `16√5488`, the sources `√42 < 7`). -/
def cQ1 : ℝ := max 1 (Classical.choose exists_hnorm_one_Qphase_le)

lemma one_le_cI : 1 ≤ cI := le_max_left _ _

lemma one_le_cQ1 : 1 ≤ cQ1 := le_max_left _ _

lemma cI_pos : 0 < cI := lt_of_lt_of_le one_pos one_le_cI

lemma cQ1_pos : 0 < cQ1 := lt_of_lt_of_le one_pos one_le_cQ1

/-- `𝒜(u) ≤ c_I √(‖u‖₁ ‖u‖₂)`. -/
theorem wiener_le_cI {u : Field} (hu : MZ 2 u) :
    wiener u ≤ cI * Real.sqrt (hnorm 1 u * hnorm 2 u) :=
  ((Classical.choose_spec exists_wiener_interp).2 u hu).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _))

/-- `‖Π_F Q_τ(F,F)‖₁ ≤ c_{Q1} √(‖F‖₁‖F‖₂) ‖F‖₂`. -/
theorem hnorm_one_PiF_Qphase_le (τ : ℝ) {F : Field} (hF : MZ 2 F) :
    hnorm 1 (PiF (Qphase τ F F)) ≤ cQ1 * Real.sqrt (hnorm 1 F * hnorm 2 F) * hnorm 2 F :=
  ((Classical.choose_spec exists_hnorm_one_Qphase_le).2 τ F hF).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.sqrt_nonneg _)) (hnorm_nonneg _ _))

/-- The static allowance `|E⁰| ≤ cStat P(q) a_F² b_F` (reading choice 2). -/
def cStat : ℝ := 2 ^ 10

/-- The heat allowance `|E_heat| ≤ cHeat P(q) a_F b_F²` (reading choice 2). -/
def cHeat : ℝ := 2 ^ 10

/-- The leading role-15 normalization `K₁ = 32 nearC₀ c_{Q1}`: with `nearD1_le`
(`|D₁^N(F; h)| ≤ nearC₀ N(q) ‖h‖₁ b_F²`, `Native/NearAssembly.lean`, `nearC₀ = 26`) and the `H¹`
product leaf, the hypothesis `K₁ √P_F y^{3/2} N(q) ≤ 1` makes the fast–fast near term a `1/32`
share of the dissipation. -/
def h1K₁ : ℝ := 32 * nearC₀ * cQ1

lemma one_le_nearC₀ : 1 ≤ nearC₀ := by norm_num [nearC₀]

/-- The profile constant: `nearN q ≤ profC q^{−49/100}` and `nearP q ≤ profC q^{−29/100}` for
`q ≥ 1` (`nearProfilesEl` at `δ = 1/100`, `Near/Profiles.lean`). -/
def profC : ℝ :=
  max 1 (Classical.choose (nearProfilesEl (1 / 100) (by norm_num)))

lemma one_le_profC : 1 ≤ profC := le_max_left _ _

lemma profC_pos : 0 < profC := lt_of_lt_of_le one_pos one_le_profC

theorem nearN_le_profC {q : ℝ} (hq : 1 ≤ q) : nearN q ≤ profC * q ^ (-(49 / 100 : ℝ)) := by
  have h := (Classical.choose_spec (nearProfilesEl (1 / 100) (by norm_num)) q hq).1
  have e : q ^ (-1 / 2 + 1 / 100 : ℝ) = q ^ (-(49 / 100) : ℝ) := by
    rw [show (-1 / 2 + 1 / 100 : ℝ) = -(49 / 100) by norm_num]
  rw [e] at h
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by linarith) _))

theorem nearP_le_profC {q : ℝ} (hq : 1 ≤ q) : nearP q ≤ profC * q ^ (-(29 / 100 : ℝ)) := by
  have h := (Classical.choose_spec (nearProfilesEl (1 / 100) (by norm_num)) q hq).2
  have e : q ^ (-3 / 10 + 1 / 100 : ℝ) = q ^ (-(29 / 100) : ℝ) := by
    rw [show (-3 / 10 + 1 / 100 : ℝ) = -(29 / 100) by norm_num]
  rw [e] at h
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by linarith) _))

/-- A bound for `‖Π_S Q_{rt}(y,y)‖₁ + ‖Π_S g‖₁` on the piece: `8(W_S + c₄ y + c₄)(B_S + y + 1) + φ`
(from (M4) `‖Q(y,y)‖₁ ≤ 8 𝒜(y)‖y‖₂`, `𝒜(y) ≤ W_S + c₄ b_F + c₄‖ψ‖₂`, `‖ψ‖₂ ≤ 1`). -/
def hSrc (φ : ℝ) (caps : Caps) : ℝ :=
  8 * (cp caps.WS + c4 * cp caps.yF + c4) * (cp caps.BS + cp caps.yF + 1) + φ

/-- A bound for `(1/8)‖2Π_F Q_τ(S,F)‖₁`: `W_S y + c_I B_S √(P_F y)` (from (M4) and the Wiener
interpolation `𝒜(F) ≤ c_I √(a_F b_F)`). -/
def mixNear (caps : Caps) : ℝ :=
  cp caps.WS * cp caps.yF + cI * cp caps.BS * Real.sqrt (cp caps.PF * cp caps.yF)

/-- A bound for `‖Π_F Q_τ(F,F)‖₁`: `c_{Q1} √P_F y^{3/2}`. -/
def ffCoef (caps : Caps) : ℝ := cQ1 * Real.sqrt (cp caps.PF) * cp caps.yF ^ (3 / 2 : ℝ)

/-- A bound for `‖Π_F Q_{rt}(y,y)‖₁` once `‖Π_F H_ψ‖₁ ≤ 1`: `ffCoef + 8 mixNear + 1`. -/
def srcAll (caps : Caps) : ℝ := ffCoef caps + 8 * mixNear caps + 1

/-- Role 8 (domains): `1`. -/
def role8 : ℝ := 1

/-- Role 9 (genuine `H¹` fast source including FAR): the FAR differential
`|D₁^B(F; h)| ≤ 2¹⁴ ‖h‖₁ b_F²/q` on the whole source, a `1/64` share. -/
def role9 (caps : Caps) : ℝ := 2 ^ 20 * srcAll caps

/-- Role 13 (static coercivity `|2E⁰| ≤ a_F²/128`): `cStat P(q) y ≤ 1/256` through
`P(q) ≤ profC q^{−29/100}`. -/
def role13 (caps : Caps) : ℝ := (2 ^ 8 * cStat * profC * cp caps.yF) ^ (100 / 29 : ℝ)

/-- Role 14 (both input heats `|E_heat| ≤ b_F²/64`): `cHeat P(q) y ≤ 1/64`, the proper role of
degree `3v` in Table quant-fixed (here `100 v / 29`, since `nearP` has exponent `−29/100`). -/
def role14 (caps : Caps) : ℝ := (2 ^ 6 * cHeat * profC * cp caps.yF) ^ (100 / 29 : ℝ)

/-- The mixed near partner of role 15: `8 nearC₀ N(q) mixNear ≤ 1/64` through
`N(q) ≤ profC q^{−49/100}`. -/
def role15mix (caps : Caps) : ℝ := (2 ^ 9 * nearC₀ * profC * mixNear caps) ^ (100 / 49 : ℝ)

/-- Role 28, operator: `|⟨z₁, X₁ z₁⟩| ≤ 2⁹ B_S a_F²/q ≤ 2⁻²⁰ a_F²`. -/
def role28op (caps : Caps) : ℝ := 2 ^ 29 * cp caps.BS

/-- Role 28, metric–`Q` (fast–fast insertion): `2⁹ c_{Q1} B_S P_F/q ≤ 1/64`. -/
def role28Q (caps : Caps) : ℝ := 2 ^ 15 * cQ1 * cp caps.BS * cp caps.PF

/-- Role 28, metric–`Q` (slow–fast insertion): `2¹²(B_S W_S + c_I B_S²)/q ≤ 1/64`. -/
def role28SF (caps : Caps) : ℝ := 2 ^ 18 * (cp caps.BS * cp caps.WS + cI * cp caps.BS ^ 2)

/-- Role 28, slow source into `X₁`: `2⁹ hSrc/q ≤ 1/64`. -/
def role28src (φ : ℝ) (caps : Caps) : ℝ := 2 ^ 15 * hSrc φ caps

/-- The timed metric multiplier of `X₁`'s uncancelled insertions,
`m = (2⁹ hSrc + 2¹²(B_S W_S + c_I B_S²) + 2⁸ B_S)/q`, constant on the piece. -/
def mCoef (φ : ℝ) (caps : Caps) : ℝ :=
  2 ^ 9 * hSrc φ caps + 2 ^ 12 * (cp caps.BS * cp caps.WS + cI * cp caps.BS ^ 2) +
    2 ^ 8 * cp caps.BS

/-- Role 28, timed quota (TeX: "`(2/ℓ₁)∫m ≤ 1` on a true piece"; NEW378/LOCAL362 are MISSING, the
quota is paid additively): `(2/ℓ₁) Tp mCoef/q ≤ 1`. -/
def role28timed (Tp φ : ℝ) (caps : Caps) : ℝ := 4 * (1 + Tp) * mCoef φ caps

/-- The force roles 11, 12, 18, 29, 30 (all `O(φ/q)`): `‖ψ‖₂ ≤ 1`, `‖H_ψ‖₁ ≤ 2⁻¹⁶/nearC₀`,
`‖H_ψ‖₀ ≤ 1/(1+Tp)`, the `f_f` budget. -/
def roleForce (Tp φ : ℝ) (caps : Caps) : ℝ :=
  2 ^ 22 * (1 + nearC₀) * (1 + c4) * (1 + φ) * (1 + Tp) *
    (cp caps.BS + cp caps.yF + cp caps.WS + cp caps.AS + cp caps.PF + 1)

/-- **The `H¹` role threshold** `q₁(Tp, μ, φ, caps)` (roles 8, 9, 11–14, 28–30 and the mixed
partner of 15; the leading fast–fast near term is the `K₁` hypothesis). -/
def h1Threshold (Tp μ φ : ℝ) (caps : Caps) : ℝ :=
  role8 + role9 caps + role13 caps + role14 caps + role15mix caps + role28op caps +
    role28Q caps + role28SF caps + role28src φ caps + role28timed Tp φ caps + roleForce Tp φ caps
    + 0 * μ

/-- The genuine `L²` source `N_f`: the constant bound `4(1+c₄) φ (W_S + y + A_S + P_F + 1)/q` of
`‖Π_F H_ψ‖₀` on the piece. -/
def nfConst (φ : ℝ) (caps : Caps) (r : ℝ) : ℝ :=
  4 * (1 + c4) * φ * (cp caps.WS + cp caps.yF + cp caps.AS + cp caps.PF + 1) / |r|

/-- The constant bound `32(1+c₄) φ (B_S + y + W_S + 1)/q` of `‖H_ψ‖₁` on the piece. -/
def h1Const (φ : ℝ) (caps : Caps) (r : ℝ) : ℝ :=
  32 * (1 + c4) * φ * (cp caps.BS + cp caps.yF + cp caps.WS + 1) / |r|

/-- The tested force term `f_f = 2⁸ B_S h1Const²/q` (the metric–force insertion after Young). -/
def ffConst (φ : ℝ) (caps : Caps) (r : ℝ) : ℝ := 2 ^ 8 * cp caps.BS * h1Const φ caps r ^ 2 / |r|

/-- The timed multiplier `m = mCoef/q`. -/
def mConst (φ : ℝ) (caps : Caps) (r : ℝ) : ℝ := mCoef φ caps / |r|

/-- `N̄ = 1` (reading choice 3). -/
def h1Nbar (_μ _φ : ℝ) : ℝ := 1

/-- `π = 1` (reading choice 3). -/
def h1Pi (_μ _φ : ℝ) : ℝ := 1

/-! ### Elementary facts about the thresholds -/

lemma hSrc_nonneg {φ : ℝ} (hφ : 0 ≤ φ) (caps : Caps) : 0 ≤ hSrc φ caps := by
  have := cp_nonneg caps.WS
  have := cp_nonneg caps.yF
  have := cp_nonneg caps.BS
  have := c4_pos
  unfold hSrc
  positivity

lemma mixNear_nonneg (caps : Caps) : 0 ≤ mixNear caps := by
  have := cp_nonneg caps.WS
  have := cp_nonneg caps.yF
  have := cp_nonneg caps.BS
  have := cI_pos
  unfold mixNear
  positivity

lemma ffCoef_nonneg (caps : Caps) : 0 ≤ ffCoef caps := by
  have := cp_nonneg caps.PF
  have := cp_nonneg caps.yF
  have := cQ1_pos
  unfold ffCoef
  positivity

lemma srcAll_nonneg (caps : Caps) : 0 ≤ srcAll caps := by
  have := ffCoef_nonneg caps
  have := mixNear_nonneg caps
  unfold srcAll
  linarith

lemma mCoef_nonneg {φ : ℝ} (hφ : 0 ≤ φ) (caps : Caps) : 0 ≤ mCoef φ caps := by
  have := hSrc_nonneg hφ caps
  have := cp_nonneg caps.WS
  have := cp_nonneg caps.BS
  have := cI_pos
  unfold mCoef
  positivity

lemma roleForce_nonneg {Tp φ : ℝ} (hTp : 0 ≤ Tp) (hφ : 0 ≤ φ) (caps : Caps) :
    0 ≤ roleForce Tp φ caps := by
  have := nearC₀_pos
  have := cp_nonneg caps.WS
  have := cp_nonneg caps.yF
  have := cp_nonneg caps.BS
  have := cp_nonneg caps.AS
  have := cp_nonneg caps.PF
  have := c4_pos
  unfold roleForce
  positivity

lemma roles_nonneg {Tp φ : ℝ} (hTp : 0 ≤ Tp) (hφ : 0 ≤ φ) (caps : Caps) :
    0 ≤ role9 caps ∧ 0 ≤ role13 caps ∧ 0 ≤ role14 caps ∧ 0 ≤ role15mix caps ∧
      0 ≤ role28op caps ∧ 0 ≤ role28Q caps ∧ 0 ≤ role28SF caps ∧ 0 ≤ role28src φ caps ∧
      0 ≤ role28timed Tp φ caps ∧ 0 ≤ roleForce Tp φ caps := by
  have := cp_nonneg caps.WS
  have := cp_nonneg caps.yF
  have := cp_nonneg caps.BS
  have := cp_nonneg caps.AS
  have := cp_nonneg caps.PF
  have := cI_pos
  have := cQ1_pos
  have := profC_pos
  have := nearC₀_pos
  have := srcAll_nonneg caps
  have := mixNear_nonneg caps
  have := hSrc_nonneg hφ caps
  have := mCoef_nonneg hφ caps
  have := roleForce_nonneg hTp hφ caps
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, this⟩
  · unfold role9; positivity
  · unfold role13 cStat; positivity
  · unfold role14 cHeat; positivity
  · unfold role15mix; positivity
  · unfold role28op; positivity
  · unfold role28Q; positivity
  · unfold role28SF; positivity
  · unfold role28src; positivity
  · unfold role28timed; positivity

/-- Role 8 is paid: `1 ≤ q₁`. -/
lemma one_le_h1Threshold {Tp μ φ : ℝ} (hTp : 0 ≤ Tp) (hφ : 0 ≤ φ) (caps : Caps) :
    1 ≤ h1Threshold Tp μ φ caps := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := roles_nonneg hTp hφ caps
  unfold h1Threshold role8
  linarith

/-- Each role term is below the threshold. -/
lemma role_le_h1Threshold {Tp μ φ : ℝ} (hTp : 0 ≤ Tp) (hφ : 0 ≤ φ) (caps : Caps) :
    role9 caps ≤ h1Threshold Tp μ φ caps ∧ role13 caps ≤ h1Threshold Tp μ φ caps ∧
      role14 caps ≤ h1Threshold Tp μ φ caps ∧ role15mix caps ≤ h1Threshold Tp μ φ caps ∧
      role28op caps ≤ h1Threshold Tp μ φ caps ∧ role28Q caps ≤ h1Threshold Tp μ φ caps ∧
      role28SF caps ≤ h1Threshold Tp μ φ caps ∧ role28src φ caps ≤ h1Threshold Tp μ φ caps ∧
      role28timed Tp φ caps ≤ h1Threshold Tp μ φ caps ∧
      roleForce Tp φ caps ≤ h1Threshold Tp μ φ caps := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := roles_nonneg hTp hφ caps
  unfold h1Threshold role8
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

lemma nfConst_nonneg {φ : ℝ} (hφ : 0 ≤ φ) (caps : Caps) (r : ℝ) : 0 ≤ nfConst φ caps r := by
  have := cp_nonneg caps.WS
  have := cp_nonneg caps.yF
  have := cp_nonneg caps.AS
  have := cp_nonneg caps.PF
  have := c4_pos
  unfold nfConst
  positivity

lemma h1Const_nonneg {φ : ℝ} (hφ : 0 ≤ φ) (caps : Caps) (r : ℝ) : 0 ≤ h1Const φ caps r := by
  have := cp_nonneg caps.WS
  have := cp_nonneg caps.yF
  have := cp_nonneg caps.BS
  have := c4_pos
  unfold h1Const
  positivity

lemma ffConst_nonneg {φ : ℝ} (hφ : 0 ≤ φ) (caps : Caps) (r : ℝ) : 0 ≤ ffConst φ caps r := by
  have := cp_nonneg caps.BS
  have := h1Const_nonneg hφ caps r
  unfold ffConst
  positivity

lemma mConst_nonneg {φ : ℝ} (hφ : 0 ≤ φ) (caps : Caps) (r : ℝ) : 0 ≤ mConst φ caps r := by
  have := mCoef_nonneg hφ caps
  unfold mConst
  positivity

lemma h1Nbar_nonneg (μ φ : ℝ) : 0 ≤ h1Nbar μ φ := by unfold h1Nbar; norm_num

lemma h1Pi_nonneg (μ φ : ℝ) : 0 ≤ h1Pi μ φ := by unfold h1Pi; norm_num

lemma h1Nbar_atMostLinear : AtMostLinear h1Nbar := fun _ _ =>
  ⟨1, fun μ hμ => by unfold h1Nbar; linarith⟩

lemma h1Pi_atMostLinear : AtMostLinear h1Pi := fun _ _ =>
  ⟨1, fun μ hμ => by unfold h1Pi; linarith⟩

lemma h1K₁_nonneg : 0 ≤ h1K₁ := by
  have := cQ1_pos
  have := nearC₀_pos
  unfold h1K₁
  positivity

end Quant

end OVNS

end
