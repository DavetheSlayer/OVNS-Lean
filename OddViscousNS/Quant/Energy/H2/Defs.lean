import OddViscousNS.Quant.Energy.H1.Identity
import OddViscousNS.Quant.Energy.Native.NearAssembly
import OddViscousNS.Quant.Energy.Slow.Barrier

/-!
# Theorem 1.2, fixed force — E8, the corrected `H²` energy: definitions

The objects of the `H²` energy interface `H2EnergyInterface` (`Interfaces.lean`; TeX
`quantitative_energies.tex` eq. quant-metric at `s = 2`, "the same construction at weight two",
the virtual barrier paragraph; spec `t12_energy_spec.md` §1.2, §2.2 E8; survey
`t12_energy_derivation.md` §2.3).  The design follows the `H¹` layer (`H1/Defs.lean`,
`H1/Identity.lean`), whose definitions are shared by import: `X1op`, `metM`, `lapF`, `fastNL`,
`slowNL`, `Qnr`, `profC`, `cI`, `hSrc`.  Everything here lives in the namespace `OVNS.Quant.H2`, so
that this layer can be imported together with `H1/Bounds.lean` and the slow layer.

## The corrected energy (TeX: `W = 2(e₂(M₂) + E⁰₂)`, `e₂ = ½(‖F‖₂² + ⟨z₂, M₂ z₂⟩)`, `z₂ = AF`)
* `E⁰₂ = Re⟨R₋(F,F), A²F⟩` is `cubicE 2 (−1) r τ F` (`Native/Defs.lean`; `cubicCorr2` along the
  actual solution, phase `τ = r t`): "the same construction at weight two" (TeX, purefast cubic
  paragraph; LOCAL210 §1 `E_j`, `j = 2`).
* The **signed metric at weight two**.  The TeX puts `M₂ = X_{1,2} + X_{2,2} + Z₂`.  Lean: as for
  `s = 1` (`H1/Defs.lean`, reading choice 1) the fixed-force energy keeps `M₂ = X_{1,2}` only;
  the terms which `X_{2,2}`, `Z₂` would cancel are paid by the multiplier `G` at a degree `< d`.
  The form
  `⟨z₂, X_{1,2} z₂⟩ = metForm2 r τ S F = 4 Re⟨A²F, Q^♯_{metM}(S,F)⟩` uses the **same** multiplier
  `metM` as at `s = 1` (denominator `−(|p|²+|k|²+|j|²) + irδ`): the weight enters only through the
  pairing.  Indeed `Re⟨z₂, m L₂ z₂⟩ = ½⟨z₂, m (L₂ + L₂*) z₂⟩` for `m = metM`
  (`conj m(−p,k) = m(p,q)`),
  which is Body 12 §6's `X1 = χ e^{irδt}(L_s + L_s*)/d₁` at `s = 2`.  The Hermitian numerator is
  the TeX's `(v−u)[l(v+u)(v²+u²) − uv(v²+uv+u²)]` (`Bounds.lean`, `num2`).
* **`cat_neutral` at `σ = 2`.**  The survey `t12_energy_derivation.md` §2.3 reports "SFF resonant
  at `σ = 2`: not neutral".  That is an artifact of the library statement: `cat_term` holds at
  every weight and only `summable_tripT` restricts `cat_neutral` to `σ ≤ 1`.  On the resonant set
  `|q| = |k|`, so the weight is symmetric; `cat_neutral_two` (`Identity.lean`) proves
  `⟨A²F, Q_res(S,F)⟩ = 0` for `S ∈ H²`, `F ∈ H³`.  This is the TeX's "the exact zero-phase energy
  vertex vanishes before division".  Hence the slow–fast term cancels exactly as at `s = 1`.
* `h2Energy = W = b_F² + ⟨z₂, X₁ z₂⟩ + 2E⁰₂`.

## The remainders
`cubicHeat2 = Re⟨R₋(AF,F) + R₋(F,AF), A²F⟩` is `E_heat` at weight two; the output heat cancels the
test derivative as at `s = 1`.

## The multiplier and the residual (`H2EnergyInterface`: `G`, `H`)
`G(u) = 3(G₀ + G₁ c_y(u)²)` with constants `G₀ = h2G0`, `G₁ = h2G1` on the piece, and
`c_y = ‖y_S‖₃` the `H³` norm of the corrected slow field `y_S = S + R_S` (`corrSlow`,
`Slow/Equation.lean`): this is how the short slow `H³` price of the TeX (eq. quant-short-slow)
enters; `H = 2 h2H1` is a constant.  Nothing of `G`, `H` depends on `CH`.

## The role thresholds (TeX Table quant-roles, Table quant-fixed; `t12_h2_scaffold.md`)
`h2Threshold θ CH₀ μ φ caps` is a sum of nonnegative terms: the floor `1`, the slow budget
`budgetPoly` and `32 c₄ y²` (roles 18–21: `∫ ‖corrRes‖₁² ≤ 4φ² + 4`, `‖R_S‖₂ ≤ 1/4`), the filter
floor `2φ` (role 23), `16 c₄ y` (the transform `c_S ≤ c_y + ρ₃ c_F`, role 19), the metric operator
(role 28) `2⁶ c_bil B_S`, the static and heat roles 16, 17, the FAR partner of role 31, the mixed
roles `Q9`, `Q10`, the metric insertions (role 28), the slow source (role 28), the short price
(role 31, high mixed), and the residual role 32 `2⁷ Hn / W_*(CH₀)`.  Caps enter through `cp`.
The dependence on the resonant constant is only through the last term, for `CH ≥ CH₀`
(`t12_h2_scaffold.md`, "Dependence on `CH`").
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.H2

/-! ### A. The weight-two forms -/

/-- `⟨z₂, X₁ z₂⟩ = 4 Re⟨A²F, X₁(S)F⟩`, the `X_{1,2}` quadratic form on `z₂ = AF` (TeX eq.
quant-metric at `s = 2`; Body 12 §6). -/
def metForm2 (r τ : ℝ) (S F : Field) : ℝ := 4 * pair 2 F (X1op r τ S F)

/-- The polarized form `⟨z_F, X₁ z_G⟩ = 2 Re⟨A²G, X₁ F⟩ + 2 Re⟨A²F, X₁ G⟩` at weight two. -/
def metBil2 (r τ : ℝ) (S F G : Field) : ℝ :=
  2 * pair 2 G (X1op r τ S F) + 2 * pair 2 F (X1op r τ S G)

lemma metForm2_eq_bil (r τ : ℝ) (S F : Field) : metForm2 r τ S F = metBil2 r τ S F F := by
  unfold metForm2 metBil2
  ring

/-- `E_heat` at weight two: `Re⟨R₋(AF,F) + R₋(F,AF), A²F⟩`, both `−AF` input slots (TeX: "`E_heat`
has both `−AF` input slots; the output heat cancels the test derivative"; "the same construction
at weight two"). -/
def cubicHeat2 (r τ : ℝ) (F : Field) : ℝ :=
  pair 2 F (Quant.corr (-1) r τ (lapF F) F) + pair 2 F (Quant.corr (-1) r τ F (lapF F))


variable {r : ℝ} {g : Field} {y : ℝ → Field}

/-! ### B. The energy along the actual solution -/

/-- `⟨z₂, X₁ z₂⟩` along the actual solution (`S = Π_S x`, `F = Π_F x`, phase `τ = r t`). -/
def metricCorr2 (r : ℝ) (g : Field) (y : ℝ → Field) (t : ℝ) : ℝ :=
  metForm2 r (r * t) (PiS (actual r g y t)) (PiF (actual r g y t))

/-- `E⁰₂ = Re⟨R₋(F,F), A²F⟩` along the actual solution. -/
def cubicCorr2 (r : ℝ) (g : Field) (y : ℝ → Field) (t : ℝ) : ℝ :=
  cubicE 2 (-1) r (r * t) (PiF (actual r g y t))

/-- **The corrected `H²` energy** `W = 2(e₂(M₂) + E⁰₂) = b_F² + ⟨z₂, X₁ z₂⟩ + 2E⁰₂` (TeX; fixed
force reading `M₂ = X_{1,2}`). -/
def h2Energy (r : ℝ) (g : Field) (y : ℝ → Field) (t : ℝ) : ℝ :=
  fastNorm 2 r g y t ^ 2 + metricCorr2 r g y t + 2 * cubicCorr2 r g y t

/-! ### C. Constants -/

/-- The constant of the polarized `X₁` bound at weight two (Body 12 §6 eq. (12), `2⁹`; the
termwise proof of `Bounds.lean` gives `152 c₄`, with `8` helicity patterns paid by absolute
values instead of the paired Schur lemma). -/
def cBil : ℝ := 2 ^ 8 * c4

/-- The constant of the genuine `H¹`-direction form at weight two (Body 12 §6 eq. (14), `2¹¹`
for the form, `2⁹` for the pairing; termwise `76 c₄`). -/
def cSrc : ℝ := 2 ^ 7 * c4

/-- The FAR constant `|D₂^B(F; h)| ≤ (c_far/q) ‖h‖₂ b_F c_F` (M4 and `|corrSym| ≤ 1/q` on the far
set; the cyclic cancellation is not needed at `H²`). -/
def cFar : ℝ := 2 ^ 6 * c4

/-- The static allowance `|E⁰₂| ≤ cStat2 (P(q) + q^{−1/2}) b_F³` (role 16). -/
def cStat2 : ℝ := 2 ^ 10 * (1 + c4)

/-- The heat allowance `|E₂_heat| ≤ cHeat2 (P(q) + q^{−1/2}) b_F c_F²` (role 17). -/
def cHeat2 : ℝ := 2 ^ 12 * (1 + c4)

/-- The product-leaf constant `‖Π_F Q_τ(F,F)‖₂ ≤ c_Q √(ab) c` (`hnorm_two_Qphase_le`). -/
def cQ2 : ℝ := 32 * Real.sqrt 5488

/-- **The role-31 normalization** `K₂ = 64 C₀ (c_Q + 16 c_I)`: `K₂ √P_F y^{3/2} N(q) ≤ 1` pays the
leading fast–fast near term and the leading part of the high mixed term (through the transform
`c_S ≤ c_y + ρ₃ c_F`, `ρ₃ ≤ 1`) with one `1/64` share.  An absolute constant, independent of
`CH`. -/
def h2K₂ : ℝ := 64 * nearC₀ * (cQ2 + 16 * cI)

/-- The profile constant of the native coefficient `M = C₀ N(q) + c_far/q ≤ Mc q^{−49/100}`. -/
def h2Mc : ℝ := nearC₀ * profC + cFar

/-- The clip mass `m₀ = 1/4` (absolute). -/
def h2m₀ : ℝ := 1 / 4

/-! ### D. Cap polynomials -/

/-- `𝒜(y) ≤ W_S + c₄ y + c₄` once `‖ψ‖₂ ≤ 1`. -/
def wyCap (caps : Caps) : ℝ := cp caps.WS + c4 * cp caps.yF + c4

/-- `√P_F y^{3/2}`, the leading coefficient at the caps. -/
def h2Lead (caps : Caps) : ℝ := Real.sqrt (cp caps.PF) * cp caps.yF ^ (3 / 2 : ℝ)

/-- `√(P_F y)`. -/
def h2Root (caps : Caps) : ℝ := Real.sqrt (cp caps.PF * cp caps.yF)

/-- `Λ̄₀ = 32 φ (c₄ + 2 𝒜(y)-cap)`, the zeroth-order part of `‖fastNL‖₂` (the filter, with
`‖ψ‖₃ ≤ 4φ`). -/
def h2L0 (φ : ℝ) (caps : Caps) : ℝ := 32 * φ * (c4 + 2 * wyCap caps)

/-- `Λ̄_c = (c_Q + 16 c_I) √(P_F y) + 16 W_S + 32 c₄`, the coefficient of `c_F` in `‖fastNL‖₂`. -/
def h2Lc (caps : Caps) : ℝ := (cQ2 + 16 * cI) * h2Root caps + 16 * cp caps.WS + 32 * c4

/-- `Λ̄_y = 16 c_I √(P_F y) + 16 c₄`, the coefficient of `c_y` in `‖fastNL‖₂`. -/
def h2Ly (caps : Caps) : ℝ := 16 * cI * h2Root caps + 16 * c4

/-- The parameter `A₃ = a_h-cap + μ^{3/2}` of the slow `H³` price: `Bh⁴Aζ²/A₃⁴` is then of degree
`6` and `A₃² ∫ b_ζ²` of degree `7` (TeX eq. quant-short-slow with the actual `L²_t H²` budget). -/
def h2A3 (μ : ℝ) (caps : Caps) : ℝ := cp caps.AH + 1 + μ ^ (3 / 2 : ℝ)

/-- **The slow `H³` price on a piece of length `≤ 2`**: `∫ₛᵗ ‖y_S‖₃² ≤ h2Price` (TeX eq.
quant-short-slow; `corr_horiz_h2_law`, `corr_vert_h2_law` of `Slow/Barrier.lean`). -/
def h2Price (μ φ : ℝ) (caps : Caps) : ℝ :=
  (cp caps.BH + 1) ^ 2 + 900 * (cp caps.AH + 1) ^ 2 * (cp caps.BH + 1) ^ 2 +
    (cp caps.BS + 1) ^ 2 + 226 * h2A3 μ caps ^ 2 * (2 * cp caps.JS + 1) +
    26 * (cp caps.BH + 1) ^ 4 * (cp caps.AS + 1) ^ 2 / h2A3 μ caps ^ 4 +
    6 * (4 * φ ^ 2 + 4)

/-- The numerator `H_n` of the residual: `H' ≤ H_n/q`
(`16 h₁² + κ Λ̄_y/2 + κ Λ̄₀/2`, `h₁ = 32(1+c₄) φ (B_S+y+W_S+1)/q`, `κ = c_bil B_S/q`). -/
def h2Hn (φ : ℝ) (caps : Caps) : ℝ :=
  16 * (32 * (1 + c4) * φ * (cp caps.BS + cp caps.yF + cp caps.WS + 1)) ^ 2 +
    cBil * cp caps.BS * (h2Ly caps + h2L0 φ caps)

/-! ### E. The role thresholds -/

/-- Role 16 (static coercivity `|2E⁰₂| ≤ b_F²/64`). -/
def role16 (caps : Caps) : ℝ :=
  (2 ^ 8 * cStat2 * profC * cp caps.yF) ^ (100 / 29 : ℝ) + (2 ^ 8 * cStat2 * cp caps.yF) ^ 2

/-- Role 17 (both input heats, `|E₂_heat| ≤ c_F²/64`). -/
def role17 (caps : Caps) : ℝ :=
  (2 ^ 8 * cHeat2 * profC * cp caps.yF) ^ (100 / 29 : ℝ) + (2 ^ 8 * cHeat2 * cp caps.yF) ^ 2

/-- Role 31, FAR partner of the leading term: `(c_Q + 16 c_I) (c_far/q) √P_F y^{3/2} ≤ 2⁻¹⁰`. -/
def role31far (caps : Caps) : ℝ := 2 ^ 10 * (cQ2 + 16 * cI) * cFar * h2Lead caps

/-- Role 31, low mixed partner: `M y (16 W_S + 32 c₄) ≤ 1/64` through `M ≤ Mc q^{−49/100}`
(Table quant-fixed "Low mixed `H²`", with `W_S` in place of `M_∞`). -/
def role31mix (caps : Caps) : ℝ :=
  (2 ^ 6 * h2Mc * (cp caps.yF * (16 * cp caps.WS + 32 * c4))) ^ (100 / 49 : ℝ)

/-- Role 31, the filter direction: `M Λ̄₀ ≤ 1/2⁶`. -/
def role31psi (φ : ℝ) (caps : Caps) : ℝ := (2 ^ 6 * h2Mc * h2L0 φ caps) ^ (100 / 49 : ℝ)

/-- Role 31, the short slow price (Table quant-fixed "Independent short mixed reserve"):
`M Λ̄_y √P_y ≤ 1/2⁶`. -/
def role31price (μ φ : ℝ) (caps : Caps) : ℝ :=
  (2 ^ 6 * h2Mc * (h2Ly caps * Real.sqrt (h2Price μ φ caps))) ^ (100 / 49 : ℝ)

/-- Role 28, metric: operator and the three insertions of `fastNL` in `X₁`. -/
def role28 (μ φ : ℝ) (caps : Caps) : ℝ :=
  2 ^ 6 * cBil * cp caps.BS * (1 + h2Lc caps) + 2 ^ 8 * cBil * cp caps.BS * h2L0 φ caps +
    2 ^ 8 * cBil * cp caps.BS * (h2Ly caps * h2Price μ φ caps)

/-- Role 28, slow source into `X₁`: `2⁷ c_src hSrc ≤ q`. -/
def role28src2 (φ : ℝ) (caps : Caps) : ℝ := 2 ^ 7 * cSrc * hSrc φ caps

/-- Role 32, the residual: `H_n/q ≤ W_*/128`, at the lower bound `CH₀` of the resonant constant. -/
def role32 (θ CH₀ μ φ : ℝ) (caps : Caps) : ℝ :=
  128 * h2Hn φ caps / WStar 1 caps.PF (resCoeff θ CH₀ μ φ caps)

/-- **The `H²` role threshold** `q₂(θ, CH₀, μ, φ, caps)` (roles 16, 17, 28, 32 and the non-leading
partners of 31, with the slow budget roles 18–21 needed for the short price).  It depends on the
resonant constant only through `role32`, at a lower bound `CH₀ ≤ CH`. -/
def h2Threshold (θ CH₀ μ φ : ℝ) (caps : Caps) : ℝ :=
  1 + budgetPoly φ caps + 32 * c4 * cp caps.yF ^ 2 + 2 * φ + 16 * c4 * cp caps.yF +
    role16 caps + role17 caps + role31far caps + role31mix caps + role31psi φ caps +
    role31price μ φ caps + role28 μ φ caps + role28src2 φ caps + role32 θ CH₀ μ φ caps

/-! ### F. The multiplier and the residual -/

/-- `G₀ = 16 (M Λ̄₀)² + 16 (κ Λ̄_c)² + κ Λ̄₀/2 + 64 (c_src hSrc/q)²` with `M = C₀ N(q) + c_far/q`
and `κ = c_bil B_S/q` (`nM`, `kap`). -/
def nM (r : ℝ) : ℝ := nearC₀ * nearN |r| + cFar / |r|

/-- `κ = c_bil B_S/q`. -/
def kap (caps : Caps) (r : ℝ) : ℝ := cBil * cp caps.BS / |r|

/-- The constant part `G₀'` of the multiplier. -/
def h2G0 (φ : ℝ) (caps : Caps) (r : ℝ) : ℝ :=
  16 * (nM r * h2L0 φ caps) ^ 2 + 16 * (kap caps r * h2Lc caps) ^ 2 +
    kap caps r * h2L0 φ caps / 2 + 64 * (cSrc * hSrc φ caps / |r|) ^ 2

/-- The coefficient `G₁'` of `c_y²` in the multiplier. -/
def h2G1 (caps : Caps) (r : ℝ) : ℝ :=
  16 * (nM r * h2Ly caps) ^ 2 + kap caps r * h2Ly caps / 2

/-- The bound `h₁ = 32(1+c₄) φ (B_S+y+W_S+1)/q` of `‖H_ψ‖₁` on the piece. -/
def hPsiC (φ : ℝ) (caps : Caps) (r : ℝ) : ℝ :=
  32 * (1 + c4) * φ * (cp caps.BS + cp caps.yF + cp caps.WS + 1) / |r|

/-- The residual `H'`. -/
def h2H1 (φ : ℝ) (caps : Caps) (r : ℝ) : ℝ :=
  16 * hPsiC φ caps r ^ 2 + kap caps r * h2Ly caps / 2 + kap caps r * h2L0 φ caps / 2

/-- **The multiplier** `G(u) = 3 (G₀' + G₁' c_y(u)²)` of `W' ≤ … + G W + H`. -/
def h2G (φ : ℝ) (caps : Caps) (r : ℝ) (g : Field) (y : ℝ → Field) (u : ℝ) : ℝ :=
  3 * (h2G0 φ caps r + h2G1 caps r * hnorm 3 (corrSlow r g y u) ^ 2)

/-- **The residual** `H(u) = 2 H'` (a constant on the piece). -/
def h2H (φ : ℝ) (caps : Caps) (r : ℝ) : ℝ := 2 * h2H1 φ caps r

/-! ### G. Elementary facts -/

lemma c4_nonneg' : 0 ≤ c4 := c4_pos.le

lemma cBil_nonneg : 0 ≤ cBil := by have := c4_pos; unfold cBil; positivity

lemma cSrc_nonneg : 0 ≤ cSrc := by have := c4_pos; unfold cSrc; positivity

lemma cFar_nonneg : 0 ≤ cFar := by have := c4_pos; unfold cFar; positivity

lemma cStat2_pos : 0 < cStat2 := by have := c4_pos; unfold cStat2; positivity

lemma cHeat2_pos : 0 < cHeat2 := by have := c4_pos; unfold cHeat2; positivity

lemma cQ2_nonneg : 0 ≤ cQ2 := by unfold cQ2; positivity

lemma h2K₂_nonneg : 0 ≤ h2K₂ := by
  have := cQ2_nonneg
  have := cI_pos
  have := nearC₀_pos
  unfold h2K₂
  positivity

lemma h2Mc_nonneg : 0 ≤ h2Mc := by
  have := profC_pos
  have := cFar_nonneg
  have := nearC₀_pos
  unfold h2Mc
  positivity

lemma wyCap_nonneg (caps : Caps) : 0 ≤ wyCap caps := by
  have := cp_nonneg caps.WS
  have := cp_nonneg caps.yF
  have := c4_pos
  unfold wyCap
  positivity

lemma h2Root_nonneg (caps : Caps) : 0 ≤ h2Root caps := Real.sqrt_nonneg _

lemma h2Lead_nonneg (caps : Caps) : 0 ≤ h2Lead caps := by
  have := cp_nonneg caps.yF
  unfold h2Lead
  positivity

lemma h2L0_nonneg {φ : ℝ} (hφ : 0 ≤ φ) (caps : Caps) : 0 ≤ h2L0 φ caps := by
  have := wyCap_nonneg caps
  have := c4_pos
  unfold h2L0
  positivity

lemma h2Lc_nonneg (caps : Caps) : 0 ≤ h2Lc caps := by
  have := h2Root_nonneg caps
  have := cQ2_nonneg
  have := cI_pos
  have := cp_nonneg caps.WS
  have := c4_pos
  unfold h2Lc
  positivity

lemma h2Ly_nonneg (caps : Caps) : 0 ≤ h2Ly caps := by
  have := h2Root_nonneg caps
  have := cI_pos
  have := c4_pos
  unfold h2Ly
  positivity

lemma h2A3_pos {μ : ℝ} (hμ : 0 ≤ μ) (caps : Caps) : 0 < h2A3 μ caps := by
  have := cp_nonneg caps.AH
  have := Real.rpow_nonneg hμ (3 / 2 : ℝ)
  unfold h2A3
  linarith

lemma h2Price_nonneg {μ φ : ℝ} (hμ : 0 ≤ μ) (caps : Caps) : 0 ≤ h2Price μ φ caps := by
  have := cp_nonneg caps.JS
  have := cp_nonneg caps.AH
  have := cp_nonneg caps.BH
  have := cp_nonneg caps.AS
  have := cp_nonneg caps.BS
  have := h2A3_pos hμ caps
  unfold h2Price
  positivity

lemma h2Hn_nonneg {φ : ℝ} (hφ : 0 ≤ φ) (caps : Caps) : 0 ≤ h2Hn φ caps := by
  have := h2Ly_nonneg caps
  have := h2L0_nonneg hφ caps
  have := cp_nonneg caps.BS
  have := cBil_nonneg
  unfold h2Hn
  positivity

lemma nM_nonneg (r : ℝ) : 0 ≤ nM r := by
  have := nearC₀_pos
  have := nearN_nonneg |r|
  have := cFar_nonneg
  unfold nM
  positivity

lemma kap_nonneg (caps : Caps) (r : ℝ) : 0 ≤ kap caps r := by
  have := cBil_nonneg
  have := cp_nonneg caps.BS
  unfold kap
  positivity

lemma h2G0_nonneg {φ : ℝ} (hφ : 0 ≤ φ) (caps : Caps) (r : ℝ) : 0 ≤ h2G0 φ caps r := by
  have := kap_nonneg caps r
  have := h2L0_nonneg hφ caps
  unfold h2G0
  positivity

lemma h2G1_nonneg (caps : Caps) (r : ℝ) : 0 ≤ h2G1 caps r := by
  have := kap_nonneg caps r
  have := h2Ly_nonneg caps
  unfold h2G1
  positivity

lemma h2H1_nonneg {φ : ℝ} (hφ : 0 ≤ φ) (caps : Caps) (r : ℝ) : 0 ≤ h2H1 φ caps r := by
  have := kap_nonneg caps r
  have := h2Ly_nonneg caps
  have := h2L0_nonneg hφ caps
  unfold h2H1
  positivity


end OVNS.Quant.H2

end
