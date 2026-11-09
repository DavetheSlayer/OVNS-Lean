import OddViscousNS.Quant.Joint.Interfaces
import OddViscousNS.Quant.Energy.H2.Bounds
import OddViscousNS.Quant.Energy.Slow.Lattice2D

/-!
# Theorem 1.2, joint large force: the signed metric objects (step J5, pilot)

The signed metric `M_s = X_{1,s} + X_{2,s} + Z_s` of TeX eq. quant-metric, at the weights
`s = 1, 2`, as **block operators on the fast Fourier lattice**, and the slow splitting at a height
`D`.  In `H1/Defs.lean` and `H2/Defs.lean` the metric is `X₁` alone, with `X₂`, `Z` as reference
heat integrals; at the joint scale the `X₂` and `Z` terms carry the `R³` (survey §3.3), so they have
to be actual objects.  Sources: Body 12 §§6–8 (`X₁`, `X₂`, `Z`, the exact coefficient identity),
LOCAL83
(`validation_forced85_full88/fresh_gate85_signed88_20261103A/INDEPENDENT_LOCAL83_GATE_001.md`: the
homological identity and the group `T`), LOCAL95
(`checkpoints/FULL_GROUP_PREFACTOR_95_CANDIDATE.md`,
`forced_group_reprice_v96/fresh_gate95_author96_20261103A/INDEPENDENT_LOCAL95_FULL_PROOF_001.md`:
the four fast labels).  Paths are relative to `upstream/bodies_v7/joint/`.

## Design
* **All fields are read in the energy coordinates** `z = A^{s/2} F`.  A block `O k j : V3 →L[ℂ] V3`
  acts on `z_j`, and `⟨G, O F⟩ = ∑_{k,j} ⟨G_k, O k j F_j⟩`.  So the weights `(K/J)^s` of the sources
  are in the blocks, exactly as `𝓛_s = A^{s/2} 𝓛 A^{−s/2}` of Body 12.
* **A slow leaf is a vector.**  `blk m p k j v` is the edge `j → k` of `Q^♯_m(v, ·)` through the
  slow mode `p` (`p + j = k`, not enforced), so
  `Qm m f g k = ∑'_p blk m p k (k − p) (f p) (g (k − p))` (`Qm_eq_tsum_blk`).  Modes are explicit,
  so nothing depends on a normal form of `l − (l − a)`.
* **The reverse edge uses `conj v`.**  For real `S`, `S_{−p} = conj S_p`, so the two exterior edges
  of `X₁` and the adjoint `𝓛*` have one slow datum `v = S_p` (`Field` reality is not a hypothesis of
  any block bound).  This is the source's "the conjugate slow coefficient in `L*` has magnitude
  `f_a` by reality" (LOCAL95 §2).  On a real `S` the blocks are literally `L + L*`.
* **The outer denominator is explicit.**  `X₂` and `Z` are defined by their coefficient, `outerInv`:
  channel by channel in the exterior helicities `c, e`, by `1/(−Σ + irδ_lj)`, with
  `δ_lj = λ_e(j) − λ_c(l)` (Body 12 §7: "the negative integral is the actual outer
  `1/[−Sigma + ir delta_lj]`").  This is the object all of J5 prices (`|d₂| ≥ q|n|F₀/2`, Bodies
  33, 42).  The heat-integral form is the scalar identity `outer_heat_integral`, the inverse
  property is `outerInv_inverse`: this is the check of the definition.
* **Masks are scalars.**  The forms `X2Form`, `ZForm`, `YLForm` carry a multiplier `μ` of the
  leaves: Body 42: "multiplying only by a scalar between zero and one".  The high-ancestor sector is
  `hiMask₃`, `hiMask₂`; `μ = 1` is the whole form.

## The reference definitions of `H1/Defs.lean`
`X2form` is **half** of `⟨z₁, X₂ z₁⟩`, contrary to its docstring: `X1bil S F G` is `⟨z_F, X₁ z_G⟩`,
so `X1bil S_u F_u (𝓛 F_u) = Re⟨z_u, X₁ 𝓛₁ z_u⟩ = ½⟨z_u, (X₁𝓛₁ + 𝓛₁*X₁) z_u⟩`, whereas Body 12 §7 has
`X₂ = −∫ E_u [X₁𝓛 + 𝓛*X₁] E_u du`.  It is not used anywhere, so nothing is affected.  The objects
below follow Body 12.

## Status
Definitions, with the two scalar checks at the end of this file.  Layout of the directory:
* `Positive.lean`: the seven and thirteen convolution classes, multilinear in the leaves;
* `Block.lean`: the block bounds at weight two: `𝓛`, `X₁`, both rootings, `Z`, the cubic kernel;
* `Product.lean`: `‖B(S,S)‖₁ ≲ M_∞ b` (Body 30);
* `HighAncestor.lean`: rows 2, 3: the three fixed-time estimates, the tails, `row23_piece`;
* `Whole.lean`: the whole forms (NEW378, LOCAL577) and the links to `Qm`, `tripT`, `Lop`, `Bslow`;
* `Phase.lean`: filter covariance, the homological identities, the heat formula of `X₂`.
-/

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

/-! ### A. The slow splitting at height `D` -/

open Classical in
/-- `P_{>D} u`, the part of `u` at `|p| > D` (LOCAL440: "`b_> = ‖P_{|p|>R} S‖₂`"). -/
def hiP (D : ℝ) (u : Field) : Field := fun k => if D < absk k then u k else 0

open Classical in
/-- `P_{≤D} u`, the complementary part. -/
def loP (D : ℝ) (u : Field) : Field := fun k => if D < absk k then 0 else u k

/-- `W_> = ‖1_{|p|>D} û‖_{ℓ¹}` (LOCAL440, LOCAL441). -/
def tailW (D : ℝ) (u : Field) : ℝ := wiener (hiP D u)

/-- `b_> = ‖P_{>D} u‖₂` (LOCAL440, LOCAL441). -/
def tailB (D : ℝ) (u : Field) : ℝ := hnorm 2 (hiP D u)

lemma loP_add_hiP (D : ℝ) (u : Field) : loP D u + hiP D u = u := by
  funext k
  simp only [Pi.add_apply, loP, hiP]
  split_ifs <;> simp

/-! ### B. The helical block of a triad multiplier -/

/-- `hel a k` as an operator. -/
def helL (a : Sgn) (k : Mode) : V3 →L[ℂ] V3 :=
  LinearMap.toContinuousLinearMap
    { toFun := hel a k, map_add' := hel_add a k, map_smul' := fun c v => hel_smul a k c v }

@[simp] lemma helL_apply (a : Sgn) (k : Mode) (v : V3) : helL a k v = hel a k v := rfl

private lemma vert_add_right' (p q : Mode) (A B B' : V3) :
    vert p q A (B + B') = vert p q A B + vert p q A B' := by
  simp only [vert, dotM_add, mul_add, add_smul, smul_add, leray_add]
  abel

private lemma vert_smul_right' (p q : Mode) (c : ℂ) (A B : V3) :
    vert p q A (c • B) = c • vert p q A B := by
  have h : (Complex.I * dotM A q) • (c • B) + (Complex.I * dotM (c • B) p) • A =
      c • ((Complex.I * dotM A q) • B + (Complex.I * dotM B p) • A) := by
    rw [dotM_smul]
    module
  rw [vert, vert, h, leray_smul, smul_comm]

/-- The vertex with its first input frozen, as an operator. -/
def vertR (p q : Mode) (A : V3) : V3 →L[ℂ] V3 :=
  LinearMap.toContinuousLinearMap
    { toFun := vert p q A
      map_add' := vert_add_right' p q A
      map_smul' := fun c B => vert_smul_right' p q c A B }

@[simp] lemma vertR_apply (p q : Mode) (A B : V3) : vertR p q A B = vert p q A B := rfl

/-- The edge `j → k` of `Q^♯_m(v, ·)` through the slow mode `p`, `p + j = k`:
`w ↦ ∑_{abc} m^{abc}(p, j) H_c(k) vert(p, j; H_a(p) v, H_b(j) w)`, the summand of `Qm`. -/
def blk (m : Mult) (p k j : Mode) (v : V3) : V3 →L[ℂ] V3 :=
  ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, m a b c p j • (helL c k ∘L vertR p j (hel a p v) ∘L helL b j)

lemma blk_apply (m : Mult) (p k j : Mode) (v w : V3) :
    blk m p k j v w = ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn,
      m a b c p j • hel c k (vert p j (hel a p v) (hel b j w)) := by
  simp [blk]

/-- `Q^♯_m(f, g)` is the sum of its edges. -/
lemma Qm_eq_tsum_blk (m : Mult) (f g : Field) (k : Mode) :
    Qm m f g k = ∑' p, blk m p k (k - p) (f p) (g (k - p)) :=
  tsum_congr fun p => (blk_apply m p k (k - p) (f p) (g (k - p))).symm

/-! ### C. The edges of the metric at weight `s` -/

/-- The weight `(|k|/|j|)^s` of an edge `j → k` on the energy coordinates. -/
def wt (s : ℕ) (k j : Mode) : ℝ := (absk k / absk j) ^ s

/-- The edge of `𝓛_s = A^{s/2} 2Π_F Q_τ(S, ·) A^{−s/2}` through the slow vector `v` at `p`, resonant
edges included (Body 12 §6 `L_s`; `Lop` of `H1/Defs.lean` on the energy coordinates). -/
def Lb (s : ℕ) (τ : ℝ) (p k j : Mode) (v : V3) : V3 →L[ℂ] V3 :=
  ((2 * wt s k j : ℝ) : ℂ) • blk (phaseM τ) p k j v

/-- The edge of the adjoint: `(𝓛_s*)_{kj} = ((𝓛_s)_{jk})†`, whose slow leaf is at `−p`, with the
coefficient `conj v` (LOCAL95 §2). -/
def Lad (s : ℕ) (τ : ℝ) (p k j : Mode) (v : V3) : V3 →L[ℂ] V3 :=
  ContinuousLinearMap.adjoint (Lb s τ (-p) j k (conjV v))

/-- The block of `X_{1,s}` through the slow vector `v` at `p`: `L^m + (L^m)*` with the multiplier
`metM` (own denominator, own mask, own phase), that is `χ e^{irδt}[L_s + L_s*]/d₁` of Body 12 §§3,
6. On a real slow field its form is `metForm2` at `s = 2` and `X1form` at `s = 1`; see `X1Form`. -/
def X1b (s : ℕ) (r τ : ℝ) (p k j : Mode) (v : V3) : V3 →L[ℂ] V3 :=
  ((2 * wt s k j : ℝ) : ℂ) • blk (metM r τ) p k j v +
    ContinuousLinearMap.adjoint (((2 * wt s j k : ℝ) : ℂ) • blk (metM r τ) (-p) j k (conjV v))

/-! ### D. The outer inverse, `X₂` and `Z` -/

/-- The exterior phase `δ_lj = λ_e(j) − λ_c(l)` (Body 12 §7; helicity `c` at the output `l`, `e` at
the input `j`): the intermediate helicity has cancelled. -/
def outerPhi (c e : Sgn) (l j : Mode) : ℝ := lam e j - lam c l

/-- **The outer inverse**: `H⁻¹` on the block `T` from `j` to `l` with heat `H`:
`∑_{c,e} (−H + i r δ_lj)⁻¹ H_c(l) T H_e(j)`. -/
def outerInv (r H : ℝ) (l j : Mode) (T : V3 →L[ℂ] V3) : V3 →L[ℂ] V3 :=
  ∑ c : Sgn, ∑ e : Sgn,
    resolv (-1) H (r * outerPhi c e l j) • (helL c l ∘L T ∘L helL e j)

/-- The outer heat `Σ = |l|² + |j|² + |a|² + |b|²`: two exterior fast heats and two slow ancestor
heats.  "There is NEVER an added `M²`" (Body 12 §7). -/
def heat4 (l j a b : Mode) : ℝ := absSq l + absSq j + absSq a + absSq b

/-- **Both rootings** `X₁ 𝓛 + 𝓛* X₁` at the exteriors `l`, `j = l − a − b`, with the intermediate
`m = l − a`: the slow leaves are `f_a` (first edge) and `g_b` (second edge).  Each inner `X₁` keeps
its own heat, mask and phase (Body 12 §7; LOCAL95 §2 eq. (A), (B)). -/
def twoRoot (s : ℕ) (r τ : ℝ) (f g : Field) (l a b : Mode) : V3 →L[ℂ] V3 :=
  X1b s r τ a l (l - a) (f a) ∘L Lb s τ b (l - a) (l - a - b) (g b) +
    Lad s τ a l (l - a) (f a) ∘L X1b s r τ b (l - a) (l - a - b) (g b)

/-- **The block of `X_{2,s}`**, bilinear in the slow data `(f, g)`: `X₂ = H₂⁻¹(X₁𝓛 + 𝓛*X₁)` (Body 12
§7, LOCAL83).  On the diagonal `f = g = S` this is the coefficient of
`−∫₀^∞ E_u [X₁(t+u; S_u) 𝓛(t+u; S_u) + 𝓛*X₁] E_u du` (`outer_heat_integral`). -/
def X2b (s : ℕ) (r τ : ℝ) (f g : Field) (l a b : Mode) : V3 →L[ℂ] V3 :=
  outerInv r (heat4 l (l - a - b) a b) l (l - a - b) (twoRoot s r τ f g l a b)

/-- The edge `(a, b) ↦ a + b` of the slow product `B_slow`: the coefficient of `Bslow`, polarized
(`Bslow_eq_tsum`). -/
def slowV (a b : Mode) (v w : V3) : V3 := blk resM a (a + b) b v w

/-- **The block of `Z_s`** at the exteriors `l`, `k = l − a − b`: the leaves `f_a`, `g_b` merge into
the slow vector `slowV a b f_a g_b` at `a + b`; the inner `X₁` keeps its **merged** heat `|a+b|²`,
the outer heat has `|a|² + |b|²` (Body 12 §8 eq. (19): "They are distinct"). -/
def Zb (s : ℕ) (r τ : ℝ) (f g : Field) (l a b : Mode) : V3 →L[ℂ] V3 :=
  outerInv r (heat4 l (l - a - b) a b) l (l - a - b)
    (X1b s r τ (a + b) l (l - a - b) (slowV a b (f a) (g b)))

/-! ### E. The forms, on the energy coordinates -/

/-- The energy coordinates `z_s = A^{s/2} F`. -/
def zOf (s : ℕ) (F : Field) : Field := fun k => ((absk k ^ s : ℝ) : ℂ) • F k

/-- The indices `(l, a, b)`: the output and the two slow leaves. -/
abbrev I3 := Mode × Mode × Mode

/-- The indices `(l, a, b, c)`: the output and the three slow leaves (LOCAL95 §2: `m = l − a`,
`k = m − b`, `j = k − c`). -/
abbrev I4 := Mode × Mode × Mode × Mode

/-- `⟨G, X₁(S) F⟩`, on the energy coordinates. -/
def X1Form (s : ℕ) (r τ : ℝ) (S G F : Field) : ℂ :=
  ∑' x : Mode × Mode, inner ℂ (G x.1) (X1b s r τ x.2 x.1 (x.1 - x.2) (S x.2) (F (x.1 - x.2)))

/-- `⟨G, μ X₂(f, g) F⟩`, with the scalar multiplier `μ` of `(l, a, b)`. -/
def X2Form (μ : I3 → ℂ) (s : ℕ) (r τ : ℝ) (f g G F : Field) : ℂ :=
  ∑' x : I3, μ x * inner ℂ (G x.1) (X2b s r τ f g x.1 x.2.1 x.2.2 (F (x.1 - x.2.1 - x.2.2)))

/-- `⟨G, μ Z(f, g) F⟩`. -/
def ZForm (μ : I3 → ℂ) (s : ℕ) (r τ : ℝ) (f g G F : Field) : ℂ :=
  ∑' x : I3, μ x * inner ℂ (G x.1) (Zb s r τ f g x.1 x.2.1 x.2.2 (F (x.1 - x.2.1 - x.2.2)))

/-- The block of `(X₂ + Z) 𝓛` at the four fast labels, on the leaves `(f, g, h)`. -/
def YLb (s : ℕ) (r τ : ℝ) (f g h : Field) (x : I4) : V3 →L[ℂ] V3 :=
  (X2b s r τ f g x.1 x.2.1 x.2.2.1 + Zb s r τ f g x.1 x.2.1 x.2.2.1) ∘L
    Lb s τ x.2.2.2 (x.1 - x.2.1 - x.2.2.1) (x.1 - x.2.1 - x.2.2.1 - x.2.2.2) (h x.2.2.2)

/-- The input label `j = l − a − b − c` of `x = (l, a, b, c)`. -/
def inJ (x : I4) : Mode := x.1 - x.2.1 - x.2.2.1 - x.2.2.2

/-- `⟨G, μ (X₂ + Z) 𝓛 F⟩`, the undifferentiated part of the cubic group: `X₂` with both rootings,
`Z`, and the last edge `𝓛` with its resonant edges.  The literal adjoints `𝓛*X₂`, `𝓛*Z` are the
conjugate form with `G, F` exchanged (`X₂`, `Z` are Hermitian), so every bound on this form pays
them: on the diagonal `⟨z, (Y𝓛 + 𝓛*Y) z⟩ = 2 Re⟨z, Y𝓛 z⟩`. -/
def YLForm (μ : I4 → ℂ) (s : ℕ) (r τ : ℝ) (f g h G F : Field) : ℂ :=
  ∑' x : I4, μ x * inner ℂ (G x.1) (YLb s r τ f g h x (F (inJ x)))

/-- `⟨G, (X₁ + X₂ + Z)(S) F⟩`: the metric `M_s` (TeX eq. quant-metric). -/
def metricForm (s : ℕ) (r τ : ℝ) (S G F : Field) : ℂ :=
  X1Form s r τ S G F + X2Form 1 s r τ S S G F + ZForm 1 s r τ S S G F

/-- `e_s = ½(‖F‖_s² + ⟨z_s, M_s z_s⟩)` (TeX; Body 12 §9; LOCAL83). -/
def metEnergy (s : ℕ) (r τ : ℝ) (S F : Field) : ℝ :=
  1 / 2 * (hnorm s F ^ 2 + (metricForm s r τ S (zOf s F) (zOf s F)).re)

/-- `⟨z, T_s z⟩`, the group `T = Y𝓛 + 𝓛*Y + D_S Y[B(S,S)]`, `Y = X₂ + Z`, all six pieces (TeX
eq. quant-metric; LOCAL83): both slow slots of `X₂` and of `Z` are differentiated, the merged leaf
`h = B(S,S)` keeps its own heat. -/
def cubicT (s : ℕ) (r τ : ℝ) (S z : Field) : ℝ :=
  2 * (YLForm 1 s r τ S S S z z).re +
    (X2Form 1 s r τ (Bslow S) S z z + X2Form 1 s r τ S (Bslow S) z z +
      ZForm 1 s r τ (Bslow S) S z z + ZForm 1 s r τ S (Bslow S) z z).re

open Classical in
/-- The high-ancestor mask of the three leaves: at least one ancestral length exceeds `D`
(LOCAL440 step 1, LOCAL441). -/
def hiMask₃ (D : ℝ) (x : I4) : ℂ :=
  if D < absk x.2.1 ∨ D < absk x.2.2.1 ∨ D < absk x.2.2.2 then 1 else 0

open Classical in
/-- The high-ancestor mask of the two leaves of `X₂`: `X_{2,hi}` of LOCAL655 (Body 41). -/
def hiMask₂ (D : ℝ) (x : I3) : ℂ := if D < absk x.2.1 ∨ D < absk x.2.2 then 1 else 0

/-- `⟨G, A^{1/2} μ X₂(f, g) F⟩`: the output half (Body 12 (17): "no `A` is commuted through `X₂`";
the derivative sits on the output label only). -/
def X2HalfForm (μ : I3 → ℂ) (s : ℕ) (r τ : ℝ) (f g G F : Field) : ℂ :=
  ∑' x : I3, μ x * ((absk x.1 : ℝ) : ℂ) *
    inner ℂ (G x.1) (X2b s r τ f g x.1 x.2.1 x.2.2 (F (x.1 - x.2.1 - x.2.2)))

/-- `⟨G, μ D_S X₂[h] F⟩`: both slots of `X₂` differentiated (Body 12 §7, LOCAL83). -/
def DSX2Form (μ : I3 → ℂ) (s : ℕ) (r τ : ℝ) (h S G F : Field) : ℂ :=
  X2Form μ s r τ h S G F + X2Form μ s r τ S h G F

open Classical in
/-- The high-intermediate sector `M > D`, `M ≥ 4 max(L, J)` of Bodies 33, 42. -/
def hiIntMask (D : ℝ) (x : I3) : ℂ :=
  if D < absk (x.1 - x.2.1) ∧ 4 * absk x.1 ≤ absk (x.1 - x.2.1) ∧
    4 * absk (x.1 - x.2.1 - x.2.2) ≤ absk (x.1 - x.2.1) then 1 else 0

/-! ### F. Checks of the definitions -/

/-- **The exact coefficient identity** (Body 12 §7: "the negative integral is the actual outer
`1/[−Sigma + ir delta_lj]`"): the heat integral of `X₂`, `Z` at one coefficient is `resolv`.  So
`outerInv` is `−∫₀^∞ E_u (·) E_u du` with the phase advanced once. -/
theorem outer_heat_integral {H : ℝ} (hH : 0 < H) (z : ℝ) :
    -∫ u in Ioi (0 : ℝ), Complex.exp (((-H : ℝ) + (z : ℝ) * Complex.I) * u) = resolv (-1) H z := by
  have hre : (((-H : ℝ) : ℂ) + (z : ℝ) * Complex.I).re < 0 := by simpa using hH
  have hne : ((-H : ℝ) : ℂ) + (z : ℝ) * Complex.I ≠ 0 := fun h0 => by
    rw [h0] at hre
    simp at hre
  rw [integral_exp_mul_complex_Ioi hre 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, resolv]
  have e : (((-1 : ℝ) * H : ℝ) : ℂ) = ((-H : ℝ) : ℂ) := by push_cast; ring
  rw [e]
  field_simp

/-- `outerInv` **is the inverse** of the outer operator `−Σ + irδ`, on the transverse part: applying
`−H + i r δ_lj` channel by channel returns `P_l T P_j`.  Together with `outer_heat_integral` this is
`H₂ X₂ = X₁𝓛 + 𝓛*X₁` and `H₂ Z = X₁(B(S,S))` at one coefficient (LOCAL83: "`H₂Y₂ − X₁L − L*X₁ −
D_SX₁[BSS] = 0` precisely with the PLUS sign in `Z`"). -/
theorem outerInv_inverse {r H : ℝ} (hH : 0 < H) (l j : Mode) (T : V3 →L[ℂ] V3) (w : V3) :
    ∑ c : Sgn, ∑ e : Sgn, ((((-H : ℝ) : ℂ) + ((r * outerPhi c e l j : ℝ) : ℂ) * Complex.I) •
        hel c l (outerInv r H l j T (hel e j w))) =
      leray l (T (leray j w)) := by
  have hne : ∀ c e, (((-H : ℝ) : ℂ) + ((r * outerPhi c e l j : ℝ) : ℂ) * Complex.I) *
      resolv (-1) H (r * outerPhi c e l j) = 1 := fun c e => by
    have h0 := resolv_den_ne_zero (Or.inr rfl) hH.ne' (r * outerPhi c e l j)
    have e1 : (((-1 : ℝ) * H : ℝ) : ℂ) = ((-H : ℝ) : ℂ) := by push_cast; ring
    rw [e1] at h0
    rw [resolv, e1]
    field_simp
  have hch : ∀ c e, hel c l (outerInv r H l j T (hel e j w)) =
      resolv (-1) H (r * outerPhi c e l j) • hel c l (T (hel e j w)) := by
    intro c e
    have hsum : ∀ (x : Sgn → V3), hel c l (∑ c', x c') = ∑ c', hel c l (x c') := fun x => by
      simp [hel_add]
    simp only [outerInv, sum_apply, smul_apply, ContinuousLinearMap.comp_apply, helL_apply]
    rw [hsum, Fintype.sum_eq_single c (fun c' hc' => ?_)]
    · rw [hsum, Fintype.sum_eq_single e (fun e' he' => ?_)]
      · rw [hel_smul, hel_idem, hel_idem]
      · rw [hel_smul, hel_idem, hel_orth he', map_zero, hel_zero_right, smul_zero]
    · rw [hsum]
      refine Finset.sum_eq_zero fun e' _ => ?_
      rw [hel_smul, hel_orth (Ne.symm hc'), smul_zero]
  have hL : ∀ v : V3, ∑ c : Sgn, hel c l v = leray l v := hel_sum l
  calc _ = ∑ c : Sgn, ∑ e : Sgn, hel c l (T (hel e j w)) := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
        rw [hch, smul_smul, hne, one_smul]
    _ = ∑ c : Sgn, hel c l (T (leray j w)) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [← hel_sum j w, map_sum]
        simp [hel_add]
    _ = leray l (T (leray j w)) := hL _

end OVNS.Quant.Metric

end
