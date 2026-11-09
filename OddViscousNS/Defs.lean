import OddViscousNS.Basic

/-!
# Proof-internal definitions

Everything is gauge-free: instead of a helical *basis* `h_a(k)` we use the helical *projectors*
`H_a(k) = ½(P_k + a i C_k/|k|)` (`hel`).  All nonlinearities are special cases of `Qm`, the triad
sum with a bounded multiplier `m` (the manuscript's `Q^♯`), and all PDE theory is done for the
*filtered* equation `y' = -A y - N t (y,y) + G t` (`IsHeatSol`), which has no skew linear term.
-/

open scoped ComplexConjugate ENNReal Topology
open MeasureTheory Set Filter

noncomputable section

namespace OVNS

/-- `f` has finite `H^s` norm and zero mean. -/
structure MZ (s : ℝ) (f : Field) : Prop where
  inH : InH s f
  mean : f 0 = 0

/-- The Wiener norm `𝒜(u) = ∑ₖ |û_k|`. -/
def wiener (u : Field) : ℝ := ∑' k, ‖u k‖

/-- Helicity signs: `true ↦ +1`, `false ↦ -1`. -/
abbrev Sgn := Bool

/-- The numeric value of a helicity sign. -/
def sg (a : Sgn) : ℝ := if a then 1 else -1

/-- The helical projector `H_a(k) = ½(P_k + a i C_k/|k|)`; zero at `k = 0`. -/
def hel (a : Sgn) (k : Mode) (v : V3) : V3 :=
  if k = 0 then 0 else
    (1 / 2 : ℂ) • (leray k v + (Complex.I * (sg a / absk k : ℝ)) • cross (modeVec k) v)

/-- The dispersion relation `λ_a(k) = a k₃ |k|`. -/
def lam (a : Sgn) (k : Mode) : ℝ := sg a * (k 2 : ℝ) * absk k

/-- The filter `R(τ)` at mode `k`: multiplies the `a`-helical part by `e^{iτλ_a(k)}`. -/
def rot (τ : ℝ) (k : Mode) (v : V3) : V3 :=
  ∑ a : Sgn, Complex.exp (Complex.I * (τ * lam a k : ℝ)) • hel a k v

/-- The filter `R(τ)` on fields. -/
def rotF (τ : ℝ) (u : Field) : Field := fun k => rot τ k (u k)

/-- The symmetric physical vertex `½ P_{p+q}[i(A·q)B + i(B·p)A]`. -/
def vert (p q : Mode) (A B : V3) : V3 :=
  (1 / 2 : ℂ) • leray (p + q) ((Complex.I * dotM A q) • B + (Complex.I * dotM B p) • A)

/-- The symmetric bilinear convection `B(f,g) = ½ℙ[(f·∇)g + (g·∇)f]`. -/
def Bsym (f g : Field) (k : Mode) : V3 := ∑' p : Mode, vert p (k - p) (f p) (g (k - p))

/-- The phase `Φ^{abc}_{pq,p+q} = λ_a(p) + λ_b(q) - λ_c(p+q)`. -/
def Phi (a b c : Sgn) (p q : Mode) : ℝ := lam a p + lam b q - lam c (p + q)

/-- Triad multipliers `m(a,b,c,p,q)`. -/
abbrev Mult := Sgn → Sgn → Sgn → Mode → Mode → ℂ

/-- A multiplier bounded by one. -/
def Mult.Bdd (m : Mult) : Prop := ∀ a b c p q, ‖m a b c p q‖ ≤ 1

/-- A multiplier respecting reality: `m(a,b,c,-p,-q) = conj m(a,b,c,p,q)`. -/
def Mult.Real (m : Mult) : Prop := ∀ a b c p q, m a b c (-p) (-q) = conj (m a b c p q)

/-- The manuscript's `Q^♯`: the helical triad sum with multiplier `m`. -/
def Qm (m : Mult) (f g : Field) (k : Mode) : V3 :=
  ∑' p : Mode, ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn,
    m a b c p (k - p) • hel c k (vert p (k - p) (hel a p (f p)) (hel b (k - p) (g (k - p))))

/-- The oscillating multiplier `e^{iτΦ}`. -/
def phaseM (τ : ℝ) : Mult := fun a b c p q => Complex.exp (Complex.I * (τ * Phi a b c p q : ℝ))

open Classical in
/-- The resonant multiplier `𝟏_{Φ=0}`. -/
def resM : Mult := fun a b c p q => if Phi a b c p q = 0 then 1 else 0

/-- `Q_τ`, the phased (filtered) convection. -/
def Qphase (τ : ℝ) : Field → Field → Field := Qm (phaseM τ)

/-- `Q_res`, the exactly resonant bilinear form. -/
def Qres : Field → Field → Field := Qm resM

open Classical in
/-- The slow projection `Π_S` (`k₃ = 0`). -/
def PiS (u : Field) : Field := fun k => if k 2 = 0 then u k else 0

open Classical in
/-- The fast projection `Π_F` (`k₃ ≠ 0`). -/
def PiF (u : Field) : Field := fun k => if k 2 = 0 then 0 else u k

open Classical in
/-- The horizontal slow part `h` of a field. -/
def PiH (u : Field) : Field :=
  fun k => if k 2 = 0 then WithLp.toLp 2 ![u k 0, u k 1, 0] else 0

open Classical in
/-- The vertical slow part `ζ` of a field. -/
def PiV (u : Field) : Field :=
  fun k => if k 2 = 0 then WithLp.toLp 2 ![0, 0, u k 2] else 0

/-- The weighted real pairing `Re⟨c, Λ^{2σ} F⟩`, `Λ = |∇|`. -/
def pair (σ : ℝ) (c F : Field) : ℝ :=
  ∑' k, sobWeight σ k * (inner ℂ (c k) (F k)).re

/-- The bilinear families the local theory runs on: bounded by the two pointwise majorants of
`Lemma fg:lem:maj`, additive, mode-wise continuous in time, preserving the admissible class. -/
structure Majorized (N : ℝ → Field → Field → Field) : Prop where
  add_left : ∀ t f f' g, MZ 2 f → MZ 2 f' → MZ 2 g → N t (f + f') g = N t f g + N t f' g
  sub_left : ∀ t f f' g, MZ 2 f → MZ 2 f' → MZ 2 g → N t (f - f') g = N t f g - N t f' g
  add_right : ∀ t f g g', MZ 2 f → MZ 2 g → MZ 2 g' → N t f (g + g') = N t f g + N t f g'
  sub_right : ∀ t f g g', MZ 2 f → MZ 2 g → MZ 2 g' → N t f (g - g') = N t f g - N t f g'
  maj₁ : ∀ t f g k, MZ 2 f → MZ 2 g →
    ‖N t f g k‖ ≤ ∑' p, (absk p + absk (k - p)) * ‖f p‖ * ‖g (k - p)‖
  maj₂ : ∀ t f g k, MZ 2 f → MZ 2 g →
    ‖N t f g k‖ ≤ 2 * absk k * ∑' p, ‖f p‖ * ‖g (k - p)‖
  real : ∀ t f g, Adm 2 f → Adm 2 g → IsReal (N t f g)
  sol : ∀ t f g, MZ 2 f → MZ 2 g → IsSolenoidal (N t f g)
  mean : ∀ t f g, MZ 2 f → MZ 2 g → N t f g 0 = 0
  cont : ∀ f g k, MZ 2 f → MZ 2 g → Continuous fun t => N t f g k

/-- Forces `G` for the local theory: `H¹`-valued, bounded by `Γ`, norm-continuous. -/
structure GoodForce (G : ℝ → Field) (Γ : ℝ) : Prop where
  adm : ∀ t, Adm 1 (G t)
  bd : ∀ t, hnorm 1 (G t) ≤ Γ
  cont : ∀ t₀, Tendsto (fun t => hnorm 1 (G t - G t₀)) (𝓝 t₀) (𝓝 0)

/-- `y ∈ C([0,T); H²_sol)` solves `y' = -A y - N t (y,y) + G t` mode by mode. -/
structure IsHeatSol (N : ℝ → Field → Field → Field) (G : ℝ → Field) (T : ℝ≥0∞)
    (y : ℝ → Field) : Prop where
  adm : ∀ t, 0 ≤ t → ENNReal.ofReal t < T → Adm 2 (y t)
  cont : ∀ t₀, 0 ≤ t₀ → ENNReal.ofReal t₀ < T →
    Tendsto (fun t => hnorm 2 (y t - y t₀)) (𝓝[Ici 0] t₀) (𝓝 0)
  mode : ∀ k t, 0 ≤ t → ENNReal.ofReal t < T → HasDerivWithinAt (fun s => y s k)
    ((-(absSq k : ℝ) : ℂ) • y t k - N t (y t) (y t) k + G t k) (Ici 0) t

/-- The filtered original nonlinearity, started at absolute time `t₀`. -/
def filtN (r t₀ : ℝ) : ℝ → Field → Field → Field := fun t => Qphase (r * (t + t₀))

/-- The filtered force `R(-r(t+t₀)) g`. -/
def filtG (r t₀ : ℝ) (g : Field) : ℝ → Field := fun t => rotF (-(r * (t + t₀))) g

/-- A reference solution: `w' = -A w - Q_res(w,w) + Π_S g`. -/
abbrev RefSol (g : Field) (T : ℝ≥0∞) (w : ℝ → Field) : Prop :=
  IsHeatSol (fun _ => Qres) (fun _ => PiS g) T w

end OVNS
