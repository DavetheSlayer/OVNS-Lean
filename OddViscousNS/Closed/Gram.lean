import OddViscousNS.Closed.Metric
import OddViscousNS.Filtered

/-!
# The cubic `⟨B(w,w), h(A)w⟩`, its triad form, and the row-operator hypothesis

Gauge-free objects of the proof of Lemma `weighted-cubic` (bounded.tex), following the
reconstruction in `OddViscousNS_data/reports/uf661_row_operator.md`:

* `curlS j v = i j × v` (the curl symbol `S_j`, eigenvalues `±|j|` on `j^⊥`);
* `triT p l q (a,b,c) = d₁ det(S_p a, b, c) + d₂ det(a, S_l b, c) + d₃ det(a, b, S_q c)` with the
  metric differences `d₁ = h_q − h_l`, `d₂ = h_p − h_q`, `d₃ = h_l − h_p`;
* the cyclic weights `Wk ω k p = 3ω(A_k)/(ω(A_p)+ω(A_l)+ω(A_k))` with `ω = lamW`;
* the pair Gram form `gramQ p l k c`, the closed form of `c* V V* c` for the bilinear map
  `V_{k,p}(f,g)·c = triT p l (-k) f g c / 6`;
* `RowBound g`: the finite-computation hypothesis of Theorem 1.3 — for every output `k ≠ 0` the
  row operator `G_k = ∑_p W² G(k,p)` has largest eigenvalue at most `g(|k|²)`.  This is exactly
  the proposition the UF661 Gram certificates (plus their analytic tails) establish numerically.
-/

open scoped ENNReal ComplexConjugate
open MeasureTheory Set

noncomputable section

namespace OVNS

/-- The bilinear (conjugation-free) dot product on `ℂ³`. -/
def dotV (a b : V3) : ℂ := ∑ i, a i * b i

/-- `det(a,b,c) = (a × b)·c`. -/
def det3 (a b c : V3) : ℂ := dotV (cross a b) c

/-- The curl symbol `S_j v = i j × v`. -/
def curlS (j : Mode) (v : V3) : V3 := Complex.I • cross (modeVec j) v

/-- `h(|j|²)`. -/
def hm (j : Mode) : ℝ := hmet (nsq j)

/-- The symmetrized triad form `T(p,l,q)(a,b,c)`. -/
def triT (p l q : Mode) (a b c : V3) : ℂ :=
  ((hm q - hm l : ℝ) : ℂ) * det3 (curlS p a) b c + ((hm p - hm q : ℝ) : ℂ) * det3 a (curlS l b) c
    + ((hm l - hm p : ℝ) : ℂ) * det3 a b (curlS q c)

/-- The cyclic-weight table `λ` (values `/10⁵` on the bands ending at the listed edges; `1`
above `120`). -/
def lamEdges : List ℕ := [1, 2, 3, 4, 5, 6, 8, 10, 12, 14, 16, 18, 20, 23, 26, 29, 32, 36, 42, 50, 64, 90, 120]

def lamVals : List ℕ :=
  [96598, 87296, 87810, 90647, 83652, 84516, 83271, 83833, 83500, 83045, 83423, 82208, 81819,
   81397, 80467, 79629, 78642, 78984, 80302, 81387, 83141, 86345, 93256, 100000]

/-- `λ(j)`: the value of the first band whose edge is `≥ j`; `1` for `j > 120`. -/
def lamW (j : ℕ) : ℝ :=
  match lamEdges.findIdx? (fun e => j ≤ e) with
  | some i => (lamVals.getD i 100000 : ℝ) / 100000
  | none => 1

/-- The cyclic weight on the output slot, `W_k(p) = 3λ(A_k)/(λ(A_p)+λ(A_l)+λ(A_k))`, `l = k − p`. -/
def Wk (ω : ℕ → ℝ) (k p : Mode) : ℝ :=
  3 * ω (nsq k) / (ω (nsq p) + ω (nsq (k - p)) + ω (nsq k))

/-- The pair Gram form: with `l = k − p`, `d₁ = h_k − h_l`, `d₂ = h_p − h_k`, `d₃ = h_l − h_p`,
`L* = A_p d₁ + A_l d₂ + A_k d₃`, `E = p × k`, `N = k × E`,
`gramQ = [(A_l A_k d₁² + A_p A_k d₂²)|E·c|² + (L*² + A_p A_l d₃²)|N·c|²/A_k] / (A_p A_l A_k)`;
zero if a mode vanishes.  It equals `c* V V* c` for `V = V_{k,p}` (Lemma `pair Gram`). -/
def gramQ (p l k : Mode) (c : V3) : ℝ :=
  if p = 0 ∨ l = 0 ∨ k = 0 then 0 else
    let Ap := absSq p
    let Al := absSq l
    let Ak := absSq k
    let d₁ := hm k - hm l
    let d₂ := hm p - hm k
    let d₃ := hm l - hm p
    let Ls := Ap * d₁ + Al * d₂ + Ak * d₃
    let E := cross (modeVec p) (modeVec k)
    let N := cross (modeVec k) E
    ((Al * Ak * d₁ ^ 2 + Ap * Ak * d₂ ^ 2) * ‖dotV E c‖ ^ 2
      + (Ls ^ 2 + Ap * Al * d₃ ^ 2) * ‖dotV N c‖ ^ 2 / Ak) / (Ap * Al * Ak)

/-- The row quadratic form at output `k`, summed in `[0,∞]`.  `gramQ` is the Gram of `T`, not of
`V = T/6` (`triT_sq_le`, and `c*VV*c = gramQ/36` in `PairGram`), so this is
`36 · h_k · c* G_k c = 36 ∑_p W² c*VV*c/(A_p h_p A_l h_l)` with UF661's `G_k`. -/
def rowQ (k : Mode) (c : V3) : ℝ≥0∞ :=
  ∑' p : Mode, ENNReal.ofReal (Wk lamW k p ^ 2 * gramQ p (k - p) k c /
    (absSq p * hm p * absSq (k - p) * hm (k - p)))

/-- **The finite-computation hypothesis of Theorem 1.3.** For every output `k ≠ 0` and every
`c ⊥ k`, `h_k · c* G_k c ≤ g(|k|²) · h_k ‖c‖²`, i.e. `λ_max(G_k) ≤ g(|k|²)`, with UF661's `G_k`.
Since `rowQ k c = 36 h_k c* G_k c`, the factor `36` is on the right.  Without it the statement is
false: at `k = (1,1,0)`, `c = e₃` the single term `p = (1,0,0)` already gives `.5645 > M₀ h_k`. -/
def RowBound (g : ℕ → ℝ) : Prop :=
  ∀ k : Mode, k ≠ 0 → ∀ c : V3, dotM c k = 0 →
    rowQ k c ≤ ENNReal.ofReal (36 * g (nsq k) * hm k * ‖c‖ ^ 2)

/-- The worst full row square `M₀ = .185955292`. -/
def M₀ : ℝ := 185955292 / 1000000000

/-- `F* = F₀ − J₀ d₀ = 151004149/162240000`, the two-band affinity bound. -/
def Fstar : ℝ := 151004149 / 162240000

/-- `κ₀ = 208013/500000`. -/
def κ₀ : ℝ := 208013 / 500000

theorem M₀_mul_Fstar_lt : M₀ * Fstar < κ₀ ^ 2 := by
  norm_num [M₀, Fstar, κ₀]

/-- The cubic `⟨B(w,w), h(A)w⟩ = ∑_k h(|k|²) Re⟨w_k, B(w,w)_k⟩`. -/
def cubic (u : Field) : ℝ := ∑' k, hm k * (inner ℂ (u k) (convec u k)).re

/-- Real-valued `X, Y, Z` (the `tsum`s of the summable series for `H²` fields). -/
def Xr (u : Field) : ℝ := ∑' k, (if k = 0 then 0 else ‖u k‖ ^ 2)
def Yr (u : Field) : ℝ := ∑' k, hm k * ‖u k‖ ^ 2
def Zr (u : Field) : ℝ := ∑' k, absSq k * hm k * ‖u k‖ ^ 2

/-- The dissipative input law `P_k = A_k h_k |u_k|²/Z`. -/
def Pk (u : Field) (k : Mode) : ℝ := absSq k * hm k * ‖u k‖ ^ 2 / Zr u

/-- `t = Y/Z`. -/
def tYZ (u : Field) : ℝ := Yr u / Zr u

/-- `Q_k = P_k/(t A_k)` (zero at `k = 0`). -/
def Qk (u : Field) (k : Mode) : ℝ := if k = 0 then 0 else Pk u k / (tYZ u * absSq k)

/-- `R_k = ∑_{p+l=k, p×l≠0} P_p P_l`. -/
def Rk (u : Field) (k : Mode) : ℝ :=
  ∑' p : Mode, if cross (modeVec p) (modeVec (k - p)) = 0 then 0 else Pk u p * Pk u (k - p)

end OVNS
