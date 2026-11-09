import OddViscousNS.Quant.Energy.Near.Defs

/-!
# Theorem 1.2, fixed force — E5/E8 native layer: the purefast cubic corrector (definitions)

Fourier-side definitions of the **purefast cubic corrector** `E_j(F) = Re⟨R₋(F,F), A^j F⟩`, of
its **native nonlinear differential** `D_j(F; h) = DE_j(F)[Π_F h]` (all three slots
differentiated), of its near/far split, and of the kernel weight `Z1`, following
`OddViscousNS_data/reports/t12_leading_coeff.md` §1 (provenance: LOCAL210
`FULL_LOCAL_PROOF_210.md` §1, §12; proof volume Body 18 §1–2; TeX quantitative_energies
l.316–330 "The purefast nonresonant cubic uses the denominator `−|k|² + irΦ`").

## Objects (sources ↔ Lean)
* The corrector multiplier (LOCAL210 §1: "`R` has multiplier `C exp(irtΦ)/(ε|k|² + irΦ)`,
  `ε = +1` or `−1`, with its full outer mask `Φ ≠ 0`"): `corrSym ε r τ = e^{iτΦ}/(ε|k|² + irΦ)`
  (`resolv` is the resolvent symbol `1/(εK² + iz)`), masked by `NonRes` (`k ≠ 0 ∧ Φ ≠ 0`;
  "zero output is evaluated before division").  In the library's filtered convention the
  oscillation at absolute time `t` is `phaseM (r t)`, so `τ = r t`.  `ε = −1` is the purefast
  `R₋` (TeX l.316), `ε = +1` the slow corrector `R_S`; LOCAL210 proves both signs.
* `corr ε r τ f g = Qm (corrM ε r τ) f g` is `R(f, g)`: the library's helical triad sum `Q^♯`
  (`Defs.lean`) with the corrector multiplier; `C_{pv}^k = (α|p| − β|v|) g/2` is the library's
  vertex `vert_hel` (`Trilinear.lean`), checked against the physical product in the report.
* `cubicE j ε r τ F = pair j F (corr ε r τ F F)` is `E_j(F) = Re⟨R(F,F), A^j F⟩`
  (`pair σ c F = Re⟨c, Λ^{2σ}F⟩`, `A^j = Λ^{2j}`; `j = 1`: the `H¹` energy corrector `E⁰`,
  `j = 2`: "the same construction at weight two").
* `cubicD j ε r τ F h` is the directional derivative in the fast direction `Π_F h`,
  `Re⟨R(Π_F h, F) + R(F, Π_F h), A^j F⟩ + Re⟨R(F,F), A^j Π_F h⟩` (report §1: "All three slots
  are differentiated: both inputs and the test"; LOCAL210 §1 `K_j = DE_j(w)[Q]`).  The source
  direction of roles 15/31 is `h = Π_F Q_τ(S+F, S+F)`; `h` is *not* the metric multiplier.
* The **near/far split** is on the OUTER phase: `NearT` is `0 < |Φ| < 1`, `FarT` is `|Φ| ≥ 1`
  (Body 18 §1 "split into N: 0 < |Φ| < 1 and B: |Φ| ≥ 1"); `nearD`/`farD` are the two parts of
  `cubicD`.  The mask is invariant under re-rooting the triad (`Phi_cyc`, `Phi_swap`), which is
  what lets the cyclic cancellation of `Kernel.lean` survive the split.
* `Z1 q m K Φ = 32/(mK√(K⁴ + q²Φ²))` is the LOCAL210 (1.2) kernel at sorted legs `m ≤ B₀ ≤ K`;
  its square is `32²` times the unit kernel `nearKer` of `Near/Defs.lean` (`Z1_sq_eq_nearKer`).
* `fres j ε z s = s^j/(εs + iz)` is the cyclic scalar `f_j` of LOCAL210 §1 (`z = rΦ`).
* `wgtE1`, `wgtE2`: the native slot weights at the three positions of `h` (small / middle /
  large leg): `E1` = `(H¹(h), H²(F), H²(F))`, `E2` = `(H²(h), H²(F), H³(F on the larger F leg))`
  (LOCAL210 §1; report §1 "Native").

## Reading choices
* `ε` is a real parameter with the hypothesis `ε = 1 ∨ ε = −1` where a bound needs it.
* The output `k = p + q ≠ 0` is part of every mask, so all three multipliers are bounded by one
  for every `r` (`corrM_bdd`); at `k = 0` the helical projector `hel c 0` vanishes anyway.
* `cubicD` applies `Π_F` to the direction itself: `cubicD j ε r τ F h = cubicD j ε r τ F (Π_F h)`
  (`cubicD_PiF`).
-/

noncomputable section

namespace OVNS.Quant

open scoped ComplexConjugate

/-! ### The resolvent symbol -/

/-- The resolvent symbol `1/(εK² + iz)` of the normal form (TeX l.316: denominator
`−|k|² + irΦ`, i.e. `ε = −1`, `K² = |k|²`, `z = rΦ`). -/
def resolv (ε K2 z : ℝ) : ℂ := 1 / ((ε * K2 : ℝ) + (z : ℝ) * Complex.I)

theorem norm_resolv (ε K2 z : ℝ) :
    ‖resolv ε K2 z‖ = 1 / Real.sqrt ((ε * K2) ^ 2 + z ^ 2) := by
  rw [resolv, norm_div, norm_one, Complex.norm_add_mul_I]

/-- For `ε = ±1`: `|1/(εK² + iz)| = 1/√(K⁴ + z²)` (with `K2 = K²`). -/
theorem norm_resolv_sgn {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (K2 z : ℝ) :
    ‖resolv ε K2 z‖ = 1 / Real.sqrt (K2 ^ 2 + z ^ 2) := by
  rw [norm_resolv]
  rcases hε with rfl | rfl <;> ring_nf

/-- The resolvent is bounded by `1/K²` (the real part of the denominator). -/
theorem norm_resolv_le {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {K2 : ℝ} (hK : 0 < K2) (z : ℝ) :
    ‖resolv ε K2 z‖ ≤ 1 / K2 := by
  rw [norm_resolv_sgn hε]
  apply one_div_le_one_div_of_le hK
  rw [Real.le_sqrt hK.le (by positivity)]
  nlinarith [sq_nonneg z]

/-- The denominator `εK² + iz` is nonzero for `K² ≠ 0`. -/
theorem resolv_den_ne_zero {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {K2 : ℝ} (hK : K2 ≠ 0) (z : ℝ) :
    ((ε * K2 : ℝ) : ℂ) + (z : ℝ) * Complex.I ≠ 0 := by
  intro h
  have h1 := congrArg Complex.re h
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.zero_re] at h1
  rcases hε with rfl | rfl
  · exact hK (by linarith)
  · exact hK (by linarith)

/-- Conjugation flips the sign of `z`. -/
theorem conj_resolv (ε K2 z : ℝ) : conj (resolv ε K2 z) = resolv ε K2 (-z) := by
  simp only [resolv, map_div₀, map_one, map_add, Complex.conj_ofReal, map_mul, Complex.conj_I,
    Complex.ofReal_neg]
  ring

/-! ### The phase masks and the corrector multipliers -/

/-- The nonresonant outer mask `k ≠ 0 ∧ Φ ≠ 0` (LOCAL210 §1 "full outer mask `Φ ≠ 0`"). -/
def NonRes (a b c : Sgn) (p q : Mode) : Prop := p + q ≠ 0 ∧ Phi a b c p q ≠ 0

/-- The near mask `k ≠ 0 ∧ 0 < |Φ| < 1` (Body 18 §1, sector `N`). -/
def NearT (a b c : Sgn) (p q : Mode) : Prop :=
  p + q ≠ 0 ∧ 0 < |Phi a b c p q| ∧ |Phi a b c p q| < 1

/-- The far mask `k ≠ 0 ∧ 1 ≤ |Φ|` (Body 18 §1, sector `B`). -/
def FarT (a b c : Sgn) (p q : Mode) : Prop := p + q ≠ 0 ∧ 1 ≤ |Phi a b c p q|

theorem nonRes_iff (a b c : Sgn) (p q : Mode) :
    NonRes a b c p q ↔ NearT a b c p q ∨ FarT a b c p q := by
  unfold NonRes NearT FarT
  constructor
  · rintro ⟨hk, hΦ⟩
    rcases lt_or_ge |Phi a b c p q| 1 with h | h
    · exact Or.inl ⟨hk, abs_pos.mpr hΦ, h⟩
    · exact Or.inr ⟨hk, h⟩
  · rintro (⟨hk, h0, -⟩ | ⟨hk, h1⟩)
    · exact ⟨hk, abs_pos.mp h0⟩
    · exact ⟨hk, fun h => by rw [h, abs_zero] at h1; exact absurd h1 (by norm_num)⟩

theorem not_nearT_and_farT (a b c : Sgn) (p q : Mode) :
    ¬ (NearT a b c p q ∧ FarT a b c p q) := by
  rintro ⟨⟨-, -, h1⟩, ⟨-, h2⟩⟩
  linarith

/-- The phase is odd under `(p, q) ↦ (−p, −q)`. -/
theorem Phi_neg (a b c : Sgn) (p q : Mode) : Phi a b c (-p) (-q) = -Phi a b c p q := by
  have h : -p + -q = -(p + q) := by abel
  simp only [Phi, h, lam_neg]
  ring

/-- The near mask of the pattern `(s₁, s₂, +)` on the legs `(p, k − p)` is the near set
`IsNear s₁ s₂ p k` of `Near/Defs.lean` (for a nonzero output `k`). -/
theorem nearT_iff_isNear (s₁ s₂ : Sgn) {p k : Mode} (hk : k ≠ 0) :
    NearT s₁ s₂ true p (k - p) ↔ IsNear s₁ s₂ p k := by
  have e : p + (k - p) = k := by abel
  simp only [NearT, IsNear, e, nearPhi_eq_Phi, hk, ne_eq, not_false_eq_true, true_and]

/-- The symbol `e^{iτΦ}/(ε|k|² + irΦ)` of the triad `(a, b, c, p, q)`, `k = p + q`
(LOCAL210 §1; TeX l.316). -/
def corrSym (ε r τ : ℝ) (a b c : Sgn) (p q : Mode) : ℂ :=
  phaseM τ a b c p q * resolv ε (absSq (p + q)) (r * Phi a b c p q)

/-- `|e^{iτΦ}/(ε|k|² + irΦ)| ≤ 1/|k|²`. -/
theorem norm_corrSym_le {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (r τ : ℝ) (a b c : Sgn) {p q : Mode}
    (hk : p + q ≠ 0) : ‖corrSym ε r τ a b c p q‖ ≤ 1 / absSq (p + q) := by
  have h1 := one_le_absSq hk
  rw [corrSym, norm_mul]
  calc ‖phaseM τ a b c p q‖ * ‖resolv ε (absSq (p + q)) (r * Phi a b c p q)‖
      ≤ 1 * (1 / absSq (p + q)) :=
        mul_le_mul (phaseM_bdd τ a b c p q) (norm_resolv_le hε (by linarith) _)
          (norm_nonneg _) zero_le_one
    _ = 1 / absSq (p + q) := one_mul _

theorem norm_corrSym_le_one {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (r τ : ℝ) (a b c : Sgn) {p q : Mode}
    (hk : p + q ≠ 0) : ‖corrSym ε r τ a b c p q‖ ≤ 1 :=
  (norm_corrSym_le hε r τ a b c hk).trans ((div_le_one (by linarith [one_le_absSq hk])).2
    (one_le_absSq hk))

/-- The exact modulus: `|e^{iτΦ}/(ε|k|² + irΦ)| = 1/√(|k|⁴ + r²Φ²)` (the Lorentzian of the
near moment, `Near/Defs.lean`). -/
theorem norm_corrSym {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (r τ : ℝ) (a b c : Sgn) (p q : Mode) :
    ‖corrSym ε r τ a b c p q‖ =
      1 / Real.sqrt (absSq (p + q) ^ 2 + (r * Phi a b c p q) ^ 2) := by
  have h1 : ‖phaseM τ a b c p q‖ = 1 := by
    rw [phaseM, mul_comm, Complex.norm_exp_ofReal_mul_I]
  rw [corrSym, norm_mul, norm_resolv_sgn hε, h1, one_mul]

/-- Reality of the symbol: `m(−p, −q) = conj m(p, q)`. -/
theorem corrSym_neg (ε r τ : ℝ) (a b c : Sgn) (p q : Mode) :
    corrSym ε r τ a b c (-p) (-q) = conj (corrSym ε r τ a b c p q) := by
  have h : -p + -q = -(p + q) := by abel
  rw [corrSym, corrSym, map_mul, ← phaseM_real τ a b c p q, conj_resolv, h, absSq_neg,
    Phi_neg, mul_neg]

open Classical in
/-- The purefast corrector multiplier `𝟏_{k≠0, Φ≠0} e^{iτΦ}/(ε|k|² + irΦ)` (LOCAL210 §1). -/
def corrM (ε r τ : ℝ) : Mult := fun a b c p q =>
  if NonRes a b c p q then corrSym ε r τ a b c p q else 0

open Classical in
/-- The near part `𝟏_{k≠0, 0<|Φ|<1} e^{iτΦ}/(ε|k|² + irΦ)` of the corrector multiplier. -/
def nearCorrM (ε r τ : ℝ) : Mult := fun a b c p q =>
  if NearT a b c p q then corrSym ε r τ a b c p q else 0

open Classical in
/-- The far part `𝟏_{k≠0, |Φ|≥1} e^{iτΦ}/(ε|k|² + irΦ)` of the corrector multiplier. -/
def farCorrM (ε r τ : ℝ) : Mult := fun a b c p q =>
  if FarT a b c p q then corrSym ε r τ a b c p q else 0

/-- The near/far split of the multiplier (Body 18 §1: the split is exhaustive). -/
theorem corrM_eq_add (ε r τ : ℝ) (a b c : Sgn) (p q : Mode) :
    corrM ε r τ a b c p q = nearCorrM ε r τ a b c p q + farCorrM ε r τ a b c p q := by
  unfold corrM nearCorrM farCorrM
  by_cases hN : NearT a b c p q
  · have hF : ¬ FarT a b c p q := fun hF => not_nearT_and_farT a b c p q ⟨hN, hF⟩
    rw [ite_eq_left ((nonRes_iff a b c p q).2 (Or.inl hN)), ite_eq_left hN, ite_eq_right hF,
      add_zero]
  · by_cases hF : FarT a b c p q
    · rw [ite_eq_left ((nonRes_iff a b c p q).2 (Or.inr hF)), ite_eq_right hN, ite_eq_left hF,
        zero_add]
    · rw [ite_eq_right (fun h => ((nonRes_iff a b c p q).1 h).elim hN hF), ite_eq_right hN,
        ite_eq_right hF, add_zero]

theorem corrM_bdd {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (r τ : ℝ) : (corrM ε r τ).Bdd := by
  intro a b c p q
  unfold corrM
  split_ifs with h
  · exact norm_corrSym_le_one hε r τ a b c h.1
  · simp

theorem nearCorrM_bdd {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (r τ : ℝ) : (nearCorrM ε r τ).Bdd := by
  intro a b c p q
  unfold nearCorrM
  split_ifs with h
  · exact norm_corrSym_le_one hε r τ a b c h.1
  · simp

theorem farCorrM_bdd {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (r τ : ℝ) : (farCorrM ε r τ).Bdd := by
  intro a b c p q
  unfold farCorrM
  split_ifs with h
  · exact norm_corrSym_le_one hε r τ a b c h.1
  · simp

theorem nonRes_neg (a b c : Sgn) (p q : Mode) : NonRes a b c (-p) (-q) ↔ NonRes a b c p q := by
  have h : -p + -q = -(p + q) := by abel
  unfold NonRes
  rw [h, neg_ne_zero, Phi_neg, neg_ne_zero]

theorem nearT_neg (a b c : Sgn) (p q : Mode) : NearT a b c (-p) (-q) ↔ NearT a b c p q := by
  have h : -p + -q = -(p + q) := by abel
  unfold NearT
  rw [h, neg_ne_zero, Phi_neg, abs_neg]

theorem farT_neg (a b c : Sgn) (p q : Mode) : FarT a b c (-p) (-q) ↔ FarT a b c p q := by
  have h : -p + -q = -(p + q) := by abel
  unfold FarT
  rw [h, neg_ne_zero, Phi_neg, abs_neg]

/-- Reality of the corrector multiplier (LOCAL210 §12: reality is preserved). -/
theorem corrM_real (ε r τ : ℝ) : (corrM ε r τ).Real := by
  intro a b c p q
  unfold corrM
  rw [corrSym_neg]
  by_cases h : NonRes a b c p q
  · rw [ite_eq_left ((nonRes_neg a b c p q).2 h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h ((nonRes_neg a b c p q).1 h')), ite_eq_right h, map_zero]

theorem nearCorrM_real (ε r τ : ℝ) : (nearCorrM ε r τ).Real := by
  intro a b c p q
  unfold nearCorrM
  rw [corrSym_neg]
  by_cases h : NearT a b c p q
  · rw [ite_eq_left ((nearT_neg a b c p q).2 h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h ((nearT_neg a b c p q).1 h')), ite_eq_right h, map_zero]

theorem farCorrM_real (ε r τ : ℝ) : (farCorrM ε r τ).Real := by
  intro a b c p q
  unfold farCorrM
  rw [corrSym_neg]
  by_cases h : FarT a b c p q
  · rw [ite_eq_left ((farT_neg a b c p q).2 h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h ((farT_neg a b c p q).1 h')), ite_eq_right h, map_zero]

/-- The near mask is invariant under re-rooting a triad of nonzero legs (LOCAL210 §1: "`|Φ|` is
common to all three rootings"): `(a, b, c, p, q) ↦ (b, c, a, q, −(p + q))`. -/
theorem nearT_cyc {p q : Mode} (hp : p ≠ 0) (hk : p + q ≠ 0) (a b c : Sgn) :
    NearT a b c p q ↔ NearT b c a q (-(p + q)) := by
  have h : q + -(p + q) = -p := by abel
  simp only [NearT, h, neg_ne_zero, ← Phi_cyc, hp, hk, ne_eq, not_false_eq_true, true_and]

/-- The near mask is invariant under swapping the second input and the output
(`Phi_swap`): `(a, b, c, p, q) ↦ (a, c, b, p, −(p + q))`, for `q ≠ 0`, `p + q ≠ 0`. -/
theorem nearT_swap {p q : Mode} (hq : q ≠ 0) (hk : p + q ≠ 0) (a b c : Sgn) :
    NearT a b c p q ↔ NearT a c b p (-(p + q)) := by
  have h : p + -(p + q) = -q := by abel
  simp only [NearT, h, neg_ne_zero, ← Phi_swap, hq, hk, ne_eq, not_false_eq_true, true_and]

/-! ### The corrector fields and the cubic correctors -/

/-- `R(f, g) = Q^♯_{corrM}(f, g)`: the corrector field (LOCAL210 §1 `R(w,w)`). -/
def corr (ε r τ : ℝ) (f g : Field) : Field := Qm (corrM ε r τ) f g

/-- The near part `R_N(f, g)` (outer phase `0 < |Φ| < 1`). -/
def nearCorr (ε r τ : ℝ) (f g : Field) : Field := Qm (nearCorrM ε r τ) f g

/-- The far part `R_B(f, g)` (outer phase `|Φ| ≥ 1`). -/
def farCorr (ε r τ : ℝ) (f g : Field) : Field := Qm (farCorrM ε r τ) f g

/-- The purefast cubic corrector `E_j(F) = Re⟨R(F,F), A^j F⟩` (TeX l.316 `E⁰` for `j = 1`,
"the same construction at weight two" for `j = 2`; LOCAL210 §1 `E_j`).  The physical object
uses `ε = −1` (`R₋`). -/
def cubicE (j : ℕ) (ε r τ : ℝ) (F : Field) : ℝ := pair j F (corr ε r τ F F)

/-- The native nonlinear differential `D_j(F; h) = DE_j(F)[Π_F h]`, the sum of the three slot
derivatives `Re⟨R(Π_F h, F), A^j F⟩ + Re⟨R(F, Π_F h), A^j F⟩ + Re⟨R(F,F), A^j Π_F h⟩`
(report §1; LOCAL210 §1 `K_j`). -/
def cubicD (j : ℕ) (ε r τ : ℝ) (F h : Field) : ℝ :=
  pair j F (corr ε r τ (PiF h) F) + pair j F (corr ε r τ F (PiF h)) +
    pair j (PiF h) (corr ε r τ F F)

/-- The near part `D_j^N(F; h)` of the native differential (the roles 15/31 object). -/
def nearD (j : ℕ) (ε r τ : ℝ) (F h : Field) : ℝ :=
  pair j F (nearCorr ε r τ (PiF h) F) + pair j F (nearCorr ε r τ F (PiF h)) +
    pair j (PiF h) (nearCorr ε r τ F F)

/-- The far part `D_j^B(F; h)` of the native differential (first-power degree, separate). -/
def farD (j : ℕ) (ε r τ : ℝ) (F h : Field) : ℝ :=
  pair j F (farCorr ε r τ (PiF h) F) + pair j F (farCorr ε r τ F (PiF h)) +
    pair j (PiF h) (farCorr ε r τ F F)

theorem cubicD_PiF (j : ℕ) (ε r τ : ℝ) (F h : Field) :
    cubicD j ε r τ F (PiF h) = cubicD j ε r τ F h := by
  have e : PiF (PiF h) = PiF h := by
    funext k
    by_cases hk : k 2 = 0 <;> simp [PiF, hk]
  simp only [cubicD, e]

theorem nearD_PiF (j : ℕ) (ε r τ : ℝ) (F h : Field) :
    nearD j ε r τ F (PiF h) = nearD j ε r τ F h := by
  have e : PiF (PiF h) = PiF h := by
    funext k
    by_cases hk : k 2 = 0 <;> simp [PiF, hk]
  simp only [nearD, e]

/-! ### The kernel weight and the cyclic scalars -/

/-- The LOCAL210 (1.2) kernel `Z1 = 32/(mK√(K⁴ + q²Φ²))` at sorted legs `m ≤ B₀ ≤ K`, `q = |r|`
(report §1; Body 18 §2).  The unit kernel of `Near/Defs.lean` is `Z1/32`. -/
def Z1 (q m K Φ : ℝ) : ℝ := 32 / (m * K * Real.sqrt (K ^ 4 + q ^ 2 * Φ ^ 2))

theorem Z1_nonneg {q m K : ℝ} (hm : 0 ≤ m) (hK : 0 ≤ K) (Φ : ℝ) : 0 ≤ Z1 q m K Φ := by
  unfold Z1
  positivity

theorem Z1_sq (q m K Φ : ℝ) :
    Z1 q m K Φ ^ 2 = 32 ^ 2 / (m ^ 2 * K ^ 2 * (K ^ 4 + q ^ 2 * Φ ^ 2)) := by
  unfold Z1
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]

/-- `Z1² = 32² κ_N²`: the kernel of LOCAL210 (1.2) squared is `32²` times the unit native kernel
`nearKer` of `Near/Defs.lean` (at the legs `m = minLeg p k`, `K = |k|`, `Φ = nearPhi`). -/
theorem Z1_sq_eq_nearKer (q : ℝ) (s₁ s₂ : Sgn) (p k : Mode) :
    Z1 q (minLeg p k) (absk k) (nearPhi s₁ s₂ p k) ^ 2 = 32 ^ 2 * nearKer q s₁ s₂ p k := by
  rw [Z1_sq, nearKer, mul_one_div]

/-- The `q`-free bound `Z1 ≤ 32/(mK³)` (LOCAL210 §6 "small-`q` face"). -/
theorem Z1_le {q m K : ℝ} (hm : 0 < m) (hK : 0 < K) (Φ : ℝ) :
    Z1 q m K Φ ≤ 32 / (m * K ^ 3) := by
  unfold Z1
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  have h : K ^ 2 ≤ Real.sqrt (K ^ 4 + q ^ 2 * Φ ^ 2) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    nlinarith [sq_nonneg (q * Φ)]
  calc m * K ^ 3 = m * K * K ^ 2 := by ring
    _ ≤ m * K * Real.sqrt (K ^ 4 + q ^ 2 * Φ ^ 2) :=
        mul_le_mul_of_nonneg_left h (by positivity)

/-- The cyclic scalar `f_j(s) = s^j/(εs + iz)` of LOCAL210 §1, `z = rΦ`: the resolvent weighted
by the output power `|out|^{2j} = s^j`, `s = |out|²`. -/
def fres (j : ℕ) (ε z s : ℝ) : ℂ := (s : ℂ) ^ j * resolv ε s z

/-- The native slot weights of `E1` at sorted legs `m ≤ B ≤ K`, indexed by the position of `h`
(`0` = small leg `m`, `1` = middle leg `B`, `2` = large leg `K`): `H¹(h) · H²(F) · H²(F)`
(LOCAL210 §1 "E1 weights h_H1, H2, H2"). -/
def wgtE1 (m B K : ℝ) : Fin 3 → ℝ := ![m * B ^ 2 * K ^ 2, B * m ^ 2 * K ^ 2, K * m ^ 2 * B ^ 2]

/-- The native slot weights of `E2`: `H²(h) · H²(F) · H³(F on the larger F leg)` (LOCAL210 §1
"E2 weights h_H2, H2, H3 (H3 on the larger w frequency in each order region)"). -/
def wgtE2 (m B K : ℝ) : Fin 3 → ℝ :=
  ![m ^ 2 * B ^ 2 * K ^ 3, B ^ 2 * m ^ 2 * K ^ 3, K ^ 2 * m ^ 2 * B ^ 3]

end OVNS.Quant

end
