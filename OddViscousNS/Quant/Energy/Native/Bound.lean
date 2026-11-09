import OddViscousNS.Quant.Energy.Native.Kernel

/-!
# Theorem 1.2, fixed force — E5/E8 native layer: from the kernel to the roles 15/31 coefficient

The analytic chain of `OddViscousNS_data/reports/t12_leading_coeff.md` §2 Steps 3–5 (LOCAL210
§6–7, §12; Bodies 18–21; TeX quantitative_energies l.316–352):

* **A. The two Cauchy–Schwarz steps** (LOCAL210 §6 "ONE kernel Cauchy", report Step 3), proved
  in the abstract form used by every native role: `nearBox_cauchy` (fixed largest output `k`,
  Cauchy–Schwarz over the near box), `sum_nearBox_sq_le` (the restricted positive double sum is
  enlarged to the unrestricted one, which factors as `‖V‖₂²‖W‖₂²`), `output_cauchy_near` (Cauchy
  over the output), and the chain `moment_cauchy`: for a nonnegative kernel `κ` with per-output
  moment `Σ_{p ∈ box(k)} κ(k,p)² ≤ M`,
  `Σ_k U_k Σ_{p ∈ box(k)} κ(k,p) V_p W_{k−p} ≤ √M ‖U‖₂ ‖V‖₂ ‖W‖₂`; `moment_cauchy_near` is the
  instance `κ = √(Σ_s nearW)`, `M = 𝔐_N(q)` (`Near/Defs.lean`), the pattern of
  `Resonant/Cauchy.lean` (`fibre_cauchy`, `output_cauchy`) on the near box instead of `SFib`.
* **B. The near/far split and the derivative identity**: `corr_eq_near_add_far`,
  `cubicD_eq_near_add_far` (proved: `Qm` is additive in the multiplier, `pair` in its slot), and
  `hasDerivAt_cubicE`: `cubicD` is the directional derivative of `cubicE`
  (report §1, TeX l.318 "`(E⁰)' = … − DE⁰[Π_F Q_τ(S+F,S+F)] − …`").
* **C. The native near bounds** (LOCAL210 (6.1); report §1) are assembled in `NearAssembly.lean`
  (`nearD1_le`, `nearD2_le`, through `Triad.lean` and `TriadBound.lean`), from the Cauchy chain A.
* **D. The product leaves** (LOCAL210 §7; Body 18 §1; report Step 4), with the
  sources' constants `41` (`4√104`) and `7` (`√42`) REPLACED by the library's explicit ones:
  `‖Π_F Q_τ(F,F)‖₂ ≤ 32√5488 √(ab) c` (`hnorm_two_Qphase_le`) and
  `‖Π_F Q_τ(F,F)‖₁ ≤ 16√5488 √(ab) b` (`hnorm_one_Qphase_le`), PROVED; the same bounds with the
  library's own (cruder) constants are PROVED (`exists_hnorm_two_Qphase_le`,
  `exists_hnorm_one_Qphase_le`: `hnorm_Qm_le` (M4) and the Wiener interpolation
  `exists_wiener_interp`, `𝒜(F) ≤ c_I √(ab)`, `c_I = 2√5488`).
* **E. The roles 15/31 coefficient** (report Step 5) is in `NearAssembly.lean`, from C and D.
-/

noncomputable section

namespace OVNS.Quant

/-! ### A. The two Cauchy–Schwarz steps over the near box -/

/-- Fixed-output (kernel) Cauchy–Schwarz over the near box (LOCAL210 §6 "at fixed largest output
`k`, `|Σ_p Z1 V(p) W0(k−p)|² ≤ S(k) Σ_p |V(p)|²|W0(k−p)|²`"). -/
theorem nearBox_cauchy (k : Mode) (κ V W : Mode → ℝ) :
    ∑ p ∈ nearBox k, κ p * (V p * W (k - p)) ≤
      Real.sqrt (∑ p ∈ nearBox k, κ p ^ 2) *
        Real.sqrt (∑ p ∈ nearBox k, (V p * W (k - p)) ^ 2) :=
  Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-- The shear `(k, p) ↦ (p, k − p)` of the lattice square. -/
private def shear : Mode × Mode ≃ Mode × Mode where
  toFun x := (x.2, x.1 - x.2)
  invFun y := (y.1 + y.2, y.1)
  left_inv x := by ext <;> simp
  right_inv y := by ext <;> simp

private lemma shear_apply (x : Mode × Mode) : shear x = (x.2, x.1 - x.2) := rfl

/-- The restricted positive double sum is below the unrestricted one, which factors
(LOCAL210 §6 "enlarge the positive restricted double sum to the unrestricted one. It factors
into `‖V‖₂²‖W0‖₂²`"). -/
theorem sum_nearBox_sq_le {V W : Mode → ℝ} (hV : Summable fun p => V p ^ 2)
    (hW : Summable fun p => W p ^ 2) :
    (Summable fun k => ∑ p ∈ nearBox k, (V p * W (k - p)) ^ 2) ∧
      ∑' k, ∑ p ∈ nearBox k, (V p * W (k - p)) ^ 2 ≤ (∑' p, V p ^ 2) * ∑' p, W p ^ 2 := by
  have hP : Summable fun y : Mode × Mode => V y.1 ^ 2 * W y.2 ^ 2 :=
    Summable.mul_of_nonneg (f := fun p => V p ^ 2) (g := fun p => W p ^ 2) hV hW
      (fun p => sq_nonneg (V p)) (fun p => sq_nonneg (W p))
  have hH : Summable fun x : Mode × Mode => V x.2 ^ 2 * W (x.1 - x.2) ^ 2 := by
    have h := shear.summable_iff.mpr hP
    refine h.congr fun x => ?_
    simp only [Function.comp, shear_apply]
  have hH0 : ∀ x : Mode × Mode, 0 ≤ V x.2 ^ 2 * W (x.1 - x.2) ^ 2 := fun x => by positivity
  have hle : ∀ k, ∑ p ∈ nearBox k, (V p * W (k - p)) ^ 2 ≤
      ∑' p, V p ^ 2 * W (k - p) ^ 2 := fun k => by
    have e : ∀ p, (V p * W (k - p)) ^ 2 = V p ^ 2 * W (k - p) ^ 2 := fun p => mul_pow _ _ _
    simp only [e]
    exact (hH.prod_factor k).sum_le_tsum _ fun p _ => hH0 (k, p)
  have hS : Summable fun k => ∑' p, V p ^ 2 * W (k - p) ^ 2 := hH.prod
  have hsum :=
    Summable.of_nonneg_of_le (fun k => Finset.sum_nonneg fun p _ => sq_nonneg _) hle hS
  refine ⟨hsum, ?_⟩
  calc ∑' k, ∑ p ∈ nearBox k, (V p * W (k - p)) ^ 2 ≤ ∑' k, ∑' p, V p ^ 2 * W (k - p) ^ 2 :=
        hsum.tsum_le_tsum hle hS
    _ = ∑' x : Mode × Mode, V x.2 ^ 2 * W (x.1 - x.2) ^ 2 := hH.tsum_prod.symm
    _ = ∑' y : Mode × Mode, V y.1 ^ 2 * W y.2 ^ 2 := by
        rw [← shear.tsum_eq (fun y : Mode × Mode => V y.1 ^ 2 * W y.2 ^ 2)]
        exact tsum_congr fun x => by simp only [shear_apply]
    _ = (∑' p, V p ^ 2) * ∑' p, W p ^ 2 := (hV.tsum_mul_tsum hW hP).symm

/-- Cauchy–Schwarz for nonnegative real series (`Resonant/Cauchy.lean` has it privately). -/
theorem cs_tsum_nonneg' {a b : Mode → ℝ} (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (ha2 : Summable fun k => a k ^ 2) (hb2 : Summable fun k => b k ^ 2) :
    Summable (fun k => a k * b k) ∧
      ∑' k, a k * b k ≤ Real.sqrt (∑' k, a k ^ 2) * Real.sqrt (∑' k, b k ^ 2) := by
  have h := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
    ha hb (by simpa only [Real.rpow_two] using ha2) (by simpa only [Real.rpow_two] using hb2)
  simp only [Real.rpow_two] at h
  simpa only [Real.sqrt_eq_rpow] using h

/-- Output Cauchy–Schwarz over the largest leg (LOCAL210 §6 "Pair with `U(k)`, use Cauchy over
`k` ONCE"). -/
theorem output_cauchy_near {U V W : Mode → ℝ} (hU : ∀ k, 0 ≤ U k)
    (hU2 : Summable fun k => U k ^ 2) (hV2 : Summable fun p => V p ^ 2)
    (hW2 : Summable fun p => W p ^ 2) :
    Summable (fun k => U k * Real.sqrt (∑ p ∈ nearBox k, (V p * W (k - p)) ^ 2)) ∧
      ∑' k, U k * Real.sqrt (∑ p ∈ nearBox k, (V p * W (k - p)) ^ 2) ≤
        Real.sqrt (∑' k, U k ^ 2) * Real.sqrt (∑' p, V p ^ 2) * Real.sqrt (∑' p, W p ^ 2) := by
  obtain ⟨hS, hle⟩ := sum_nearBox_sq_le hV2 hW2
  have hsq : ∀ k, Real.sqrt (∑ p ∈ nearBox k, (V p * W (k - p)) ^ 2) ^ 2 =
      ∑ p ∈ nearBox k, (V p * W (k - p)) ^ 2 := fun k =>
    Real.sq_sqrt (Finset.sum_nonneg fun p _ => sq_nonneg _)
  have hS' : Summable fun k => Real.sqrt (∑ p ∈ nearBox k, (V p * W (k - p)) ^ 2) ^ 2 :=
    hS.congr fun k => (hsq k).symm
  have hcs := cs_tsum_nonneg' hU (fun k => Real.sqrt_nonneg _) hU2 hS'
  refine ⟨hcs.1, hcs.2.trans ?_⟩
  have e : ∑' k, Real.sqrt (∑ p ∈ nearBox k, (V p * W (k - p)) ^ 2) ^ 2 =
      ∑' k, ∑ p ∈ nearBox k, (V p * W (k - p)) ^ 2 := tsum_congr hsq
  rw [e, mul_assoc, ← Real.sqrt_mul (tsum_nonneg fun p => sq_nonneg (V p))]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle) (Real.sqrt_nonneg _)

/-- **The kernel–output Cauchy chain** (LOCAL210 §6; report §2 Step 3): for a nonnegative kernel
`κ` whose per-output near moment is at most `M`, and nonnegative `ℓ²` sequences `U, V, W`,
`Σ_k U_k Σ_{p ∈ box(k)} κ(k,p) V_p W_{k−p} ≤ √M ‖U‖₂ ‖V‖₂ ‖W‖₂`.  "The native trilinear bound
is therefore `sup_k √S(k)` times the three native norms." -/
theorem moment_cauchy {κ : Mode → Mode → ℝ} {M : ℝ} (hκ : ∀ k p, 0 ≤ κ k p)
    (hM : ∀ k, ∑ p ∈ nearBox k, κ k p ^ 2 ≤ M) {U V W : Mode → ℝ} (hU : ∀ k, 0 ≤ U k)
    (hV : ∀ p, 0 ≤ V p) (hW : ∀ p, 0 ≤ W p) (hU2 : Summable fun k => U k ^ 2)
    (hV2 : Summable fun p => V p ^ 2) (hW2 : Summable fun p => W p ^ 2) :
    Summable (fun k => U k * ∑ p ∈ nearBox k, κ k p * (V p * W (k - p))) ∧
      ∑' k, U k * ∑ p ∈ nearBox k, κ k p * (V p * W (k - p)) ≤
        Real.sqrt M *
          (Real.sqrt (∑' k, U k ^ 2) * Real.sqrt (∑' p, V p ^ 2) * Real.sqrt (∑' p, W p ^ 2)) := by
  obtain ⟨hS, hle⟩ := output_cauchy_near hU hU2 hV2 hW2
  have hterm : ∀ k, U k * ∑ p ∈ nearBox k, κ k p * (V p * W (k - p)) ≤
      Real.sqrt M * (U k * Real.sqrt (∑ p ∈ nearBox k, (V p * W (k - p)) ^ 2)) := by
    intro k
    have h1 := nearBox_cauchy k (κ k) V W
    have h2 : Real.sqrt (∑ p ∈ nearBox k, κ k p ^ 2) ≤ Real.sqrt M := Real.sqrt_le_sqrt (hM k)
    calc U k * ∑ p ∈ nearBox k, κ k p * (V p * W (k - p))
        ≤ U k * (Real.sqrt M * Real.sqrt (∑ p ∈ nearBox k, (V p * W (k - p)) ^ 2)) := by
          refine mul_le_mul_of_nonneg_left (h1.trans ?_) (hU k)
          exact mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
      _ = _ := by ring
  have hnn : ∀ k, 0 ≤ U k * ∑ p ∈ nearBox k, κ k p * (V p * W (k - p)) := fun k =>
    mul_nonneg (hU k) (Finset.sum_nonneg fun p _ =>
      mul_nonneg (hκ k p) (mul_nonneg (hV p) (hW _)))
  have hS' : Summable fun k =>
      Real.sqrt M * (U k * Real.sqrt (∑ p ∈ nearBox k, (V p * W (k - p)) ^ 2)) :=
    hS.mul_left _
  have hsum := Summable.of_nonneg_of_le hnn hterm hS'
  refine ⟨hsum, ?_⟩
  calc ∑' k, U k * ∑ p ∈ nearBox k, κ k p * (V p * W (k - p))
      ≤ ∑' k, Real.sqrt M * (U k * Real.sqrt (∑ p ∈ nearBox k, (V p * W (k - p)) ^ 2)) :=
        hsum.tsum_le_tsum hterm hS'
    _ = Real.sqrt M * ∑' k, U k * Real.sqrt (∑ p ∈ nearBox k, (V p * W (k - p)) ^ 2) :=
        tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg _)

/-- The summed unit near kernel `κ_N(k, p) = √(Σ_{(s₁,s₂)} nearW q s₁ s₂ p k)` of the output `k`
(the four patterns of `Near/Defs.lean` combined in `ℓ²`). -/
def nearKerSum (q : ℝ) (k p : Mode) : ℝ := Real.sqrt (∑ s : Sgn × Sgn, nearW q s.1 s.2 p k)

theorem nearKerSum_nonneg (q : ℝ) (k p : Mode) : 0 ≤ nearKerSum q k p := Real.sqrt_nonneg _

/-- Its per-output moment is exactly `momN q k`. -/
theorem sum_nearKerSum_sq (q : ℝ) (k : Mode) :
    ∑ p ∈ nearBox k, nearKerSum q k p ^ 2 = momN q k := by
  unfold momN nearKerSum
  exact Finset.sum_congr rfl fun p _ =>
    Real.sq_sqrt (Finset.sum_nonneg fun s _ => nearW_nonneg q s.1 s.2 p k)

/-- **The near-moment Cauchy chain** (Body 18 §2 "One kernel Cauchy then output Cauchy turns the
moment into an operator bound"): with the summed unit kernel,
`Σ_k U_k Σ_{p ∈ box(k)} κ_N(k,p) V_p W_{k−p} ≤ √𝔐_N(q) ‖U‖₂ ‖V‖₂ ‖W‖₂`. -/
theorem moment_cauchy_near (q : ℝ) {U V W : Mode → ℝ} (hU : ∀ k, 0 ≤ U k) (hV : ∀ p, 0 ≤ V p)
    (hW : ∀ p, 0 ≤ W p) (hU2 : Summable fun k => U k ^ 2) (hV2 : Summable fun p => V p ^ 2)
    (hW2 : Summable fun p => W p ^ 2) :
    ∑' k, U k * ∑ p ∈ nearBox k, nearKerSum q k p * (V p * W (k - p)) ≤
      Real.sqrt (MomN q) *
        (Real.sqrt (∑' k, U k ^ 2) * Real.sqrt (∑' p, V p ^ 2) * Real.sqrt (∑' p, W p ^ 2)) :=
  (moment_cauchy (fun k p => nearKerSum_nonneg q k p)
    (fun k => by rw [sum_nearKerSum_sq]; exact momN_le_MomN q k) hU hV hW hU2 hV2 hW2).2

/-! ### B. The near/far split and the derivative identity -/

/-- `Qm` is additive in the multiplier, for summable inputs (`NormalForm.lean` has it
privately). -/
theorem Qm_add_mult' {m m₁ m₂ : Mult} {f h : Field} (h₁ : m₁.Bdd) (h₂ : m₂.Bdd)
    (hm : ∀ a b c p q, m a b c p q = m₁ a b c p q + m₂ a b c p q) (hf : MZ 2 f) (hh : MZ 2 h) :
    Qm m f h = Qm m₁ f h + Qm m₂ f h := by
  funext k
  rw [Pi.add_apply]
  unfold Qm
  rw [← (summable_Qm_term h₁ hf hh k).tsum_add (summable_Qm_term h₂ hf hh k)]
  refine tsum_congr fun p => ?_
  simp only [hm, add_smul, Finset.sum_add_distrib]

/-- The near/far split of the corrector (Body 18 §1). -/
theorem corr_eq_near_add_far {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (r τ : ℝ) {f g : Field} (hf : MZ 2 f)
    (hg : MZ 2 g) : corr ε r τ f g = nearCorr ε r τ f g + farCorr ε r τ f g :=
  Qm_add_mult' (nearCorrM_bdd hε r τ) (farCorrM_bdd hε r τ) (corrM_eq_add ε r τ) hf hg

theorem _root_.OVNS.MZ.PiF' {s : ℝ} {h : Field} (hh : MZ s h) : MZ s (PiF h) :=
  ⟨hh.inH.PiF, by simp [PiF]⟩

theorem _root_.OVNS.MZ.mono' {s s' : ℝ} (hs : s ≤ s') {f : Field} (hf : MZ s' f) : MZ s f :=
  ⟨hf.inH.mono hs, hf.mean⟩

/-- **The near/far split of the native differential**, `j ∈ {1, 2}`: `D_j = D_j^N + D_j^B`
(Body 18 §1 "Split the OUTER expression into N and B"). -/
theorem cubicD_eq_near_add_far {j : ℕ} (hj : j = 1 ∨ j = 2) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (r τ : ℝ) {F h : Field} (hF : MZ 3 F) (hh : MZ 3 h) :
    cubicD j ε r τ F h = nearD j ε r τ F h + farD j ε r τ F h := by
  have hj1 : (1 : ℝ) ≤ j := by rcases hj with rfl | rfl <;> norm_num
  have hj2 : (j : ℝ) ≤ 2 := by rcases hj with rfl | rfl <;> norm_num
  have hF2 : MZ 2 F := hF.mono' (by norm_num)
  have hFj : MZ j F := hF.mono' (by linarith)
  have hh3 : MZ 3 (PiF h) := hh.PiF'
  have hh2 : MZ 2 (PiF h) := hh3.mono' (by norm_num)
  have hhj : MZ j (PiF h) := hh3.mono' (by linarith)
  have hFj1 : InH ((j : ℝ) + 1) F := hF.inH.mono (by linarith)
  have hhj1 : InH ((j : ℝ) + 1) (PiF h) := hh3.inH.mono (by linarith)
  have hN : ∀ {f g : Field}, MZ j f → MZ j g → MZ 2 f → MZ 2 g →
      InH ((j : ℝ) - 1) (nearCorr ε r τ f g) := fun hf hg hf2 hg2 =>
    (hnorm_Qm_le (nearCorrM_bdd hε r τ) hj1 hf hg hf2 hg2).1
  have hB : ∀ {f g : Field}, MZ j f → MZ j g → MZ 2 f → MZ 2 g →
      InH ((j : ℝ) - 1) (farCorr ε r τ f g) := fun hf hg hf2 hg2 =>
    (hnorm_Qm_le (farCorrM_bdd hε r τ) hj1 hf hg hf2 hg2).1
  unfold cubicD nearD farD
  rw [corr_eq_near_add_far hε r τ hh2 hF2, corr_eq_near_add_far hε r τ hF2 hh2,
    corr_eq_near_add_far hε r τ hF2 hF2, pair_add hFj1 (hN hhj hFj hh2 hF2) (hB hhj hFj hh2 hF2),
    pair_add hFj1 (hN hFj hhj hF2 hh2) (hB hFj hhj hF2 hh2),
    pair_add hhj1 (hN hFj hFj hF2 hF2) (hB hFj hFj hF2 hF2)]
  ring

/-- The vertex is `ℂ`-linear in its first vector. -/
private lemma vert_smul_left' (p q : Mode) (c : ℂ) (A B : V3) :
    vert p q (c • A) B = c • vert p q A B := by
  simp only [vert, dotM_smul, smul_smul, ← leray_smul, smul_add]
  congr 2 <;> congr 1 <;> ring

/-- The vertex is `ℂ`-linear in its second vector. -/
private lemma vert_smul_right' (p q : Mode) (c : ℂ) (A B : V3) :
    vert p q A (c • B) = c • vert p q A B := by
  simp only [vert, dotM_smul, smul_smul, ← leray_smul, smul_add]
  congr 2 <;> congr 1 <;> ring

/-- `Qm` is `ℂ`-homogeneous in its first field. -/
private lemma Qm_smul_left' (m : Mult) (c : ℂ) (f g : Field) :
    Qm m (c • f) g = c • Qm m f g := by
  funext k
  rw [Pi.smul_apply]
  unfold Qm
  rw [← tsum_const_smul'']
  refine tsum_congr fun p => ?_
  simp only [Pi.smul_apply, hel_smul, vert_smul_left', Finset.smul_sum, smul_comm c]

/-- `Qm` is `ℂ`-homogeneous in its second field. -/
private lemma Qm_smul_right' (m : Mult) (c : ℂ) (f g : Field) :
    Qm m f (c • g) = c • Qm m f g := by
  funext k
  rw [Pi.smul_apply]
  unfold Qm
  rw [← tsum_const_smul'']
  refine tsum_congr fun p => ?_
  simp only [Pi.smul_apply, hel_smul, vert_smul_right', Finset.smul_sum, smul_comm c]

/-- The terms of `pair σ c F` are summable for `c ∈ H^{σ+1}`, `F ∈ H^{σ-1}`. -/
private lemma summable_pair_term {σ : ℝ} {c F : Field} (hc : InH (σ + 1) c)
    (hF : InH (σ - 1) F) : Summable fun k => sobWeight σ k * (inner ℂ (c k) (F k)).re := by
  refine Summable.of_norm_bounded (pair_le hc hF).1 fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sobWeight_nonneg σ k), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (sobWeight_nonneg σ k)
  exact (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)

/-- Expansion of the pairing along a line, cubic in `t`. -/
private lemma pair_line {σ : ℝ} {c c' X₀ X₁ X₂ : Field} (hc : InH (σ + 1) c)
    (hc' : InH (σ + 1) c') (h₀ : InH (σ - 1) X₀) (h₁ : InH (σ - 1) X₁) (h₂ : InH (σ - 1) X₂)
    (t : ℝ) :
    pair σ (c + (t : ℂ) • c') (X₀ + (t : ℂ) • X₁ + ((t : ℂ) ^ 2) • X₂) =
      pair σ c X₀ + t * (pair σ c X₁ + pair σ c' X₀) + t ^ 2 * (pair σ c X₂ + pair σ c' X₁) +
        t ^ 3 * pair σ c' X₂ := by
  have s00 := summable_pair_term hc h₀
  have s01 := summable_pair_term hc h₁
  have s02 := summable_pair_term hc h₂
  have s10 := summable_pair_term hc' h₀
  have s11 := summable_pair_term hc' h₁
  have s12 := summable_pair_term hc' h₂
  simp only [pair]
  rw [← s01.tsum_add s10, ← s02.tsum_add s11, ← tsum_mul_left, ← tsum_mul_left,
    ← tsum_mul_left, ← s00.tsum_add ((s01.add s10).mul_left _),
    ← (s00.add ((s01.add s10).mul_left _)).tsum_add ((s02.add s11).mul_left _),
    ← ((s00.add ((s01.add s10).mul_left _)).add ((s02.add s11).mul_left _)).tsum_add
      (s12.mul_left _)]
  refine tsum_congr fun k => ?_
  simp only [Pi.add_apply, Pi.smul_apply, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, Complex.add_re, Complex.conj_ofReal, ← Complex.ofReal_pow,
    Complex.re_ofReal_mul]
  ring


/-- The corrector along a line is a quadratic polynomial in `t`. -/
private lemma corr_line {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (r τ : ℝ) {F G : Field} (hF : MZ 2 F)
    (hG : MZ 2 G) (t : ℝ) :
    corr ε r τ (F + (t : ℂ) • G) (F + (t : ℂ) • G) =
      corr ε r τ F F + (t : ℂ) • (corr ε r τ G F + corr ε r τ F G) +
        ((t : ℂ) ^ 2) • corr ε r τ G G := by
  have hM := majorized_Qm (fun _ => corrM ε r τ) (fun _ => corrM_bdd hε r τ)
    (fun _ => corrM_real ε r τ) fun _ _ _ _ _ => continuous_const
  have htG : MZ 2 ((t : ℂ) • G) := ⟨hG.inH.smul _, by simp [hG.mean]⟩
  have hFt : MZ 2 (F + (t : ℂ) • G) := ⟨hF.inH.add htG.inH, by simp [hF.mean, hG.mean]⟩
  unfold corr
  rw [hM.add_left 0 _ _ _ hF htG hFt, hM.add_right 0 _ _ _ hF hF htG,
    hM.add_right 0 _ _ _ htG hF htG]
  simp only [Qm_smul_left', Qm_smul_right', smul_add, smul_smul]
  rw [sq]
  abel

/-- **The derivative identity** (TeX l.318; report §1; LOCAL210 §1 `K_j = DE_j(w)[Q]`): `cubicD`
is the directional derivative of the cubic corrector `cubicE` in the fast direction `Π_F h`,
`d/dt E_j(F + t Π_F h)|_{t=0} = D_j(F; h)`.  Route: `corr` is bilinear on `MZ 2`
fields (`Qm_add_left`/`Qm_add_right` of `Majorant.lean`, `Qm` is `ℂ`-homogeneous), `pair` is
additive in each slot with absolutely convergent terms (`pair_add`, `pair_le` with `Adm 3`), so
`t ↦ E_j(F + tΠ_F h)` is a cubic polynomial in `t` whose linear coefficient is `cubicD`. -/
theorem hasDerivAt_cubicE {j : ℕ} (hj : j = 1 ∨ j = 2) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (r τ : ℝ) {F h : Field} (hF : Adm 3 F) (hh : Adm 3 h) :
    HasDerivAt (fun t : ℝ => cubicE j ε r τ (F + (t : ℂ) • PiF h)) (cubicD j ε r τ F h) 0 := by
  have hj1 : (1 : ℝ) ≤ j := by rcases hj with rfl | rfl <;> norm_num
  have hj2 : (j : ℝ) ≤ 2 := by rcases hj with rfl | rfl <;> norm_num
  have hF3 : MZ 3 F := ⟨hF.inH, hF.mean⟩
  have hG3 : MZ 3 (PiF h) := ⟨hh.inH.PiF, by simp [PiF]⟩
  have hF2 : MZ 2 F := ⟨hF.inH.mono (by norm_num), hF.mean⟩
  have hG2 : MZ 2 (PiF h) := ⟨hG3.inH.mono (by norm_num), hG3.mean⟩
  have hFj : MZ j F := ⟨hF.inH.mono (by linarith), hF.mean⟩
  have hGj : MZ j (PiF h) := ⟨hG3.inH.mono (by linarith), hG3.mean⟩
  have hFj1 : InH ((j : ℝ) + 1) F := hF3.inH.mono (by linarith)
  have hGj1 : InH ((j : ℝ) + 1) (PiF h) := hG3.inH.mono (by linarith)
  have hC : ∀ {f g : Field}, MZ j f → MZ j g → MZ 2 f → MZ 2 g →
      InH ((j : ℝ) - 1) (corr ε r τ f g) := fun hf hg hf2 hg2 =>
    (hnorm_Qm_le (corrM_bdd hε r τ) hj1 hf hg hf2 hg2).1
  set G := PiF h
  have e : (fun t : ℝ => cubicE j ε r τ (F + (t : ℂ) • G)) = fun t =>
      pair j F (corr ε r τ F F) +
        t * (pair j F (corr ε r τ G F + corr ε r τ F G) + pair j G (corr ε r τ F F)) +
        t ^ 2 * (pair j F (corr ε r τ G G) + pair j G (corr ε r τ G F + corr ε r τ F G)) +
        t ^ 3 * pair j G (corr ε r τ G G) := by
    funext t
    rw [cubicE, corr_line hε r τ hF2 hG2 t]
    exact pair_line hFj1 hGj1 (hC hFj hFj hF2 hF2)
      ((hC hGj hFj hG2 hF2).add (hC hFj hGj hF2 hG2)) (hC hGj hGj hG2 hG2) t
  rw [e]
  have hD : cubicD j ε r τ F h =
      pair j F (corr ε r τ G F + corr ε r τ F G) + pair j G (corr ε r τ F F) := by
    rw [cubicD, pair_add hFj1 (hC hGj hFj hG2 hF2) (hC hFj hGj hF2 hG2)]
  rw [hD]
  set A := pair j F (corr ε r τ F F)
  set B := pair j F (corr ε r τ G F + corr ε r τ F G) + pair j G (corr ε r τ F F)
  set C := pair j F (corr ε r τ G G) + pair j G (corr ε r τ G F + corr ε r τ F G)
  set D := pair j G (corr ε r τ G G)
  have h1 : HasDerivAt (fun t : ℝ => t * B) B 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const B
  have h2 : HasDerivAt (fun t : ℝ => t ^ 2 * C) 0 0 := by
    simpa using ((hasDerivAt_pow 2 (0 : ℝ)).mul_const C)
  have h3 : HasDerivAt (fun t : ℝ => t ^ 3 * D) 0 0 := by
    simpa using ((hasDerivAt_pow 3 (0 : ℝ)).mul_const D)
  have h := (((hasDerivAt_const (0 : ℝ) A).add h1).add h2).add h3
  rw [zero_add, add_zero, add_zero] at h
  exact h

/-! ### Explicit lattice constants (private copy of `Lattice.lean`'s dyadic counting) -/

/-- The lattice ball `{|k| ≤ R}` as a finset. -/
private def ballF (R : ℝ) : Finset Mode := (finite_ball R).toFinset

private lemma mem_ballF {R : ℝ} {k : Mode} : k ∈ ballF R ↔ absk k ≤ R := by
  simp [ballF]

private lemma ballF_mono {r R : ℝ} (h : r ≤ R) : ballF r ⊆ ballF R := fun _ hk =>
  mem_ballF.2 ((mem_ballF.1 hk).trans h)

private lemma card_ballF_le {R : ℝ} (hR : 1 ≤ R) : ((ballF R).card : ℝ) ≤ 343 * R ^ 3 := by
  have h1 : ballF R ⊆ ballF (⌈R⌉₊ : ℝ) := ballF_mono (Nat.le_ceil R)
  have h2 : (ballF R).card ≤ (2 * ⌈R⌉₊ + 1) ^ 3 := (Finset.card_le_card h1).trans (card_ball_le _)
  have h3 : ((⌈R⌉₊ : ℕ) : ℝ) < R + 1 := Nat.ceil_lt_add_one (by linarith)
  have h4 : ((2 * ⌈R⌉₊ + 1 : ℕ) : ℝ) ≤ 7 * R := by
    push_cast
    linarith
  calc ((ballF R).card : ℝ) ≤ ((2 * ⌈R⌉₊ + 1 : ℕ) : ℝ) ^ 3 := by exact_mod_cast h2
    _ ≤ (7 * R) ^ 3 := pow_le_pow_left₀ (by positivity) h4 3
    _ = 343 * R ^ 3 := by ring

/-- A shell `r < |k| ≤ 2r` has at most `2744 r³` points. -/
private lemma shell_sum_le (ψ : Mode → ℝ) {r B : ℝ} (hr : 1 ≤ r) (hB : 0 ≤ B)
    (hψ : ∀ k, r < absk k → ψ k ≤ B) :
    ∑ k ∈ ballF (2 * r) \ ballF r, ψ k ≤ 2744 * r ^ 3 * B := by
  have h1 : ∀ k ∈ ballF (2 * r) \ ballF r, ψ k ≤ B := fun k hk =>
    hψ k (not_le.1 fun h => (Finset.mem_sdiff.1 hk).2 (mem_ballF.2 h))
  have h2 := Finset.sum_le_card_nsmul _ _ _ h1
  have h3 : ((ballF (2 * r) \ ballF r).card : ℝ) ≤ 2744 * r ^ 3 := by
    have h4 := card_ballF_le (R := 2 * r) (by linarith)
    have h5 : ((ballF (2 * r) \ ballF r).card : ℝ) ≤ (ballF (2 * r)).card := by
      exact_mod_cast Finset.card_le_card Finset.sdiff_subset
    have e : 343 * (2 * r) ^ 3 = 2744 * r ^ 3 := by ring
    linarith
  rw [nsmul_eq_mul] at h2
  exact h2.trans (mul_le_mul_of_nonneg_right h3 hB)

private lemma inv_absSq_le {r : ℝ} {k : Mode} (hr : 0 < r) (h : r < absk k) :
    (absSq k)⁻¹ ≤ (r ^ 2)⁻¹ := by
  rw [← absk_sq]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hr.le h.le 2)

private lemma inv_absSq_sq_le {r : ℝ} {k : Mode} (hr : 0 < r) (h : r < absk k) :
    (absSq k)⁻¹ ^ 2 ≤ (r ^ 4)⁻¹ := by
  have h1 := pow_le_pow_left₀ (inv_nonneg.2 (absSq_nonneg k)) (inv_absSq_le hr h) 2
  have e : ((r ^ 2)⁻¹) ^ 2 = (r ^ 4)⁻¹ := by
    rw [inv_pow]
    ring_nf
  rwa [e] at h1

/-- Dyadic summation of the `|k|⁻⁴` tail, from radius `R` up to `2ⁿR`. -/
private lemma dyadic_tail {ψ : Mode → ℝ} (hψ : ∀ k, ψ k ≤ (absSq k)⁻¹ ^ 2) {R : ℝ} (hR : 1 ≤ R)
    (n : ℕ) :
    ∑ k ∈ ballF (2 ^ n * R), ψ k ≤ ∑ k ∈ ballF R, ψ k + 5488 / R * (1 - (1 / 2) ^ n) := by
  have hR0 : 0 < R := by linarith
  induction n with
  | zero => simp
  | succ n ih =>
    have hr1 : 1 ≤ (2 : ℝ) ^ n * R :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) hR
    have hr0 : 0 < (2 : ℝ) ^ n * R := by linarith
    have e : (2 : ℝ) ^ (n + 1) * R = 2 * (2 ^ n * R) := by ring
    rw [e, ← Finset.sum_sdiff (ballF_mono (show 2 ^ n * R ≤ 2 * (2 ^ n * R) by linarith))]
    have hsh := shell_sum_le ψ hr1 (B := (((2 : ℝ) ^ n * R) ^ 4)⁻¹) (by positivity)
      (fun k hk => (hψ k).trans (inv_absSq_sq_le hr0 hk))
    have e2 : 2744 * ((2 : ℝ) ^ n * R) ^ 3 * (((2 : ℝ) ^ n * R) ^ 4)⁻¹
        = 2744 / R * (1 / 2) ^ n := by
      have : ((1 : ℝ) / 2) ^ n = ((2 : ℝ) ^ n)⁻¹ := by simp
      rw [this]
      field_simp
    have e3 : 5488 / R * (1 - ((1 : ℝ) / 2) ^ (n + 1))
        = 5488 / R * (1 - (1 / 2) ^ n) + 2744 / R * (1 / 2) ^ n := by
      rw [pow_succ]
      ring
    rw [e3]
    rw [e2] at hsh
    linarith

/-- Summability with the tail bound `∑_{|k|>R} |k|⁻⁴ ≤ 5488/R`. -/
private lemma summable_tail {ψ : Mode → ℝ} (h0 : ∀ k, 0 ≤ ψ k)
    (hψ : ∀ k, ψ k ≤ (absSq k)⁻¹ ^ 2) {R : ℝ} (hR : 1 ≤ R) :
    Summable ψ ∧ ∑' k, ψ k ≤ ∑ k ∈ ballF R, ψ k + 5488 / R := by
  have hR0 : 0 < R := by linarith
  have key : ∀ s : Finset Mode, ∑ k ∈ s, ψ k ≤ ∑ k ∈ ballF R, ψ k + 5488 / R := by
    intro s
    obtain ⟨M, hM⟩ := (s.image absk).exists_le
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M (one_lt_two : (1 : ℝ) < 2)
    have hsub : s ⊆ ballF (2 ^ n * R) := fun k hk => mem_ballF.2 (by
      have h1 := hM _ (Finset.mem_image_of_mem absk hk)
      have h2 : (2 : ℝ) ^ n ≤ 2 ^ n * R := le_mul_of_one_le_right (by positivity) hR
      linarith)
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => h0 k).trans ?_
    refine (dyadic_tail hψ hR n).trans ?_
    have h3 : (0 : ℝ) ≤ 5488 / R * (1 / 2) ^ n := by positivity
    have e : 5488 / R * (1 - ((1 : ℝ) / 2) ^ n) = 5488 / R - 5488 / R * (1 / 2) ^ n := by ring
    linarith
  exact ⟨summable_of_sum_le h0 key, Real.tsum_le_of_sum_le h0 key⟩

/-- The weight `|k|⁻²`, zero at `k = 0`. -/
private def w4 (k : Mode) : ℝ := if k = 0 then 0 else (absSq k)⁻¹

private lemma w4_nonneg (k : Mode) : 0 ≤ w4 k := by
  unfold w4
  split_ifs
  · exact le_rfl
  · exact inv_nonneg.2 (absSq_nonneg k)

private lemma w4_le (k : Mode) : w4 k ≤ (absSq k)⁻¹ := by
  unfold w4
  split_ifs
  · exact inv_nonneg.2 (absSq_nonneg k)
  · exact le_rfl

private lemma w4_sq (k : Mode) : w4 k ^ 2 = if k = 0 then 0 else (absSq k)⁻¹ ^ 2 := by
  unfold w4
  split_ifs <;> simp

/-- `∑_{0<|k|≤2ⁿ} |k|⁻² ≤ 2744·2ⁿ`. -/
private lemma low_dyadic (n : ℕ) : ∑ k ∈ ballF (2 ^ n), w4 k ≤ 2744 * 2 ^ n := by
  induction n with
  | zero =>
    have h1 : ∀ k ∈ ballF ((2 : ℝ) ^ 0), w4 k ≤ 1 := fun k _ => by
      by_cases hk : k = 0
      · simp [w4, hk]
      · simpa [w4, hk] using inv_le_one_of_one_le₀ (one_le_absSq hk)
    have h2 := Finset.sum_le_card_nsmul _ _ _ h1
    have h3 := card_ballF_le (R := (2 : ℝ) ^ 0) (by simp)
    rw [nsmul_eq_mul] at h2
    norm_num at h2 h3 ⊢
    have h4 : ((ballF 1).card : ℝ) ≤ 343 := by exact_mod_cast h3
    linarith
  | succ n ih =>
    have hr1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
    have hr0 : (0 : ℝ) < 2 ^ n := by positivity
    have e : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
    rw [e, ← Finset.sum_sdiff (ballF_mono (show (2 : ℝ) ^ n ≤ 2 * 2 ^ n by linarith))]
    have hsh := shell_sum_le w4 hr1 (B := (((2 : ℝ) ^ n) ^ 2)⁻¹) (by positivity)
      (fun k hk => (w4_le k).trans (inv_absSq_le hr0 hk))
    have e2 : 2744 * ((2 : ℝ) ^ n) ^ 3 * (((2 : ℝ) ^ n) ^ 2)⁻¹ = 2744 * 2 ^ n := by
      field_simp
    rw [e2] at hsh
    linarith

/-- `∑_{0<|k|≤R} |k|⁻² ≤ 5488 R`. -/
private lemma low_sum {R : ℝ} (hR : 1 ≤ R) : ∑ k ∈ ballF R, w4 k ≤ 5488 * R := by
  obtain ⟨n, h1, h2⟩ := exists_nat_pow_near hR (one_lt_two : (1 : ℝ) < 2)
  refine (Finset.sum_le_sum_of_subset_of_nonneg (ballF_mono h2.le)
    fun k _ _ => w4_nonneg k).trans ?_
  refine (low_dyadic (n + 1)).trans ?_
  rw [pow_succ]
  linarith

/-! ### Cauchy–Schwarz against the Sobolev norms -/

private lemma cs_tsum {f g : Mode → ℝ} (hf : ∀ k, 0 ≤ f k) (hg : ∀ k, 0 ≤ g k)
    (hf2 : Summable fun k => f k ^ 2) (hg2 : Summable fun k => g k ^ 2) :
    (Summable fun k => f k * g k) ∧
      ∑' k, f k * g k ≤ Real.sqrt (∑' k, f k ^ 2) * Real.sqrt (∑' k, g k ^ 2) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have key := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hpq hf hg
    (by simpa using hf2) (by simpa using hg2)
  simpa [Real.sqrt_eq_rpow] using key

private lemma weighted_cs {s : ℝ} {f : Field} {w a : Mode → ℝ} (hf : InH s f)
    (hw : ∀ k, 0 ≤ w k) (hw2 : Summable fun k => w k ^ 2)
    (ha : ∀ k, a k = w k * (Real.sqrt (sobWeight s k) * ‖f k‖)) :
    Summable a ∧ ∑' k, a k ≤ Real.sqrt (∑' k, w k ^ 2) * hnorm s f := by
  have e : ∀ k, (Real.sqrt (sobWeight s k) * ‖f k‖) ^ 2 = sobWeight s k * ‖f k‖ ^ 2 := fun k => by
    rw [mul_pow, Real.sq_sqrt (sobWeight_nonneg s k)]
  have hf' : Summable fun k => (Real.sqrt (sobWeight s k) * ‖f k‖) ^ 2 := by
    simp only [e]
    exact hf
  obtain rfl : a = _ := funext ha
  have h := cs_tsum hw (fun k => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) hw2 hf'
  simp only [e] at h
  exact h

private lemma sqrt_sob {s : ℝ} {n : ℕ} (hs : s = n) {k : Mode} (hk : k ≠ 0) :
    Real.sqrt (sobWeight s k) = absk k ^ n := by
  have h : (2 * s : ℝ) = ((2 * n : ℕ) : ℝ) := by
    push_cast
    rw [hs]
  rw [sobWeight, ite_eq_right hk, h, Real.rpow_natCast, pow_mul',
    Real.sqrt_sq (pow_nonneg (absk_nonneg k) n)]

private lemma w4_mul_ne (m : ℕ) {s : ℝ} (hs : s = ((m + 2 : ℕ) : ℝ)) (f : Field) {k : Mode}
    (hk : k ≠ 0) :
    absk k ^ m * ‖f k‖ = w4 k * (Real.sqrt (sobWeight s k) * ‖f k‖) := by
  have h : absSq k ≠ 0 := (zero_lt_one.trans_le (one_le_absSq hk)).ne'
  rw [w4, ite_eq_right hk, sqrt_sob hs hk, pow_add, absk_sq]
  field_simp

private lemma w4_mul (m : ℕ) {s : ℝ} (hs : s = ((m + 2 : ℕ) : ℝ)) {f : Field} (hf : f 0 = 0)
    (k : Mode) : absk k ^ m * ‖f k‖ = w4 k * (Real.sqrt (sobWeight s k) * ‖f k‖) := by
  by_cases hk : k = 0
  · subst hk
    simp [w4, hf]
  · exact w4_mul_ne m hs f hk

/-! ### Low and high frequency weights -/

/-- The weight `|k|⁻¹` on `0 < |k| ≤ R`. -/
private def wLo (R : ℝ) (k : Mode) : ℝ := if absk k ≤ R ∧ k ≠ 0 then (absk k)⁻¹ else 0

/-- The weight `|k|⁻²` on `|k| > R`. -/
private def wHi (R : ℝ) (k : Mode) : ℝ := if absk k ≤ R then 0 else (absSq k)⁻¹

private lemma wLo_nonneg (R : ℝ) (k : Mode) : 0 ≤ wLo R k := by
  unfold wLo
  split_ifs
  · exact inv_nonneg.2 (absk_nonneg k)
  · exact le_rfl

private lemma wHi_nonneg (R : ℝ) (k : Mode) : 0 ≤ wHi R k := by
  unfold wHi
  split_ifs
  · exact le_rfl
  · exact inv_nonneg.2 (absSq_nonneg k)

private lemma wLo_sq_le (R : ℝ) (k : Mode) : wLo R k ^ 2 ≤ w4 k := by
  unfold wLo
  split_ifs with h
  · rw [w4, ite_eq_right h.2, inv_pow, absk_sq]
  · simpa using w4_nonneg k

private lemma wLo_sum {R : ℝ} (hR : 1 ≤ R) :
    (Summable fun k => wLo R k ^ 2) ∧ ∑' k, wLo R k ^ 2 ≤ 5488 * R := by
  have h0 : ∀ k ∉ ballF R, wLo R k ^ 2 = 0 := fun k hk => by
    have h : ¬ (absk k ≤ R ∧ k ≠ 0) := fun h => hk (mem_ballF.2 h.1)
    simp [wLo, h]
  refine ⟨summable_of_ne_finset_zero h0, ?_⟩
  rw [tsum_eq_sum h0]
  exact (Finset.sum_le_sum fun k _ => wLo_sq_le R k).trans (low_sum hR)

private lemma wHi_sum {R : ℝ} (hR : 1 ≤ R) :
    (Summable fun k => wHi R k ^ 2) ∧ ∑' k, wHi R k ^ 2 ≤ 5488 / R := by
  have h := summable_tail (ψ := fun k => wHi R k ^ 2) (fun k => sq_nonneg _) (fun k => by
    unfold wHi
    split_ifs
    · simpa using sq_nonneg (absSq k)⁻¹
    · exact le_rfl) hR
  have h0 : ∑ k ∈ ballF R, wHi R k ^ 2 = 0 := Finset.sum_eq_zero fun k hk => by
    simp [wHi, mem_ballF.1 hk]
  rw [h0, zero_add] at h
  exact h

private lemma ne_zero_of_lt {R : ℝ} (hR : 1 ≤ R) {k : Mode} (h : ¬ absk k ≤ R) : k ≠ 0 := by
  rintro rfl
  exact h (by rw [absk_eq_zero.2 rfl]; linarith)

/-- The high-frequency part is controlled by `(5488/R)^{1/2} ‖f‖₂`. -/
private lemma high_part {f : Field} (hf : InH 2 f) {R : ℝ} (hR : 1 ≤ R) :
    (Summable fun k => if absk k ≤ R then 0 else ‖f k‖) ∧
      ∑' k, (if absk k ≤ R then 0 else ‖f k‖) ≤ Real.sqrt (5488 / R) * hnorm 2 f := by
  have hw := wHi_sum hR
  have h := weighted_cs (w := wHi R) (a := fun k => if absk k ≤ R then 0 else ‖f k‖) hf
    (wHi_nonneg R) hw.1 (fun k => by
      by_cases hk : absk k ≤ R
      · simp [hk, wHi]
      · have hk0 := ne_zero_of_lt hR hk
        have h1 := w4_mul_ne 0 (s := 2) (by norm_num) f hk0
        simp only [pow_zero, one_mul, w4, ite_eq_right hk0] at h1
        simpa [hk, wHi] using h1)
  exact ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hw.2)
    (hnorm_nonneg 2 f))⟩

/-- The low-frequency part is controlled by `(5488 R)^{1/2} ‖f‖₁`. -/
private lemma low_part {f : Field} (hf : InH 1 f) (hf0 : f 0 = 0) {R : ℝ} (hR : 1 ≤ R) :
    (Summable fun k => if absk k ≤ R then ‖f k‖ else 0) ∧
      ∑' k, (if absk k ≤ R then ‖f k‖ else 0) ≤ Real.sqrt (5488 * R) * hnorm 1 f := by
  have hw := wLo_sum hR
  have h := weighted_cs (w := wLo R) (a := fun k => if absk k ≤ R then ‖f k‖ else 0) hf
    (wLo_nonneg R) hw.1 (fun k => by
      by_cases hk0 : k = 0
      · subst hk0
        simp [hf0]
      by_cases hk : absk k ≤ R
      · have h1 : absk k ≠ 0 := fun h => hk0 (absk_eq_zero.1 h)
        rw [ite_eq_left hk, wLo, ite_eq_left ⟨hk, hk0⟩, sqrt_sob (n := 1) (by norm_num) hk0,
          pow_one]
        field_simp
      · simp [hk, wLo])
  exact ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hw.2)
    (hnorm_nonneg 1 f))⟩

/-- Splitting at frequency `R ≥ 1`. -/
private lemma wiener_split {u : Field} (hu : MZ 2 u) {R : ℝ} (hR : 1 ≤ R) :
    wiener u ≤ Real.sqrt (5488 * R) * hnorm 1 u + Real.sqrt (5488 / R) * hnorm 2 u := by
  have hL := low_part (hu.inH.mono (by norm_num)) hu.mean hR
  have hH := high_part hu.inH hR
  have e : wiener u = ∑' k, (if absk k ≤ R then ‖u k‖ else 0) +
      ∑' k, (if absk k ≤ R then 0 else ‖u k‖) := by
    rw [← hL.1.tsum_add hH.1, wiener]
    refine tsum_congr fun k => ?_
    split_ifs <;> simp
  rw [e]
  exact add_le_add hL.2 hH.2

/-- Wiener interpolation with the library's explicit constant (`Lattice.lean`'s
`exists_wiener_interp`, constant made explicit): `𝒜(u) ≤ 2√5488 ‖u‖₁^{1/2} ‖u‖₂^{1/2}`. -/
private lemma wiener_interp_le {u : Field} (hu : MZ 2 u) :
    wiener u ≤ 2 * Real.sqrt 5488 * Real.sqrt (hnorm 1 u * hnorm 2 u) := by
  have hu1 : InH 1 u := hu.inH.mono (by norm_num)
  have hA0 := hnorm_nonneg 1 u
  have hAB : hnorm 1 u ≤ hnorm 2 u := hnorm_mono (by norm_num) hu.inH
  rcases hA0.eq_or_lt with hA | hA
  · have h0 : u = 0 := eq_zero_of_hnorm_eq_zero hu1 hu.mean hA.symm
    subst h0
    simp only [wiener, Pi.zero_apply, norm_zero, tsum_zero]
    positivity
  have hB : 0 < hnorm 2 u := hA.trans_le hAB
  have hR : 1 ≤ hnorm 2 u / hnorm 1 u := (one_le_div hA).2 hAB
  refine (wiener_split hu hR).trans (le_of_eq ?_)
  have e1 : (5488 : ℝ) * (hnorm 2 u / hnorm 1 u) * hnorm 1 u ^ 2
      = 5488 * (hnorm 1 u * hnorm 2 u) := by
    field_simp
  have e2 : (5488 : ℝ) / (hnorm 2 u / hnorm 1 u) * hnorm 2 u ^ 2
      = 5488 * (hnorm 1 u * hnorm 2 u) := by
    field_simp
  have h1 : Real.sqrt (5488 * (hnorm 2 u / hnorm 1 u)) * hnorm 1 u
      = Real.sqrt (5488 * (hnorm 1 u * hnorm 2 u)) := by
    rw [← e1, Real.sqrt_mul (mul_nonneg (by norm_num) (div_pos hB hA).le) (_ ^ 2), Real.sqrt_sq hA0]
  have h2 : Real.sqrt (5488 / (hnorm 2 u / hnorm 1 u)) * hnorm 2 u
      = Real.sqrt (5488 * (hnorm 1 u * hnorm 2 u)) := by
    rw [← e2, Real.sqrt_mul (div_pos (by norm_num) (div_pos hB hA)).le (_ ^ 2),
      Real.sqrt_sq hB.le]
  rw [h1, h2, Real.sqrt_mul (by norm_num)]
  ring

/-! ### D. The product leaves -/

private lemma two_rpow_three : (2 : ℝ) ^ (3 : ℝ) = 8 := by
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

private lemma two_rpow_two : (2 : ℝ) ^ (2 : ℝ) = 4 := by
  rw [Real.rpow_two]
  norm_num

/-- **The `H²` product leaf** (LOCAL210 §7 "`‖Qfull(w,w)‖₂ ≤ 4√104 √(ab) c ≤ 41 √(ab) c`";
Body 18 §1; report Step 4: Fourier Young `‖Q(w,w)‖_s ≤ C‖ŵ‖_{ℓ¹}‖w‖_{s+1}` and the Agmon-`ℓ¹`
bound `‖ŵ‖_{ℓ¹} ≤ 2√(ab)` from `Σ_{|k|≤R}|k|^{−2} ≲ R`, `Σ_{|k|>R}|k|^{−4} ≲ 1/R`): for `F ∈ H³`
(`a = ‖F‖₁`, `b = ‖F‖₂`, `c = ‖F‖₃`), `‖Π_F Q_τ(F,F)‖₂ ≤ 32√5488 √(ab) c`.  The sources'
constant `41` is not reached by this route (it would need `𝒜(F) ≤ (41/16)√(ab)`, whereas the
continuum computation, not formalized here, suggests the best `𝒜`-constant is near `2π`); PROVED
with (M4) and the explicit Wiener interpolation `𝒜(F) ≤ 2√5488 √(ab)`. -/
theorem hnorm_two_Qphase_le (τ : ℝ) {F : Field} (hF : MZ 3 F) :
    hnorm 2 (PiF (Qphase τ F F)) ≤
      32 * Real.sqrt 5488 * Real.sqrt (hnorm 1 F * hnorm 2 F) * hnorm 3 F := by
  have hF2 : MZ 2 F := hF.mono' (by norm_num)
  obtain ⟨hI, hQ⟩ := hnorm_Qm_le (phaseM_bdd τ) (σ := 3) (by norm_num) hF hF hF2 hF2
  have e : (3 : ℝ) - 1 = 2 := by norm_num
  rw [e] at hI hQ
  rw [two_rpow_three] at hQ
  have hwF := wiener_interp_le hF2
  have hc := hnorm_nonneg 3 F
  calc hnorm 2 (PiF (Qphase τ F F)) ≤ hnorm 2 (Qm (phaseM τ) F F) := hnorm_PiF_le hI
    _ ≤ 8 * (wiener F * hnorm 3 F + hnorm 3 F * wiener F) := hQ
    _ = 16 * wiener F * hnorm 3 F := by ring
    _ ≤ 16 * (2 * Real.sqrt 5488 * Real.sqrt (hnorm 1 F * hnorm 2 F)) * hnorm 3 F := by gcongr
    _ = _ := by ring

/-- **The `H¹` product leaf** (LOCAL210 §7 "`‖Qfull(w,w)‖₁ ≤ √42 √(ab) b ≤ 7 √(ab) b`"): for
`F ∈ H²`, `‖Π_F Q_τ(F,F)‖₁ ≤ 16√5488 √(ab) b` (sources' `7` replaced, see above).  PROVED. -/
theorem hnorm_one_Qphase_le (τ : ℝ) {F : Field} (hF : MZ 2 F) :
    hnorm 1 (PiF (Qphase τ F F)) ≤
      16 * Real.sqrt 5488 * Real.sqrt (hnorm 1 F * hnorm 2 F) * hnorm 2 F := by
  obtain ⟨hI, hQ⟩ := hnorm_Qm_le (phaseM_bdd τ) (σ := 2) (by norm_num) hF hF hF hF
  have e : (2 : ℝ) - 1 = 1 := by norm_num
  rw [e] at hI hQ
  rw [two_rpow_two] at hQ
  have hwF := wiener_interp_le hF
  have hb := hnorm_nonneg 2 F
  calc hnorm 1 (PiF (Qphase τ F F)) ≤ hnorm 1 (Qm (phaseM τ) F F) := hnorm_PiF_le hI
    _ ≤ 4 * (wiener F * hnorm 2 F + hnorm 2 F * wiener F) := hQ
    _ = 8 * wiener F * hnorm 2 F := by ring
    _ ≤ 8 * (2 * Real.sqrt 5488 * Real.sqrt (hnorm 1 F * hnorm 2 F)) * hnorm 2 F := by gcongr
    _ = _ := by ring

/-- The `H²` product leaf with the library's own constant: `‖Π_F Q_τ(F,F)‖₂ ≤ C √(ab) c`, from
`hnorm_Qm_le` ((M4), `σ = 3`: `‖Q‖₂ ≤ 16 𝒜(F) c`) and `exists_wiener_interp`
(`𝒜(F) ≤ c_I √(ab)`).  PROVED; `C = 16 c_I` with `c_I = 2√5488 ≫ 41/16`. -/
theorem exists_hnorm_two_Qphase_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) (F : Field), MZ 3 F →
    hnorm 2 (PiF (Qphase τ F F)) ≤ C * Real.sqrt (hnorm 1 F * hnorm 2 F) * hnorm 3 F := by
  obtain ⟨cI, hcI, hw⟩ := exists_wiener_interp
  refine ⟨16 * cI, by positivity, fun τ F hF => ?_⟩
  have hF2 : MZ 2 F := hF.mono' (by norm_num)
  obtain ⟨hI, hQ⟩ := hnorm_Qm_le (phaseM_bdd τ) (σ := 3) (by norm_num) hF hF hF2 hF2
  have e : (3 : ℝ) - 1 = 2 := by norm_num
  rw [e] at hI hQ
  rw [two_rpow_three] at hQ
  have hwF := hw F hF2
  have hc := hnorm_nonneg 3 F
  calc hnorm 2 (PiF (Qphase τ F F)) ≤ hnorm 2 (Qm (phaseM τ) F F) := hnorm_PiF_le hI
    _ ≤ 8 * (wiener F * hnorm 3 F + hnorm 3 F * wiener F) := hQ
    _ = 16 * wiener F * hnorm 3 F := by ring
    _ ≤ 16 * (cI * Real.sqrt (hnorm 1 F * hnorm 2 F)) * hnorm 3 F := by gcongr
    _ = 16 * cI * Real.sqrt (hnorm 1 F * hnorm 2 F) * hnorm 3 F := by ring

/-- The `H¹` product leaf with the library's own constant (`σ = 2`: `‖Q‖₁ ≤ 8 𝒜(F) b`).
PROVED; `C = 8 c_I`. -/
theorem exists_hnorm_one_Qphase_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) (F : Field), MZ 2 F →
    hnorm 1 (PiF (Qphase τ F F)) ≤ C * Real.sqrt (hnorm 1 F * hnorm 2 F) * hnorm 2 F := by
  obtain ⟨cI, hcI, hw⟩ := exists_wiener_interp
  refine ⟨8 * cI, by positivity, fun τ F hF => ?_⟩
  obtain ⟨hI, hQ⟩ := hnorm_Qm_le (phaseM_bdd τ) (σ := 2) (by norm_num) hF hF hF hF
  have e : (2 : ℝ) - 1 = 1 := by norm_num
  rw [e] at hI hQ
  rw [two_rpow_two] at hQ
  have hwF := hw F hF
  have hb := hnorm_nonneg 2 F
  calc hnorm 1 (PiF (Qphase τ F F)) ≤ hnorm 1 (Qm (phaseM τ) F F) := hnorm_PiF_le hI
    _ ≤ 4 * (wiener F * hnorm 2 F + hnorm 2 F * wiener F) := hQ
    _ = 8 * wiener F * hnorm 2 F := by ring
    _ ≤ 8 * (cI * Real.sqrt (hnorm 1 F * hnorm 2 F)) * hnorm 2 F := by gcongr
    _ = 8 * cI * Real.sqrt (hnorm 1 F * hnorm 2 F) * hnorm 2 F := by ring

end OVNS.Quant

end
