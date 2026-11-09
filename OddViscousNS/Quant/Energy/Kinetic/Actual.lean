import OddViscousNS.Quant.Energy.Kinetic.Symbol

/-!
# E4.1–E4.2: the split actual solution and the exchange identities

TeX eq. quant-actual-system: with `x = z − ψ = S + F`,
`F' + AF + 𝓛_τ(S)F = −Π_F Q_τ(F,F) − H_{ψ,F}`, `S' + AS + B(S,S) = h₀`.  Here these are
derived from the library's filtered equation `y' = −Ay − Q_{rt}(y,y) + R(−rt)g`
(`IsHeatSol (filtN r 0) (filtG r 0 g)`) and the corrector `ψ' = −Aψ + Π_F R(−rt)g` (`psi_mode`):

* `actual_mode`: `x' = −Ax − Q_{rt}(y,y) + Π_S g` (`Π_S R(τ)g = Π_S g`, `PiS_rotF`);
  `fast_mode`/`slow_mode` project it (`fastRHS`, `slowRHS`); `actual_adm`: `x(t) ∈ Adm 2`.
* `heatPair_fast`: `F` is a `HeatPair` at `σ ∈ {0,1}` with force `−Π_F Q_{rt}(y,y)` (template
  `heatPair_tildeE`, survey §1.3), whence the kinetic law `fast_energy_identity`
  `‖F t‖₀² + 2∫a_F² = ‖F s‖₀² − 2∫⟨F, Π_F Q_{rt}(y,y)⟩` and the continuity of `‖F‖₀²`, `a_F²`.
* E4.2, the polarized cyclic identities (survey §2.1 (b)): `pair_Qphase_self` (`⟨Q_τ(f,f),f⟩ = 0`
  by the cyclic triad symmetry `Phi_cyc`), the sector vanishing lemmas, and
  `pair_fast_Qphase`: `⟨Π_F Q_τ(x,x), F⟩ = −⟨Q_τ(F,F), S⟩`, i.e. `2⟨Q(S,F),F⟩ = −⟨Q(F,F),S⟩`
  (`pair_exchange`); the resonant part of `⟨Q(F,F),S⟩` vanishes (`PiS_Qres_fast`), so no
  resonant term enters E4.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS

/-! ### Pairing algebra -/

lemma norm_pair_term_le' (σ : ℝ) (c F : Field) (k : Mode) :
    ‖sobWeight σ k * (inner ℂ (c k) (F k)).re‖ ≤ sobWeight σ k * ‖c k‖ * ‖F k‖ := by
  rw [norm_mul, Real.norm_of_nonneg (sobWeight_nonneg σ k), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (sobWeight_nonneg σ k)
  exact (Complex.abs_re_le_norm _).trans (norm_inner_le_norm (𝕜 := ℂ) _ _)

lemma pair_summable {σ : ℝ} {c F : Field} (hc : InH (σ + 1) c) (hF : InH (σ - 1) F) :
    Summable fun k => sobWeight σ k * (inner ℂ (c k) (F k)).re :=
  Summable.of_norm_bounded (pair_le hc hF).1 (norm_pair_term_le' σ c F)

/-- The pairing is additive in the first slot. -/
lemma pair_add_left {σ : ℝ} {c c' F : Field} (hc : InH (σ + 1) c) (hc' : InH (σ + 1) c')
    (hF : InH (σ - 1) F) : pair σ (c + c') F = pair σ c F + pair σ c' F := by
  simp only [pair]
  rw [← (pair_summable hc hF).tsum_add (pair_summable hc' hF)]
  refine tsum_congr fun k => ?_
  rw [Pi.add_apply, inner_add_left, Complex.add_re, mul_add]

lemma pair_neg_right (σ : ℝ) (c F : Field) : pair σ c (-F) = -pair σ c F := by
  simp only [pair, Pi.neg_apply, inner_neg_right, Complex.neg_re, mul_neg, tsum_neg]

/-- A pairing whose terms vanish mode by mode. -/
lemma pair_eq_zero_of_disjoint (σ : ℝ) {Z W : Field} (h : ∀ k, Z k = 0 ∨ W k = 0) :
    pair σ Z W = 0 := by
  simp only [pair]
  rw [← tsum_zero]
  refine tsum_congr fun k => ?_
  rcases h k with h | h <;> simp [h]

/-- A fast test field only sees the fast part of the second slot. -/
lemma pair_PiF_right (σ : ℝ) {F : Field} (hF : PiF F = F) (W : Field) :
    pair σ F (PiF W) = pair σ F W := by
  simp only [pair]
  refine tsum_congr fun k => ?_
  by_cases hk : k 2 = 0
  · rw [fast_zero hF hk]; simp
  · rw [PiF_apply_fast _ hk]

/-! ### Sector vanishing of the phased convection -/

lemma Qphase_slow_slow (τ : ℝ) {S : Field} (hS : PiS S = S) {k : Mode} (hk : k 2 ≠ 0) :
    Qphase τ S S k = 0 :=
  Qm_eq_zero fun p => by
    by_cases hp : p 2 = 0
    · exact Or.inr (slow_zero hS (by simpa [hp] using hk))
    · exact Or.inl (slow_zero hS hp)

lemma Qphase_slow_fast (τ : ℝ) {S F : Field} (hS : PiS S = S) (hF : PiF F = F) {k : Mode}
    (hk : k 2 = 0) : Qphase τ S F k = 0 :=
  Qm_eq_zero fun p => by
    by_cases hp : p 2 = 0
    · exact Or.inr (fast_zero hF (by simp [hk, hp]))
    · exact Or.inl (slow_zero hS hp)

/-- `Lemma lem:energy` for the phased convection: `⟨Q_τ(f,f), f⟩ = 0` on real fields (cyclic
triad symmetry; `Phi_cyc`). -/
theorem pair_Qphase_self (τ : ℝ) {f : Field} (hf : Adm 2 f) : pair 0 f (Qphase τ f f) = 0 := by
  refine pair_zero_of_cyc (tripT (phaseM τ) f f f) (inner_Qm (phaseM_bdd τ) hf.real hf.mz hf.mz)
    (summable_tripT (phaseM_bdd τ) (by norm_num) hf.mz hf.mz hf.mz) ?_
    (tripT_cyc (fun a b c p q => by simp only [phaseM]; rw [Phi_cyc]) f)
  intro p q h
  simp [tripT, h, hel_zero_mode, tau_zero_right]

/-- The phased convection is `Majorized` (constant in time). -/
lemma majorized_Qphase (τ : ℝ) : Majorized (fun _ : ℝ => Qphase τ) :=
  majorized_Qm (fun _ => phaseM τ) (fun _ => phaseM_bdd τ) (fun _ => phaseM_real τ)
    fun _ _ _ _ _ => continuous_const

/-- **E4.2, the exchange identity** (survey §2.1 (b): "`2⟨Q(S,F),F⟩ = −⟨Q(F,F),S⟩`, by polarizing
`⟨Q_τ(x,x), x⟩ = 0`"): for `x = S + F ∈ Adm 2`,
`⟨Q_τ(x,x), F⟩ = −⟨Q_τ(F,F), S⟩`. -/
theorem pair_fast_Qphase (τ : ℝ) {x : Field} (hx : Adm 2 x) :
    pair 0 (PiF x) (Qphase τ x x) = -pair 0 (PiS x) (Qphase τ (PiF x) (PiF x)) := by
  set S := PiS x with hSdef
  set F := PiF x with hFdef
  have hS : Adm 2 S := hx.PiS
  have hF : Adm 2 F := hx.PiF
  have hS' : PiS S = S := by
    funext k; by_cases hk : k 2 = 0 <;> simp [hSdef, PiS, hk]
  have hF' : PiF F = F := by
    funext k; by_cases hk : k 2 = 0 <;> simp [hFdef, PiF, hk]
  have hM := majorized_Qphase τ
  have hx' : x = S + F := (PiS_add_PiF x).symm
  have hsum : MZ 2 (S + F) := by rw [← hx']; exact hx.mz
  have hcomm : Qphase τ F S = Qphase τ S F := Qm_comm_of_symm (phaseM_symm τ) hF.mz hS.mz
  have hsplit : Qphase τ x x = Qphase τ S S + Qphase τ S F + Qphase τ S F + Qphase τ F F := by
    conv_lhs => rw [hx']
    rw [hM.add_left 0 _ _ _ hS.mz hF.mz hsum, hM.add_right 0 _ _ _ hS.mz hS.mz hF.mz,
      hM.add_right 0 _ _ _ hF.mz hS.mz hF.mz, hcomm]
    abel
  have hQ : ∀ {u v : Field}, Adm 2 u → Adm 2 v → InH (0 - 1) (Qphase τ u v) := fun hu hv =>
    ((hnorm_Qm_zero_le (phaseM_bdd τ) hu.mz hv.mz).1).mono (by norm_num)
  have hF1 : InH (0 + 1) F := hF.inH.mono (by norm_num)
  have hS1 : InH (0 + 1) S := hS.inH.mono (by norm_num)
  have hx1 : InH (0 + 1) x := hx.inH.mono (by norm_num)
  have hQx : InH (0 - 1) (Qphase τ x x) := hQ hx hx
  -- the test against `F`
  have h1 : pair 0 F (Qphase τ x x) = 2 * pair 0 F (Qphase τ S F) := by
    rw [hsplit, pair_add hF1 ((hQ hS hS).add (hQ hS hF) |>.add (hQ hS hF)) (hQ hF hF),
      pair_add hF1 ((hQ hS hS).add (hQ hS hF)) (hQ hS hF), pair_add hF1 (hQ hS hS) (hQ hS hF),
      pair_Qphase_self τ hF,
      pair_eq_zero_of_disjoint 0 (fun k => by
        by_cases hk : k 2 = 0
        · exact Or.inl (fast_zero hF' hk)
        · exact Or.inr (Qphase_slow_slow τ hS' hk))]
    ring
  -- the test against `S`
  have h2 : pair 0 S (Qphase τ x x) = pair 0 S (Qphase τ F F) := by
    rw [hsplit, pair_add hS1 ((hQ hS hS).add (hQ hS hF) |>.add (hQ hS hF)) (hQ hF hF),
      pair_add hS1 ((hQ hS hS).add (hQ hS hF)) (hQ hS hF), pair_add hS1 (hQ hS hS) (hQ hS hF),
      pair_Qphase_self τ hS,
      pair_eq_zero_of_disjoint 0 (fun k => by
        by_cases hk : k 2 = 0
        · exact Or.inr (Qphase_slow_fast τ hS' hF' hk)
        · exact Or.inl (slow_zero hS' hk))]
    ring
  -- the cyclic identity for `x`
  have h3 : pair 0 S (Qphase τ x x) + pair 0 F (Qphase τ x x) = 0 := by
    rw [← pair_add_left hS1 hF1 hQx, ← hx', pair_Qphase_self τ hx]
  linarith

/-- `2⟨Q_τ(S,F), F⟩ = −⟨Q_τ(F,F), S⟩`. -/
theorem pair_exchange (τ : ℝ) {x : Field} (hx : Adm 2 x) :
    2 * pair 0 (PiF x) (Qphase τ (PiS x) (PiF x)) =
      -pair 0 (PiS x) (Qphase τ (PiF x) (PiF x)) := by
  have h := pair_fast_Qphase τ hx
  set S := PiS x
  set F := PiF x
  have hS : Adm 2 S := hx.PiS
  have hF : Adm 2 F := hx.PiF
  have hS' : PiS S = S := by
    funext k; by_cases hk : k 2 = 0 <;> simp [S, PiS, hk]
  have hF' : PiF F = F := by
    funext k; by_cases hk : k 2 = 0 <;> simp [F, PiF, hk]
  have hM := majorized_Qphase τ
  have hx' : x = S + F := (PiS_add_PiF x).symm
  have hsum : MZ 2 (S + F) := by rw [← hx']; exact hx.mz
  have hQ : ∀ {u v : Field}, Adm 2 u → Adm 2 v → InH (0 - 1) (Qphase τ u v) := fun hu hv =>
    ((hnorm_Qm_zero_le (phaseM_bdd τ) hu.mz hv.mz).1).mono (by norm_num)
  have hF1 : InH (0 + 1) F := hF.inH.mono (by norm_num)
  have hcomm : Qphase τ F S = Qphase τ S F := Qm_comm_of_symm (phaseM_symm τ) hF.mz hS.mz
  have hsplit : Qphase τ x x = Qphase τ S S + Qphase τ S F + Qphase τ S F + Qphase τ F F := by
    conv_lhs => rw [hx']
    rw [hM.add_left 0 _ _ _ hS.mz hF.mz hsum, hM.add_right 0 _ _ _ hS.mz hS.mz hF.mz,
      hM.add_right 0 _ _ _ hF.mz hS.mz hF.mz, hcomm]
    abel
  rw [hsplit, pair_add hF1 ((hQ hS hS).add (hQ hS hF) |>.add (hQ hS hF)) (hQ hF hF),
    pair_add hF1 ((hQ hS hS).add (hQ hS hF)) (hQ hS hF), pair_add hF1 (hQ hS hS) (hQ hS hF),
    pair_Qphase_self τ hF,
    pair_eq_zero_of_disjoint 0 (fun k => by
      by_cases hk : k 2 = 0
      · exact Or.inl (fast_zero hF' hk)
      · exact Or.inr (Qphase_slow_slow τ hS' hk))] at h
  linarith

namespace Quant

variable {μ φ r : ℝ} {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-! ### E4.1: the split system -/

/-- `Π_S R(τ) g = Π_S g` for solenoidal mean-zero `g` (the filter is the Leray projector on slow
modes, `rot_slow`): the slow force is the unfiltered `g_S`. -/
lemma PiS_rotF {g : Field} (hg : Adm 2 g) (τ : ℝ) : PiS (rotF τ g) = PiS g := by
  funext k
  by_cases hk : k 2 = 0
  · rw [PiS_apply_slow _ hk, PiS_apply_slow _ hk]
    show rot τ k (g k) = g k
    rw [rot_slow τ hk]
    by_cases h0 : k = 0
    · subst h0; simp [leray, hg.mean]
    · exact leray_of_perp h0 (hg.sol k)
  · rw [PiS_apply_fast _ hk, PiS_apply_fast _ hk]

lemma lt_lifespan {t b : ℝ} (htb : t ≤ b) (hbT : ENNReal.ofReal b < Ty) :
    ENNReal.ofReal t < Ty :=
  (ENNReal.ofReal_le_ofReal htb).trans_lt hbT

private lemma conjV_sub (a b : V3) : conjV (a - b) = conjV a - conjV b := by
  ext i; simp [conjV]

private lemma dotM_sub' (a b : V3) (k : Mode) : dotM (a - b) k = dotM a k - dotM b k := by
  simp [dotM, sub_mul, Finset.sum_sub_distrib]

/-- The split field `x(t) = y(t) − ψ(t)` is admissible on the lifespan. -/
lemma actual_adm (h : ActualSol μ φ r g y Ty) {t : ℝ} (ht : 0 ≤ t)
    (htT : ENNReal.ofReal t < Ty) : Adm 2 (actual r g y t) := by
  have h1 := h.sol.adm t ht htT
  have h2 := psi_adm (r := r) (t₀ := 0) h.force_adm t ht
  refine ⟨h1.inH.sub h2.inH, fun k => ?_, fun k => ?_, ?_⟩
  · simp only [actual, Pi.sub_apply, h1.real k, h2.real k, conjV_sub]
  · simp only [actual, Pi.sub_apply, dotM_sub', h1.sol k, h2.sol k, sub_zero]
  · simp [actual, h1.mean, h2.mean]

/-- The mode equation of the split field `x = y − ψ`:
`x' = −Ax − Q_{rt}(y,y) + Π_S g` (TeX eq. quant-actual-system before projecting). -/
theorem actual_mode (h : ActualSol μ φ r g y Ty) (k : Mode) {t : ℝ} (ht : 0 ≤ t)
    (htT : ENNReal.ofReal t < Ty) :
    HasDerivWithinAt (fun s => actual r g y s k)
      ((-(absSq k : ℝ) : ℂ) • actual r g y t k - Qphase (r * t) (y t) (y t) k + PiS g k)
      (Ici 0) t := by
  have h1 := h.sol.mode k t ht htT
  have h2 := (psi_mode (r := r) (t₀ := 0) h.force_adm k t).hasDerivWithinAt (s := Ici 0)
  refine (h1.sub h2).congr_deriv ?_
  have e : filtG r 0 g t k - PiF (filtG r 0 g t) k = PiS (filtG r 0 g t) k := by
    have := congrFun (PiS_add_PiF (filtG r 0 g t)) k
    simp only [Pi.add_apply] at this
    rw [← this]
    abel
  have e2 : PiS (filtG r 0 g t) k = PiS g k := by rw [filtG, PiS_rotF h.force_adm]
  simp only [filtN, add_zero, actual, Pi.sub_apply]
  rw [smul_sub, ← e2, ← e]
  abel

/-- The fast equation `F' = −AF − Π_F Q_{rt}(y,y)` (`fastRHS`). -/
theorem fast_mode (h : ActualSol μ φ r g y Ty) (k : Mode) {t : ℝ} (ht : 0 ≤ t)
    (htT : ENNReal.ofReal t < Ty) :
    HasDerivWithinAt (fun s => PiF (actual r g y s) k) (fastRHS r g y t k) (Ici 0) t := by
  by_cases hk : k 2 = 0
  · have e : (fun s => PiF (actual r g y s) k) = fun _ => 0 :=
      funext fun s => PiF_apply_slow _ hk
    rw [e]
    have e2 : fastRHS r g y t k = 0 := by simp [fastRHS, PiF_apply_slow _ hk]
    rw [e2]
    exact (hasDerivWithinAt_const _ _ _)
  · have e : (fun s => PiF (actual r g y s) k) = fun s => actual r g y s k :=
      funext fun s => PiF_apply_fast _ hk
    rw [e]
    refine (actual_mode h k ht htT).congr_deriv ?_
    simp [fastRHS, PiF_apply_fast _ hk, PiS_apply_fast _ hk]

/-- The slow equation `S' = −AS − Π_S Q_{rt}(y,y) + Π_S g` (`slowRHS`). -/
theorem slow_mode (h : ActualSol μ φ r g y Ty) (k : Mode) {t : ℝ} (ht : 0 ≤ t)
    (htT : ENNReal.ofReal t < Ty) :
    HasDerivWithinAt (fun s => PiS (actual r g y s) k) (slowRHS r g y t k) (Ici 0) t := by
  by_cases hk : k 2 = 0
  · have e : (fun s => PiS (actual r g y s) k) = fun s => actual r g y s k :=
      funext fun s => PiS_apply_slow _ hk
    rw [e]
    refine (actual_mode h k ht htT).congr_deriv ?_
    simp [slowRHS, PiS_apply_slow _ hk]
  · have e : (fun s => PiS (actual r g y s) k) = fun _ => 0 :=
      funext fun s => PiS_apply_fast _ hk
    rw [e]
    have e2 : slowRHS r g y t k = 0 := by simp [slowRHS, PiS_apply_fast _ hk]
    rw [e2]
    exact (hasDerivWithinAt_const _ _ _)

/-- Every mode of `Q_{rt}(y t, y t)` is continuous in `t` on `[0,b]` (from the `HeatPair` of the
filtered solution and the continuity of the filtered force). -/
lemma continuousOn_Qphase_mode (h : ActualSol μ φ r g y Ty) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < Ty) (k : Mode) :
    ContinuousOn (fun t => Qphase (r * t) (y t) (y t) k) (Icc 0 b) := by
  have hP := h.sol.heatPair (majorized_filtN r 0) (goodForce_filtG r 0 h.force_adm) hb hbT
  have h1 := hP.force_cont k
  have h2 : ContinuousOn (fun t => filtG r 0 g t k) (Icc 0 b) := by
    have hc : Continuous fun t : ℝ => rot (-(r * (t + 0))) k (g k) :=
      (continuous_iff_continuousAt.2 fun τ => (hasDerivAt_rot k (g k) τ).continuousAt).comp
        (by fun_prop)
    exact hc.continuousOn
  refine (h2.sub h1).congr fun t ht => ?_
  simp only [Pi.sub_apply, filtN, add_zero]
  abel

lemma continuousOn_actual_mode (h : ActualSol μ φ r g y Ty) {b : ℝ}
    (hbT : ENNReal.ofReal b < Ty) (k : Mode) :
    ContinuousOn (fun t => actual r g y t k) (Icc 0 b) := fun _ ht =>
  ((actual_mode h k ht.1 (lt_lifespan ht.2 hbT)).mono Icc_subset_Ici_self).continuousWithinAt

lemma continuousOn_fast_mode (h : ActualSol μ φ r g y Ty) {b : ℝ}
    (hbT : ENNReal.ofReal b < Ty) (k : Mode) :
    ContinuousOn (fun t => PiF (actual r g y t) k) (Icc 0 b) := fun _ ht =>
  ((fast_mode h k ht.1 (lt_lifespan ht.2 hbT)).mono Icc_subset_Ici_self).continuousWithinAt

lemma continuousOn_slow_mode (h : ActualSol μ φ r g y Ty) {b : ℝ}
    (hbT : ENNReal.ofReal b < Ty) (k : Mode) :
    ContinuousOn (fun t => PiS (actual r g y t) k) (Icc 0 b) := fun _ ht =>
  ((slow_mode h k ht.1 (lt_lifespan ht.2 hbT)).mono Icc_subset_Ici_self).continuousWithinAt

lemma continuousOn_PiF_Qphase_mode (h : ActualSol μ φ r g y Ty) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < Ty) (k : Mode) :
    ContinuousOn (fun t => PiF (Qphase (r * t) (y t) (y t)) k) (Icc 0 b) := by
  by_cases hk : k 2 = 0
  · simp only [PiF_apply_slow _ hk]; exact continuousOn_const
  · simp only [PiF_apply_fast _ hk]; exact continuousOn_Qphase_mode h hb hbT k

lemma continuousOn_PiS_Qphase_mode (h : ActualSol μ φ r g y Ty) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < Ty) (k : Mode) :
    ContinuousOn (fun t => PiS (Qphase (r * t) (y t) (y t)) k) (Icc 0 b) := by
  by_cases hk : k 2 = 0
  · simp only [PiS_apply_slow _ hk]; exact continuousOn_Qphase_mode h hb hbT k
  · simp only [PiS_apply_fast _ hk]; exact continuousOn_const

lemma continuousOn_fastRHS_mode (h : ActualSol μ φ r g y Ty) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < Ty) (k : Mode) :
    ContinuousOn (fun t => fastRHS r g y t k) (Icc 0 b) := by
  have hF := continuousOn_fast_mode h hbT k
  have hQ := continuousOn_PiF_Qphase_mode h hb hbT k
  unfold fastRHS
  exact ((continuousOn_const (c := (-(absSq k : ℝ) : ℂ))).smul hF).sub hQ

lemma continuousOn_slowRHS_mode (h : ActualSol μ φ r g y Ty) {b : ℝ} (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < Ty) (k : Mode) :
    ContinuousOn (fun t => slowRHS r g y t k) (Icc 0 b) := by
  have hS := continuousOn_slow_mode h hbT k
  have hQ := continuousOn_PiS_Qphase_mode h hb hbT k
  unfold slowRHS
  exact (((continuousOn_const (c := (-(absSq k : ℝ) : ℂ))).smul hS).sub hQ).add continuousOn_const

/-- The sup bound of `‖Q_{rt}(y,y)‖₀` on `[0,b]`: `2 c₄ M²` with `M = sup ‖y‖₂`. -/
lemma exists_Qphase_bound (h : ActualSol μ φ r g y Ty) {b : ℝ} (hbT : ENNReal.ofReal b < Ty) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t ∈ Icc 0 b, InH 0 (Qphase (r * t) (y t) (y t)) ∧
      hnorm 0 (Qphase (r * t) (y t) (y t)) ≤ D := by
  obtain ⟨M, hM⟩ := h.sol.exists_bound hbT
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  refine ⟨2 * c4 * max M 0 ^ 2, by have := c4_pos; positivity, fun t ht => ?_⟩
  have hy := (h.sol.adm t ht.1 (lt_lifespan ht.2 hbT)).mz
  obtain ⟨hI, hle⟩ := hnorm_Qm_zero_le (phaseM_bdd (r * t)) hy hy
  refine ⟨hI, hle.trans ?_⟩
  have h1 : hnorm 1 (y t) ≤ max M 0 := (hnorm_mono (by norm_num) hy.inH).trans
    ((hM t ht).trans (le_max_left _ _))
  have h2 : wiener (y t) ≤ c4 * max M 0 :=
    (wiener_le hy).trans (mul_le_mul_of_nonneg_left ((hM t ht).trans (le_max_left _ _)) c4_pos.le)
  have h3 := hnorm_nonneg 1 (y t)
  have h4 := wiener_nonneg (y t)
  have h5 := c4_pos
  nlinarith [mul_le_mul h1 h2 h4 hM0]

/-- **E4.1**: the fast part `F = Π_F x` is a `HeatPair` at `σ ∈ {0, 1}` with force
`−Π_F Q_{rt}(y,y)` (TeX eq. quant-actual-system, first line). -/
theorem heatPair_fast (h : ActualSol μ φ r g y Ty) {σ b : ℝ} (hσ : σ = 0 ∨ σ = 1) (hb : 0 ≤ b)
    (hbT : ENNReal.ofReal b < Ty) :
    HeatPair σ 0 b (fun t => PiF (actual r g y t))
      (fun t => -PiF (Qphase (r * t) (y t) (y t))) := by
  have hσ2 : σ ≤ 2 := by rcases hσ with rfl | rfl <;> norm_num
  have hσ1 : σ - 1 ≤ 0 := by rcases hσ with rfl | rfl <;> norm_num
  refine ⟨fun t ht => ((actual_adm h ht.1 (lt_lifespan ht.2 hbT)).inH.mono hσ2).PiF,
    fun k t ht => ?_, fun k => ?_, ?_⟩
  · refine ((fast_mode h k ht.1 (lt_lifespan ht.2 hbT)).mono Icc_subset_Ici_self).congr_deriv ?_
    simp only [fastRHS, Pi.neg_apply]
    abel
  · exact (continuousOn_PiF_Qphase_mode h hb hbT k).neg
  · obtain ⟨D, hD0, hD⟩ := exists_Qphase_bound h hbT
    calc ∫⁻ t in Icc 0 b, hsE (σ - 1) (-PiF (Qphase (r * t) (y t) (y t)))
        ≤ ∫⁻ _ in Icc 0 b, ENNReal.ofReal (D ^ 2) := by
          refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
          obtain ⟨hI, hle⟩ := hD t ht
          have hI' : InH (σ - 1) (PiF (Qphase (r * t) (y t) (y t))) := (hI.mono hσ1).PiF
          have e : hsE (σ - 1) (-PiF (Qphase (r * t) (y t) (y t))) =
              hsE (σ - 1) (PiF (Qphase (r * t) (y t) (y t))) := by
            simp [hsE]
          rw [e, hsE_eq_ofReal hI']
          refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hnorm_nonneg _ _) ?_ 2)
          exact ((hnorm_mono hσ1 hI.PiF).trans (hnorm_PiF_le hI)).trans hle
      _ < ∞ := by
          rw [setLIntegral_const, Real.volume_Icc]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- The kinetic law of the fast part (TeX: `½(‖F‖₀²)' + a_F² = −Re⟨Q_τ(y,y), F⟩`, integrated):
`‖F t‖₀² + 2∫ₛᵗ a_F² = ‖F s‖₀² − 2∫ₛᵗ ⟨F, Π_F Q_{ru}(y,y)⟩`. -/
theorem fast_energy_identity (h : ActualSol μ φ r g y Ty) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : ENNReal.ofReal t < Ty) :
    fastNorm 0 r g y t ^ 2 + 2 * ∫ u in s..t, fastNorm 1 r g y u ^ 2 =
      fastNorm 0 r g y s ^ 2 + 2 * ∫ u in s..t,
        pair 0 (PiF (actual r g y u)) (-PiF (Qphase (r * u) (y u) (y u))) := by
  have hP := heatPair_fast h (σ := 0) (Or.inl rfl) (hs.trans hst) ht
  have := hP.energy_identity hs hst le_rfl
  rw [zero_add] at this
  exact this

/-- `‖F‖₀²` and `a_F²` are continuous along the solution. -/
theorem continuousOn_fastNorm_sq (h : ActualSol μ φ r g y Ty) {σ b : ℝ} (hσ : σ = 0 ∨ σ = 1)
    (hb : 0 ≤ b) (hbT : ENNReal.ofReal b < Ty) :
    ContinuousOn (fun t => fastNorm σ r g y t ^ 2) (Icc 0 b) :=
  (heatPair_fast h hσ hb hbT).continuousOn_hnorm_sq hb

/-- The dissipation and the force pairing of the kinetic law are integrable. -/
theorem intervalIntegrable_fast (h : ActualSol μ φ r g y Ty) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : ENNReal.ofReal t < Ty) :
    IntervalIntegrable (fun u => fastNorm 1 r g y u ^ 2) volume s t ∧
      IntervalIntegrable (fun u => pair 0 (PiF (actual r g y u))
        (-PiF (Qphase (r * u) (y u) (y u)))) volume s t := by
  have hP := (heatPair_fast h (σ := 0) (Or.inl rfl) (hs.trans hst) ht).mono hs le_rfl
  have h1 := hP.intervalIntegrable_dissipation hst
  rw [zero_add] at h1
  exact ⟨h1, hP.intervalIntegrable_pair hst⟩

end Quant

end OVNS

end
