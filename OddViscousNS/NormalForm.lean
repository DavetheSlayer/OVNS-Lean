import OddViscousNS.RefBounds

/-! # The low-frequency normal form and high-frequency tail (`Lemma fg:lem:nf`, `fg:lem:gap`) -/

open Set
open scoped ENNReal ComplexConjugate
noncomputable section
namespace OVNS

/-- The low nonzero-phase triads. -/
def IsLow (N : ℕ) (a b c : Sgn) (p q : Mode) : Prop :=
  absk p ≤ N ∧ absk q ≤ N ∧ absk (p + q) ≤ N ∧ Phi a b c p q ≠ 0

open Classical in
/-- The multiplier `𝟏_low e^{iτΦ}`. -/
def oscLowM (τ : ℝ) (N : ℕ) : Mult := fun a b c p q =>
  if IsLow N a b c p q then phaseM τ a b c p q else 0

open Classical in
/-- The multiplier `𝟏_{Φ≠0, not low} e^{iτΦ}`. -/
def oscHighM (τ : ℝ) (N : ℕ) : Mult := fun a b c p q =>
  if Phi a b c p q ≠ 0 ∧ ¬ IsLow N a b c p q then phaseM τ a b c p q else 0

open Classical in
/-- The normal-form multiplier `𝟏_low e^{iτΦ}/(i r Φ)`. -/
def nfM (r τ : ℝ) (N : ℕ) : Mult := fun a b c p q =>
  if IsLow N a b c p q then phaseM τ a b c p q / (Complex.I * (r * Phi a b c p q : ℝ)) else 0

/-- The primitive `R_N`. -/
def RN (r t₀ : ℝ) (N : ℕ) (w : ℝ → Field) (t : ℝ) : Field :=
  Qm (nfM r (r * (t + t₀)) N) (w t) (w t)

/-- The time derivative of the reference, as a formal right-hand side. -/
def wdot (g : Field) (w : Field) : Field := fun k =>
  (-(absSq k : ℝ) : ℂ) • w k - Qres w w k + PiS g k

/-- The derivative defect `G_N`. -/
def GN (r t₀ : ℝ) (N : ℕ) (g : Field) (w : ℝ → Field) (t : ℝ) : Field :=
  Qm (nfM r (r * (t + t₀)) N) (wdot g (w t)) (w t) +
    Qm (nfM r (r * (t + t₀)) N) (w t) (wdot g (w t))

/-- The low oscillation. -/
def oscLow (τ : ℝ) (N : ℕ) (w : Field) : Field := Qm (oscLowM τ N) w w

/-- The high oscillation. -/
def oscHigh (τ : ℝ) (N : ℕ) (w : Field) : Field := Qm (oscHighM τ N) w w

private lemma Phi_neg (a b c : Sgn) (p q : Mode) : Phi a b c (-p) (-q) = -Phi a b c p q := by
  have h : -p + -q = -(p + q) := by abel
  simp only [Phi, lam_neg, h]
  ring

private lemma isLow_neg {N : ℕ} {a b c : Sgn} {p q : Mode} :
    IsLow N a b c (-p) (-q) ↔ IsLow N a b c p q := by
  have h : -p + -q = -(p + q) := by abel
  simp only [IsLow, absk_neg, h, Phi_neg, ne_eq, neg_eq_zero]

/-- The finite ball, as a finset. -/
private def ball (N : ℕ) : Finset Mode := (finite_ball N).toFinset

private lemma mem_ball {N : ℕ} {k : Mode} : k ∈ ball N ↔ absk k ≤ N := by
  simp [ball]

/-- There are finitely many low phases, so a positive gap. -/
theorem exists_phase_gap (N : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a b c p q, IsLow N a b c p q → δ ≤ |Phi a b c p q| := by
  classical
  let S : Finset (Sgn × Sgn × Sgn × Mode × Mode) :=
    ((Finset.univ : Finset Sgn) ×ˢ (Finset.univ : Finset Sgn) ×ˢ (Finset.univ : Finset Sgn) ×ˢ
      ball N ×ˢ ball N).filter fun x => Phi x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 ≠ 0
  have hmem : ∀ a b c p q, IsLow N a b c p q → (a, b, c, p, q) ∈ S := fun a b c p q h => by
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, mem_ball]
    exact ⟨⟨h.1, h.2.1⟩, h.2.2.2⟩
  have hpos : ∀ x ∈ S, Phi x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 ≠ 0 := fun x hx =>
    (Finset.mem_filter.1 hx).2
  clear_value S
  by_cases hS : S.Nonempty
  · obtain ⟨x, hx, hmin⟩ := S.exists_min_image
      (fun x => |Phi x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2|) hS
    refine ⟨|Phi x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2|, abs_pos.2 (hpos x hx), ?_⟩
    intro a b c p q h
    exact hmin (a, b, c, p, q) (hmem a b c p q h)
  · exact ⟨1, one_pos, fun a b c p q h => (hS ⟨(a, b, c, p, q), hmem a b c p q h⟩).elim⟩

lemma oscLowM_bdd (τ : ℝ) (N : ℕ) : (oscLowM τ N).Bdd := by
  intro a b c p q
  unfold oscLowM
  split_ifs
  · exact phaseM_bdd τ a b c p q
  · simp

lemma oscHighM_bdd (τ : ℝ) (N : ℕ) : (oscHighM τ N).Bdd := by
  intro a b c p q
  unfold oscHighM
  split_ifs
  · exact phaseM_bdd τ a b c p q
  · simp

lemma oscLowM_real (τ : ℝ) (N : ℕ) : (oscLowM τ N).Real := by
  intro a b c p q
  by_cases h : IsLow N a b c p q
  · simp only [oscLowM, isLow_neg, h, ite_true]
    exact phaseM_real τ a b c p q
  · simp [oscLowM, isLow_neg, h]

lemma oscHighM_real (τ : ℝ) (N : ℕ) : (oscHighM τ N).Real := by
  intro a b c p q
  by_cases h : Phi a b c p q ≠ 0 ∧ ¬ IsLow N a b c p q
  · have h' : Phi a b c (-p) (-q) ≠ 0 ∧ ¬ IsLow N a b c (-p) (-q) := by
      rw [isLow_neg, Phi_neg, neg_ne_zero]
      exact h
    simp only [oscHighM]
    rw [ite_eq_left h, ite_eq_left h']
    exact phaseM_real τ a b c p q
  · have h' : ¬ (Phi a b c (-p) (-q) ≠ 0 ∧ ¬ IsLow N a b c (-p) (-q)) := by
      rw [isLow_neg, Phi_neg, neg_ne_zero]
      exact h
    simp [oscHighM, h, h']

private lemma phase_split (τ : ℝ) (N : ℕ) (a b c : Sgn) (p q : Mode) :
    phaseM τ a b c p q = resM a b c p q + oscLowM τ N a b c p q + oscHighM τ N a b c p q := by
  by_cases h0 : Phi a b c p q = 0
  · have hl : ¬ IsLow N a b c p q := fun h => h.2.2.2 h0
    simp [resM, oscLowM, oscHighM, phaseM, h0, hl]
  · by_cases hl : IsLow N a b c p q
    · simp [resM, oscLowM, oscHighM, h0, hl]
    · simp [resM, oscLowM, oscHighM, h0, hl]

/-- `Qm` is additive in the multiplier, for summable inputs. -/
private lemma Qm_add_mult {m m₁ m₂ : Mult} {f h : Field} (h₁ : m₁.Bdd) (h₂ : m₂.Bdd)
    (hm : ∀ a b c p q, m a b c p q = m₁ a b c p q + m₂ a b c p q) (hf : MZ 2 f) (hh : MZ 2 h) :
    Qm m f h = Qm m₁ f h + Qm m₂ f h := by
  funext k
  rw [Pi.add_apply]
  unfold Qm
  rw [← (summable_Qm_term h₁ hf hh k).tsum_add (summable_Qm_term h₂ hf hh k)]
  refine tsum_congr fun p => ?_
  simp only [hm, add_smul, Finset.sum_add_distrib]

/-- The splitting `Q_τ(w,w) = Q_res(w,w) + Osc_low + Osc_high`. -/
theorem Qphase_split (τ : ℝ) (N : ℕ) {w : Field} (hw : MZ 2 w) :
    Qphase τ w w = Qres w w + oscLow τ N w + oscHigh τ N w := by
  have hb : Mult.Bdd fun a b c p q => resM a b c p q + oscLowM τ N a b c p q := by
    intro a b c p q
    by_cases h0 : Phi a b c p q = 0
    · have hl : ¬ IsLow N a b c p q := fun h => h.2.2.2 h0
      simp [resM, oscLowM, h0, hl]
    · have := oscLowM_bdd τ N a b c p q
      simpa [resM, h0] using this
  have h1 : Qphase τ w w =
      Qm (fun a b c p q => resM a b c p q + oscLowM τ N a b c p q) w w + oscHigh τ N w :=
    Qm_add_mult hb (oscHighM_bdd τ N) (phase_split τ N) hw hw
  have h2 : Qm (fun a b c p q => resM a b c p q + oscLowM τ N a b c p q) w w =
      Qres w w + oscLow τ N w :=
    Qm_add_mult resM_bdd (oscLowM_bdd τ N) (fun _ _ _ _ _ => rfl) hw hw
  rw [h1, h2]

/-! ### Multiplier supports and congruence -/

/-- `Qm` depends on the left input only where the multiplier is nonzero. -/
private lemma Qm_congr_left {m : Mult} {u u' v : Field}
    (h : ∀ a b c p q, m a b c p q ≠ 0 → u p = u' p) : Qm m u v = Qm m u' v := by
  funext k
  refine tsum_congr fun p => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  by_cases hm : m a b c p (k - p) = 0
  · simp [hm]
  · rw [h a b c p (k - p) hm]

/-- `Qm` depends on the right input only where the multiplier is nonzero. -/
private lemma Qm_congr_right {m : Mult} {u v v' : Field}
    (h : ∀ a b c p q, m a b c p q ≠ 0 → v q = v' q) : Qm m u v = Qm m u v' := by
  funext k
  refine tsum_congr fun p => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  by_cases hm : m a b c p (k - p) = 0
  · simp [hm]
  · rw [h a b c p (k - p) hm]

/-! ### The high tail -/

/-- The projection to `|k| > M`. -/
private def hiPart (M : ℕ) (u : Field) : Field := u - lowPass M u

private lemma hiPart_apply (M : ℕ) (u : Field) (k : Mode) :
    hiPart M u k = if absk k ≤ M then 0 else u k := by
  by_cases h : absk k ≤ M <;> simp [hiPart, lowPass, h]

private lemma hiPart_low {M : ℕ} (u : Field) {k : Mode} (h : absk k ≤ M) : hiPart M u k = 0 := by
  rw [hiPart_apply, ite_eq_left h]

private lemma hiPart_high {M : ℕ} (u : Field) {k : Mode} (h : (M : ℝ) < absk k) :
    hiPart M u k = u k := by
  rw [hiPart_apply, ite_eq_right (not_le.2 h)]

private lemma norm_hiPart_le (M : ℕ) (u : Field) (k : Mode) : ‖hiPart M u k‖ ≤ ‖u k‖ := by
  rw [hiPart_apply]
  split_ifs <;> simp

private lemma hiPart_term_le (s : ℝ) (M : ℕ) (u : Field) (k : Mode) :
    sobWeight s k * ‖hiPart M u k‖ ^ 2 ≤ sobWeight s k * ‖u k‖ ^ 2 :=
  mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_hiPart_le M u k) 2)
    (sobWeight_nonneg s k)

private lemma hiPart_inH {s : ℝ} (M : ℕ) {u : Field} (hu : InH s u) : InH s (hiPart M u) :=
  Summable.of_nonneg_of_le
    (fun k => mul_nonneg (sobWeight_nonneg s k) (sq_nonneg _)) (hiPart_term_le s M u) hu

private lemma hiPart_mz (M : ℕ) {u : Field} (hu : MZ 2 u) : MZ 2 (hiPart M u) :=
  ⟨hiPart_inH M hu.inH, hiPart_low u (by simp [absk_eq_zero.2 rfl])⟩

private lemma hnorm_hiPart_le (M : ℕ) {u : Field} (hu : InH 2 u) :
    hnorm 2 (hiPart M u) ≤ hnorm 2 u :=
  Real.sqrt_le_sqrt ((hiPart_inH M hu).tsum_le_tsum (hiPart_term_le 2 M u) hu)

private lemma sobWeight_one_eq {k : Mode} (hk : k ≠ 0) : sobWeight 1 k = absk k ^ 2 := by
  have e : (2 * 1 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  rw [sobWeight, ite_eq_right hk, e, Real.rpow_natCast]

private lemma sobWeight_two_eq {k : Mode} (hk : k ≠ 0) : sobWeight 2 k = absk k ^ 4 := by
  have e : (2 * 2 : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
  rw [sobWeight, ite_eq_right hk, e, Real.rpow_natCast]

/-- For fields above frequency `M`, `‖f‖₁ ≤ M⁻¹ ‖f‖₂`. -/
private lemma hnorm_one_hi_le {M : ℕ} (hM : 1 ≤ M) {u : Field} (hu : InH 2 u)
    (hlow : ∀ k, absk k ≤ M → u k = 0) : hnorm 1 u ≤ (M : ℝ)⁻¹ * hnorm 2 u := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have h1 : InH 1 u := hu.mono (by norm_num)
  have hle : ∑' k, sobWeight 1 k * ‖u k‖ ^ 2 ≤
      ((M : ℝ)⁻¹) ^ 2 * ∑' k, sobWeight 2 k * ‖u k‖ ^ 2 := by
    rw [← tsum_mul_left]
    refine h1.tsum_le_tsum (fun k => ?_) (hu.mul_left _)
    by_cases hk : absk k ≤ M
    · simp [hlow k hk]
    · have hk' : (M : ℝ) < absk k := not_le.1 hk
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [absk_eq_zero.2 rfl] at hk'
        linarith
      rw [sobWeight_one_eq hk0, sobWeight_two_eq hk0, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have hs : (M : ℝ) ^ 2 ≤ absk k ^ 2 := pow_le_pow_left₀ hM0.le hk'.le 2
      have : ((M : ℝ)⁻¹) ^ 2 * absk k ^ 4 = absk k ^ 2 * (absk k ^ 2 / (M : ℝ) ^ 2) := by
        field_simp
      rw [this]
      refine le_mul_of_one_le_right (sq_nonneg _) ?_
      rwa [one_le_div (by positivity)]
  calc hnorm 1 u ≤ Real.sqrt (((M : ℝ)⁻¹) ^ 2 * ∑' k, sobWeight 2 k * ‖u k‖ ^ 2) :=
        Real.sqrt_le_sqrt hle
    _ = (M : ℝ)⁻¹ * hnorm 2 u := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity), hnorm]

/-- Numerics of the tail: `M⁻¹ c₄ + √(c_b/M) ≤ 2 (c₄ + √c_b)/√N` when `N ≤ 3M`. -/
private lemma tail_numerics {cb : ℝ} (hcb : 0 < cb) {N M : ℕ} (hN : 2 ≤ N) (hM : 1 ≤ M)
    (hNM : N ≤ 3 * M) :
    (M : ℝ)⁻¹ * c4 + Real.sqrt (cb / M) ≤ 2 * (c4 + Real.sqrt cb) / Real.sqrt N := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNM' : (N : ℝ) ≤ 3 * M := by exact_mod_cast hNM
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have h1 : (M : ℝ)⁻¹ ≤ 2 / Real.sqrt N := by
    rw [inv_eq_one_div, div_le_div_iff₀ hM0 hs, one_mul]
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    nlinarith
  have h2 : Real.sqrt (cb / M) ≤ 2 * Real.sqrt cb / Real.sqrt N := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    rw [div_pow, mul_pow, Real.sq_sqrt hcb.le, Real.sq_sqrt hN0.le, div_le_div_iff₀ hM0 hN0]
    nlinarith
  calc (M : ℝ)⁻¹ * c4 + Real.sqrt (cb / M)
      ≤ 2 / Real.sqrt N * c4 + 2 * Real.sqrt cb / Real.sqrt N := by
        gcongr
        exact c4_pos.le
    _ = 2 * (c4 + Real.sqrt cb) / Real.sqrt N := by ring

/-- The high tail: universal `C` with `‖Osc_high(w)‖₀ ≤ C N^{-1/2} ‖w‖₂²`. -/
theorem exists_oscHigh_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) (N : ℕ) (w : Field), 2 ≤ N → MZ 2 w →
      InH 0 (oscHigh τ N w) ∧ hnorm 0 (oscHigh τ N w) ≤ C / Real.sqrt N * hnorm 2 w ^ 2 := by
  classical
  obtain ⟨cb, hcb, htail⟩ := exists_wiener_tail
  refine ⟨4 * (c4 + Real.sqrt cb), by have := c4_pos; positivity, fun τ N w hN hw => ?_⟩
  obtain ⟨M, hMdef⟩ : ∃ M, M = N / 2 := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by omega
  have hMN : 2 * M ≤ N := by omega
  have hNM : N ≤ 3 * M := by omega
  have hMN' : (2 : ℝ) * M ≤ N := by exact_mod_cast hMN
  have hMpos : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  let m₁ : Mult := fun a b c p q => if (M : ℝ) < absk p then oscHighM τ N a b c p q else 0
  let m₂ : Mult := fun a b c p q => if (M : ℝ) < absk p then 0 else oscHighM τ N a b c p q
  have hsplit : ∀ a b c p q, oscHighM τ N a b c p q = m₁ a b c p q + m₂ a b c p q := by
    intro a b c p q
    by_cases h : (M : ℝ) < absk p <;> simp [m₁, m₂, h]
  have hb₁ : m₁.Bdd := fun a b c p q => by
    by_cases h : (M : ℝ) < absk p
    · simpa [m₁, h] using oscHighM_bdd τ N a b c p q
    · simp [m₁, h]
  have hb₂ : m₂.Bdd := fun a b c p q => by
    by_cases h : (M : ℝ) < absk p
    · simp [m₂, h]
    · simpa [m₂, h] using oscHighM_bdd τ N a b c p q
  have hsupp₁ : ∀ a b c p q, m₁ a b c p q ≠ 0 → w p = hiPart M w p := fun a b c p q h => by
    by_cases hp : (M : ℝ) < absk p
    · exact (hiPart_high w hp).symm
    · simp [m₁, hp] at h
  have hsupp₂ : ∀ a b c p q, m₂ a b c p q ≠ 0 → w q = hiPart M w q := fun a b c p q h => by
    by_cases hp : (M : ℝ) < absk p
    · simp [m₂, hp] at h
    · have h' : oscHighM τ N a b c p q ≠ 0 := by simpa [m₂, hp] using h
      refine (hiPart_high w ?_).symm
      by_contra hq
      have hp' : absk p ≤ M := not_lt.1 hp
      have hq' : absk q ≤ M := not_lt.1 hq
      have hlow : Phi a b c p q ≠ 0 → IsLow N a b c p q := fun h0 =>
        ⟨by linarith, by linarith, by linarith [absk_add_le p q], h0⟩
      refine h' ?_
      simp only [oscHighM]
      refine ite_eq_right ?_
      rintro ⟨h0, hn⟩
      exact hn (hlow h0)
  have hi := hiPart_mz M hw
  have heq : oscHigh τ N w = Qm m₁ (hiPart M w) w + Qm m₂ w (hiPart M w) := by
    rw [← Qm_congr_left hsupp₁, ← Qm_congr_right hsupp₂]
    exact Qm_add_mult hb₁ hb₂ hsplit hw hw
  obtain ⟨hI₁, hB₁⟩ := hnorm_Qm_zero_le hb₁ hi hw
  obtain ⟨hI₂, hB₂⟩ := hnorm_Qm_zero_le hb₂ hw hi
  have hlowi : ∀ k, absk k ≤ M → hiPart M w k = 0 := fun k hk => hiPart_low w hk
  set b := hnorm 2 w with hb
  have hb0 : 0 ≤ b := hnorm_nonneg 2 w
  have hc1 : hnorm 1 (hiPart M w) ≤ (M : ℝ)⁻¹ * b :=
    (hnorm_one_hi_le hM1 hi.inH hlowi).trans
      (mul_le_mul_of_nonneg_left (hnorm_hiPart_le M hw.inH) (by positivity))
  have hc2 : wiener (hiPart M w) ≤ Real.sqrt (cb / M) * b :=
    (htail M _ hM1 hi hlowi).trans
      (mul_le_mul_of_nonneg_left (hnorm_hiPart_le M hw.inH) (Real.sqrt_nonneg _))
  have hc3 : wiener w ≤ c4 * b := wiener_le hw
  have hc4 : hnorm 1 w ≤ b := hnorm_mono (by norm_num) hw.inH
  have hY : hnorm 1 (hiPart M w) * wiener w + wiener (hiPart M w) * hnorm 1 w ≤
      ((M : ℝ)⁻¹ * c4 + Real.sqrt (cb / M)) * b ^ 2 := by
    have h1 : hnorm 1 (hiPart M w) * wiener w ≤ (M : ℝ)⁻¹ * b * (c4 * b) :=
      mul_le_mul hc1 hc3 (wiener_nonneg _) (by positivity)
    have h2 : wiener (hiPart M w) * hnorm 1 w ≤ Real.sqrt (cb / M) * b * b :=
      mul_le_mul hc2 hc4 (hnorm_nonneg _ _) (by positivity)
    nlinarith
  have hnum := tail_numerics hcb hN hM1 hNM
  have hb2 : 0 ≤ b ^ 2 := sq_nonneg b
  have hY' := mul_le_mul_of_nonneg_right hnum hb2
  rw [heq]
  refine ⟨hI₁.add hI₂, (hnorm_add_le hI₁ hI₂).trans ?_⟩
  have e : 4 * (c4 + Real.sqrt cb) / Real.sqrt N * b ^ 2 =
      2 * (2 * (c4 + Real.sqrt cb) / Real.sqrt N * b ^ 2) := by ring
  rw [e]
  have h3 : wiener w * hnorm 1 (hiPart M w) + hnorm 1 w * wiener (hiPart M w) =
      hnorm 1 (hiPart M w) * wiener w + wiener (hiPart M w) * hnorm 1 w := by ring
  linarith

/-! ### Finite-support multipliers -/

/-- All three legs of the triads carried by `m` lie in the ball. -/
private def LowSupp (N : ℕ) (m : Mult) : Prop :=
  ∀ a b c p q, m a b c p q ≠ 0 → absk p ≤ N ∧ absk q ≤ N ∧ absk (p + q) ≤ N

/-- The triad vertex with helical projections. -/
private def triL (a b c : Sgn) (p q k : Mode) (x y : V3) : V3 :=
  hel c k (vert p q (hel a p x) (hel b q y))

/-- A low multiplier gives a finite sum, for all inputs. -/
private lemma Qm_eq_sum {m : Mult} {N : ℕ} (hs : LowSupp N m) (u v : Field) (k : Mode) :
    Qm m u v k = ∑ p ∈ ball N, ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn,
      m a b c p (k - p) • triL a b c p (k - p) k (u p) (v (k - p)) := by
  refine tsum_eq_sum fun p hp => ?_
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
    Finset.sum_eq_zero fun c _ => ?_
  have h : m a b c p (k - p) = 0 := by_contra fun h => hp (mem_ball.2 (hs _ _ _ _ _ h).1)
  rw [h, zero_smul]

/-- A low multiplier has output in the ball. -/
private lemma Qm_low_zero {m : Mult} {N : ℕ} (hs : LowSupp N m) (u v : Field) {k : Mode}
    (hk : (N : ℝ) < absk k) : Qm m u v k = 0 := by
  rw [Qm_eq_sum hs]
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun a _ =>
    Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ => ?_
  have h : m a b c p (k - p) = 0 := by
    by_contra h
    have := (hs _ _ _ _ _ h).2.2
    rw [add_sub_cancel] at this
    linarith
  rw [h, zero_smul]

private lemma norm_triL_le (a b c : Sgn) (p q k : Mode) (x y : V3) :
    ‖triL a b c p q k x y‖ ≤ ((absk q + absk p) / 2) * (‖x‖ * ‖y‖) := by
  have hn : 0 ≤ absk q + absk p := add_nonneg (absk_nonneg q) (absk_nonneg p)
  calc ‖triL a b c p q k x y‖ ≤ ‖vert p q (hel a p x) (hel b q y)‖ := norm_hel_le _ _ _
    _ ≤ (1 / 2) * (absk q + absk p) * (‖hel a p x‖ * ‖hel b q y‖) := norm_vert_le₁ _ _ _ _
    _ ≤ (1 / 2) * (absk q + absk p) * (‖x‖ * ‖y‖) := by
        gcongr
        · exact norm_hel_le _ _ _
        · exact norm_hel_le _ _ _
    _ = ((absk q + absk p) / 2) * (‖x‖ * ‖y‖) := by ring

/-- The crude bound on a low `Qm`: (number of triads) × (largest term). -/
private lemma norm_Qm_low_le {m : Mult} {N : ℕ} {M A B : ℝ} {u v : Field} (hs : LowSupp N m)
    (hM : ∀ a b c p q, ‖m a b c p q‖ ≤ M) (hM0 : 0 ≤ M) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : ∀ p, absk p ≤ N → ‖u p‖ ≤ A) (hB : ∀ p, absk p ≤ N → ‖v p‖ ≤ B) (k : Mode) :
    ‖Qm m u v k‖ ≤ (2 * N + 1) ^ 3 * 8 * (M * N * A * B) := by
  have hX : 0 ≤ M * N * A * B := by positivity
  have hterm : ∀ p a b c, ‖m a b c p (k - p) • triL a b c p (k - p) k (u p) (v (k - p))‖ ≤
      M * N * A * B := by
    intro p a b c
    by_cases h0 : m a b c p (k - p) = 0
    · simpa [h0] using hX
    obtain ⟨hp, hq, -⟩ := hs _ _ _ _ _ h0
    rw [norm_smul]
    have h1 := norm_triL_le a b c p (k - p) k (u p) (v (k - p))
    have h2 : ‖u p‖ * ‖v (k - p)‖ ≤ A * B :=
      mul_le_mul (hA p hp) (hB _ hq) (norm_nonneg _) hA0
    have h3 : ((absk (k - p) + absk p) / 2) ≤ N := by linarith
    have h4 : ‖triL a b c p (k - p) k (u p) (v (k - p))‖ ≤ N * (A * B) :=
      h1.trans (mul_le_mul h3 h2 (by positivity) (by positivity))
    calc ‖m a b c p (k - p)‖ * ‖triL a b c p (k - p) k (u p) (v (k - p))‖
        ≤ M * (N * (A * B)) := mul_le_mul (hM ..) h4 (norm_nonneg _) hM0
      _ = M * N * A * B := by ring
  rw [Qm_eq_sum hs]
  have hcard : ((ball N).card : ℝ) ≤ (2 * N + 1) ^ 3 := by
    have := card_ball_le N
    exact_mod_cast this
  calc _ ≤ ∑ _p ∈ ball N, ∑ _a : Sgn, ∑ _b : Sgn, ∑ _c : Sgn, M * N * A * B :=
        norm_sum_le_of_le _ fun p _ => norm_sum_le_of_le _ fun a _ =>
          norm_sum_le_of_le _ fun b _ => norm_sum_le_of_le _ fun c _ => hterm p a b c
    _ = (ball N).card * 8 * (M * N * A * B) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ (2 * N + 1) ^ 3 * 8 * (M * N * A * B) := by gcongr

private lemma inH_of_supp {N : ℕ} {F : Field} (hF : ∀ k, (N : ℝ) < absk k → F k = 0) (s : ℝ) :
    InH s F :=
  summable_of_ne_finset_zero (s := ball N) fun k hk => by
    rw [hF k (not_le.1 fun h => hk (mem_ball.2 h))]
    simp

private lemma sobWeight_two_le {N : ℕ} {k : Mode} (hk : absk k ≤ N) :
    sobWeight 2 k ≤ (N : ℝ) ^ 4 := by
  by_cases h0 : k = 0
  · simp [sobWeight, h0]
  · rw [sobWeight_two_eq h0]
    exact pow_le_pow_left₀ (absk_nonneg k) hk 4

private lemma hnorm_two_le_of_supp {N : ℕ} {F : Field} {B : ℝ}
    (hF : ∀ k, (N : ℝ) < absk k → F k = 0) (hB0 : 0 ≤ B) (hB : ∀ k, ‖F k‖ ≤ B) :
    hnorm 2 F ≤ (2 * N + 1) ^ 2 * N ^ 2 * B := by
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have hz : ∀ k ∉ ball N, sobWeight 2 k * ‖F k‖ ^ 2 = 0 := fun k hk => by
    rw [hF k (not_le.1 fun h => hk (mem_ball.2 h))]
    simp
  rw [tsum_eq_sum hz]
  have hcard : ((ball N).card : ℝ) ≤ (2 * N + 1) ^ 3 := by
    have := card_ball_le N
    exact_mod_cast this
  have h1 : (1 : ℝ) ≤ 2 * N + 1 := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  calc ∑ k ∈ ball N, sobWeight 2 k * ‖F k‖ ^ 2 ≤ ∑ _k ∈ ball N, (N : ℝ) ^ 4 * B ^ 2 :=
        Finset.sum_le_sum fun k hk => mul_le_mul (sobWeight_two_le (mem_ball.1 hk))
          (pow_le_pow_left₀ (norm_nonneg _) (hB k) 2) (sq_nonneg _) (by positivity)
    _ = (ball N).card * ((N : ℝ) ^ 4 * B ^ 2) := by simp
    _ ≤ (2 * N + 1) ^ 3 * ((N : ℝ) ^ 4 * B ^ 2) := by gcongr
    _ ≤ (2 * N + 1) * ((2 * N + 1) ^ 3 * ((N : ℝ) ^ 4 * B ^ 2)) :=
        le_mul_of_one_le_left (by positivity) h1
    _ = ((2 * N + 1) ^ 2 * N ^ 2 * B) ^ 2 := by ring

/-! ### The normal-form multiplier -/

private lemma nfM_supp (r τ : ℝ) (N : ℕ) : LowSupp N (nfM r τ N) := by
  intro a b c p q h
  by_cases hl : IsLow N a b c p q
  · exact ⟨hl.1, hl.2.1, hl.2.2.1⟩
  · exact absurd (ite_eq_right hl) h

private lemma oscLowM_supp (τ : ℝ) (N : ℕ) : LowSupp N (oscLowM τ N) := by
  intro a b c p q h
  by_cases hl : IsLow N a b c p q
  · exact ⟨hl.1, hl.2.1, hl.2.2.1⟩
  · exact absurd (ite_eq_right hl) h

private lemma norm_nfM_le {δ r : ℝ} {N : ℕ} (hδ : 0 < δ)
    (hgap : ∀ a b c p q, IsLow N a b c p q → δ ≤ |Phi a b c p q|) (hr : r ≠ 0) (τ : ℝ)
    (a b c : Sgn) (p q : Mode) : ‖nfM r τ N a b c p q‖ ≤ 1 / (|r| * δ) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  by_cases hl : IsLow N a b c p q
  · simp only [nfM]
    rw [ite_eq_left hl, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_mul]
    have h1 := phaseM_bdd τ a b c p q
    have h2 := hgap a b c p q hl
    exact div_le_div₀ zero_le_one h1 (by positivity) (by gcongr)
  · simp only [nfM]
    rw [ite_eq_right hl, norm_zero]
    positivity

private lemma nfM_real (r τ : ℝ) (N : ℕ) : (nfM r τ N).Real := by
  intro a b c p q
  by_cases hl : IsLow N a b c p q
  · simp only [nfM]
    rw [ite_eq_left (isLow_neg.2 hl), ite_eq_left hl, phaseM_real τ a b c p q, Phi_neg, map_div₀,
      map_mul, Complex.conj_I, Complex.conj_ofReal]
    congr 1
    push_cast
    ring
  · simp only [nfM]
    rw [ite_eq_right (fun h => hl (isLow_neg.1 h)), ite_eq_right hl, map_zero]

private lemma conjV_real_smul (s : ℝ) (v : V3) : conjV ((s : ℂ) • v) = (s : ℂ) • conjV v := by
  ext i
  simp [conjV]

private lemma Qm_const_mul (c : ℂ) (m : Mult) (u v : Field) :
    Qm (fun a b d p q => c * m a b d p q) u v = c • Qm m u v := by
  funext k
  rw [Pi.smul_apply]
  unfold Qm
  rw [← tsum_const_smul'']
  refine tsum_congr fun p => ?_
  simp only [Finset.smul_sum, mul_smul]

/-- `Qm` of the normal-form multiplier preserves the admissible class. -/
private lemma adm_nf {δ r : ℝ} {N : ℕ} (hδ : 0 < δ)
    (hgap : ∀ a b c p q, IsLow N a b c p q → δ ≤ |Phi a b c p q|) (hr : r ≠ 0) (τ : ℝ)
    {x : Field} (hx : Adm 2 x) : Adm 3 (Qm (nfM r τ N) x x) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = |r| * δ := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; positivity
  let m : Mult := fun a b d p q => (s : ℂ) * nfM r τ N a b d p q
  have hmb : m.Bdd := fun a b d p q => by
    simp only [m]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
    calc s * ‖nfM r τ N a b d p q‖ ≤ s * (1 / (|r| * δ)) :=
          mul_le_mul_of_nonneg_left (norm_nfM_le hδ hgap hr τ a b d p q) hs0.le
      _ = 1 := by rw [hs]; field_simp
  have hmr : m.Real := fun a b d p q => by
    simp only [m]
    rw [nfM_real r τ N a b d p q, map_mul, Complex.conj_ofReal]
  have hmaj := majorized_Qm (fun _ => m) (fun _ => hmb) (fun _ => hmr)
    (fun _ _ _ _ _ => continuous_const)
  have heq : Qm (nfM r τ N) x x = ((s⁻¹ : ℝ) : ℂ) • Qm m x x := by
    rw [Qm_const_mul, smul_smul]
    have : ((s⁻¹ : ℝ) : ℂ) * (s : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ hs0.ne', Complex.ofReal_one]
    rw [this, one_smul]
  refine ⟨inH_of_supp (N := N) (fun k hk => Qm_low_zero (nfM_supp r τ N) x x hk) 3, ?_, ?_, ?_⟩
  · intro k
    rw [heq, Pi.smul_apply, Pi.smul_apply, conjV_real_smul, hmaj.real 0 x x hx hx k]
  · intro k
    rw [heq, Pi.smul_apply, dotM_smul, hmaj.sol 0 x x hx.mz hx.mz k, mul_zero]
  · rw [heq, Pi.smul_apply, hmaj.mean 0 x x hx.mz hx.mz, smul_zero]

/-! ### Coefficient bounds -/

private lemma sob_zero_term {x : Field} (h0 : x 0 = 0) (k : Mode) :
    sobWeight 0 k * ‖x k‖ ^ 2 = ‖x k‖ ^ 2 := by
  by_cases hk : k = 0
  · simp [hk, h0]
  · simp [sobWeight, hk]

private lemma coeff_le {x : Field} {E : ℝ} (hx : Adm 2 x) (hE : hnorm 0 x ^ 2 ≤ E) (p : Mode) :
    ‖x p‖ ≤ Real.sqrt E := by
  have h := sobWeight_mul_norm_le (hx.inH.mono (by norm_num : (0 : ℝ) ≤ 2)) p
  rw [sob_zero_term hx.mean] at h
  exact Real.le_sqrt_of_sq_le (h.trans hE)

private lemma norm_Qres_le {x : Field} {E : ℝ} (hx : Adm 2 x) (hE : hnorm 0 x ^ 2 ≤ E) (k : Mode) :
    ‖Qres x x k‖ ≤ 2 * absk k * E := by
  have h0 : InH 0 x := hx.inH.mono (by norm_num)
  have hs : Summable fun k => ‖x k‖ ^ 2 := by
    have : Summable fun k => sobWeight 0 k * ‖x k‖ ^ 2 := h0
    simpa only [sob_zero_term hx.mean] using this
  have ht : ∑' k, ‖x k‖ ^ 2 = hnorm 0 x ^ 2 := by
    rw [hnorm_sq h0]
    exact tsum_congr fun k => (sob_zero_term hx.mean k).symm
  have hc := (convR_le_of_l2 (a := fun k => ‖x k‖) (b := fun k => ‖x k‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hs hs k).2
  rw [Real.mul_self_sqrt (by rw [ht]; positivity), ht] at hc
  refine (norm_Qm_le₂ resM_bdd hx.mz hx.mz k).trans ?_
  exact mul_le_mul_of_nonneg_left (hc.trans hE) (by have := absk_nonneg k; positivity)

private lemma norm_force_le {g : Field} {φ : ℝ} (hg : Adm 2 g) (hφ : hnorm 1 g ≤ φ) (k : Mode) :
    ‖PiS g k‖ ≤ φ := by
  have hφ0 : 0 ≤ φ := (hnorm_nonneg 1 g).trans hφ
  have hle : ‖PiS g k‖ ≤ ‖g k‖ := by
    by_cases h : k 2 = 0 <;> simp [PiS, h]
  by_cases hk : k = 0
  · rw [hk, hg.mean, norm_zero] at hle
    rw [hk]
    exact hle.trans hφ0
  refine hle.trans ?_
  have h1 := sobWeight_mul_norm_le (hg.inH.mono (by norm_num : (1 : ℝ) ≤ 2)) k
  have h2 : 1 ≤ sobWeight 1 k := by
    have := sobWeight_mono (by norm_num : (0 : ℝ) ≤ 1) k
    simpa [sobWeight, hk] using this
  have h3 : ‖g k‖ ^ 2 ≤ φ ^ 2 := by
    calc ‖g k‖ ^ 2 ≤ sobWeight 1 k * ‖g k‖ ^ 2 := le_mul_of_one_le_left (sq_nonneg _) h2
      _ ≤ hnorm 1 g ^ 2 := h1
      _ ≤ φ ^ 2 := pow_le_pow_left₀ (hnorm_nonneg _ _) hφ 2
  exact (sq_le_sq₀ (norm_nonneg _) hφ0).1 h3

private lemma norm_wdot_le {g x : Field} {E φ : ℝ} {N : ℕ} (hg : Adm 2 g) (hφ : hnorm 1 g ≤ φ)
    (hx : Adm 2 x) (hE : hnorm 0 x ^ 2 ≤ E) {k : Mode} (hk : absk k ≤ N) :
    ‖wdot g x k‖ ≤ N ^ 2 * Real.sqrt E + 2 * N * E + φ := by
  have hE0 : 0 ≤ E := (sq_nonneg _).trans hE
  have h1 : ‖(-(absSq k : ℝ) : ℂ) • x k‖ ≤ N ^ 2 * Real.sqrt E := by
    rw [norm_smul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (absSq_nonneg k), ← absk_sq]
    exact mul_le_mul (pow_le_pow_left₀ (absk_nonneg k) hk 2) (coeff_le hx hE k) (norm_nonneg _)
      (by positivity)
  have h2 : ‖Qres x x k‖ ≤ 2 * N * E :=
    (norm_Qres_le hx hE k).trans (by gcongr)
  calc ‖wdot g x k‖ ≤ ‖(-(absSq k : ℝ) : ℂ) • x k‖ + ‖Qres x x k‖ + ‖PiS g k‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add h1 h2) (norm_force_le hg hφ k)

/-! ### Time derivative -/

private lemma vert_add_left (p q : Mode) (A A' B : V3) :
    vert p q (A + A') B = vert p q A B + vert p q A' B := by
  have h : (Complex.I * dotM (A + A') q) • B + (Complex.I * dotM B p) • (A + A') =
      ((Complex.I * dotM A q) • B + (Complex.I * dotM B p) • A) +
        ((Complex.I * dotM A' q) • B + (Complex.I * dotM B p) • A') := by
    rw [dotM_add, mul_add, add_smul, smul_add]
    abel
  simp only [vert]
  rw [h, leray_add, smul_add]

private lemma vert_add_right (p q : Mode) (A B B' : V3) :
    vert p q A (B + B') = vert p q A B + vert p q A B' := by
  have h : (Complex.I * dotM A q) • (B + B') + (Complex.I * dotM (B + B') p) • A =
      ((Complex.I * dotM A q) • B + (Complex.I * dotM B p) • A) +
        ((Complex.I * dotM A q) • B' + (Complex.I * dotM B' p) • A) := by
    rw [dotM_add, mul_add, add_smul, smul_add]
    abel
  simp only [vert]
  rw [h, leray_add, smul_add]

private lemma vert_smul_left (s : ℂ) (p q : Mode) (A B : V3) :
    vert p q (s • A) B = s • vert p q A B := by
  have h : (Complex.I * dotM (s • A) q) • B + (Complex.I * dotM B p) • (s • A) =
      s • ((Complex.I * dotM A q) • B + (Complex.I * dotM B p) • A) := by
    rw [dotM_smul, smul_add, smul_smul, smul_smul, smul_smul]
    congr 2
    · ring
    · ring
  simp only [vert]
  rw [h, leray_smul, smul_comm]

private lemma vert_smul_right (s : ℂ) (p q : Mode) (A B : V3) :
    vert p q A (s • B) = s • vert p q A B := by
  have h : (Complex.I * dotM A q) • (s • B) + (Complex.I * dotM (s • B) p) • A =
      s • ((Complex.I * dotM A q) • B + (Complex.I * dotM B p) • A) := by
    rw [dotM_smul, smul_add, smul_smul, smul_smul, smul_smul]
    congr 2
    · ring
    · ring
  simp only [vert]
  rw [h, leray_smul, smul_comm]

/-- `triL` as a continuous real-bilinear map. -/
private def triB (a b c : Sgn) (p q k : Mode) : V3 →L[ℝ] V3 →L[ℝ] V3 :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (triL a b c p q k)
      (fun x x' y => by simp only [triL, hel_add, vert_add_left])
      (fun s x y => by
        simp only [triL]
        rw [← Complex.coe_smul, hel_smul, vert_smul_left, hel_smul, Complex.coe_smul])
      (fun x y y' => by simp only [triL, hel_add, vert_add_right])
      (fun s x y => by
        simp only [triL]
        rw [← Complex.coe_smul, hel_smul, vert_smul_right, hel_smul, Complex.coe_smul]))
    ((absk q + absk p) / 2)
    (fun x y => by
      rw [mul_assoc]
      exact norm_triL_le a b c p q k x y)

private lemma triB_apply (a b c : Sgn) (p q k : Mode) (x y : V3) :
    triB a b c p q k x y = triL a b c p q k x y := rfl

private lemma hasDeriv_term {a b c : Sgn} {p q k : Mode} {X Y : ℝ → V3} {x' y' : V3}
    {m : ℝ → ℂ} {m' : ℂ} {t : ℝ} (hm : HasDerivAt m m' t)
    (hX : HasDerivWithinAt X x' (Ici 0) t) (hY : HasDerivWithinAt Y y' (Ici 0) t) :
    HasDerivWithinAt (fun s => m s • triL a b c p q k (X s) (Y s))
      (m' • triL a b c p q k (X t) (Y t) +
        m t • (triL a b c p q k x' (Y t) + triL a b c p q k (X t) y')) (Ici 0) t := by
  have h := (triB a b c p q k).hasDerivWithinAt_of_bilinear hX hY
  have h' := hm.hasDerivWithinAt.smul h
  simp only [triB_apply] at h'
  convert h' using 1
  rw [add_comm, add_comm (triL a b c p q k x' (Y t))]

private lemma hasDeriv_nfM {r t₀ : ℝ} (hr : r ≠ 0) (N : ℕ) (a b c : Sgn) (p q : Mode) (t : ℝ) :
    HasDerivAt (fun s => nfM r (r * (s + t₀)) N a b c p q)
      (oscLowM (r * (t + t₀)) N a b c p q) t := by
  by_cases hl : IsLow N a b c p q
  · simp only [nfM, oscLowM, phaseM]
    simp only [ite_eq_left hl]
    have hΦ : (Phi a b c p q : ℂ) ≠ 0 := by exact_mod_cast hl.2.2.2
    have h1 : HasDerivAt (fun s : ℝ => r * (s + t₀) * Phi a b c p q) (r * Phi a b c p q) t := by
      have := (((hasDerivAt_id t).add_const t₀).const_mul r).mul_const (Phi a b c p q)
      simpa using this
    have h2 := ((h1.ofReal_comp).const_mul Complex.I).cexp.div_const
      (Complex.I * ((r * Phi a b c p q : ℝ) : ℂ))
    convert h2 using 1
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
    push_cast
    field_simp
  · simp only [nfM, oscLowM]
    simp only [ite_eq_right hl]
    exact hasDerivAt_const t 0

variable {g : Field} {T : ℝ≥0∞} {w : ℝ → Field} {r t₀ : ℝ} {N : ℕ}

/-- `R_N' = Osc_low + G_N`, mode by mode. -/
theorem RN_mode (hr : r ≠ 0) (_hg : Adm 2 g) (hw : RefSol g T w) (k : Mode) {t : ℝ} (ht : 0 ≤ t)
    (htT : ENNReal.ofReal t < T) :
    HasDerivWithinAt (fun s => RN r t₀ N w s k)
      (oscLow (r * (t + t₀)) N (w t) k + GN r t₀ N g w t k) (Ici 0) t := by
  have hmode : ∀ l, HasDerivWithinAt (fun s => w s l) (wdot g (w t) l) (Ici 0) t :=
    fun l => hw.mode l t ht htT
  have key : HasDerivWithinAt
      (fun s => ∑ p ∈ ball N, ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn,
        nfM r (r * (s + t₀)) N a b c p (k - p) • triL a b c p (k - p) k (w s p) (w s (k - p)))
      (∑ p ∈ ball N, ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn,
        (oscLowM (r * (t + t₀)) N a b c p (k - p) •
            triL a b c p (k - p) k (w t p) (w t (k - p)) +
          nfM r (r * (t + t₀)) N a b c p (k - p) •
            (triL a b c p (k - p) k (wdot g (w t) p) (w t (k - p)) +
              triL a b c p (k - p) k (w t p) (wdot g (w t) (k - p))))) (Ici 0) t :=
    HasDerivWithinAt.fun_sum fun p _ => HasDerivWithinAt.fun_sum fun a _ =>
      HasDerivWithinAt.fun_sum fun b _ => HasDerivWithinAt.fun_sum fun c _ =>
        hasDeriv_term (hasDeriv_nfM hr N a b c p (k - p) t) (hmode p) (hmode (k - p))
  have e : (fun s => RN r t₀ N w s k) = fun s => ∑ p ∈ ball N, ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn,
      nfM r (r * (s + t₀)) N a b c p (k - p) • triL a b c p (k - p) k (w s p) (w s (k - p)) :=
    funext fun s => Qm_eq_sum (nfM_supp _ _ _) _ _ _
  rw [e]
  convert key using 1
  rw [oscLow, GN, Pi.add_apply, Qm_eq_sum (oscLowM_supp _ _), Qm_eq_sum (nfM_supp _ _ _),
    Qm_eq_sum (nfM_supp _ _ _)]
  simp only [smul_add, Finset.sum_add_distrib]

/-- `R_N` and `G_N` are finitely supported, admissible, and `O(1/|r|)`. -/
theorem exists_normal_form_bound (N : ℕ) (E φ : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (r t₀ : ℝ) (g : Field) (w : ℝ → Field) (t : ℝ), r ≠ 0 → Adm 2 g →
      hnorm 1 g ≤ φ → Adm 2 (w t) → hnorm 0 (w t) ^ 2 ≤ E →
      Adm 3 (RN r t₀ N w t) ∧ hnorm 2 (RN r t₀ N w t) ≤ K / |r| ∧
      InH 0 (GN r t₀ N g w t) ∧ hnorm 0 (GN r t₀ N g w t) ≤ K / |r| := by
  obtain ⟨δ, hδ, hgap⟩ := exists_phase_gap N
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = Real.sqrt |E| := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = N ^ 2 * A + 2 * N * |E| + |φ| := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = (2 * N + 1) ^ 2 * N ^ 2 * ((2 * N + 1) ^ 3 * 8 * (N / δ)) :=
    ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
  refine ⟨Z * A * (A + 2 * D), by positivity, fun r t₀ g w t hr hg hφ hw hE => ?_⟩
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hE' : hnorm 0 (w t) ^ 2 ≤ |E| := hE.trans (le_abs_self E)
  have hφ' : hnorm 1 g ≤ |φ| := hφ.trans (le_abs_self φ)
  have hwA : ∀ p, ‖w t p‖ ≤ A := fun p => by
    rw [hA]
    exact coeff_le hw hE' p
  have hdot : ∀ p, absk p ≤ N → ‖wdot g (w t) p‖ ≤ D := fun p hp => by
    rw [hD, hA]
    exact norm_wdot_le hg hφ' hw hE' hp
  have hs := nfM_supp r (r * (t + t₀)) N
  have hM := norm_nfM_le hδ hgap hr (r * (t + t₀))
  have hMpos : 0 ≤ 1 / (|r| * δ) := by positivity
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = (2 * (N : ℝ) + 1) ^ 3 * 8 * (1 / (|r| * δ) * N) := ⟨_, rfl⟩
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have hZY : (2 * (N : ℝ) + 1) ^ 2 * N ^ 2 * Y = Z / |r| := by
    rw [hY, hZ]
    field_simp
  have hRk : ∀ k, ‖RN r t₀ N w t k‖ ≤ Y * (A * A) := fun k => by
    have := norm_Qm_low_le hs hM hMpos hA0 hA0 (fun p _ => hwA p) (fun p _ => hwA p) k
    refine this.trans (le_of_eq ?_)
    rw [hY]
    ring
  have hG₁ : ∀ k, ‖Qm (nfM r (r * (t + t₀)) N) (wdot g (w t)) (w t) k‖ ≤ Y * (D * A) := fun k => by
    have := norm_Qm_low_le hs hM hMpos hD0 hA0 hdot (fun p _ => hwA p) k
    refine this.trans (le_of_eq ?_)
    rw [hY]
    ring
  have hG₂ : ∀ k, ‖Qm (nfM r (r * (t + t₀)) N) (w t) (wdot g (w t)) k‖ ≤ Y * (A * D) := fun k => by
    have := norm_Qm_low_le hs hM hMpos hA0 hD0 (fun p _ => hwA p) hdot k
    refine this.trans (le_of_eq ?_)
    rw [hY]
    ring
  have hRs : ∀ k, (N : ℝ) < absk k → RN r t₀ N w t k = 0 := fun k hk => Qm_low_zero hs _ _ hk
  have hGs : ∀ k, (N : ℝ) < absk k → GN r t₀ N g w t k = 0 := fun k hk => by
    simp only [GN, Pi.add_apply]
    rw [Qm_low_zero hs _ _ hk, Qm_low_zero hs _ _ hk, add_zero]
  have hGk : ∀ k, ‖GN r t₀ N g w t k‖ ≤ Y * (2 * (A * D)) := fun k => by
    simp only [GN, Pi.add_apply]
    refine (norm_add_le _ _).trans ?_
    have h1 := hG₁ k
    have h2 := hG₂ k
    have e : Y * (2 * (A * D)) = Y * (D * A) + Y * (A * D) := by ring
    rw [e]
    exact add_le_add h1 h2
  have hR2 := hnorm_two_le_of_supp hRs (by positivity) hRk
  have hG2 := hnorm_two_le_of_supp hGs (by positivity) hGk
  have hAD : 0 ≤ Z / |r| * (A * A) := by positivity
  have hAD' : 0 ≤ Z / |r| * (2 * (A * D)) := by positivity
  have hrew : Z * A * (A + 2 * D) / |r| = Z / |r| * (A * A) + Z / |r| * (2 * (A * D)) := by ring
  have hRle : (2 * (N : ℝ) + 1) ^ 2 * N ^ 2 * (Y * (A * A)) = Z / |r| * (A * A) := by
    rw [← hZY]
    ring
  have hGle : (2 * (N : ℝ) + 1) ^ 2 * N ^ 2 * (Y * (2 * (A * D))) = Z / |r| * (2 * (A * D)) := by
    rw [← hZY]
    ring
  rw [hRle] at hR2
  rw [hGle] at hG2
  refine ⟨adm_nf hδ hgap hr _ hw, ?_, inH_of_supp hGs 0, ?_⟩
  · rw [hrew]
    linarith
  · rw [hrew]
    have := hnorm_mono (by norm_num : (0 : ℝ) ≤ 2) (inH_of_supp hGs 2)
    linarith

/-- `R_N(t)` is mode-wise continuous and supported in `|k| ≤ N`. -/
theorem RN_support (k : Mode) (hk : (N : ℝ) < absk k) (t : ℝ) : RN r t₀ N w t k = 0 :=
  Qm_low_zero (nfM_supp _ _ _) _ _ hk

end OVNS
