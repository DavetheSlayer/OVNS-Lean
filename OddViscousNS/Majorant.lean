import OddViscousNS.Young
import OddViscousNS.Helical

/-! # Restricted multiplier majorants (`Lemma fg:lem:maj`) -/

open scoped ComplexConjugate
noncomputable section
namespace OVNS

variable {m : Mult} {f g : Field}

/-! ### The vertex -/

/-- `dotM` is additive in the mode. -/
private lemma dotM_add_mode (v : V3) (p q : Mode) : dotM v (p + q) = dotM v p + dotM v q := by
  simp only [dotM, Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib]

/-- The vertex is bounded by its two scalar couplings. -/
private lemma norm_vert_aux (p q : Mode) (A B : V3) :
    ‖vert p q A B‖ ≤ (1 / 2) * (‖dotM A q‖ * ‖B‖ + ‖dotM B p‖ * ‖A‖) := by
  have h1 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [vert, norm_smul, h1]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine (norm_leray_le _ _).trans ((norm_add_le _ _).trans (le_of_eq ?_))
  simp [norm_smul]

lemma norm_vert_le₁ (p q : Mode) (A B : V3) :
    ‖vert p q A B‖ ≤ (1 / 2) * (absk q + absk p) * (‖A‖ * ‖B‖) := by
  refine (norm_vert_aux p q A B).trans ?_
  nlinarith [mul_le_mul_of_nonneg_right (norm_dotM_le A q) (norm_nonneg B),
    mul_le_mul_of_nonneg_right (norm_dotM_le B p) (norm_nonneg A)]
/-- For transverse inputs, the vertex is bounded by the output frequency. -/
lemma norm_vert_le₂ (p q : Mode) {A B : V3} (hA : dotM A p = 0) (hB : dotM B q = 0) :
    ‖vert p q A B‖ ≤ absk (p + q) * (‖A‖ * ‖B‖) := by
  have e1 : dotM A q = dotM A (p + q) := by rw [dotM_add_mode, hA, zero_add]
  have e2 : dotM B p = dotM B (p + q) := by rw [dotM_add_mode, hB, add_zero]
  refine (norm_vert_aux p q A B).trans ?_
  rw [e1, e2]
  nlinarith [mul_le_mul_of_nonneg_right (norm_dotM_le A (p + q)) (norm_nonneg B),
    mul_le_mul_of_nonneg_right (norm_dotM_le B (p + q)) (norm_nonneg A)]

private lemma vert_add_left (p q : Mode) (A A' B : V3) :
    vert p q (A + A') B = vert p q A B + vert p q A' B := by
  simp only [vert, dotM_add, mul_add, add_smul, smul_add, leray_add]
  abel

private lemma vert_add_right (p q : Mode) (A B B' : V3) :
    vert p q A (B + B') = vert p q A B + vert p q A B' := by
  simp only [vert, dotM_add, mul_add, add_smul, smul_add, leray_add]
  abel

/-! ### Helicity sums -/

/-- A multiplier of size at most one on the two helical components is a contraction. -/
private lemma norm_sum_smul_hel_le (c : Sgn → ℂ) (hc : ∀ s, ‖c s‖ ≤ 1) (k : Mode) (W : V3) :
    ‖∑ s : Sgn, c s • hel s k W‖ ≤ ‖W‖ := by
  have horth : inner ℂ (c true • hel true k W) (c false • hel false k W) = 0 := by
    rw [inner_smul_left, inner_smul_right, ← inner_hel_right, hel_orth (by simp),
      inner_zero_right, mul_zero, mul_zero]
  have h1 : ‖∑ s : Sgn, c s • hel s k W‖ ^ 2 =
      ‖c true • hel true k W‖ ^ 2 + ‖c false • hel false k W‖ ^ 2 := by
    rw [Fintype.sum_bool, @norm_add_sq ℂ, horth]
    simp
  have h2 : ∀ s, ‖c s • hel s k W‖ ^ 2 ≤ ‖hel s k W‖ ^ 2 := fun s => by
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    rw [norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hc s)
  have h3 : ‖hel true k W‖ ^ 2 + ‖hel false k W‖ ^ 2 = ‖leray k W‖ ^ 2 := by
    rw [← norm_sq_hel_sum, Fintype.sum_bool]
  have h4 : ‖leray k W‖ ^ 2 ≤ ‖W‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_leray_le k W) 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
    (by linarith [h2 true, h2 false])

/-- Cauchy-Schwarz in the helicity pair, squared. -/
private lemma sq_sum_norm_hel_le (k : Mode) (v : V3) :
    (∑ a : Sgn, ‖hel a k v‖) ^ 2 ≤ 2 * ‖v‖ ^ 2 := by
  have h1 : ‖hel true k v‖ ^ 2 + ‖hel false k v‖ ^ 2 = ‖leray k v‖ ^ 2 := by
    rw [← norm_sq_hel_sum, Fintype.sum_bool]
  have h2 : ‖leray k v‖ ^ 2 ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_leray_le k v) 2
  rw [Fintype.sum_bool]
  nlinarith [sq_nonneg (‖hel true k v‖ - ‖hel false k v‖)]

/-- `∑_{a,b} ‖H_a A‖ ‖H_b B‖ ≤ 2 ‖A‖ ‖B‖`. -/
private lemma sum_mul_sum_norm_hel_le (p q : Mode) (A B : V3) :
    (∑ a : Sgn, ‖hel a p A‖) * (∑ b : Sgn, ‖hel b q B‖) ≤ 2 * (‖A‖ * ‖B‖) := by
  have hx : 0 ≤ ∑ a : Sgn, ‖hel a p A‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hy : 0 ≤ ∑ b : Sgn, ‖hel b q B‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h : ((∑ a : Sgn, ‖hel a p A‖) * (∑ b : Sgn, ‖hel b q B‖)) ^ 2 ≤
      (2 * (‖A‖ * ‖B‖)) ^ 2 := by
    calc _ = (∑ a : Sgn, ‖hel a p A‖) ^ 2 * (∑ b : Sgn, ‖hel b q B‖) ^ 2 := mul_pow _ _ _
      _ ≤ (2 * ‖A‖ ^ 2) * (2 * ‖B‖ ^ 2) :=
        mul_le_mul (sq_sum_norm_hel_le p A) (sq_sum_norm_hel_le q B) (sq_nonneg _) (by positivity)
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (mul_nonneg hx hy) (by positivity) two_ne_zero).mp h

/-- The triad sum at one `p`, given any bound on the vertex. -/
private lemma norm_triad_le {C : ℝ} (hC : 0 ≤ C) (μ : Sgn → Sgn → Sgn → ℂ)
    (hμ : ∀ a b c, ‖μ a b c‖ ≤ 1) (k p q : Mode) (A B : V3)
    (hW : ∀ a b, ‖vert p q (hel a p A) (hel b q B)‖ ≤ C * (‖hel a p A‖ * ‖hel b q B‖)) :
    ‖∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, μ a b c • hel c k (vert p q (hel a p A) (hel b q B))‖ ≤
      2 * C * (‖A‖ * ‖B‖) := by
  calc _ ≤ ∑ a : Sgn, ∑ b : Sgn,
        ‖∑ c : Sgn, μ a b c • hel c k (vert p q (hel a p A) (hel b q B))‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
    _ ≤ ∑ a : Sgn, ∑ b : Sgn, C * (‖hel a p A‖ * ‖hel b q B‖) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
          (norm_sum_smul_hel_le _ (hμ a b) k _).trans (hW a b)
    _ = C * ((∑ a : Sgn, ‖hel a p A‖) * (∑ b : Sgn, ‖hel b q B‖)) := by
        simp only [Fintype.sum_bool]
        ring
    _ ≤ C * (2 * (‖A‖ * ‖B‖)) :=
        mul_le_mul_of_nonneg_left (sum_mul_sum_norm_hel_le p q A B) hC
    _ = _ := by ring

/-- The summand of `Qm`. -/
private def tri (m : Mult) (f g : Field) (k p : Mode) : V3 :=
  ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn,
    m a b c p (k - p) • hel c k (vert p (k - p) (hel a p (f p)) (hel b (k - p) (g (k - p))))

private lemma norm_tri_le₁ (hm : m.Bdd) (f g : Field) (k p : Mode) :
    ‖tri m f g k p‖ ≤ (absk p + absk (k - p)) * ‖f p‖ * ‖g (k - p)‖ := by
  have h := norm_triad_le (C := (1 / 2) * (absk (k - p) + absk p))
    (by have := absk_nonneg (k - p); have := absk_nonneg p; positivity)
    (fun a b c => m a b c p (k - p)) (fun a b c => hm a b c p (k - p)) k p (k - p) (f p)
    (g (k - p)) (fun a b => norm_vert_le₁ _ _ _ _)
  refine h.trans (le_of_eq ?_)
  ring

private lemma norm_tri_le₂ (hm : m.Bdd) (f g : Field) (k p : Mode) :
    ‖tri m f g k p‖ ≤ 2 * absk k * (‖f p‖ * ‖g (k - p)‖) := by
  have hk : p + (k - p) = k := by abel
  exact norm_triad_le (C := absk k) (absk_nonneg k)
    (fun a b c => m a b c p (k - p)) (fun a b c => hm a b c p (k - p)) k p (k - p) (f p)
    (g (k - p)) (fun a b => by
      have h := norm_vert_le₂ p (k - p) (dotM_hel a p (f p)) (dotM_hel b (k - p) (g (k - p)))
      rwa [hk] at h)

/-! ### Summability and Young -/

/-- The sequence `|k| ‖x k‖`. -/
private def gr (x : Field) : Mode → ℝ := fun k => absk k * ‖x k‖

private lemma gr_nonneg (x : Field) (k : Mode) : 0 ≤ gr x k :=
  mul_nonneg (absk_nonneg k) (norm_nonneg _)

private lemma gr_sq {x : Field} (hx : x 0 = 0) (k : Mode) :
    gr x k ^ 2 = sobWeight 1 k * ‖x k‖ ^ 2 := by
  by_cases hk : k = 0
  · subst hk
    simp [sobWeight, gr, hx]
  · rw [sobWeight, ite_eq_right hk, mul_one, Real.rpow_two, gr, mul_pow]

private lemma gr_summable {x : Field} (hx : MZ 2 x) : Summable fun k => gr x k ^ 2 := by
  have e : (fun k => gr x k ^ 2) = fun k => sobWeight 1 k * ‖x k‖ ^ 2 := funext (gr_sq hx.mean)
  rw [e]
  exact hx.inH.mono (by norm_num)

private lemma gr_sqrt {x : Field} (hx : MZ 2 x) :
    Real.sqrt (∑' k, gr x k ^ 2) = hnorm 1 x := by
  have e : (fun k => gr x k ^ 2) = fun k => sobWeight 1 k * ‖x k‖ ^ 2 := funext (gr_sq hx.mean)
  rw [e, hnorm]

/-- `‖x‖ * (|·| ‖y‖)` in `ℓ²`, with the `ℓ²` norm bounded by `𝒜(x) ‖y‖₁`. -/
private lemma young_nm_gr {x y : Field} (hx : MZ 2 x) (hy : MZ 2 y) :
    (∀ k, Summable fun p => ‖x p‖ * gr y (k - p)) ∧
      Summable (fun k => convR (fun p => ‖x p‖) (gr y) k ^ 2) ∧
      Real.sqrt (∑' k, convR (fun p => ‖x p‖) (gr y) k ^ 2) ≤ wiener x * hnorm 1 y := by
  obtain ⟨h1, h2, h3⟩ := young_l1_l2 (a := fun p => ‖x p‖) (b := gr y) (fun _ => norm_nonneg _)
    (gr_nonneg y) (summable_wiener hx.inH) (gr_summable hy)
  refine ⟨h1, h2, ?_⟩
  calc _ ≤ Real.sqrt (wiener x ^ 2 * ∑' k, gr y k ^ 2) := Real.sqrt_le_sqrt h3
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (wiener_nonneg x), gr_sqrt hy]

/-- `(|·| ‖x‖) * ‖y‖` in `ℓ²`, with the `ℓ²` norm bounded by `‖x‖₁ 𝒜(y)`. -/
private lemma young_gr_nm {x y : Field} (hx : MZ 2 x) (hy : MZ 2 y) :
    (∀ k, Summable fun p => gr x p * ‖y (k - p)‖) ∧
      Summable (fun k => convR (gr x) (fun p => ‖y p‖) k ^ 2) ∧
      Real.sqrt (∑' k, convR (gr x) (fun p => ‖y p‖) k ^ 2) ≤ hnorm 1 x * wiener y := by
  obtain ⟨h1, h2, h3⟩ := young_nm_gr hy hx
  have hc : convR (gr x) (fun p => ‖y p‖) = convR (fun p => ‖y p‖) (gr x) :=
    funext (convR_comm _ _)
  refine ⟨fun k => ?_, by rwa [hc], by rw [hc, mul_comm]; exact h3⟩
  refine ((Equiv.subLeft k).summable_iff.2 (h1 k)).congr fun p => ?_
  simp [mul_comm]

/-- Summability of the first majorant. -/
private lemma summable_maj₁ (hf : MZ 2 f) (hg : MZ 2 g) (k : Mode) :
    Summable fun p => (absk p + absk (k - p)) * ‖f p‖ * ‖g (k - p)‖ := by
  refine (((young_gr_nm hf hg).1 k).add ((young_nm_gr hf hg).1 k)).congr fun p => ?_
  simp only [gr]
  ring

/-- The first majorant as a sum of two convolutions. -/
private lemma tsum_maj₁ (hf : MZ 2 f) (hg : MZ 2 g) (k : Mode) :
    ∑' p, (absk p + absk (k - p)) * ‖f p‖ * ‖g (k - p)‖ =
      convR (gr f) (fun p => ‖g p‖) k + convR (fun p => ‖f p‖) (gr g) k := by
  rw [convR, convR, ← ((young_gr_nm hf hg).1 k).tsum_add ((young_nm_gr hf hg).1 k)]
  refine tsum_congr fun p => ?_
  simp only [gr]
  ring

/-- Summability of the second majorant. -/
private lemma summable_maj₂ (hf : MZ 2 f) (hg : MZ 2 g) (k : Mode) :
    Summable fun p => ‖f p‖ * ‖g (k - p)‖ :=
  Summable.of_nonneg_of_le (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun _ => mul_le_mul_of_nonneg_left
      ((summable_wiener hg.inH).le_tsum _ fun _ _ => norm_nonneg _) (norm_nonneg _))
    ((summable_wiener hf.inH).mul_right (∑' q, ‖g q‖))

/-- The triad summand of `Qm` is summable for `H²` inputs and bounded `m`. -/
lemma summable_Qm_term_of_bdd (hm : m.Bdd) (hf : MZ 2 f) (hg : MZ 2 g) (k : Mode) :
    Summable fun p => ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn,
      m a b c p (k - p) • hel c k (vert p (k - p) (hel a p (f p)) (hel b (k - p) (g (k - p)))) :=
  Summable.of_norm_bounded (summable_maj₁ hf hg k) (norm_tri_le₁ hm f g k)

/-- The triad summand of `Qm` is summable for `H²` inputs. -/
lemma summable_Qm_term (hm : m.Bdd) (hf : MZ 2 f) (hg : MZ 2 g) (k : Mode) :
    Summable fun p => ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn,
      m a b c p (k - p) • hel c k (vert p (k - p) (hel a p (f p)) (hel b (k - p) (g (k - p)))) :=
  summable_Qm_term_of_bdd hm hf hg k

private lemma summable_tri (hm : m.Bdd) (hf : MZ 2 f) (hg : MZ 2 g) (k : Mode) :
    Summable (tri m f g k) :=
  summable_Qm_term_of_bdd hm hf hg k

/-- First majorant of `(fg:eq:maj1)`. -/
theorem norm_Qm_le₁ (hm : m.Bdd) (hf : MZ 2 f) (hg : MZ 2 g) (k : Mode) :
    ‖Qm m f g k‖ ≤ ∑' p, (absk p + absk (k - p)) * ‖f p‖ * ‖g (k - p)‖ :=
  tsum_of_norm_bounded (summable_maj₁ hf hg k).hasSum (norm_tri_le₁ hm f g k)
/-- Second majorant of `(fg:eq:maj1)`. -/
theorem norm_Qm_le₂ (hm : m.Bdd) (hf : MZ 2 f) (hg : MZ 2 g) (k : Mode) :
    ‖Qm m f g k‖ ≤ 2 * absk k * ∑' p, ‖f p‖ * ‖g (k - p)‖ := by
  rw [← tsum_mul_left]
  exact tsum_of_norm_bounded ((summable_maj₂ hf hg k).mul_left _).hasSum (norm_tri_le₂ hm f g k)

/-! ### Sobolev bounds from the pointwise majorants -/

/-- (M3) from the first pointwise majorant alone. -/
private lemma hnorm_zero_of_pointwise {F : Field} (hf : MZ 2 f) (hg : MZ 2 g)
    (h : ∀ k, ‖F k‖ ≤ ∑' p, (absk p + absk (k - p)) * ‖f p‖ * ‖g (k - p)‖) :
    InH 0 F ∧ hnorm 0 F ≤ hnorm 1 f * wiener g + wiener f * hnorm 1 g := by
  obtain ⟨-, hU2, hU3⟩ := young_gr_nm hf hg
  obtain ⟨-, hV2, hV3⟩ := young_nm_gr hf hg
  set U : Mode → ℝ := convR (gr f) (fun p => ‖g p‖) with hU
  set V : Mode → ℝ := convR (fun p => ‖f p‖) (gr g) with hV
  have hU0 : ∀ k, 0 ≤ U k := fun k =>
    tsum_nonneg fun p => mul_nonneg (gr_nonneg f p) (norm_nonneg _)
  have hV0 : ∀ k, 0 ≤ V k := fun k =>
    tsum_nonneg fun p => mul_nonneg (norm_nonneg _) (gr_nonneg g _)
  have hM := Real.Lp_add_le_tsum_of_nonneg (p := 2) one_le_two hU0 hV0
    (by simpa only [Real.rpow_two] using hU2) (by simpa only [Real.rpow_two] using hV2)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hM
  obtain ⟨hM1, hM2⟩ := hM
  have hL0 : ∀ k, 0 ≤ sobWeight 0 k * ‖F k‖ ^ 2 := fun k =>
    mul_nonneg (sobWeight_nonneg 0 k) (sq_nonneg _)
  have key : ∀ k, sobWeight 0 k * ‖F k‖ ^ 2 ≤ (U k + V k) ^ 2 := fun k => by
    have hw : sobWeight 0 k ≤ 1 := by
      unfold sobWeight
      split_ifs <;> simp
    have h1 : ‖F k‖ ≤ U k + V k := (h k).trans_eq (tsum_maj₁ hf hg k)
    calc sobWeight 0 k * ‖F k‖ ^ 2 ≤ 1 * ‖F k‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hw (sq_nonneg _)
      _ ≤ (U k + V k) ^ 2 := by
          rw [one_mul]
          exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hF : InH 0 F := Summable.of_nonneg_of_le hL0 key hM1
  refine ⟨hF, ?_⟩
  calc hnorm 0 F ≤ Real.sqrt (∑' k, (U k + V k) ^ 2) :=
        Real.sqrt_le_sqrt (hF.tsum_le_tsum key hM1)
    _ ≤ _ := by linarith

/-- `|k|^{2(σ-1)} |k|² = |k|^{2σ}` away from the origin. -/
private lemma weight_step (σ : ℝ) {k : Mode} (hk : k ≠ 0) :
    sobWeight (σ - 1) k * absk k ^ 2 = absk k ^ (2 * σ) := by
  have h : 0 < absk k := one_pos.trans_le (one_le_absk hk)
  rw [sobWeight, ite_eq_right hk, ← Real.rpow_two, ← Real.rpow_add h]
  congr 1
  ring

/-- (M4) from the second pointwise majorant alone. -/
private lemma hnorm_of_pointwise {F : Field} {σ : ℝ} (hσ : 1 ≤ σ) (hf : MZ σ f) (hg : MZ σ g)
    (hf2 : MZ 2 f) (hg2 : MZ 2 g)
    (h : ∀ k, ‖F k‖ ≤ 2 * absk k * ∑' p, ‖f p‖ * ‖g (k - p)‖) :
    InH (σ - 1) F ∧
      hnorm (σ - 1) F ≤ 2 ^ σ * (wiener f * hnorm σ g + hnorm σ f * wiener g) := by
  obtain ⟨hs, hb⟩ := product_estimate hσ hf hg (summable_wiener hf2.inH) (summable_wiener hg2.inH)
  set W : Mode → ℝ := fun k => absk k ^ (2 * σ) * (∑' p, ‖f p‖ * ‖g (k - p)‖) ^ 2 with hW
  have hW0 : ∀ k, 0 ≤ W k := fun k =>
    mul_nonneg (Real.rpow_nonneg (absk_nonneg k) _) (sq_nonneg _)
  have hL0 : ∀ k, 0 ≤ sobWeight (σ - 1) k * ‖F k‖ ^ 2 := fun k =>
    mul_nonneg (sobWeight_nonneg _ k) (sq_nonneg _)
  have key : ∀ k, sobWeight (σ - 1) k * ‖F k‖ ^ 2 ≤ 4 * W k := fun k => by
    by_cases hk : k = 0
    · have h0 : sobWeight (σ - 1) k = 0 := by simp [sobWeight, hk]
      rw [h0, zero_mul]
      exact mul_nonneg (by norm_num) (hW0 k)
    calc sobWeight (σ - 1) k * ‖F k‖ ^ 2
        ≤ sobWeight (σ - 1) k * (2 * absk k * ∑' p, ‖f p‖ * ‖g (k - p)‖) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (h k) 2)
            (sobWeight_nonneg _ k)
      _ = 4 * (sobWeight (σ - 1) k * absk k ^ 2) * (∑' p, ‖f p‖ * ‖g (k - p)‖) ^ 2 := by ring
      _ = 4 * W k := by
          rw [weight_step σ hk, hW]
          ring
  have hs4 : Summable fun k => 4 * W k := hs.mul_left 4
  have hF : InH (σ - 1) F := Summable.of_nonneg_of_le hL0 key hs4
  refine ⟨hF, ?_⟩
  have h2 : (2 : ℝ) ^ σ = 2 * 2 ^ (σ - 1) := by
    rw [mul_comm, ← Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    ring
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  calc hnorm (σ - 1) F ≤ Real.sqrt (∑' k, 4 * W k) :=
        Real.sqrt_le_sqrt (hF.tsum_le_tsum key hs4)
    _ = 2 * Real.sqrt (∑' k, W k) := by
        rw [tsum_mul_left, Real.sqrt_mul (by norm_num), h4]
    _ ≤ 2 * (2 ^ (σ - 1) * (wiener f * hnorm σ g + hnorm σ f * wiener g)) :=
        mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by
        rw [h2]
        ring

/-- (M3): `‖Q^♯(f,g)‖₀ ≤ ‖f‖₁ 𝒜(g) + 𝒜(f) ‖g‖₁`. -/
theorem hnorm_Qm_zero_le (hm : m.Bdd) (hf : MZ 2 f) (hg : MZ 2 g) :
    InH 0 (Qm m f g) ∧ hnorm 0 (Qm m f g) ≤ hnorm 1 f * wiener g + wiener f * hnorm 1 g :=
  hnorm_zero_of_pointwise hf hg (norm_Qm_le₁ hm hf hg)
/-- (M4): for `σ ≥ 1`, `‖Q^♯(f,g)‖_{σ-1} ≤ 2^σ (𝒜(f)‖g‖_σ + ‖f‖_σ 𝒜(g))`. -/
theorem hnorm_Qm_le (hm : m.Bdd) {σ : ℝ} (hσ : 1 ≤ σ) (hf : MZ σ f) (hg : MZ σ g)
    (hf2 : MZ 2 f) (hg2 : MZ 2 g) :
    InH (σ - 1) (Qm m f g) ∧
      hnorm (σ - 1) (Qm m f g) ≤ 2 ^ σ * (wiener f * hnorm σ g + hnorm σ f * wiener g) :=
  hnorm_of_pointwise hσ hf hg hf2 hg2 (norm_Qm_le₂ hm hf2 hg2)

/-- The same (M3), (M4) bounds for any `Majorized` family at `H²` regularity. -/
theorem Majorized.hnorm_zero_le {N : ℝ → Field → Field → Field} (hN : Majorized N) (t : ℝ)
    (hf : MZ 2 f) (hg : MZ 2 g) :
    InH 0 (N t f g) ∧ hnorm 0 (N t f g) ≤ hnorm 1 f * wiener g + wiener f * hnorm 1 g :=
  hnorm_zero_of_pointwise hf hg fun k => hN.maj₁ t f g k hf hg
theorem Majorized.hnorm_le {N : ℝ → Field → Field → Field} (hN : Majorized N) (t : ℝ) {σ : ℝ}
    (hσ : 1 ≤ σ) (hf : MZ σ f) (hg : MZ σ g) (hf2 : MZ 2 f) (hg2 : MZ 2 g) :
    InH (σ - 1) (N t f g) ∧
      hnorm (σ - 1) (N t f g) ≤ 2 ^ σ * (wiener f * hnorm σ g + hnorm σ f * wiener g) :=
  hnorm_of_pointwise hσ hf hg hf2 hg2 fun k => hN.maj₂ t f g k hf2 hg2

/-! ### The concrete multipliers -/

/-- The phase is odd under `(p, q) ↦ (-p, -q)`. -/
private lemma Phi_neg (a b c : Sgn) (p q : Mode) : Phi a b c (-p) (-q) = -Phi a b c p q := by
  simp only [Phi, ← neg_add, lam_neg]
  ring

lemma phaseM_bdd (τ : ℝ) : (phaseM τ).Bdd := fun a b c p q => by
  rw [phaseM, mul_comm, Complex.norm_exp_ofReal_mul_I]
lemma phaseM_real (τ : ℝ) : (phaseM τ).Real := fun a b c p q => by
  simp only [phaseM, Phi_neg, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
  congr 1
  push_cast
  ring
lemma resM_bdd : resM.Bdd := fun a b c p q => by
  unfold resM
  split_ifs <;> simp
lemma resM_real : resM.Real := fun a b c p q => by
  by_cases h : Phi a b c p q = 0
  · simp [resM, Phi_neg, h]
  · simp [resM, Phi_neg, h]

/-! ### Algebra of `Qm` -/

private lemma tri_add_left (m : Mult) (f f' g : Field) (k p : Mode) :
    tri m (f + f') g k p = tri m f g k p + tri m f' g k p := by
  simp only [tri, Pi.add_apply, hel_add, vert_add_left, smul_add, Finset.sum_add_distrib]

private lemma tri_add_right (m : Mult) (f g g' : Field) (k p : Mode) :
    tri m f (g + g') k p = tri m f g k p + tri m f g' k p := by
  simp only [tri, Pi.add_apply, hel_add, vert_add_right, smul_add, Finset.sum_add_distrib]

private lemma MZ.sub' {s : ℝ} {x y : Field} (hx : MZ s x) (hy : MZ s y) : MZ s (x - y) :=
  ⟨hx.inH.sub hy.inH, by simp [hx.mean, hy.mean]⟩

private lemma Qm_add_left (hm : m.Bdd) {f' : Field} (hf : MZ 2 f) (hf' : MZ 2 f') (hg : MZ 2 g) :
    Qm m (f + f') g = Qm m f g + Qm m f' g := by
  funext k
  change ∑' p, tri m (f + f') g k p = ∑' p, tri m f g k p + ∑' p, tri m f' g k p
  rw [← (summable_tri hm hf hg k).tsum_add (summable_tri hm hf' hg k)]
  exact tsum_congr (tri_add_left m f f' g k)

private lemma Qm_add_right (hm : m.Bdd) {g' : Field} (hf : MZ 2 f) (hg : MZ 2 g) (hg' : MZ 2 g') :
    Qm m f (g + g') = Qm m f g + Qm m f g' := by
  funext k
  change ∑' p, tri m f (g + g') k p = ∑' p, tri m f g k p + ∑' p, tri m f g' k p
  rw [← (summable_tri hm hf hg k).tsum_add (summable_tri hm hf hg' k)]
  exact tsum_congr (tri_add_right m f g g' k)

private lemma conjV_add' (a b : V3) : conjV (a + b) = conjV a + conjV b := by
  ext i
  simp [conjV]

private lemma conjV_smul' (c : ℂ) (a : V3) : conjV (c • a) = conj c • conjV a := by
  ext i
  simp [conjV]

/-- Conjugation as an additive map. -/
private def conjHom : V3 →+ V3 :=
  AddMonoidHom.mk' conjV conjV_add'

private lemma continuous_conjHom : Continuous conjHom :=
  (AddMonoidHomClass.isometry_of_norm conjHom norm_conjV).continuous

/-- The pairing with a fixed mode as an additive map. -/
private def dotHom (k : Mode) : V3 →+ ℂ :=
  AddMonoidHom.mk' (fun v => dotM v k) fun a b => dotM_add a b k

private lemma continuous_dotHom (k : Mode) : Continuous (dotHom k) := by
  change Continuous fun v : V3 => ∑ i, v i * (k i : ℂ)
  fun_prop

private lemma dotM_conjV (v : V3) (k : Mode) : dotM (conjV v) (-k) = -conj (dotM v k) := by
  simp [dotM, conjV, Finset.sum_neg_distrib]

private lemma conjV_vert (p q : Mode) (A B : V3) :
    conjV (vert p q A B) = vert (-p) (-q) (conjV A) (conjV B) := by
  have h2 : conj (1 / 2 : ℂ) = 1 / 2 := by
    rw [map_div₀, map_one, Complex.conj_ofNat]
  simp only [vert, conjV_smul', conjV_leray, conjV_add', h2, map_mul, Complex.conj_I, dotM_conjV,
    neg_add]
  simp only [mul_neg, neg_mul]

private lemma tri_conj (hr : m.Real) (hfr : IsReal f) (hgr : IsReal g) (k p : Mode) :
    tri m f g (-k) (-p) = conjV (tri m f g k p) := by
  have e : -k - -p = -(k - p) := by abel
  simp only [tri, e, Fintype.sum_bool, conjV_add', conjV_smul', conjV_hel, conjV_vert, hr _ _ _ p,
    hfr p, hgr (k - p)]

private lemma Qm_real (hm : m.Bdd) (hr : m.Real) {f g : Field} (hf : Adm 2 f) (hg : Adm 2 g) :
    IsReal (Qm m f g) := fun k => by
  have hs := summable_tri hm (f := f) (g := g) ⟨hf.inH, hf.mean⟩ ⟨hg.inH, hg.mean⟩ k
  have h1 : conjV (Qm m f g k) = ∑' p, conjV (tri m f g k p) :=
    hs.map_tsum conjHom continuous_conjHom
  rw [h1]
  change ∑' p, tri m f g (-k) p = _
  rw [← (Equiv.neg Mode).tsum_eq]
  exact tsum_congr fun p => tri_conj hr hf.real hg.real k p

private lemma Qm_sol (hm : m.Bdd) (hf : MZ 2 f) (hg : MZ 2 g) :
    IsSolenoidal (Qm m f g) := fun k => by
  have h1 : dotM (Qm m f g k) k = ∑' p, dotM (tri m f g k p) k :=
    (summable_tri hm hf hg k).map_tsum (dotHom k) (continuous_dotHom k)
  rw [h1]
  simp [tri, dotM_add, dotM_smul, dotM_hel]

private lemma Qm_zero (m : Mult) (f g : Field) : Qm m f g 0 = 0 := by
  simp [Qm, hel_zero_mode]

/-- Any continuous-in-time bounded real multiplier family gives a `Majorized` family. -/
theorem majorized_Qm (m : ℝ → Mult) (hb : ∀ t, (m t).Bdd) (hr : ∀ t, (m t).Real)
    (hc : ∀ a b c p q, Continuous fun t => m t a b c p q) :
    Majorized (fun t => Qm (m t)) where
  add_left t _ _ _ hf hf' hg := Qm_add_left (hb t) hf hf' hg
  sub_left t f f' g hf hf' hg := by
    rw [eq_sub_iff_add_eq, ← Qm_add_left (hb t) (hf.sub' hf') hf' hg, sub_add_cancel]
  add_right t _ _ _ hf hg hg' := Qm_add_right (hb t) hf hg hg'
  sub_right t f g g' hf hg hg' := by
    rw [eq_sub_iff_add_eq, ← Qm_add_right (hb t) hf (hg.sub' hg') hg', sub_add_cancel]
  maj₁ t _ _ k hf hg := norm_Qm_le₁ (hb t) hf hg k
  maj₂ t _ _ k hf hg := norm_Qm_le₂ (hb t) hf hg k
  real t _ _ hf hg := Qm_real (hb t) (hr t) hf hg
  sol t _ _ hf hg := Qm_sol (hb t) hf hg
  mean t f g _ _ := Qm_zero (m t) f g
  cont f g k hf hg := by
    refine continuous_tsum (f := fun p t => tri (m t) f g k p) (fun p => ?_)
      (summable_maj₁ hf hg k) (fun p t => norm_tri_le₁ (hb t) f g k p)
    exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
      continuous_finsetSum _ fun c _ => (hc a b c p (k - p)).smul continuous_const

theorem majorized_res : Majorized (fun _ => Qres) :=
  majorized_Qm (fun _ => resM) (fun _ => resM_bdd) (fun _ => resM_real)
    fun _ _ _ _ _ => continuous_const
theorem majorized_filtN (r t₀ : ℝ) : Majorized (filtN r t₀) :=
  majorized_Qm (fun t => phaseM (r * (t + t₀))) (fun _ => phaseM_bdd _) (fun _ => phaseM_real _)
    fun a b c p q => by
      unfold phaseM
      fun_prop

end OVNS
