import OddViscousNS.Window
import OddViscousNS.RefBounds
import OddViscousNS.LocalTheory

/-! # All-time induction in fixed windows (`§ Proof of Theorem thm:general`) -/

open MeasureTheory Set intervalIntegral
open scoped ENNReal
noncomputable section
namespace OVNS

/-- A good force stays good for a larger bound. -/
private lemma GoodForce.mono_bound {G : ℝ → Field} {Γ Γ' : ℝ} (h : GoodForce G Γ) (hΓ : Γ ≤ Γ') :
    GoodForce G Γ' :=
  ⟨h.adm, fun t ↦ (h.bd t).trans hΓ, h.cont⟩

/-- The triangle inequality in the form `‖a‖ ≤ ‖a - b‖ + ‖b‖`. -/
private lemma hnorm_le_sub_add {s : ℝ} {a b : Field} (ha : InH s a) (hb : InH s b) :
    hnorm s a ≤ hnorm s (a - b) + hnorm s b := by
  simpa using hnorm_add_le (ha.sub hb) hb

/-- A filtered solution restarted at time `τ` is a filtered solution with shifted phase. -/
private lemma filtSol_shift {r τ : ℝ} {g : Field} {Ty : ℝ≥0∞} {y : ℝ → Field}
    (hy : IsHeatSol (filtN r 0) (filtG r 0 g) Ty y) (hτ : 0 ≤ τ)
    (hτ' : ENNReal.ofReal τ < Ty) :
    IsHeatSol (filtN r τ) (filtG r τ g) (Ty - ENNReal.ofReal τ) (fun t ↦ y (t + τ)) := by
  have h := hy.shift hτ hτ'
  have e1 : (fun t ↦ filtN r 0 (t + τ)) = filtN r τ := by
    funext t
    simp [filtN]
  have e2 : (fun t ↦ filtG r 0 g (t + τ)) = filtG r τ g := by
    funext t
    simp [filtG]
  rwa [e1, e2] at h

/-- The blow-up alternative passes to the restarted solution. -/
private lemma blowup_shift {N : ℝ → Field → Field → Field} {G : ℝ → Field} {τ : ℝ} {Ty : ℝ≥0∞}
    {y : ℝ → Field} (hy : IsHeatSol N G Ty y) (hτ : 0 ≤ τ) (hτ' : ENNReal.ofReal τ < Ty)
    (hbl : Ty ≠ ⊤ → ∀ C : ℝ, ¬ ∀ t, 0 ≤ t → ENNReal.ofReal t < Ty → hnorm 2 (y t) ≤ C) :
    Ty - ENNReal.ofReal τ ≠ ⊤ → ∀ C : ℝ, ¬ ∀ t, 0 ≤ t →
      ENNReal.ofReal t < Ty - ENNReal.ofReal τ → hnorm 2 (y (t + τ)) ≤ C := by
  intro hne C hC
  have hTy : Ty ≠ ⊤ := by
    rintro rfl
    exact hne (ENNReal.top_sub_coe (r := (ENNReal.ofReal τ).toNNReal) ▸ by simp)
  obtain ⟨C', hC'⟩ := hy.exists_bound hτ'
  refine hbl hTy (max C C') fun t ht htT ↦ ?_
  rcases le_total t τ with h | h
  · exact (hC' t ⟨ht, h⟩).trans (le_max_right _ _)
  · have hlt : ENNReal.ofReal (t - τ) < Ty - ENNReal.ofReal τ := by
      refine lt_tsub_iff_right.2 ?_
      rwa [← ENNReal.ofReal_add (by linarith) hτ, sub_add_cancel]
    have := hC (t - τ) (by linarith) hlt
    rw [sub_add_cancel] at this
    exact this.trans (le_max_left _ _)

/-- One window: the reference from the current state, transfer, and the triangle inequality. -/
private lemma window_step {r τ T X E J Y ρ ρend S φ : ℝ} {g : Field} {Ty : ℝ≥0∞} {y : ℝ → Field}
    (hT : 0 ≤ T)
    (hA : ∀ (g w : Field) (w' : ℝ → Field), Adm 2 g → hnorm 2 g ≤ φ →
      RefSol g ⊤ w' → w' 0 = w → hnorm 1 w ≤ ρ → hnorm 2 w ≤ S →
      (∀ t ∈ Icc 0 T, hnorm 1 (w' t) ≤ X ∧ hnorm 0 (w' t) ^ 2 ≤ E ∧ hnorm 2 (w' t) ≤ Y) ∧
      (∫ t in (0 : ℝ)..T, hnorm 2 (w' t) ^ 2) ≤ J ∧ hnorm 1 (w' T) ≤ ρend)
    (hW : ∀ (t₀ : ℝ) (w y : ℝ → Field) (Ty : ℝ≥0∞), RefSol g ⊤ w →
      (∀ t ∈ Icc 0 T, hnorm 1 (w t) ≤ X ∧ hnorm 0 (w t) ^ 2 ≤ E ∧ hnorm 2 (w t) ≤ Y) →
      (∫ t in (0 : ℝ)..T, hnorm 2 (w t) ^ 2) ≤ J →
      IsHeatSol (filtN r t₀) (filtG r t₀ g) Ty y → y 0 = w 0 →
      (Ty ≠ ⊤ → ∀ C : ℝ, ¬ ∀ t, 0 ≤ t → ENNReal.ofReal t < Ty → hnorm 2 (y t) ≤ C) →
      ENNReal.ofReal T < Ty ∧ ∀ t ∈ Icc 0 T, hnorm 1 (y t - w t) ≤ theta)
    (hg : Adm 2 g) (hgφ : hnorm 2 g ≤ φ)
    (hy : IsHeatSol (filtN r 0) (filtG r 0 g) Ty y)
    (hbl : Ty ≠ ⊤ → ∀ C : ℝ, ¬ ∀ t, 0 ≤ t → ENNReal.ofReal t < Ty → hnorm 2 (y t) ≤ C)
    (hτ : 0 ≤ τ) (hτ' : ENNReal.ofReal τ < Ty) (h1 : hnorm 1 (y τ) ≤ ρ) (h2 : hnorm 2 (y τ) ≤ S) :
    ENNReal.ofReal (T + τ) < Ty ∧ (∀ t ∈ Icc 0 T, hnorm 1 (y (t + τ)) ≤ X + 1) ∧
      hnorm 1 (y (T + τ)) ≤ ρend + 1 := by
  obtain ⟨w, hw, hw0⟩ := exists_refSol_global hg (hy.adm τ hτ hτ')
  obtain ⟨hb, hI, hend⟩ := hA g (y τ) w hg hgφ hw hw0 h1 h2
  obtain ⟨hlt, hclose⟩ := hW τ w (fun t ↦ y (t + τ)) (Ty - ENNReal.ofReal τ) hw hb hI
    (filtSol_shift hy hτ hτ') (by simp [hw0]) (blowup_shift hy hτ hτ' hbl)
  have hend' : ENNReal.ofReal (T + τ) < Ty := by
    rw [ENNReal.ofReal_add hT hτ]
    exact lt_tsub_iff_right.1 hlt
  have key : ∀ t ∈ Icc 0 T, hnorm 1 (y (t + τ)) ≤ hnorm 1 (w t) + 1 := fun t ht ↦ by
    have hyt : Adm 2 (y (t + τ)) := hy.adm _ (add_nonneg ht.1 hτ)
      ((ENNReal.ofReal_le_ofReal (by linarith [ht.2])).trans_lt hend')
    have hwt : Adm 2 (w t) := hw.adm t ht.1 ENNReal.ofReal_lt_top
    have := hnorm_le_sub_add (hyt.inH.mono (by norm_num : (1 : ℝ) ≤ 2))
      (hwt.inH.mono (by norm_num : (1 : ℝ) ≤ 2))
    linarith [hclose t ht, theta_lt_one]
  refine ⟨hend', fun t ht ↦ (key t ht).trans (by linarith [(hb t ht).1]), ?_⟩
  exact (key T ⟨hT, le_rfl⟩).trans (by linarith)

/-- The induction over windows: global existence and the uniform `H¹` bound. -/
private lemma all_windows {T ρ ρ' S : ℝ} {Ty : ℝ≥0∞} {y : ℝ → Field} (hT : 1 ≤ T)
    (hstep : ∀ τ, 0 ≤ τ → ENNReal.ofReal τ < Ty → hnorm 1 (y τ) ≤ ρ → hnorm 2 (y τ) ≤ S →
      ENNReal.ofReal (T + τ) < Ty ∧ (∀ t ∈ Icc 0 T, hnorm 1 (y (t + τ)) ≤ ρ') ∧
        hnorm 1 (y (T + τ)) ≤ ρ)
    (hsm : ∀ t, 1 ≤ t → ENNReal.ofReal t < Ty → (∀ u ∈ Icc (t - 1) t, hnorm 1 (y u) ≤ ρ') →
      hnorm 2 (y t) ≤ S)
    (h0 : 0 < Ty) (h1 : hnorm 1 (y 0) ≤ ρ) (h2 : hnorm 2 (y 0) ≤ S) :
    Ty = ⊤ ∧ ∀ t, 0 ≤ t → hnorm 1 (y t) ≤ ρ' := by
  have hTpos : 0 < T := by linarith
  have hH : ∀ j : ℕ, ENNReal.ofReal (j * T) < Ty ∧ hnorm 1 (y (j * T)) ≤ ρ ∧
      hnorm 2 (y (j * T)) ≤ S := by
    intro j
    induction j with
    | zero => simpa using ⟨h0, h1, h2⟩
    | succ j ih =>
      obtain ⟨hlt, hw, hend⟩ := hstep _ (by positivity) ih.1 ih.2.1 ih.2.2
      have e : ((j + 1 : ℕ) : ℝ) * T = T + j * T := by
        push_cast
        ring
      have hj : (0 : ℝ) ≤ j * T := by positivity
      rw [e]
      refine ⟨hlt, hend, hsm _ (by linarith) hlt fun u hu ↦ ?_⟩
      have := hw (u - j * T) ⟨by linarith [hu.1], by linarith [hu.2]⟩
      rwa [sub_add_cancel] at this
  refine ⟨?_, fun t ht ↦ ?_⟩
  · by_contra hne
    obtain ⟨j, hj⟩ := exists_nat_gt (Ty.toReal / T)
    rw [div_lt_iff₀ hTpos] at hj
    have := (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hne).1 (hH j).1
    linarith
  · set j := ⌊t / T⌋₊ with hj
    have h3 : (j : ℝ) * T ≤ t := (le_div_iff₀ hTpos).1 (Nat.floor_le (by positivity))
    have h4 : t < (j + 1 : ℝ) * T := (div_lt_iff₀ hTpos).1 (Nat.lt_floor_add_one _)
    have hH' := hH j
    have := (hstep _ (by positivity) hH'.1 hH'.2.1 hH'.2.2).2.1 (t - j * T)
      ⟨by linarith, by linarith⟩
    rwa [sub_add_cancel] at this

/-- The sliding `H³` bound from a uniform `H²` bound. -/
private lemma sliding_h3 {N : ℝ → Field → Field → Field} {G : ℝ → Field} {φ S : ℝ} {y : ℝ → Field}
    (hN : Majorized N) (hG : GoodForce G φ) (hy : IsHeatSol N G ⊤ y)
    (hS : ∀ t, 0 ≤ t → hnorm 2 (y t) ≤ S) {t : ℝ} (ht : 0 ≤ t) :
    ∫ s in t..(t + 1), hnorm 3 (y s) ^ 2 ≤ S ^ 2 + 128 * c4 ^ 2 * S ^ 4 + 2 * φ ^ 2 := by
  have h := h2_ineq hN hG hy ht (by linarith : t ≤ t + 1) ENNReal.ofReal_lt_top
  have hS0 : 0 ≤ S := (hnorm_nonneg 2 _).trans (hS t ht)
  have hbd : ‖∫ u in t..(t + 1), (128 * wiener (y u) ^ 2 * hnorm 2 (y u) ^ 2 + 2 * φ ^ 2)‖ ≤
      (128 * c4 ^ 2 * S ^ 4 + 2 * φ ^ 2) * |t + 1 - t| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu ↦ ?_
    rw [uIoc_of_le (by linarith)] at hu
    have hu0 : 0 ≤ u := ht.trans hu.1.le
    have hadm := hy.adm u hu0 ENNReal.ofReal_lt_top
    have hH := hS u hu0
    have hW : wiener (y u) ≤ c4 * S := (wiener_le ⟨hadm.inH, hadm.mean⟩).trans
      (mul_le_mul_of_nonneg_left hH c4_pos.le)
    have hW0 := wiener_nonneg (y u)
    have hH0 := hnorm_nonneg 2 (y u)
    have h1 : wiener (y u) ^ 2 ≤ (c4 * S) ^ 2 := pow_le_pow_left₀ hW0 hW 2
    have h2 : hnorm 2 (y u) ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ hH0 hH 2
    have h3 : wiener (y u) ^ 2 * hnorm 2 (y u) ^ 2 ≤ (c4 * S) ^ 2 * S ^ 2 :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    rw [Real.norm_of_nonneg (by positivity)]
    nlinarith
  have e : |t + 1 - t| = 1 := by simp
  rw [e, mul_one] at hbd
  have hbd' := (le_abs_self _).trans hbd
  have h0 := pow_le_pow_left₀ (hnorm_nonneg 2 _) (hS t ht) 2
  nlinarith [sq_nonneg (hnorm 2 (y (t + 1)))]

/-- The normalized filtered theorem, for each fixed `(μ, φ)`. -/
theorem normalized_main (μ φ : ℝ) (_hμ : 0 ≤ μ) (hφ : 0 ≤ φ) :
    ∃ R Bd : ℝ, 0 ≤ R ∧ 0 ≤ Bd ∧ ∀ (r : ℝ) (g v₀ : Field), Adm 2 g → hnorm 2 g ≤ φ →
      Adm 2 v₀ → hnorm 2 v₀ ≤ μ → R ≤ |r| →
      ∃ y, IsHeatSol (filtN r 0) (filtG r 0 g) ⊤ y ∧ y 0 = v₀ ∧
        (∀ t, 0 ≤ t → hnorm 1 (y t) ≤ Bd ∧ hnorm 2 (y t) ≤ Bd) ∧
        (∀ t, 0 ≤ t → ∫ s in t..(t + 1), hnorm 3 (y s) ^ 2 ≤ Bd) := by
  obtain ⟨ρend, hρend, hab⟩ := ref_absorption φ hφ
  set ρ : ℝ := max (max μ 1) (ρend + 1) with hρdef
  have hρμ : μ ≤ ρ := (le_max_left _ _).trans (le_max_left _ _)
  have hρ1 : 1 ≤ ρ := (le_max_right _ _).trans (le_max_left _ _)
  have hρe : ρend + 1 ≤ ρ := le_max_right _ _
  obtain ⟨T, X, E, J, hT, hX, hE, hJ, hYex⟩ := hab ρ hρ1
  obtain ⟨J₁, S₁, -, hS₁, hsm⟩ := exists_uniform_smoothing (X + 1) φ
  obtain ⟨J₂, S₂, -, hS₂, hin⟩ := exists_initial_smoothing (X + 1) φ μ
  obtain ⟨Y, -, hA⟩ := hYex (max μ S₁)
  obtain ⟨Rw, hRw, hW⟩ := window_transfer φ T X E J Y hφ (by linarith)
  set S' : ℝ := max S₁ S₂ with hS'
  have hS'0 : 0 ≤ S' := hS₁.trans (le_max_left _ _)
  refine ⟨max Rw 1, max (X + 1) (max S' (S' ^ 2 + 128 * c4 ^ 2 * S' ^ 4 + 2 * φ ^ 2)),
    hRw.trans (le_max_left _ _), (by linarith : 0 ≤ X + 1).trans (le_max_left _ _), ?_⟩
  intro r g v₀ hg hgφ hv₀ hv₀μ hr
  have hr0 : r ≠ 0 := by
    rintro rfl
    have : (1 : ℝ) ≤ |(0 : ℝ)| := (le_max_right _ _).trans hr
    norm_num at this
  have hrw : Rw ≤ |r| := (le_max_left _ _).trans hr
  have hN := majorized_filtN r 0
  have hG : GoodForce (filtG r 0 g) φ := (goodForce_filtG r 0 hg).mono_bound
    ((hnorm_mono (by norm_num) hg.inH).trans hgφ)
  obtain ⟨Ty, y, hTy0, hy, hy0, hbl⟩ := exists_maximal hN hG hv₀
  have hv1 : hnorm 1 v₀ ≤ μ := (hnorm_mono (by norm_num) hv₀.inH).trans hv₀μ
  obtain ⟨hTop, hρ'⟩ := all_windows (T := T) (ρ := ρ) (ρ' := X + 1) (S := max μ S₁) (Ty := Ty)
    (y := y) (by linarith)
    (fun τ hτ hτ' h1 h2 ↦ by
      obtain ⟨a, b, c⟩ := window_step (by linarith) hA (fun t₀ w y Ty ↦
        hW r t₀ g w y Ty hrw hr0 hg hgφ) hg hgφ hy hbl hτ hτ' h1 h2
      exact ⟨a, b, c.trans hρe⟩)
    (fun t ht1 ht hu ↦ ((hsm _ _ Ty y hN hG hy t ht1 ht hu).2).trans (le_max_right _ _))
    hTy0 (by rw [hy0]; exact hv1.trans hρμ) (by rw [hy0]; exact hv₀μ.trans (le_max_left _ _))
  subst hTop
  have hH2 : ∀ t, 0 ≤ t → hnorm 2 (y t) ≤ S' := by
    intro t ht
    rcases le_total 1 t with h | h
    · exact (hsm _ _ ⊤ y hN hG hy t h ENNReal.ofReal_lt_top
        fun u hu ↦ hρ' u (by linarith [hu.1])).2.trans (le_max_left _ _)
    · exact (hin _ _ ⊤ y hN hG hy (hy0 ▸ hv₀μ) t ⟨ht, h⟩ ENNReal.ofReal_lt_top
        fun u hu ↦ hρ' u hu.1).2.trans (le_max_right _ _)
  refine ⟨y, hy, hy0, fun t ht ↦ ⟨(hρ' t ht).trans (le_max_left _ _),
    ((hH2 t ht).trans (le_max_left _ _)).trans (le_max_right _ _)⟩, fun t ht ↦ ?_⟩
  exact (sliding_h3 hN hG hy hH2 ht).trans
    ((le_max_right _ _).trans (le_max_right _ _))

end OVNS
