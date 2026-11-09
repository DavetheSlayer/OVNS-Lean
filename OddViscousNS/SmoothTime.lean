import OddViscousNS.Persist

/-! # Time smoothness at positive times (`Proposition prop:smooth`, Step 3)

Rather than iterating the Leibniz rule with binomial coefficients, every time derivative of the
solution is written as the evaluation of a formal expression `Ex` built from the solution, the
linear symbol and the bilinear convection; `Ex.dt` differentiates such expressions formally.  All
estimates use polynomial decay of the coefficients with respect to the weight `wt k = 1 + |k|`,
which is submultiplicative, so that convolutions are controlled termwise. -/

open MeasureTheory Set
open scoped ENNReal Topology
noncomputable section
namespace OVNS

/-! ### The polynomial weight -/

/-- The polynomial weight `1 + |k|`. -/
private def wt (k : Mode) : ℝ := 1 + absk k

private lemma one_le_wt (k : Mode) : 1 ≤ wt k := le_add_of_nonneg_right (absk_nonneg k)

private lemma wt_pos (k : Mode) : 0 < wt k := lt_of_lt_of_le one_pos (one_le_wt k)

private lemma absk_le_wt (k : Mode) : absk k ≤ wt k := by simp [wt]

private lemma wt_add_le (p q : Mode) : wt (p + q) ≤ wt p * wt q := by
  have h := absk_add_le p q
  have h1 := absk_nonneg p
  have h2 := absk_nonneg q
  simp only [wt]
  nlinarith [mul_nonneg h1 h2]

/-- The summable decay `(1 + |k|)⁻⁴`. -/
private def dec (k : Mode) : ℝ := (wt k ^ 4)⁻¹

private lemma dec_nonneg (k : Mode) : 0 ≤ dec k := inv_nonneg.2 (pow_pos (wt_pos k) 4).le

private lemma dec_mul (k : Mode) : dec k * wt k ^ 4 = 1 :=
  inv_mul_cancel₀ (pow_pos (wt_pos k) 4).ne'

private lemma dec_le_inv4 {k : Mode} (hk : k ≠ 0) : dec k ≤ (absSq k)⁻¹ ^ 2 := by
  have h0 : 0 < absk k := lt_of_lt_of_le one_pos (one_le_absk hk)
  have h : (absSq k)⁻¹ ^ 2 = (absk k ^ 4)⁻¹ := by
    rw [← absk_sq k]
    field_simp
  rw [h]
  exact inv_anti₀ (pow_pos h0 4) (pow_le_pow_left₀ h0.le (absk_le_wt k) 4)

private lemma summable_dec : Summable dec := by
  classical
  have h1 : Summable fun k : Mode => if k = 0 then (1 : ℝ) else 0 :=
    (hasSum_ite_eq (0 : Mode) (1 : ℝ)).summable
  refine Summable.of_nonneg_of_le dec_nonneg (fun k => ?_) (summable_inv4.add h1)
  by_cases hk : k = 0
  · subst hk
    have h : dec (0 : Mode) ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ (one_le_wt 0))
    simpa using h
  · simpa [hk] using dec_le_inv4 hk

/-- The total mass of the decay. -/
private def mass : ℝ := ∑' k, dec k

/-! ### Rapidly decaying curves -/

/-- All polynomially weighted sup-bounds of the coefficients, locally uniformly on `(0,∞)`. -/
private def Tame (c : ℝ → Field) : Prop :=
  ∀ (m : ℕ) (a b : ℝ), 0 < a → a ≤ b → ∃ C : ℝ, ∀ t ∈ Icc a b, ∀ k, wt k ^ m * ‖c t k‖ ≤ C

private lemma le_weighted (m : ℕ) (k : Mode) {x : ℝ} (hx : 0 ≤ x) : x ≤ wt k ^ m * x :=
  le_mul_of_one_le_left hx (one_le_pow₀ (one_le_wt k))

private lemma Tame.add {c d : ℝ → Field} (hc : Tame c) (hd : Tame d) :
    Tame fun t => c t + d t := by
  intro m a b ha hab
  obtain ⟨C, hC⟩ := hc m a b ha hab
  obtain ⟨D, hD⟩ := hd m a b ha hab
  refine ⟨C + D, fun t ht k => ?_⟩
  have h : ‖(c t + d t) k‖ ≤ ‖c t k‖ + ‖d t k‖ := norm_add_le _ _
  have hw : 0 ≤ wt k ^ m := (pow_pos (wt_pos k) m).le
  calc wt k ^ m * ‖(c t + d t) k‖ ≤ wt k ^ m * (‖c t k‖ + ‖d t k‖) :=
        mul_le_mul_of_nonneg_left h hw
    _ ≤ C + D := by rw [mul_add]; exact add_le_add (hC t ht k) (hD t ht k)

/-! ### The linear symbol -/

/-- The linear part `-ν|k|² + α·oddSym k` of the mode equation. -/
private def lsym (ν α : ℝ) (k : Mode) (v : V3) : V3 :=
  (-(ν * absSq k : ℝ) : ℂ) • v + (α : ℂ) • oddSym k v

private lemma oddSym_add' (k : Mode) (a b : V3) :
    oddSym k (a + b) = oddSym k a + oddSym k b := by
  simp only [oddSym, smul_add, cross_add_right, leray_add]

private lemma oddSym_smul' (k : Mode) (c : ℂ) (a : V3) : oddSym k (c • a) = c • oddSym k a := by
  simp only [oddSym, smul_comm _ c a, cross_smul_right, leray_smul]

/-- The linear part as a continuous linear map. -/
private def lsymL (ν α : ℝ) (k : Mode) : V3 →L[ℂ] V3 :=
  LinearMap.toContinuousLinearMap
    { toFun := lsym ν α k
      map_add' := fun a b => by
        simp only [lsym, oddSym_add', smul_add]
        abel
      map_smul' := fun c a => by
        simp only [lsym, oddSym_smul', RingHom.id_apply, smul_add, smul_comm c] }

private lemma norm_cross_e3_le (v : V3) : ‖cross e3 v‖ ≤ ‖v‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  simp only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp [cross, e3]
  nlinarith [sq_nonneg ‖v.ofLp 2‖]

private lemma norm_oddSym_le (k : Mode) (v : V3) : ‖oddSym k v‖ ≤ absSq k * ‖v‖ := by
  refine (norm_leray_le k _).trans ((norm_cross_e3_le _).trans ?_)
  rw [norm_smul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (absSq_nonneg k)]

private lemma absSq_le_wt (k : Mode) : absSq k ≤ wt k ^ 2 := by
  rw [← absk_sq k]
  exact pow_le_pow_left₀ (absk_nonneg k) (absk_le_wt k) 2

private lemma norm_lsym_le (ν α : ℝ) (k : Mode) (v : V3) :
    ‖lsym ν α k v‖ ≤ (|ν| + |α|) * wt k ^ 2 * ‖v‖ := by
  have h1 : ‖(-(ν * absSq k : ℝ) : ℂ) • v‖ ≤ |ν| * wt k ^ 2 * ‖v‖ := by
    rw [norm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (absSq_nonneg k)]
    gcongr
    exact absSq_le_wt k
  have h2 : ‖(α : ℂ) • oddSym k v‖ ≤ |α| * wt k ^ 2 * ‖v‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    refine mul_le_mul_of_nonneg_left ((norm_oddSym_le k v).trans ?_) (abs_nonneg α)
    exact mul_le_mul_of_nonneg_right (absSq_le_wt k) (norm_nonneg v)
  refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans (le_of_eq ?_))
  ring

private lemma Tame.lsym (ν α : ℝ) {c : ℝ → Field} (hc : Tame c) :
    Tame fun t k => lsym ν α k (c t k) := by
  intro m a b ha hab
  obtain ⟨C, hC⟩ := hc (m + 2) a b ha hab
  refine ⟨(|ν| + |α|) * C, fun t ht k => ?_⟩
  have hw : 0 ≤ wt k ^ m := (pow_pos (wt_pos k) m).le
  calc wt k ^ m * ‖OVNS.lsym ν α k (c t k)‖
      ≤ wt k ^ m * ((|ν| + |α|) * wt k ^ 2 * ‖c t k‖) :=
        mul_le_mul_of_nonneg_left (norm_lsym_le ν α k _) hw
    _ = (|ν| + |α|) * (wt k ^ (m + 2) * ‖c t k‖) := by ring
    _ ≤ (|ν| + |α|) * C :=
        mul_le_mul_of_nonneg_left (hC t ht k) (add_nonneg (abs_nonneg _) (abs_nonneg _))

/-! ### The bilinear convection -/

/-- The `p`-th term of `advect x y k`. -/
private def term (x y : Field) (k p : Mode) : V3 :=
  (Complex.I * dotM (x p) (k - p)) • y (k - p)

/-- The convection with its sign in the mode equation, polarized. -/
private def bil (x y : Field) (k : Mode) : V3 := -leray k (advect x y k)

private lemma norm_term_le_aux (x y : Field) (k p : Mode) :
    ‖term x y k p‖ ≤ ‖x p‖ * absk (k - p) * ‖y (k - p)‖ := by
  rw [term, norm_smul, norm_mul, Complex.norm_I, one_mul]
  exact mul_le_mul_of_nonneg_right (norm_dotM_le _ _) (norm_nonneg _)

/-- The Peetre-type termwise bound for the convolution. -/
private lemma weighted_term_le {x y : Field} {A B : ℝ} {m : ℕ}
    (hx : ∀ p, wt p ^ (m + 4) * ‖x p‖ ≤ A) (hy : ∀ q, wt q ^ (m + 1) * ‖y q‖ ≤ B) (k p : Mode) :
    wt k ^ m * ‖term x y k p‖ ≤ A * B * dec p := by
  set q := k - p with hq
  have hk : wt k ≤ wt p * wt q := by
    have h := wt_add_le p q
    rwa [hq, add_sub_cancel] at h
  have hP := pow_pos (wt_pos p) m
  have hQ := pow_pos (wt_pos q) m
  have hxn := norm_nonneg (x p)
  have hyn := norm_nonneg (y q)
  have hB : 0 ≤ B := (mul_nonneg (pow_pos (wt_pos q) _).le hyn).trans (hy q)
  have h1 : wt k ^ m ≤ wt p ^ m * wt q ^ m := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (wt_pos k).le hk m
  have h2 : ‖term x y k p‖ ≤ ‖x p‖ * wt q * ‖y q‖ :=
    (norm_term_le_aux x y k p).trans (by gcongr; exact absk_le_wt q)
  have h3 : wt p ^ m * ‖x p‖ ≤ A * dec p := by
    calc wt p ^ m * ‖x p‖ = (wt p ^ (m + 4) * ‖x p‖) * dec p := by
          have := dec_mul p
          calc wt p ^ m * ‖x p‖ = wt p ^ m * ‖x p‖ * (dec p * wt p ^ 4) := by rw [this, mul_one]
            _ = _ := by ring
      _ ≤ A * dec p := mul_le_mul_of_nonneg_right (hx p) (dec_nonneg p)
  have hA : 0 ≤ A * dec p := (mul_nonneg hP.le hxn).trans h3
  calc wt k ^ m * ‖term x y k p‖
      ≤ (wt p ^ m * wt q ^ m) * (‖x p‖ * wt q * ‖y q‖) := by gcongr
    _ = (wt p ^ m * ‖x p‖) * (wt q ^ (m + 1) * ‖y q‖) := by ring
    _ ≤ (A * dec p) * B := mul_le_mul h3 (hy q) (mul_nonneg (pow_pos (wt_pos q) _).le hyn) hA
    _ = A * B * dec p := by ring

private lemma norm_term_le {x y : Field} {A B : ℝ} {m : ℕ}
    (hx : ∀ p, wt p ^ (m + 4) * ‖x p‖ ≤ A) (hy : ∀ q, wt q ^ (m + 1) * ‖y q‖ ≤ B) (k p : Mode) :
    ‖term x y k p‖ ≤ A * B * dec p :=
  (le_weighted m k (norm_nonneg _)).trans (weighted_term_le hx hy k p)

private lemma summable_term {x y : Field} {A B : ℝ} {m : ℕ}
    (hx : ∀ p, wt p ^ (m + 4) * ‖x p‖ ≤ A) (hy : ∀ q, wt q ^ (m + 1) * ‖y q‖ ≤ B) (k : Mode) :
    Summable (term x y k) :=
  Summable.of_norm_bounded (summable_dec.mul_left (A * B)) (norm_term_le hx hy k)

private lemma Tame.bil {c d : ℝ → Field} (hc : Tame c) (hd : Tame d) :
    Tame fun t => bil (c t) (d t) := by
  intro m a b ha hab
  obtain ⟨A, hA⟩ := hc (m + 4) a b ha hab
  obtain ⟨B, hB⟩ := hd (m + 1) a b ha hab
  refine ⟨A * B * mass, fun t ht k => ?_⟩
  have hx := hA t ht
  have hy := hB t ht
  have hs : Summable fun p => ‖term (c t) (d t) k p‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_term_le hx hy k)
      (summable_dec.mul_left (A * B))
  have h1 : ‖OVNS.bil (c t) (d t) k‖ ≤ ∑' p, ‖term (c t) (d t) k p‖ := by
    rw [OVNS.bil, norm_neg]
    exact (norm_leray_le k _).trans (norm_tsum_le_tsum_norm hs)
  have hw : 0 ≤ wt k ^ m := (pow_pos (wt_pos k) m).le
  calc wt k ^ m * ‖OVNS.bil (c t) (d t) k‖
      ≤ wt k ^ m * ∑' p, ‖term (c t) (d t) k p‖ := mul_le_mul_of_nonneg_left h1 hw
    _ = ∑' p, wt k ^ m * ‖term (c t) (d t) k p‖ := tsum_mul_left.symm
    _ ≤ ∑' p, A * B * dec p :=
        (hs.mul_left _).tsum_le_tsum (weighted_term_le hx hy k) (summable_dec.mul_left _)
    _ = A * B * mass := tsum_mul_left

/-- The pairing `v ↦ v · q` as a continuous linear map. -/
private def dotL (q : Mode) : V3 →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => dotM v q
      map_add' := fun a b => dotM_add a b q
      map_smul' := fun c a => dotM_smul c a q }

/-- The Leray symbol as a continuous linear map. -/
private def lerayL (k : Mode) : V3 →L[ℂ] V3 :=
  LinearMap.toContinuousLinearMap
    { toFun := leray k, map_add' := leray_add k, map_smul' := leray_smul k }

private lemma hasDerivAt_term {a a' b b' : ℝ → Field} {y : ℝ} {k p : Mode}
    (ha : HasDerivAt (fun s => a s p) (a' y p) y)
    (hb : HasDerivAt (fun s => b s (k - p)) (b' y (k - p)) y) :
    HasDerivAt (fun s => term (a s) (b s) k p)
      (term (a' y) (b y) k p + term (a y) (b' y) k p) y := by
  have h1 : HasDerivAt (fun s => dotM (a s p) (k - p)) (dotM (a' y p) (k - p)) y :=
    ((dotL (k - p)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt y ha
  have h2 := (h1.const_mul Complex.I).smul hb
  rw [add_comm] at h2
  exact h2

/-- Termwise differentiation of the convection. -/
private lemma hasDerivAt_advect {a a' b b' : ℝ → Field} (ha : Tame a) (ha' : Tame a')
    (hb : Tame b) (hb' : Tame b')
    (hda : ∀ k t, 0 < t → HasDerivAt (fun s => a s k) (a' t k) t)
    (hdb : ∀ k t, 0 < t → HasDerivAt (fun s => b s k) (b' t k) t) (k : Mode) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (fun s => advect (a s) (b s) k) (advect (a' t) (b t) k + advect (a t) (b' t) k)
      t := by
  have ht2 : 0 < t / 2 := by positivity
  have hle : t / 2 ≤ 2 * t := by linarith
  obtain ⟨A, hA⟩ := ha (0 + 4) (t / 2) (2 * t) ht2 hle
  obtain ⟨A', hA'⟩ := ha' (0 + 4) (t / 2) (2 * t) ht2 hle
  obtain ⟨B, hB⟩ := hb (0 + 1) (t / 2) (2 * t) ht2 hle
  obtain ⟨B', hB'⟩ := hb' (0 + 1) (t / 2) (2 * t) ht2 hle
  have hsub : ∀ s ∈ Ioo (t / 2) (2 * t), 0 < s ∧ s ∈ Icc (t / 2) (2 * t) := fun s hs =>
    ⟨ht2.trans hs.1, Ioo_subset_Icc_self hs⟩
  have hmem : t ∈ Ioo (t / 2) (2 * t) := ⟨by linarith, by linarith⟩
  have hm := (hsub t hmem).2
  have key := hasDerivAt_tsum_of_isPreconnected (t := Ioo (t / 2) (2 * t))
    (g := fun p s => term (a s) (b s) k p)
    (g' := fun p s => term (a' s) (b s) k p + term (a s) (b' s) k p)
    (u := fun p => (A' * B + A * B') * dec p) (y₀ := t) (y := t)
    (summable_dec.mul_left _) isOpen_Ioo isPreconnected_Ioo
    (fun p s hs => hasDerivAt_term (hda p s (hsub s hs).1) (hdb _ s (hsub s hs).1))
    (fun p s hs => by
      have h1 := norm_term_le (hA' s (hsub s hs).2) (hB s (hsub s hs).2) k p
      have h2 := norm_term_le (hA s (hsub s hs).2) (hB' s (hsub s hs).2) k p
      refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans (le_of_eq ?_))
      ring)
    hmem (summable_term (hA t hm) (hB t hm) k) hmem
  have hval : ∑' p, (term (a' t) (b t) k p + term (a t) (b' t) k p) =
      advect (a' t) (b t) k + advect (a t) (b' t) k :=
    (summable_term (hA' t hm) (hB t hm) k).tsum_add (summable_term (hA t hm) (hB' t hm) k)
  rw [hval] at key
  exact key

private lemma hasDerivAt_bil {a a' b b' : ℝ → Field} (ha : Tame a) (ha' : Tame a')
    (hb : Tame b) (hb' : Tame b')
    (hda : ∀ k t, 0 < t → HasDerivAt (fun s => a s k) (a' t k) t)
    (hdb : ∀ k t, 0 < t → HasDerivAt (fun s => b s k) (b' t k) t) (k : Mode) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (fun s => bil (a s) (b s) k) (bil (a' t) (b t) k + bil (a t) (b' t) k) t := by
  have h := ((lerayL k).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_advect ha ha' hb hb' hda hdb k ht)
  have h' : leray k (advect (a' t) (b t) k + advect (a t) (b' t) k) =
      leray k (advect (a' t) (b t) k) + leray k (advect (a t) (b' t) k) := leray_add _ _ _
  have h2 : HasDerivAt (fun s => leray k (advect (a s) (b s) k))
      (leray k (advect (a' t) (b t) k) + leray k (advect (a t) (b' t) k)) t := by
    rw [← h']
    exact h
  have h3 := h2.neg
  rw [neg_add] at h3
  exact h3

/-! ### Formal time derivatives -/

/-- Formal expressions in the solution. -/
private inductive Ex : Type
  /-- The solution itself. -/
  | var : Ex
  /-- The linear part applied to an expression. -/
  | lin : Ex → Ex
  /-- The convection of two expressions. -/
  | bil : Ex → Ex → Ex
  /-- The sum of two expressions. -/
  | add : Ex → Ex → Ex

/-- The curve an expression denotes. -/
private def Ex.eval (ν α : ℝ) (u : ℝ → Field) : Ex → ℝ → Field
  | .var, t => u t
  | .lin e, t => fun k => lsym ν α k (e.eval ν α u t k)
  | .bil e f, t => OVNS.bil (e.eval ν α u t) (f.eval ν α u t)
  | .add e f, t => e.eval ν α u t + f.eval ν α u t

/-- The formal time derivative along the unforced equation. -/
private def Ex.dt : Ex → Ex
  | .var => .add (.lin .var) (.bil .var .var)
  | .lin e => .lin e.dt
  | .bil e f => .add (.bil e.dt f) (.bil e f.dt)
  | .add e f => .add e.dt f.dt

private lemma Ex.tame {ν α : ℝ} {u : ℝ → Field} (hu : Tame u) (e : Ex) :
    Tame (e.eval ν α u) := by
  induction e with
  | var => exact hu
  | lin e ih => exact ih.lsym ν α
  | bil e f he hf => exact he.bil hf
  | add e f he hf => exact he.add hf

private lemma Ex.hasDerivAt {ν α : ℝ} {u : ℝ → Field} (hu : Tame u)
    (hdu : ∀ k t, 0 < t →
      HasDerivAt (fun s => u s k) (lsym ν α k (u t k) + OVNS.bil (u t) (u t) k) t) (e : Ex) :
    ∀ k t, 0 < t → HasDerivAt (fun s => e.eval ν α u s k) (e.dt.eval ν α u t k) t := by
  induction e with
  | var => exact hdu
  | lin e ih =>
    intro k t ht
    exact ((lsymL ν α k).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (ih k t ht)
  | bil e f he hf =>
    intro k t ht
    exact hasDerivAt_bil (Ex.tame hu e) (Ex.tame hu e.dt) (Ex.tame hu f) (Ex.tame hu f.dt)
      he hf k ht
  | add e f he hf =>
    intro k t ht
    exact (he k t ht).add (hf k t ht)

/-! ### Calculus of derivative towers -/

private lemma contDiffOn_tower {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℕ → ℝ → E} (hd : ∀ j t, 0 < t → HasDerivAt (g j) (g (j + 1) t) t) (n : ℕ) :
    ∀ j, ContDiffOn ℝ n (g j) (Ioi 0) := by
  induction n with
  | zero =>
    intro j
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun t ht => (hd j t ht).continuousAt.continuousWithinAt
  | succ n ih =>
    intro j
    rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun t ht => (hd j t ht).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact (ih (j + 1)).congr fun t ht => (hd j t ht).deriv

private lemma iteratedDerivWithin_tower {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℕ → ℝ → E} (hd : ∀ j t, 0 < t → HasDerivAt (g j) (g (j + 1) t) t) (j : ℕ) :
    ∀ t, 0 < t → iteratedDerivWithin j (g 0) (Ioi 0) t = g j t := by
  induction j with
  | zero => intro t _; simp
  | succ j ih =>
    intro t ht
    rw [iteratedDerivWithin_succ]
    have h : HasDerivWithinAt (iteratedDerivWithin j (g 0) (Ioi 0)) (g (j + 1) t) (Ioi 0) t :=
      (hd j t ht).hasDerivWithinAt.congr (fun s hs => ih s hs) (ih t ht)
    exact h.derivWithin (isOpen_Ioi.uniqueDiffOn t ht)

/-! ### Passage to and from Sobolev norms -/

private lemma sobWeight_nat (m : ℕ) {k : Mode} (hk : k ≠ 0) :
    sobWeight (m : ℝ) k = (absk k ^ m) ^ 2 := by
  have h : (2 * (m : ℝ)) = ((2 * m : ℕ) : ℝ) := by push_cast; ring
  rw [sobWeight, ite_eq_right_iff.2 (fun h0 => absurd h0 hk), h, Real.rpow_natCast, pow_mul,
    ← pow_mul, ← pow_mul, mul_comm]

private lemma tame_of_hnorm {u : ℝ → Field} (h0 : ∀ t, 0 ≤ t → u t 0 = 0)
    (hreg : ∀ (m : ℕ) (a b : ℝ), 0 < a → a ≤ b →
      ∃ C : ℝ, ∀ t ∈ Icc a b, InH m (u t) ∧ hnorm m (u t) ≤ C) : Tame u := by
  intro m a b ha hab
  obtain ⟨C, hC⟩ := hreg m a b ha hab
  refine ⟨2 ^ m * C, fun t ht k => ?_⟩
  have hC0 : 0 ≤ C := (hnorm_nonneg _ _).trans (hC t ht).2
  by_cases hk : k = 0
  · subst hk
    rw [h0 t (ha.le.trans ht.1), norm_zero, mul_zero]
    positivity
  · have h1 := one_le_absk hk
    have hA := absk_nonneg k
    have hw : wt k ≤ 2 * absk k := by simp only [wt]; linarith
    have hs : (absk k ^ m * ‖u t k‖) ^ 2 ≤ hnorm m (u t) ^ 2 := by
      have h := sobWeight_mul_norm_le (hC t ht).1 k
      rwa [sobWeight_nat _ hk, ← mul_pow] at h
    have h2 : absk k ^ m * ‖u t k‖ ≤ hnorm m (u t) :=
      (pow_le_pow_iff_left₀ (by positivity) (hnorm_nonneg _ _) two_ne_zero).1 hs
    calc wt k ^ m * ‖u t k‖ ≤ (2 * absk k) ^ m * ‖u t k‖ := by gcongr; exact (wt_pos k).le
      _ = 2 ^ m * (absk k ^ m * ‖u t k‖) := by rw [mul_pow, mul_assoc]
      _ ≤ 2 ^ m * C := by
        exact mul_le_mul_of_nonneg_left (h2.trans (hC t ht).2) (by positivity)

private lemma Tame.hsE_le {c : ℝ → Field} (hc : Tame c) (r a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, ∀ t ∈ Icc a b, hsE r (c t) ≤ ENNReal.ofReal C := by
  obtain ⟨n, hn⟩ := exists_nat_ge r
  obtain ⟨C, hC⟩ := hc (n + 2) a b ha hab
  refine ⟨C ^ 2 * mass, fun t ht => ?_⟩
  have hpt : ∀ k, sobWeight r k * ‖c t k‖ ^ 2 ≤ C ^ 2 * dec k := by
    intro k
    by_cases hk : k = 0
    · subst hk
      simpa [sobWeight] using mul_nonneg (sq_nonneg C) (dec_nonneg 0)
    · have h1 : sobWeight r k ≤ (wt k ^ n) ^ 2 := by
        refine (sobWeight_mono hn k).trans ?_
        rw [sobWeight_nat _ hk]
        exact pow_le_pow_left₀ (pow_nonneg (absk_nonneg k) n)
          (pow_le_pow_left₀ (absk_nonneg k) (absk_le_wt k) n) 2
      have h2 : (wt k ^ (n + 2) * ‖c t k‖) ^ 2 ≤ C ^ 2 := by
        have := hC t ht k
        exact pow_le_pow_left₀ (mul_nonneg (pow_pos (wt_pos k) _).le (norm_nonneg _)) this 2
      have h3 : sobWeight r k * ‖c t k‖ ^ 2 ≤ (wt k ^ n) ^ 2 * ‖c t k‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      refine h3.trans ?_
      calc (wt k ^ n) ^ 2 * ‖c t k‖ ^ 2
          = (wt k ^ (n + 2) * ‖c t k‖) ^ 2 * dec k := by
            have := dec_mul k
            calc (wt k ^ n) ^ 2 * ‖c t k‖ ^ 2
                = (wt k ^ n) ^ 2 * ‖c t k‖ ^ 2 * (dec k * wt k ^ 4) := by rw [this, mul_one]
              _ = _ := by ring
        _ ≤ C ^ 2 * dec k := mul_le_mul_of_nonneg_right h2 (dec_nonneg k)
  have hsum : Summable fun k => C ^ 2 * dec k := summable_dec.mul_left _
  have hval : ENNReal.ofReal (C ^ 2 * mass) = ∑' k, ENNReal.ofReal (C ^ 2 * dec k) := by
    rw [mass, ← tsum_mul_left,
      ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (sq_nonneg C) (dec_nonneg k)) hsum]
  rw [hval, hsE]
  exact tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal (hpt k)

/-- A global strong solution (`ν > 0`, zero force) with spatial `C^∞`-bounds at positive times is
smooth at positive times. -/
theorem smoothAtPositiveTimes {ν α : ℝ} (_hν : 0 < ν) {u₀ : Field} {u : ℝ → Field}
    (hu : IsStrongSolution ν α 0 u₀ u)
    (hreg : ∀ (m : ℕ) (a b : ℝ), 0 < a → a ≤ b →
      ∃ C : ℝ, ∀ t ∈ Icc a b, InH m (u t) ∧ hnorm m (u t) ≤ C) :
    SmoothAtPositiveTimes u := by
  have hT : Tame u := tame_of_hnorm (fun t ht => (hu.adm t ht).mean) hreg
  have hdu : ∀ k t, 0 < t →
      HasDerivAt (fun s => u s k) (lsym ν α k (u t k) + bil (u t) (u t) k) t := by
    intro k t ht
    have h := (hu.mode k t ht.le).hasDerivAt (Ici_mem_nhds ht)
    have he : (-(ν * absSq k : ℝ) : ℂ) • u t k + (α : ℂ) • oddSym k (u t k) - convec (u t) k +
        (0 : Field) k = lsym ν α k (u t k) + bil (u t) (u t) k := by
      simp only [lsym, bil, convec, Pi.zero_apply, add_zero, sub_eq_add_neg]
    rwa [he] at h
  set D : ℕ → Ex := fun j => Ex.dt^[j] Ex.var with hD
  have hDs : ∀ j, D (j + 1) = (D j).dt := fun j => Function.iterate_succ_apply' _ _ _
  have htower : ∀ k j t, 0 < t → HasDerivAt (fun s => (D j).eval ν α u s k)
      ((D (j + 1)).eval ν α u t k) t := by
    intro k j t ht
    rw [hDs]
    exact Ex.hasDerivAt hT hdu (D j) k t ht
  constructor
  · intro k
    exact contDiffOn_infty.2 fun n =>
      contDiffOn_tower (g := fun j s => (D j).eval ν α u s k) (htower k) n 0
  · intro j r a b ha hab
    obtain ⟨C, hC⟩ := (Ex.tame hT (D j) (ν := ν) (α := α)).hsE_le r a b ha hab
    refine ⟨C, fun t ht => ?_⟩
    have ht0 : 0 < t := ha.trans_le ht.1
    have he : (fun k => iteratedDerivWithin j (fun s => u s k) (Ioi 0) t) =
        (D j).eval ν α u t := by
      funext k
      exact iteratedDerivWithin_tower (g := fun j s => (D j).eval ν α u s k) (htower k) j t ht0
    rw [he]
    exact hC t ht

end OVNS
