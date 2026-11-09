import OddViscousNS.Quant.Joint.Metric.Q3Form

/-!
# The third correction: `H¹` leaves (step J5, node N8)

`pos3_band`: `∑ (α_l/L)(β_j/J²) u_a v_b w_c ≲ √(1 + ln D) ‖α‖ ‖β‖ ‖u‖₂ ‖v‖₂ ‖w‖₁`, on `L ≤ D`.

`Q3_leaf`: `O(f₁, f₂, f₃)` with `H¹` leaves: Body 33's `D_S Q₃`.  On the mask all ancestors are at
most `D`, so an `H¹` leaf is in `ℓ¹` up to `√(1 + ln D)` (`l1B_lo`): the exponents `16/15`, `16/9` of
Body 33, and `a₊`, are not needed here.  This is stronger than the source by a power of `R`.
-/

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

variable {α β u v w : Mode → ℝ} {A B U V W D : ℝ}

/-- The relabelling of three leaves. -/
def leafE : Mode × I3 ≃ I4 where
  toFun y := (y.2.1, y.2.2.1, y.2.2.2, y.1)
  invFun x := (x.2.2.2, x.1, x.2.1, x.2.2.1)
  left_inv := fun ⟨_, _, _, _⟩ => rfl
  right_inv := fun ⟨_, _, _, _⟩ => rfl

/-- **The band sum of three leaves.** -/
theorem pos3_band (hD : 1 ≤ D) (hα : L2B α A) (hβ : L2B β B) (hu : L2B u U) (hv : L2B v V)
    (hw : L1B w W) (hus : ∀ p, p 2 ≠ 0 → u p = 0) (hvs : ∀ p, p 2 ≠ 0 → v p = 0) :
    SB (fun x : I4 => α x.1 * bandW D x.1 * (β (inJ x) * (absk (inJ x))⁻¹ ^ 2) *
      (u x.2.1 * v x.2.2.1 * w x.2.2.2))
      (A * U * Real.sqrt 17 * (B * V * Real.sqrt (9 + 8 * Real.log D)) * W) := by
  have hlog : 0 ≤ 9 + 8 * Real.log D := by
    have := Real.log_nonneg hD
    linarith
  have hA := hα.bd_nonneg
  have hB := hβ.bd_nonneg
  have hU := hu.bd_nonneg
  have hV := hv.bd_nonneg
  have hF := fib_band hD
  have hin : ∀ c : Mode, SB (fun y : I3 => w c * ((α y.1 * u y.2.1 *
      (if y.2.2 2 = 0 then (absk (inJ₂ y - c))⁻¹ ^ 2 else 0)) * (β (inJ₂ y - c) * v y.2.2 *
      (if y.2.1 2 = 0 then bandW D y.1 else 0))))
      (w c * ((A * U * Real.sqrt 17) * (B * V * Real.sqrt (9 + 8 * Real.log D)))) := fun c => by
    have hβc : L2B (fun k => β (k - c)) B := by
      have e : ∀ s : Mode → ℝ, ∑' k, s (k - c) = ∑' k, s k := fun s =>
        (Equiv.subRight c).tsum_eq s
      refine ⟨fun k => hβ.nn _, (Equiv.subRight c).summable_iff.2 hβ.s, ?_⟩
      rw [e fun k => β k ^ 2]
      exact hβ.le
    set κ₁ : I3 → ℝ := fun y => if y.2.2 2 = 0 then (absk (inJ₂ y - c))⁻¹ ^ 2 else 0 with hκ₁
    set κ₂ : I3 → ℝ := fun y => if y.2.1 2 = 0 then bandW D y.1 else 0 with hκ₂
    have h10 : ∀ y, 0 ≤ κ₁ y := fun y => by
      have := inv_nonneg.2 (absk_nonneg (inJ₂ y - c))
      simp only [hκ₁]
      split_ifs <;> positivity
    have h20 : ∀ y, 0 ≤ κ₂ y := fun y => by
      have := bandW_nonneg D y.1
      simp only [hκ₂]
      split_ifs <;> positivity
    have c1 : ∀ l a, SB (fun b => κ₁ (l, a, b) ^ 2) 17 := fun l a => by
      refine (fib_w4 (l - a - c)).of_le (fun b => sq_nonneg _) fun b => le_of_eq ?_
      have e : l - a - b - c = l - a - c - b := by abel
      by_cases hb : b 2 = 0
      · simp only [hκ₁, inJ₂, hb, ↓reduceIte, e, w4]
        ring
      · simp only [hκ₁, hb, ↓reduceIte]
        ring
    have c2 : ∀ j b, SB (fun a => κ₂ (j + b + a, a, b) ^ 2) (9 + 8 * Real.log D) := fun j b => by
      refine (hF.add (j + b)).of_le (fun a => sq_nonneg _) fun a => le_of_eq ?_
      by_cases ha : a 2 = 0
      · simp only [hκ₂, ha, ↓reduceIte]
      · simp only [hκ₂, ha, ↓reduceIte]
        ring
    have hc := cs_mid h10 h20 c1 c2 (by norm_num) hlog hα hβc hu hv
    exact hc.const_mul (hw.nn c)
  have hp : 0 ≤ (A * U * Real.sqrt 17) * (B * V * Real.sqrt (9 + 8 * Real.log D)) := by positivity
  have hsum : SB (fun c => w c * ((A * U * Real.sqrt 17) * (B * V * Real.sqrt (9 + 8 * Real.log D))))
      (A * U * Real.sqrt 17 * (B * V * Real.sqrt (9 + 8 * Real.log D)) * W) := by
    refine ⟨hw.s.mul_right _, ?_⟩
    rw [tsum_mul_right, mul_comm]
    exact mul_le_mul_of_nonneg_left hw.le hp
  have hprod := SB.prod (H := fun y : Mode × I3 => w y.1 * ((α y.2.1 * u y.2.2.1 *
      (if y.2.2.2 2 = 0 then (absk (inJ₂ y.2 - y.1))⁻¹ ^ 2 else 0)) *
      (β (inJ₂ y.2 - y.1) * v y.2.2.2 *
      (if y.2.2.1 2 = 0 then bandW D y.2.1 else 0))))
    (fun y => by
      have h1 := hw.nn y.1
      have h2 := hα.nn y.2.1
      have h3 := hu.nn y.2.2.1
      have h4 := hβ.nn (inJ₂ y.2 - y.1)
      have h5 := hv.nn y.2.2.2
      have h6 := inv_nonneg.2 (absk_nonneg (inJ₂ y.2 - y.1))
      have h7 := bandW_nonneg D y.2.1
      split_ifs <;> positivity) hin hsum
  refine SB.equiv' leafE.symm hprod fun x => ?_
  have e : inJ₂ (leafE.symm x).2 - (leafE.symm x).1 = inJ x := rfl
  simp only [e]
  have e1 : (leafE.symm x).2.1 = x.1 := rfl
  have e2 : (leafE.symm x).2.2.1 = x.2.1 := rfl
  have e3 : (leafE.symm x).2.2.2 = x.2.2.1 := rfl
  have e4 : (leafE.symm x).1 = x.2.2.2 := rfl
  simp only [e1, e2, e3, e4]
  by_cases ha : x.2.1 2 = 0
  · by_cases hb : x.2.2.1 2 = 0
    · simp only [ha, hb, ↓reduceIte]
      ring
    · simp [hvs _ hb]
  · simp [hus _ ha]

/-- The low part of an `H¹` slow field is in `ℓ¹`, up to the root of a log. -/
lemma l1B_lo {f : Field} (hD : 1 ≤ D) (hf : MZ 1 f) (hf' : PiS f = f) :
    L1B (nrm (loP D f)) (Real.sqrt (9 + 8 * Real.log D) * hnorm 1 f) := by
  have hlog : 0 ≤ 9 + 8 * Real.log D := by
    have := Real.log_nonneg hD
    linarith
  have hB := (fib_band hD).slow (fun k => by
    have e : absk (-k) = absk k := by simp [absk, absSq]
    simp only [bandW, e])
  have hg := l2B_gr hf.inH
  have hb : L2B (sl fun k => bandW D k) (Real.sqrt (9 + 8 * Real.log D)) := by
    refine ⟨sl_nonneg (bandW_nonneg D), ?_, ?_⟩
    · refine hB.1.congr fun k => ?_
      simp only [sl]
      split_ifs <;> simp
    · refine Real.sqrt_le_sqrt ?_
      refine le_trans (le_of_eq ?_) hB.2
      refine tsum_congr fun k => ?_
      simp only [sl]
      split_ifs <;> simp
  obtain ⟨s0, hle⟩ := hb.pair hg
  have hle' : ∀ k, nrm (loP D f) k ≤ sl (fun k => bandW D k) k * gr f k := fun k => by
    simp only [nrm, loP, sl, gr]
    by_cases hk : k 2 = 0
    · by_cases hK : D < absk k
      · simp [hK, bandW, not_le.2 hK]
      · have hK' := not_lt.1 hK
        simp only [hK, ↓reduceIte, hk, bandW, hK']
        by_cases h0 : k = 0
        · simp [h0, hf.mean]
        · have h1 : 0 < absk k := lt_of_lt_of_le one_pos (one_le_absk h0)
          have : (absk k)⁻¹ * (absk k * ‖f k‖) = ‖f k‖ := by field_simp
          rw [this]
    · have h0 := slow_zero hf' hk
      simp [h0]
  have hs : Summable (nrm (loP D f)) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle' s0
  refine ⟨fun _ => norm_nonneg _, hs, ?_⟩
  exact (hs.tsum_le_tsum hle' s0).trans hle

variable {s : ℕ} {r τ : ℝ} {x : I4}

/-- The third slot may carry any `ℓ²` sequence, in the class of a weighted leaf. -/
lemma pos3_third {f₁ f₂ g : Mode → ℝ} {W₁ W₂ : ℝ} (hα : L2B α A) (hβ : L2B β B) (h1 : L1B f₁ W₁)
    (h2 : L1B f₂ W₂) (hg : L2B g U) :
    SB (Phi₃ α (in2 β) f₁ f₂ g) (A * (c4 * B) * (U * W₁ * W₂)) :=
  SB.equiv swap23 (SB.equiv swap12 (pos3_II' hα hβ.in2 hg h1 h2) (Phi₃_swap12 _ _ _ _ _))
    (Phi₃_swap23 _ _ _ _ _)

/-- The kernel of `O` with `H¹` leaves. -/
def Eleaf (D : ℝ) (x : I4) : ℝ :=
  2 + 2 * (absk x.2.2.2 * (absk (inJ x))⁻¹ ^ 2) +
    absk x.2.1 * absk x.2.2.1 * bandW (4 * D) x.1 * (absk (inJ x))⁻¹ ^ 2

lemma Eleaf_nonneg (D : ℝ) (x : I4) : 0 ≤ Eleaf D x := by
  have h1 := absk_nonneg x.2.2.2
  have h2 := absk_nonneg x.2.1
  have h3 := absk_nonneg x.2.2.1
  have h4 := bandW_nonneg (4 * D) x.1
  have h5 := inv_nonneg.2 (absk_nonneg (inJ x))
  unfold Eleaf
  positivity

/-- On the mask, the fine kernel over `L`. -/
lemma fine_le_Eleaf (hQ : OnQ D x) (hl0 : x.1 ≠ 0) (hj0 : inJ x ≠ 0) :
    (absk x.1)⁻¹ * Efine x ≤ Eleaf D x := by
  obtain ⟨hK15, hL7⟩ := hQ.lengths
  have hL1 := one_le_absk hl0
  have hJ1 := one_le_absk hj0
  have hL : 0 < absk x.1 := by linarith
  have hJ : 0 < absk (inJ x) := by linarith
  have ek : x.2.2.2 + inJ x = x.1 - x.2.1 - x.2.2.1 := by
    simp only [inJ]
    abel
  have hKJ := absk_add_le x.2.2.2 (inJ x)
  rw [ek] at hKJ
  have hc := hQ.c_le
  have hgt := hQ.c_gt
  have hk := hQ.l_le
  have hl4 : absk x.1 ≤ 4 * D := by linarith
  have hb : bandW (4 * D) x.1 = (absk x.1)⁻¹ := by simp [bandW, hl4]
  have hA := absk_nonneg x.2.1
  have hB := absk_nonneg x.2.2.1
  have hC := absk_nonneg x.2.2.2
  have hKn : 0 ≤ absk (x.1 - x.2.1 - x.2.2.1) := absk_nonneg _
  simp only [Efine, Eleaf, hb]
  set L := absk x.1
  set J := absk (inJ x)
  set K := absk (x.1 - x.2.1 - x.2.2.1)
  set A := absk x.2.1
  set B := absk x.2.2.1
  set C := absk x.2.2.2
  have e : L⁻¹ * ((K ^ 2 + A * B) / J ^ 2) = L⁻¹ * K * K * J⁻¹ ^ 2 + A * B * L⁻¹ * J⁻¹ ^ 2 := by
    field_simp
  rw [e]
  have hLK : L⁻¹ * K ≤ 2 := by
    rw [inv_mul_le_iff₀ hL]
    linarith [hQ.k_le]
  have hJi : J⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hJ1
  have hJi0 : 0 ≤ J⁻¹ := by positivity
  have h1 : L⁻¹ * K * K * J⁻¹ ^ 2 ≤ 2 * (C + J) * J⁻¹ ^ 2 := by
    have : L⁻¹ * K * K ≤ 2 * (C + J) := mul_le_mul hLK hKJ hKn (by norm_num)
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have h2 : 2 * (C + J) * J⁻¹ ^ 2 = 2 * (C * J⁻¹ ^ 2) + 2 * J⁻¹ := by
    field_simp
  linarith

/-- The block of `O` against the kernel. -/
lemma norm_O_leaf (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ : ℝ) (hx : Act₃ x) (hm : muQ D x ≠ 0)
    (t v w : V3) :
    ‖outerInv r (Hx₃ x) x.1 (inJ x) ((famQ s r D).Sr x τ t v w)‖ ≤
      2 ^ 36 / |r| ^ 2 * (‖t‖ * ‖v‖ * ‖w‖) * Eleaf D x := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hQ := onQ_of_ne hm
  obtain ⟨-, hL7⟩ := hQ.lengths
  have hS := norm_source_fine (D := D) hs hr τ hx t v w
  have hl0 := act_l hx
  obtain ⟨ha, hb, hc, hj⟩ := hx
  have hj0 : inJ x ≠ 0 := fun h => hj (by rw [h]; rfl)
  have hJ1 := one_le_absk hj0
  have hL : 0 < absk x.1 := by linarith
  have h2 : x.1 2 = inJ x 2 := by
    simp [inJ, ha, hb, hc]
  have hd : 3 / 4 * absk x.1 ≤ |absk (inJ x) - absk x.1| := by
    rw [abs_sub_comm]
    refine le_trans ?_ (le_abs_self _)
    linarith
  have h1 := norm_outerInv_sep hr h2 hj (H := Hx₃ x) (d := 3 / 4 * absk x.1) (by positivity) hd
    ((famQ s r D).Sr x τ t v w)
  have hV : 0 ≤ ‖t‖ * ‖v‖ * ‖w‖ := by positivity
  have hE := fine_le_Eleaf hQ hl0 hj0
  have hE0 := Efine_nonneg x
  calc _ ≤ 4 / (|r| * (3 / 4 * absk x.1)) * (2 ^ 33 / |r| * (‖t‖ * ‖v‖ * ‖w‖) * Efine x) :=
        h1.trans (mul_le_mul_of_nonneg_left hS (by positivity))
    _ = 16 / 3 * 2 ^ 33 / |r| ^ 2 * (‖t‖ * ‖v‖ * ‖w‖) * ((absk x.1)⁻¹ * Efine x) := by
        field_simp
        ring
    _ ≤ 16 / 3 * 2 ^ 33 / |r| ^ 2 * (‖t‖ * ‖v‖ * ‖w‖) * Eleaf D x :=
        mul_le_mul_of_nonneg_left hE (by positivity)
    _ ≤ _ := by
        have hK := Eleaf_nonneg D x
        have h3 : 16 / 3 * (2 : ℝ) ^ 33 / |r| ^ 2 ≤ 2 ^ 36 / |r| ^ 2 :=
          div_le_div_of_nonneg_right (by norm_num) (by positivity)
        gcongr

/-- The `H¹` norm of the low part. -/
lemma l2B_gr_lo {f : Field} (hf : InH 1 f) (D : ℝ) : L2B (gr (loP D f)) (hnorm 1 f) := by
  have h0 : ∀ k, ‖loP D f k‖ ≤ ‖f k‖ := fun k => by
    simp only [loP]
    split_ifs
    · simp
    · exact le_rfl
  obtain ⟨h1, h2⟩ := hnorm_le_of_sq (a := loP D f) (b := f) (c := 1) (s := 1) (s' := 1) hf
    zero_le_one fun k => by
      rw [one_pow, one_mul]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (h0 k) 2)
        (sobWeight_nonneg _ k)
  rw [one_mul] at h2
  exact (l2B_gr h1).mono h2

lemma loP_of_le {D : ℝ} (f : Field) {k : Mode} (h : absk k ≤ D) : loP D f k = f k := by
  simp [loP, not_lt.2 h]

/-- The majorant with `H¹` leaves. -/
def PsiQ (D : ℝ) (f₁ f₂ f₃ G F : Field) (x : I4) : ℝ :=
  2 * Phi₃ (nrm G) (nrm F) (nrm (loP D f₁)) (nrm (loP D f₂)) (nrm (loP D f₃)) x +
    2 * Phi₃ (nrm G) (in2 (nrm F)) (nrm (loP D f₁)) (nrm (loP D f₂)) (gr (loP D f₃)) x +
    nrm G x.1 * bandW (4 * D) x.1 * (nrm F (inJ x) * (absk (inJ x))⁻¹ ^ 2) *
      (gr (loP D f₁) x.2.1 * gr (loP D f₂) x.2.2.1 * nrm (loP D f₃) x.2.2.2)

/-- **`O` with `H¹` leaves** (Body 33, `D_S Q₃`). -/
theorem Q3_leaf (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ : ℝ) (hD : 1 ≤ D) {f₁ f₂ f₃ G F : Field}
    (h1 : MZ 1 f₁) (h1' : PiS f₁ = f₁) (h2 : MZ 1 f₂) (h2' : PiS f₂ = f₂) (h3 : MZ 1 f₃)
    (h3' : PiS f₃ = f₃) (hG : Summable fun k => ‖G k‖ ^ 2) (hF : Summable fun k => ‖F k‖ ^ 2)
    (hF' : PiF F = F) {W₁ W₂ W₃ : ℝ} (w1 : L1B (nrm (loP D f₁)) W₁) (w2 : L1B (nrm (loP D f₂)) W₂)
    (w3 : L1B (nrm (loP D f₃)) W₃) :
    ‖(famQ s r D).form r τ f₁ f₂ f₃ G F‖ ≤ 2 ^ 36 / |r| ^ 2 * (l2n G * l2n F *
      (2 * (W₁ * W₂ * W₃) + 2 * (c4 * (hnorm 1 f₃ * W₁ * W₂)) +
        Real.sqrt 17 * Real.sqrt (9 + 8 * Real.log (4 * D)) *
          (hnorm 1 f₁ * hnorm 1 f₂ * W₃))) := by
  have hr0 : 0 < |r| := abs_pos.2 hr
  have hD4 : 1 ≤ 4 * D := by linarith
  have α := l2B_nrm hG
  have β := l2B_nrm hF
  have s1 : SB (Phi₃ (nrm G) (nrm F) (nrm (loP D f₁)) (nrm (loP D f₂)) (nrm (loP D f₃)))
      (l2n G * l2n F * (W₁ * W₂ * W₃)) := pos3_I α β w1 w2 w3
  have s2 := pos3_third α β w1 w2 (l2B_gr_lo h3.inH D)
  have s3 := pos3_band hD4 α β (l2B_gr_lo h1.inH D) (l2B_gr_lo h2.inH D) w3
    (fun p hp => by
      have : loP D f₁ p = 0 := by
        simp only [loP]
        split_ifs
        · rfl
        · exact slow_zero h1' hp
      simp [gr, this])
    (fun p hp => by
      have : loP D f₂ p = 0 := by
        simp only [loP]
        split_ifs
        · rfl
        · exact slow_zero h2' hp
      simp [gr, this])
  have hsum := (((s1.const_mul (by norm_num : (0 : ℝ) ≤ 2)).add
    (s2.const_mul (by norm_num : (0 : ℝ) ≤ 2))).add s3).const_mul
    (by positivity : 0 ≤ 2 ^ 36 / |r| ^ 2)
  have hP : ∀ x, 0 ≤ PsiQ D f₁ f₂ f₃ G F x := fun x => by
    have n0 : ∀ (u : Field) k, 0 ≤ nrm u k := fun u k => norm_nonneg _
    have a1 := Phi₃_nonneg (n0 G) (n0 F) (n0 (loP D f₁)) (n0 (loP D f₂)) (n0 (loP D f₃)) x
    have a2 : 0 ≤ Phi₃ (nrm G) (in2 (nrm F)) (nrm (loP D f₁)) (nrm (loP D f₂)) (gr (loP D f₃)) x :=
      Phi₃_nonneg (n0 G) (fun k => div_nonneg (n0 F k) (absSq_nonneg k))
        (n0 (loP D f₁)) (n0 (loP D f₂)) (gr_nonneg (loP D f₃)) x
    have a3 := gr_nonneg (loP D f₁) x.2.1
    have a4 := gr_nonneg (loP D f₂) x.2.2.1
    have a5 := bandW_nonneg (4 * D) x.1
    have a6 := n0 G x.1
    have a7 := n0 F (inJ x)
    have a8 := n0 (loP D f₃) x.2.2.2
    have a9 := inv_nonneg.2 (absk_nonneg (inJ x))
    unfold PsiQ
    positivity
  have hb : ∀ x, ‖(famQ s r D).T r x (G x.1) (F (inJ x)) (f₁ x.2.1) (f₂ x.2.2.1) (f₃ x.2.2.2) τ‖ ≤
      2 ^ 36 / |r| ^ 2 * PsiQ D f₁ f₂ f₃ G F x := fun x => by
    refine Fam3.T_form_le h1' h2' h3' hF' (B := fun x => 2 ^ 36 / |r| ^ 2 * PsiQ D f₁ f₂ f₃ G F x)
      (fun x => mul_nonneg (by positivity) (hP x)) (fun x hx => ?_) x
    by_cases hm : muQ D x = 0
    · have : (famQ s r D).T r x (G x.1) (F (inJ x)) (f₁ x.2.1) (f₂ x.2.2.1) (f₃ x.2.2.2) τ = 0 := by
        simp only [Fam3.T]
        rw [O_zero hm, outerInv_zero]
        simp
      rw [this, norm_zero]
      exact mul_nonneg (by positivity) (hP x)
    have hQ := onQ_of_ne hm
    have hO := norm_O_leaf (D := D) hs hr τ hx hm (f₁ x.2.1) (f₂ x.2.2.1) (f₃ x.2.2.2)
    refine (norm_inner_apply_le _ _ _).trans ?_
    have hn : 0 ≤ ‖G x.1‖ * ‖F (inJ x)‖ := by positivity
    refine (mul_le_mul_of_nonneg_left hO hn).trans (le_of_eq ?_)
    have e1 := loP_of_le (D := D) f₁ hQ.a_le
    have e2 := loP_of_le (D := D) f₂ hQ.b_le
    have e3 := loP_of_le (D := D) f₃ hQ.c_le
    simp only [PsiQ, Phi₃, nrm, gr, in2, Eleaf, e1, e2, e3, div_eq_mul_inv, ← absk_sq (inJ x)]
    simp only [inv_pow]
    ring
  have hS : SB (fun x => 2 ^ 36 / |r| ^ 2 * PsiQ D f₁ f₂ f₃ G F x) (2 ^ 36 / |r| ^ 2 *
      (2 * (l2n G * l2n F * (W₁ * W₂ * W₃)) + 2 * (l2n G * (c4 * l2n F) * (hnorm 1 f₃ * W₁ * W₂)) +
        l2n G * hnorm 1 f₁ * Real.sqrt 17 * (l2n F * hnorm 1 f₂ *
          Real.sqrt (9 + 8 * Real.log (4 * D))) * W₃)) := hsum
  refine (form_le hS hb).2.trans (le_of_eq ?_)
  ring

end OVNS.Quant.Metric

end
