import OddViscousNS.Quant.Joint.Metric.LowPass

/-!
# The sum of the bands (step J5, node N6)

`hnorm_Qlo_le`: `‖Q_lo(S, F)‖_σ ≤ C_σ M ‖F‖_{σ+1}`: Body 27 at `m = σ`, Body 42 at `σ = 1`.
-/

open MeasureTheory Set Filter
open scoped ENNReal ComplexConjugate Real

noncomputable section

namespace OVNS.Quant.Metric

open GN (SupBd cv cmp)

variable {S F : Field} {M : ℝ} {i : ℕ}

lemma adm_chiF_l2 (hS2 : Summable fun k => ‖S k‖ ^ 2) :
    Summable fun k => ‖chiF i S k‖ ^ 2 :=
  Summable.of_nonneg_of_le (fun _ => by positivity)
    (fun k => pow_le_pow_left₀ (norm_nonneg _) (norm_chiF_le i S k) 2) hS2

lemma lowM_nonneg (p j : Mode) : 0 ≤ lowM p j := chiM_nonneg _ _

lemma lowM_le_one (p j : Mode) : lowM p j ≤ 1 := chiM_le_one _ _

/-- The Schur weight: the sum over the bands that reach `K`. -/
lemma sb_weight {K : ℝ} (hK : 0 < K) :
    SB (fun i : ℕ => (if K ≤ 2 ^ (i + 8) then K / 2 ^ (i + 8) else 0) ^ 2) 2 := by
  have hex : ∃ n : ℕ, K ≤ 2 ^ (n + 8) := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt K (by norm_num : (1 : ℝ) < 2)
    refine ⟨n, hn.le.trans ?_⟩
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  classical
  set m := Nat.find hex with hm
  have hmK : K ≤ 2 ^ (m + 8) := Nat.find_spec hex
  have hlt : ∀ i, i < m → ¬ K ≤ 2 ^ (i + 8) := fun i hi => Nat.find_min hex hi
  set f : ℕ → ℝ := fun i => (if K ≤ 2 ^ (i + 8) then K / 2 ^ (i + 8) else 0) ^ 2 with hf
  have hf0 : ∀ i, 0 ≤ f i := fun i => sq_nonneg _
  have hle : ∀ n, f (n + m) ≤ (1 / 2 : ℝ) ^ n := fun n => by
    have h1 : K ≤ 2 ^ (n + m + 8) := hmK.trans (pow_le_pow_right₀ (by norm_num) (by omega))
    have hp : (0 : ℝ) < 2 ^ (n + m + 8) := by positivity
    have h2 : K / 2 ^ (n + m + 8) ≤ (1 / 2) ^ n := by
      rw [div_le_iff₀ hp]
      calc K ≤ 2 ^ (m + 8) := hmK
        _ = (1 / 2) ^ n * 2 ^ (n + m + 8) := by
            have e : (2 : ℝ) ^ (n + m + 8) = 2 ^ n * 2 ^ (m + 8) := by ring
            rw [e, ← mul_assoc, ← mul_pow]
            norm_num
    have h3 : K / 2 ^ (n + m + 8) ≤ 1 := (div_le_one hp).2 h1
    have h4 : 0 ≤ K / 2 ^ (n + m + 8) := by positivity
    simp only [hf, h1, ↓reduceIte]
    calc (K / 2 ^ (n + m + 8)) ^ 2 ≤ (K / 2 ^ (n + m + 8)) ^ 1 :=
          pow_le_pow_of_le_one h4 h3 (by norm_num)
      _ ≤ _ := by rw [pow_one]; exact h2
  have hs : Summable fun n => f (n + m) :=
    Summable.of_nonneg_of_le (fun n => hf0 _) hle summable_geometric_two
  have hsf : Summable f := (summable_nat_add_iff m).1 hs
  refine ⟨hsf, ?_⟩
  rw [← hsf.sum_add_tsum_nat_add m]
  have h0 : ∑ i ∈ Finset.range m, f i = 0 := Finset.sum_eq_zero fun i hi => by
    have := hlt i (Finset.mem_range.1 hi)
    simp only [hf, this, ↓reduceIte]
    norm_num
  rw [h0, zero_add]
  exact (hs.tsum_le_tsum hle summable_geometric_two).trans (le_of_eq tsum_geometric_two)

/-- **The Schur test on the bands.** -/
lemma schur_k {x : ℕ → ℝ} (hx0 : ∀ i, 0 ≤ x i) {K : ℝ} (hK : 0 < K)
    (hsupp : ∀ i, x i ≠ 0 → K ≤ 2 ^ (i + 8))
    (hs : Summable fun i => x i ^ 2 * (2 ^ (i + 8) / K) ^ 2) :
    Summable x ∧ (∑' i, x i) ^ 2 ≤ 2 * ∑' i, x i ^ 2 * (2 ^ (i + 8) / K) ^ 2 := by
  set B := ∑' i, x i ^ 2 * (2 ^ (i + 8) / K) ^ 2 with hB
  have hB0 : 0 ≤ B := tsum_nonneg fun i => by positivity
  have hP := sb_weight hK
  have hQ : SB (fun i => (x i * (2 ^ (i + 8) / K)) ^ 2) (Real.sqrt B ^ 2) := by
    rw [Real.sq_sqrt hB0]
    simp only [mul_pow]
    exact ⟨hs, le_rfl⟩
  have hP' : SB (fun i : ℕ => (if K ≤ 2 ^ (i + 8) then K / 2 ^ (i + 8) else 0) ^ 2)
      (Real.sqrt 2 ^ 2) := by
    rw [Real.sq_sqrt (by norm_num)]
    exact hP
  have hc := SB.cs (P := fun i : ℕ => if K ≤ 2 ^ (i + 8) then K / 2 ^ (i + 8) else 0)
    (Q := fun i => x i * (2 ^ (i + 8) / K)) (fun i => by
      split_ifs
      · positivity
      · exact le_rfl) (fun i => mul_nonneg (hx0 i) (by positivity)) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) hP' hQ
  have e : (fun i : ℕ => (if K ≤ 2 ^ (i + 8) then K / 2 ^ (i + 8) else 0) *
      (x i * (2 ^ (i + 8) / K))) = x := by
    funext i
    by_cases hi : K ≤ 2 ^ (i + 8)
    · simp only [hi, ↓reduceIte]
      field_simp
    · have : x i = 0 := by
        by_contra h
        exact hi (hsupp i h)
      simp [this]
  rw [e] at hc
  refine ⟨hc.1, ?_⟩
  have h0 : 0 ≤ ∑' i, x i := tsum_nonneg hx0
  calc (∑' i, x i) ^ 2 ≤ (Real.sqrt 2 * Real.sqrt B) ^ 2 := pow_le_pow_left₀ h0 hc.2 2
    _ = 2 * B := by rw [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hB0]

/-- The norm of a block term is summable. -/
lemma blk_norm_summable {m : Mult} (hm : m.Bdd) {f g : Field} (hf : Summable fun k => ‖f k‖ ^ 2)
    (hg : Summable fun k => ‖g k‖ ^ 2) (k : Mode) :
    Summable fun p => ‖blk m p k (k - p) (f p) (g (k - p))‖ := by
  have hg' : Summable fun p => ‖g (k - p)‖ ^ 2 := (Equiv.subLeft k).summable_iff.2 hg
  have h0 : Summable fun p => ‖f p‖ * ‖g (k - p)‖ :=
    Summable.of_nonneg_of_le (fun p => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun p => by nlinarith only [sq_nonneg (‖f p‖ - ‖g (k - p)‖)]) (hf.add hg')
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) (h0.mul_left (8 * absk k))
  have hb := norm_blk_le hm (show p + (k - p) = k by abel) (f p)
  have h1 := (ContinuousLinearMap.le_opNorm (blk m p k (k - p) (f p)) (g (k - p))).trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
  exact h1.trans (le_of_eq (by ring))

/-- **The bands sum to the low product.** -/
lemma Qlo_hasSum (τ : ℝ) (hS2 : Summable fun k => ‖S k‖ ^ 2) (hF2 : Summable fun k => ‖F k‖ ^ 2)
    (k : Mode) : HasSum (fun i => Qband τ S F i k) (Qlo τ S F k) := by
  set t : Mode → V3 := fun p => ((lowM p (k - p) : ℝ) : ℂ) •
    blk (phaseM τ) p k (k - p) (S p) (F (k - p)) with ht
  have hts : Summable t := by
    refine Summable.of_norm_bounded (blk_norm_summable (phaseM_bdd τ) hS2 hF2 k) fun p => ?_
    simp only [ht]
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (lowM_nonneg _ _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (lowM_le_one _ _)
  set H : ℕ × Mode → V3 := fun x => if bnd (k - x.2) = x.1 then t x.2 else 0 with hH
  have hinj : Function.Injective fun p : Mode => (bnd (k - p), p) := fun a b h =>
    (Prod.ext_iff.1 h).2
  have hzero : ∀ x ∉ range (fun p : Mode => (bnd (k - p), p)), H x = 0 := fun x hx => by
    simp only [hH]
    split_ifs with h
    · exact absurd ⟨x.2, Prod.ext h rfl⟩ hx
    · rfl
  have hcomp : H ∘ (fun p : Mode => (bnd (k - p), p)) = t := by
    funext p
    simp [hH]
  have hsum : HasSum H (Qlo τ S F k) := by
    refine (hinj.hasSum_iff hzero).1 ?_
    rw [hcomp]
    exact hts.hasSum
  have hfib : ∀ i, HasSum (fun p => H (i, p)) (Qband τ S F i k) := fun i => by
    have hA := adm_chiF_l2 (i := i) hS2
    have hB : Summable fun k => ‖bandF i F k‖ ^ 2 :=
      Summable.of_nonneg_of_le (fun _ => by positivity)
        (fun k => pow_le_pow_left₀ (norm_nonneg _) (norm_bandF_le i F k) 2) hF2
    have h1 := (blk_summable (phaseM_bdd τ) hA hB k).hasSum
    have e : (fun p => H (i, p)) = fun p =>
        blk (phaseM τ) p k (k - p) (chiF i S p) (bandF i F (k - p)) := by
      funext p
      rw [Qband_term]
    rw [e]
    have e2 : Qband τ S F i k =
        ∑' p, blk (phaseM τ) p k (k - p) (chiF i S p) (bandF i F (k - p)) :=
      Qm_eq_tsum_blk _ _ _ _
    rw [e2]
    exact h1
  exact hsum.prod_fiberwise hfib

/-! ### The estimate -/

/-- A nonnegative double sum, in the other order. -/
lemma SB.fst_swap {ι κ : Type*} {H : ι × κ → ℝ} {C : ℝ} (h : SB H C) :
    (Summable fun y : κ × ι => H (y.2, y.1)) ∧ SB (fun k => ∑' i, H (i, k)) C := by
  have hs : Summable fun y : κ × ι => H (y.2, y.1) := (Equiv.prodComm κ ι).summable_iff.2 h.1
  refine ⟨hs, hs.prod, ?_⟩
  rw [← hs.tsum_prod]
  exact ((Equiv.prodComm κ ι).tsum_eq H).le.trans h.2

lemma sobWeight_nat (σ : ℕ) {k : Mode} (hk : k ≠ 0) : sobWeight σ k = absk k ^ (2 * σ) := by
  simp only [sobWeight, hk, ite_false]
  rw [show (2 : ℝ) * σ = ((2 * σ : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]

/-- The bands exhaust the norm. -/
lemma sb_bands (s : ℕ) (hF : InH s F) (hF0 : F 0 = 0) :
    SB (fun i : ℕ => ((2 : ℝ) ^ i) ^ (2 * s) * ∑' k, ‖bandF i F k‖ ^ 2) (hnorm s F ^ 2) := by
  set H : Mode × ℕ → ℝ := fun x => ((2 : ℝ) ^ x.2) ^ (2 * s) * ‖bandF x.2 F x.1‖ ^ 2 with hH
  have hc : SB (fun k => sobWeight s k * ‖F k‖ ^ 2) (hnorm s F ^ 2) := by
    refine ⟨hF, ?_⟩
    rw [hnorm_sq hF]
  have hin : ∀ k, SB (fun i => H (k, i)) (sobWeight s k * ‖F k‖ ^ 2) := fun k => by
    by_cases hk : k = 0
    · subst hk
      have e : ∀ i, H (0, i) = 0 := fun i => by
        simp [hH, bandF, hF0]
      simp only [e, hF0, norm_zero]
      simp [SB, summable_zero]
    have hzero : ∀ i, i ≠ bnd k → H (k, i) = 0 := fun i hi => by
      have : bandF i F k = 0 := by simp [bandF, hi.symm]
      simp [hH, this]
    have hval : H (k, bnd k) ≤ sobWeight s k * ‖F k‖ ^ 2 := by
      simp only [hH, bandF, ite_true]
      rw [sobWeight_nat s hk]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact pow_le_pow_left₀ (by positivity) (two_pow_bnd_le hk) _
    have hS := hasSum_single (bnd k) hzero
    exact ⟨hS.summable, by rw [hS.tsum_eq]; exact hval⟩
  have hp := SB.prod (H := H) (fun x => by positivity) hin hc
  have h2 := (SB.fst_swap hp).2
  have e : ∀ i : ℕ, ∑' k, H (k, i) = ((2 : ℝ) ^ i) ^ (2 * s) * ∑' k, ‖bandF i F k‖ ^ 2 :=
    fun i => by
    simp only [hH]
    rw [tsum_mul_left]
  simp only [e] at h2
  exact h2

/-- The weight of the band `i`. -/
def Yb (τ : ℝ) (S F : Field) (s : ℕ) (i : ℕ) (k : Mode) : ℝ :=
  ((2 : ℝ) ^ (i + 8)) ^ (2 * s) * dq (chiF i S) (rotF τ (bandF i F)) k

/-- The product of one band. -/
lemma dq_band (τ : ℝ) (hS : Adm 2 S) (hM : SupBd S M) (hF : Adm 2 F) (i : ℕ) :
    Summable (dq (chiF i S) (rotF τ (bandF i F))) ∧
      ∑' k, dq (chiF i S) (rotF τ (bandF i F)) k ≤ 243 * M ^ 2 * ∑' k, ‖bandF i F k‖ ^ 2 := by
  have hA := adm_bandF hF i
  have l2 := summable_norm_sq_of_inH (hA.inH.mono (by norm_num : (0 : ℝ) ≤ 2))
  have l3 := summable_norm_sq_of_inH ((hA.rotF τ).inH.mono (by norm_num : (0 : ℝ) ≤ 2))
  have hw : Summable fun k => ‖chiF i S k‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_chiF_le i S) (summable_wiener hS.inH)
  obtain ⟨h1, h2⟩ := sum_dq hw (supBd_chiF (summable_wiener hS.inH) hM i) l3
  refine ⟨h1, h2.trans ?_⟩
  have hle : ∑' k, ‖rotF τ (bandF i F) k‖ ^ 2 ≤ ∑' k, ‖bandF i F k‖ ^ 2 := by
    refine Summable.tsum_le_tsum (fun k => ?_) l3 l2
    change ‖rot τ k (bandF i F k)‖ ^ 2 ≤ _
    rw [norm_rot]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_leray_le _ _) 2
  have e : 3 * (9 * M) ^ 2 = 243 * M ^ 2 := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_left hle (by positivity)

/-- The sum of the band weights. -/
lemma sb_Yb (τ : ℝ) (hS : Adm 2 S) (hM : SupBd S M) (hF : Adm 2 F) (s : ℕ) (hFs : InH s F) :
    SB (fun x : ℕ × Mode => Yb τ S F s x.1 x.2)
      ((2 ^ 8) ^ (2 * s) * (243 * M ^ 2) * hnorm s F ^ 2) := by
  have hb := sb_bands s hFs hF.mean
  have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
  have hc : SB (fun i : ℕ => (2 ^ 8) ^ (2 * s) * (243 * M ^ 2) *
      (((2 : ℝ) ^ i) ^ (2 * s) * ∑' k, ‖bandF i F k‖ ^ 2))
      ((2 ^ 8) ^ (2 * s) * (243 * M ^ 2) * hnorm s F ^ 2) := hb.const_mul (by positivity)
  have hin : ∀ i, SB (fun k => Yb τ S F s i k) ((2 ^ 8) ^ (2 * s) * (243 * M ^ 2) *
      (((2 : ℝ) ^ i) ^ (2 * s) * ∑' k, ‖bandF i F k‖ ^ 2)) := fun i => by
    obtain ⟨h1, h3⟩ := dq_band τ hS hM hF i
    refine ⟨h1.mul_left _, ?_⟩
    simp only [Yb]
    rw [tsum_mul_left]
    have e : ((2 : ℝ) ^ (i + 8)) ^ (2 * s) = (2 ^ 8) ^ (2 * s) * ((2 : ℝ) ^ i) ^ (2 * s) := by
      rw [← mul_pow, ← pow_add, add_comm]
    rw [e]
    calc _ ≤ (2 ^ 8) ^ (2 * s) * ((2 : ℝ) ^ i) ^ (2 * s) * (243 * M ^ 2 * ∑' k, ‖bandF i F k‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := by ring
  exact SB.prod (H := fun x : ℕ × Mode => Yb τ S F s x.1 x.2)
    (fun x => mul_nonneg (by positivity) (dq_nonneg _ _ _)) hin hc

/-- The pointwise estimate at an output mode. -/
lemma Qlo_point (τ : ℝ) (hS : Adm 2 S) (hS' : PiS S = S) (hF : Adm 2 F) (σ : ℕ) {k : Mode}
    (hsum : Summable fun i => Yb τ S F (σ + 1) i k) :
    sobWeight σ k * ‖Qlo τ S F k‖ ^ 2 ≤ 2 * ∑' i, Yb τ S F (σ + 1) i k := by
  have hY0 : ∀ i, 0 ≤ Yb τ S F (σ + 1) i k := fun i =>
    mul_nonneg (by positivity) (dq_nonneg _ _ _)
  by_cases hk : k = 0
  · subst hk
    have : sobWeight σ (0 : Mode) = 0 := by simp [sobWeight]
    rw [this, zero_mul]
    have h0 : 0 ≤ ∑' i, Yb τ S F (σ + 1) i 0 := tsum_nonneg hY0
    linarith
  rw [sobWeight_nat σ hk]
  have hK1 : 1 ≤ absk k := one_le_absk hk
  have hK : 0 < absk k := by linarith
  set K := absk k with hKdef
  set x : ℕ → ℝ := fun i => ‖Qband τ S F i k‖ with hx
  have hx0 : ∀ i, 0 ≤ x i := fun i => norm_nonneg _
  have hsupp : ∀ i, x i ≠ 0 → K ≤ 2 ^ (i + 8) := fun i hi => by
    by_contra h
    rw [not_le] at h
    exact hi (by simp only [hx]; rw [Qband_zero τ hS' h, norm_zero])
  have hterm : ∀ i, K ^ (2 * σ) * (x i ^ 2 * (2 ^ (i + 8) / K) ^ 2) ≤
      Yb τ S F (σ + 1) i k := fun i => by
    by_cases hi : x i = 0
    · rw [hi]
      have := hY0 i
      simpa using this
    have hle := hsupp i hi
    have h2 := norm_Qphase_sq_le τ (adm_chiF hS i) (PiS_chiF hS' i) (adm_bandF hF i) k
    change x i ^ 2 ≤ absSq k * _ at h2
    rw [← absk_sq k] at h2
    set d := dq (chiF i S) (rotF τ (bandF i F)) k with hd
    have hd0 : 0 ≤ d := dq_nonneg _ _ _
    set T : ℝ := 2 ^ (i + 8) with hT
    have hT0 : 0 < T := by positivity
    have e : K ^ (2 * σ) * (K ^ 2 * d * (T / K) ^ 2) = K ^ (2 * σ) * (T ^ 2 * d) := by
      field_simp
    calc K ^ (2 * σ) * (x i ^ 2 * (T / K) ^ 2) ≤ K ^ (2 * σ) * (K ^ 2 * d * (T / K) ^ 2) := by
          gcongr
      _ = K ^ (2 * σ) * (T ^ 2 * d) := e
      _ ≤ T ^ (2 * σ) * (T ^ 2 * d) := by
          have : K ^ (2 * σ) ≤ T ^ (2 * σ) := pow_le_pow_left₀ hK.le hle _
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ = Yb τ S F (σ + 1) i k := by
          simp only [Yb]
          rw [← hd, ← hT]
          have : T ^ (2 * (σ + 1)) = T ^ (2 * σ) * T ^ 2 := by
            rw [← pow_add]
            congr 1
          rw [this]
          ring
  have hKp : 1 ≤ K ^ (2 * σ) := one_le_pow₀ hK1
  have hs : Summable fun i => x i ^ 2 * (2 ^ (i + 8) / K) ^ 2 :=
    Summable.of_nonneg_of_le (fun i => by positivity) (fun i => by
      refine le_trans ?_ (hterm i)
      exact le_mul_of_one_le_left (by positivity) hKp) hsum
  obtain ⟨hsx, hcs⟩ := schur_k hx0 hK hsupp hs
  have hF2 := summable_norm_sq_of_inH (hF.inH.mono (by norm_num : (0 : ℝ) ≤ 2))
  have hS2 := summable_norm_sq_of_inH (hS.inH.mono (by norm_num : (0 : ℝ) ≤ 2))
  have h1 : ‖Qlo τ S F k‖ ≤ ∑' i, x i := by
    rw [← (Qlo_hasSum τ hS2 hF2 k).tsum_eq]
    exact norm_tsum_le_tsum_norm hsx
  have h2 : ‖Qlo τ S F k‖ ^ 2 ≤ 2 * ∑' i, x i ^ 2 * (2 ^ (i + 8) / K) ^ 2 :=
    (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans hcs
  have h3 : K ^ (2 * σ) * ∑' i, x i ^ 2 * (2 ^ (i + 8) / K) ^ 2 ≤ ∑' i, Yb τ S F (σ + 1) i k := by
    rw [← tsum_mul_left]
    exact (hs.mul_left _).tsum_le_tsum hterm hsum
  calc K ^ (2 * σ) * ‖Qlo τ S F k‖ ^ 2
      ≤ K ^ (2 * σ) * (2 * ∑' i, x i ^ 2 * (2 ^ (i + 8) / K) ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 2 * (K ^ (2 * σ) * ∑' i, x i ^ 2 * (2 ^ (i + 8) / K) ^ 2) := by ring
    _ ≤ _ := by linarith

/-- The constant of the low product. -/
def CLow (σ : ℕ) : ℝ := Real.sqrt (2 * ((2 ^ 8) ^ (2 * (σ + 1)) * 243))

lemma CLow_nonneg (σ : ℕ) : 0 ≤ CLow σ := Real.sqrt_nonneg _

/-- **The low last edge** (Bodies 27, 42): `‖Q_lo(S, F)‖_σ ≤ C M ‖F‖_{σ+1}`. -/
theorem hnorm_Qlo_le (τ : ℝ) (hS : Adm 2 S) (hS' : PiS S = S) (hM : SupBd S M) (hF : Adm 2 F)
    (σ : ℕ) (hFs : InH ((σ + 1 : ℕ) : ℝ) F) :
    InH σ (Qlo τ S F) ∧ hnorm σ (Qlo τ S F) ≤ CLow σ * M * hnorm ((σ + 1 : ℕ) : ℝ) F := by
  have hY := sb_Yb τ hS hM hF (σ + 1) hFs
  obtain ⟨hs0, hs1⟩ := SB.fst_swap hY
  have hpt : ∀ k, sobWeight σ k * ‖Qlo τ S F k‖ ^ 2 ≤ 2 * ∑' i, Yb τ S F (σ + 1) i k := fun k =>
    Qlo_point τ hS hS' hF σ (hs0.prod_factor k)
  have hS2 : Summable fun k => 2 * ∑' i, Yb τ S F (σ + 1) i k := hs1.1.mul_left 2
  have hin : InH σ (Qlo τ S F) := Summable.of_nonneg_of_le
    (fun k => mul_nonneg (sobWeight_nonneg _ k) (by positivity)) hpt hS2
  refine ⟨hin, ?_⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hC : 0 ≤ CLow σ := CLow_nonneg σ
  have hn := hnorm_nonneg ((σ + 1 : ℕ) : ℝ) F
  have hsq : hnorm σ (Qlo τ S F) ^ 2 ≤ (CLow σ * M * hnorm ((σ + 1 : ℕ) : ℝ) F) ^ 2 := by
    rw [hnorm_sq hin]
    refine (Summable.tsum_le_tsum hpt hin hS2).trans ?_
    rw [tsum_mul_left]
    have h3 := hs1.2
    rw [mul_pow, mul_pow, CLow, Real.sq_sqrt (by positivity)]
    calc _ ≤ 2 * ((2 ^ 8) ^ (2 * (σ + 1)) * (243 * M ^ 2) * hnorm ((σ + 1 : ℕ) : ℝ) F ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (hnorm_nonneg _ _) (by positivity) (by norm_num)).1 hsq

end OVNS.Quant.Metric

end
