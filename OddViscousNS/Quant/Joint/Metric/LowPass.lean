import OddViscousNS.Quant.Joint.Metric.Fejer

/-!
# The low last edge (step J5, node N6)

Bodies 27, 42: `‖A^{−1/2} 𝓛_lo(S) z‖₀ ≲ M_∞ ‖z‖₀`.

The output of `Q(S_lo, F)` is `div` of a product, so one derivative is on the output; each band of
the fast input meets its own low-pass copy of `S`, whose sup norm is at most `9 M`
(`supBd_chiF`); the bands add up by a Schur test (`schur_k`), since the output of band `i` lives at
`K ≤ 2^{i+8}` (`Qband_zero`).
-/

open MeasureTheory Set Filter UnitAddTorus
open scoped ENNReal ComplexConjugate Real

noncomputable section

namespace OVNS.Quant.Metric

open GN (SupBd cv cmp)

/-! ### The divergence form of a product -/

/-- `(f·∇)g` is a divergence, for solenoidal `f`. -/
lemma advect_div {f g : Field} {k : Mode} (hf : IsSolenoidal f)
    (hs : Summable fun p => ‖f p‖ * ‖g (k - p)‖) (a : Fin 3) :
    advect f g k a = Complex.I * ∑ i, (k i : ℂ) * cv (cmp f i) (cmp g a) k := by
  have hdot : ∀ p, dotM (f p) (k - p) = dotM (f p) k := fun p => by
    have h := hf p
    simp only [dotM, Pi.sub_apply, Int.cast_sub, mul_sub, Finset.sum_sub_distrib] at h ⊢
    rw [h, sub_zero]
  have hsum : Summable fun p => (Complex.I * dotM (f p) (k - p)) • g (k - p) := by
    refine Summable.of_norm_bounded (hs.mul_left (absk k)) fun p => ?_
    rw [norm_smul, norm_mul, Complex.norm_I, one_mul, hdot]
    calc ‖dotM (f p) k‖ * ‖g (k - p)‖ ≤ (‖f p‖ * absk k) * ‖g (k - p)‖ :=
          mul_le_mul_of_nonneg_right (norm_dotM_le _ _) (norm_nonneg _)
      _ = _ := by ring
  have e := (EuclideanSpace.proj (𝕜 := ℂ) a).map_tsum hsum
  have hterm : ∀ p,
      (EuclideanSpace.proj (𝕜 := ℂ) a) ((Complex.I * dotM (f p) (k - p)) • g (k - p)) =
        Complex.I * ∑ i, (k i : ℂ) * (cmp f i p * cmp g a (k - p)) := fun p => by
    rw [hdot]
    simp only [map_smul, dotM, Finset.mul_sum, Finset.sum_mul, smul_eq_mul, GN.cmp]
    refine Finset.sum_congr rfl fun i _ => ?_
    change Complex.I * (f p i * (k i : ℂ)) * g (k - p) a =
      Complex.I * ((k i : ℂ) * (f p i * g (k - p) a))
    ring
  simp only [hterm] at e
  have hsum2 : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      Summable fun p => (k i : ℂ) * (cmp f i p * cmp g a (k - p)) := fun i _ => by
    refine Summable.mul_left _ (Summable.of_norm_bounded hs fun p => ?_)
    rw [norm_mul]
    exact mul_le_mul (GN.norm_cmp_le f i p) (GN.norm_cmp_le g a _) (norm_nonneg _) (norm_nonneg _)
  rw [tsum_mul_left, Summable.tsum_finsetSum hsum2] at e
  change advect f g k a = _
  have e2 : advect f g k a = (EuclideanSpace.proj (𝕜 := ℂ) a)
      (∑' p, (Complex.I * dotM (f p) (k - p)) • g (k - p)) := rfl
  rw [e2, e]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tsum_mul_left]
  rfl

/-- The sum of the squares of the scalar convolutions. -/
def dq (f g : Field) (k : Mode) : ℝ := ∑ a, ∑ b, ‖cv (cmp f a) (cmp g b) k‖ ^ 2

lemma dq_nonneg (f g : Field) (k : Mode) : 0 ≤ dq f g k :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

lemma cv_comm (u v : Mode → ℂ) (k : Mode) : cv u v k = cv v u k := by
  unfold cv
  rw [← (Equiv.subLeft k).tsum_eq]
  refine tsum_congr fun p => ?_
  simp only [Equiv.subLeft_apply, sub_sub_cancel]
  ring

lemma dq_comm (f g : Field) (k : Mode) : dq f g k = dq g f k := by
  unfold dq
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [cv_comm]

/-- `‖(f·∇)g‖² ≤ |k|² d²`. -/
lemma norm_advect_sq_le {f g : Field} {k : Mode} (hf : IsSolenoidal f)
    (hs : Summable fun p => ‖f p‖ * ‖g (k - p)‖) : ‖advect f g k‖ ^ 2 ≤ absSq k * dq f g k := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold dq
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [advect_div hf hs a, norm_mul, Complex.norm_I, one_mul]
  have h1 : ‖∑ i, (k i : ℂ) * cv (cmp f i) (cmp g a) k‖ ≤
      ∑ i, |(k i : ℝ)| * ‖cv (cmp f i) (cmp g a) k‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, Complex.norm_intCast]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3))
    (fun i => |(k i : ℝ)|) (fun i => ‖cv (cmp f i) (cmp g a) k‖)
  simp only [sq_abs] at h2
  calc _ ≤ (∑ i, |(k i : ℝ)| * ‖cv (cmp f i) (cmp g a) k‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

/-- `‖B(f, g)‖² ≤ |k|² d²`, the product as a divergence. -/
lemma norm_Bsym_sq_le {f g : Field} {k : Mode} (hf : IsSolenoidal f) (hg : IsSolenoidal g)
    (hf2 : Summable fun k => ‖f k‖ ^ 2) (hg2 : Summable fun k => ‖g k‖ ^ 2) (hf1 : InH 1 f)
    (hg1 : InH 1 g) : ‖Bsym f g k‖ ^ 2 ≤ absSq k * dq f g k := by
  have h := GN.norm_Bsym_le (GN.summable_adv hf2 hg1 k) (GN.summable_adv hg2 hf1 k)
  have l1 : ∀ {u v : Field}, (Summable fun k => ‖u k‖ ^ 2) → (Summable fun k => ‖v k‖ ^ 2) →
      Summable fun p => ‖u p‖ * ‖v (k - p)‖ := fun {u v} hu hv => by
    have := convR_le_of_l2 (a := fun k => ‖u k‖) (b := fun k => ‖v k‖)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hu hv k
    exact this.1
  have h1 := norm_advect_sq_le hf (l1 hf2 hg2)
  have h2 := norm_advect_sq_le hg (l1 hg2 hf2)
  rw [← dq_comm] at h2
  have n0 := norm_nonneg (Bsym f g k)
  have n1 := norm_nonneg (advect f g k)
  have n2 := norm_nonneg (advect g f k)
  have h3 : ‖Bsym f g k‖ ^ 2 ≤ (1 / 2 * (‖advect f g k‖ + ‖advect g f k‖)) ^ 2 :=
    pow_le_pow_left₀ n0 h 2
  nlinarith only [h3, h1, h2, sq_nonneg (‖advect f g k‖ - ‖advect g f k‖)]

/-- The sum of the scalar convolutions (Parseval and the sup bound). -/
lemma sum_dq {f g : Field} (hf : Summable fun k => ‖f k‖) {M : ℝ} (hM : SupBd f M)
    (hg : Summable fun k => ‖g k‖ ^ 2) :
    Summable (dq f g) ∧ ∑' k, dq f g k ≤ 3 * M ^ 2 * ∑' k, ‖g k‖ ^ 2 := by
  have hgb : ∀ b, Summable fun k => ‖cmp g b k‖ ^ 2 := fun b =>
    Summable.of_nonneg_of_le (fun _ => by positivity)
      (fun k => pow_le_pow_left₀ (norm_nonneg _) (GN.norm_cmp_le g b k) 2) hg
  have h1 := fun a b => GN.sup_product (GN.summable_cmp hf a) (hgb b) (hM.cmp hf a)
  have hs : ∀ a ∈ (Finset.univ : Finset (Fin 3)),
      Summable fun k => ∑ b, ‖cv (cmp f a) (cmp g b) k‖ ^ 2 := fun a _ =>
    summable_sum fun b _ => (h1 a b).1
  refine ⟨summable_sum hs, ?_⟩
  unfold dq
  rw [Summable.tsum_finsetSum hs]
  have hb : ∀ a, ∑' k, ∑ b, ‖cv (cmp f a) (cmp g b) k‖ ^ 2 ≤ M ^ 2 * ∑' k, ‖g k‖ ^ 2 := fun a => by
    rw [Summable.tsum_finsetSum fun b _ => (h1 a b).1]
    refine (Finset.sum_le_sum fun b _ => (h1 a b).2).trans (le_of_eq ?_)
    rw [← Finset.mul_sum, ← Summable.tsum_finsetSum fun b _ => hgb b]
    congr 2
    funext k
    exact GN.sum_norm_cmp_sq g k
  refine (Finset.sum_le_sum fun a _ => hb a).trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- The product with the filter restored. -/
lemma norm_Qphase_sq_le (τ : ℝ) {f g : Field} (hf : Adm 2 f) (hf' : PiS f = f) (hg : Adm 2 g)
    (k : Mode) : ‖Qphase τ f g k‖ ^ 2 ≤ absSq k * dq f (rotF τ g) k := by
  have hG := hg.rotF τ
  have l2 : ∀ {u : Field}, Adm 2 u → Summable fun k => ‖u k‖ ^ 2 := fun hu =>
    summable_norm_sq_of_inH (hu.inH.mono (by norm_num))
  have h1 := norm_Bsym_sq_le (k := k) hf.sol hG.sol (l2 hf) (l2 hG)
    (hf.inH.mono (by norm_num)) (hG.inH.mono (by norm_num))
  rw [Qphase_eq τ hf hg, GN.rotF_slow hf hf' τ]
  change ‖rot (-τ) k (Bsym f (rotF τ g) k)‖ ^ 2 ≤ _
  rw [norm_rot]
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_leray_le _ _) 2).trans h1

/-! ### The bands -/

/-- The dyadic band of a length. -/
def bnd (k : Mode) : ℕ := Nat.log 2 ⌊absk k⌋₊

lemma two_pow_bnd_le {k : Mode} (hk : k ≠ 0) : (2 : ℝ) ^ bnd k ≤ absk k := by
  have h1 : 1 ≤ absk k := one_le_absk hk
  have hn : ⌊absk k⌋₊ ≠ 0 := by
    have : 1 ≤ ⌊absk k⌋₊ := Nat.le_floor (by simpa using h1)
    omega
  have h2 := Nat.pow_log_le_self 2 hn
  have h3 : ((2 ^ bnd k : ℕ) : ℝ) ≤ (⌊absk k⌋₊ : ℝ) := by exact_mod_cast h2
  push_cast at h3
  exact h3.trans (Nat.floor_le (absk_nonneg k))

lemma lt_two_pow_bnd (k : Mode) : absk k < 2 ^ (bnd k + 1) := by
  have h1 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) ⌊absk k⌋₊
  have h2 : ((⌊absk k⌋₊ + 1 : ℕ) : ℝ) ≤ ((2 ^ (bnd k + 1) : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at h2
  exact (Nat.lt_floor_add_one _).trans_le h2

lemma bnd_neg (k : Mode) : bnd (-k) = bnd k := by
  have : absk (-k) = absk k := by simp [absk, absSq]
  simp only [bnd, this]

/-- The band `i` of a field. -/
def bandF (i : ℕ) (F : Field) : Field := fun k => if bnd k = i then F k else 0

/-- The trapezoid of the band `i`. -/
def Ni (i : ℕ) : ℕ := 2 ^ (i + 5)

/-- The low-pass symbol of the band `i`. -/
def chiM (i : ℕ) (p : Mode) : ℝ := vp (Ni i) (p 0) * vp (Ni i) (p 1)

/-- The low-pass slow field of the band `i`. -/
def chiF (i : ℕ) (S : Field) : Field := mulD 0 (Ni i) (mulD 1 (Ni i) S)

lemma chiF_apply (i : ℕ) (S : Field) (k : Mode) :
    chiF i S k = ((chiM i k : ℝ) : ℂ) • S k := by
  simp only [chiF, mulD, chiM, smul_smul]
  push_cast
  rfl

lemma chiM_nonneg (i : ℕ) (p : Mode) : 0 ≤ chiM i p := mul_nonneg (vp_nonneg _ _) (vp_nonneg _ _)

lemma chiM_le_one (i : ℕ) (p : Mode) : chiM i p ≤ 1 :=
  (mul_le_mul_of_nonneg_right (vp_le_one _ _) (vp_nonneg _ _)).trans
    (by rw [one_mul]; exact vp_le_one _ _)

/-- `χ_i` is one on `|p| ≤ 2^{i+5}`. -/
lemma chiM_one {i : ℕ} {p : Mode} (h : absk p ≤ 2 ^ (i + 5)) : chiM i p = 1 := by
  have hc : ∀ a : Fin 3, |((p a : ℤ) : ℝ)| ≤ (Ni i : ℝ) + 1 := fun a => by
    have h1 : |((p a : ℤ) : ℝ)| ≤ absk p := Real.abs_le_sqrt (GN.sq_le_absSq a p)
    have h2 : (Ni i : ℝ) = 2 ^ (i + 5) := by simp [Ni]
    rw [h2]
    linarith
  simp only [chiM]
  rw [vp_one (hc 0), vp_one (hc 1), one_mul]

/-- The support of `χ_i`, on slow labels. -/
lemma absk_le_of_chiM {i : ℕ} {p : Mode} (hp : p 2 = 0) (h : chiM i p ≠ 0) :
    absk p ≤ 2 ^ (i + 7) := by
  have hN : (Ni i : ℝ) = 2 ^ (i + 5) := by simp [Ni]
  have hc : ∀ a : Fin 3, chiM i p ≠ 0 → (a = 0 ∨ a = 1) →
      |((p a : ℤ) : ℝ)| < 2 * ((Ni i : ℝ) + 1) := fun a h0 ha => by
    by_contra hh
    rw [not_lt] at hh
    apply h0
    rcases ha with rfl | rfl
    · simp only [chiM]
      rw [vp_zero hh, zero_mul]
    · simp only [chiM]
      rw [vp_zero hh, mul_zero]
  have h0 := hc 0 h (Or.inl rfl)
  have h1 := hc 1 h (Or.inr rfl)
  have e : absSq p = ((p 0 : ℤ) : ℝ) ^ 2 + ((p 1 : ℤ) : ℝ) ^ 2 := by
    simp [absSq, Fin.sum_univ_three, hp]
  set N : ℝ := 2 * ((Ni i : ℝ) + 1) with hNdef
  have hN0 : 0 < N := by positivity
  have e0 : ((p 0 : ℤ) : ℝ) ^ 2 ≤ N ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h0.le 2
  have e1 : ((p 1 : ℤ) : ℝ) ^ 2 ≤ N ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1.le 2
  have hsq : absSq p ≤ (2 ^ (i + 7)) ^ 2 := by
    rw [e]
    have e2 : (2 : ℝ) ^ (i + 7) = 8 * 2 ^ (i + 4) := by ring
    have e3 : (2 : ℝ) ^ (i + 5) = 2 * 2 ^ (i + 4) := by ring
    have e4 : (16 : ℝ) ≤ 2 ^ (i + 4) := by
      have : (2 : ℝ) ^ 4 ≤ 2 ^ (i + 4) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    have e5 : N = 4 * 2 ^ (i + 4) + 2 := by
      simp only [hNdef]
      rw [hN, e3]
      ring
    rw [e2]
    rw [e5] at e0 e1
    set T : ℝ := 2 ^ (i + 4)
    nlinarith only [e0, e1, e4]
  rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 ^ (i + 7))]
  exact Real.sqrt_le_sqrt hsq

/-! ### The low-pass slow field and the band of the fast field -/

variable {S F : Field} {M : ℝ} {i : ℕ}

lemma norm_chiF_le (i : ℕ) (S : Field) (k : Mode) : ‖chiF i S k‖ ≤ ‖S k‖ :=
  (norm_mulD_le _ _ _ _).trans (norm_mulD_le _ _ _ _)

/-- `‖χ_i S‖_∞ ≤ 9 M`. -/
lemma supBd_chiF (hs : Summable fun k => ‖S k‖) (hM : SupBd S M) (i : ℕ) :
    SupBd (chiF i S) (9 * M) := by
  have h1 := supBd_mulD hs hM 1 (Ni i)
  have hs1 : Summable fun k => ‖mulD 1 (Ni i) S k‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_mulD_le 1 _ S) hs
  have h2 := supBd_mulD hs1 h1 0 (Ni i)
  have e : 3 * (3 * M) = 9 * M := by ring
  rw [e] at h2
  exact h2

private lemma conjV_smul_r (c : ℝ) (a : V3) : conjV ((c : ℂ) • a) = (c : ℂ) • conjV a := by
  ext t
  simp [conjV]

lemma chiM_neg (i : ℕ) (p : Mode) : chiM i (-p) = chiM i p := by
  simp only [chiM, Pi.neg_apply, vp_neg]

/-- `χ_i S` is admissible. -/
lemma adm_chiF (hS : Adm 2 S) (i : ℕ) : Adm 2 (chiF i S) := by
  refine ⟨?_, fun k => ?_, fun k => ?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_nonneg _ k) (by positivity))
      (fun k => ?_) hS.inH
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_chiF_le i S k) 2)
      (sobWeight_nonneg _ k)
  · simp only [chiF_apply]
    rw [chiM_neg, hS.real k, conjV_smul_r]
  · simp only [chiF_apply]
    rw [dotM_smul, hS.sol k, mul_zero]
  · rw [chiF_apply, hS.mean, smul_zero]

lemma PiS_chiF (hS' : PiS S = S) (i : ℕ) : PiS (chiF i S) = chiF i S := by
  funext k
  by_cases hk : k 2 = 0
  · simp [PiS, hk]
  · simp [PiS, hk, chiF_apply, slow_zero hS' hk]

lemma norm_bandF_le (i : ℕ) (F : Field) (k : Mode) : ‖bandF i F k‖ ≤ ‖F k‖ := by
  simp only [bandF]
  split_ifs
  · exact le_rfl
  · simp

/-- The band of an admissible field is admissible. -/
lemma adm_bandF (hF : Adm 2 F) (i : ℕ) : Adm 2 (bandF i F) := by
  refine ⟨?_, fun k => ?_, fun k => ?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_nonneg _ k) (by positivity))
      (fun k => ?_) hF.inH
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_bandF_le i F k) 2)
      (sobWeight_nonneg _ k)
  · simp only [bandF, bnd_neg]
    split_ifs
    · exact hF.real k
    · ext t
      simp [conjV]
  · simp only [bandF]
    split_ifs
    · exact hF.sol k
    · simp [dotM]
  · simp only [bandF]
    split_ifs
    · exact hF.mean
    · rfl

/-- The product of the band `i`. -/
def Qband (τ : ℝ) (S F : Field) (i : ℕ) : Field := Qphase τ (chiF i S) (bandF i F)

/-- The low symbol of the last edge: `χ` of the band of the input. -/
def lowM (p j : Mode) : ℝ := chiM (bnd j) p

/-- The low product. -/
def Qlo (τ : ℝ) (S F : Field) (k : Mode) : V3 :=
  ∑' p, ((lowM p (k - p) : ℝ) : ℂ) • blk (phaseM τ) p k (k - p) (S p) (F (k - p))

lemma Qband_term (τ : ℝ) (S F : Field) (i : ℕ) (k p : Mode) :
    blk (phaseM τ) p k (k - p) (chiF i S p) (bandF i F (k - p)) =
      if bnd (k - p) = i then
        ((lowM p (k - p) : ℝ) : ℂ) • blk (phaseM τ) p k (k - p) (S p) (F (k - p)) else 0 := by
  simp only [bandF]
  split_ifs with h
  · rw [chiF_apply, blk_smul_leaf, smul_apply, lowM, h]
  · simp

/-- The output of the band `i` lives at `K ≤ 2^{i+8}`. -/
lemma Qband_zero (τ : ℝ) (hS' : PiS S = S) {k : Mode} (hk : (2 : ℝ) ^ (i + 8) < absk k) :
    Qband τ S F i k = 0 := by
  have e : Qband τ S F i k = ∑' p, blk (phaseM τ) p k (k - p) (chiF i S p) (bandF i F (k - p)) :=
    Qm_eq_tsum_blk _ _ _ _
  rw [e]
  have : ∀ p, blk (phaseM τ) p k (k - p) (chiF i S p) (bandF i F (k - p)) = 0 := fun p => by
    rw [Qband_term]
    split_ifs with h
    swap
    · rfl
    by_cases hp : p 2 = 0
    swap
    · rw [slow_zero hS' hp, blk_zero_leaf, zero_apply, smul_zero]
    by_cases hc : lowM p (k - p) = 0
    · simp [hc]
    have h1 := absk_le_of_chiM hp (i := i) (by rwa [lowM, h] at hc)
    exfalso
    have h2 := lt_two_pow_bnd (k - p)
    rw [h] at h2
    have h3 := absk_add_le p (k - p)
    rw [add_sub_cancel] at h3
    have e1 : (2 : ℝ) ^ (i + 8) = 2 * 2 ^ (i + 7) := by ring
    have e2 : (2 : ℝ) ^ (i + 7) = 64 * 2 ^ (i + 1) := by ring
    have h4 : (0 : ℝ) < 2 ^ (i + 1) := by positivity
    nlinarith only [hk, h1, h2, h3, e1, e2, h4]
  simp only [this, tsum_zero]

end OVNS.Quant.Metric

end
