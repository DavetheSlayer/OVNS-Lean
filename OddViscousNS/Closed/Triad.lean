import OddViscousNS.Closed.Gram
import OddViscousNS.Young
import OddViscousNS.Lattice

/-!
# The triad identity: `⟨B(w,w), h(A)w⟩ = (1/6) ∑_{p+l+q=0} W_q T(p,l,q)(w_p, w_l, w_q)`

Item 1 of `OddViscousNS_data/reports/uf661_row_operator.md`.  Steps: (1.1) curl form
`C = ∑_{p+l+q=0} h_q det(S_p w_p, w_l, w_q)` using `(w·∇)w = ω × w + ∇(|w|²/2)`, `ω̂_p = i p × ŵ_p`,
the Leray projector killing multiples of `k`, and reality `ŵ_{-k} = conj ŵ_k`; (1.2) averaging over
the six permutations of the ordered triple (`det` antisymmetric, `T` permutation-invariant); the
cyclic weights `W_q = 3λ_q/(λ_p+λ_l+λ_q)` sum to `3` over the three cyclic positions.  Absolute
convergence (needed for every reordering) holds for `H²` fields: each of the three terms of `T`
is bounded by `(A_{j'} + A_{j''})·|j|·|w_p||w_l||w_q|` with three distinct modes, and
`∑ A_j|w_j| · ((|·|ŵ) * ŵ)(j) ≤ ‖w‖₂ ‖|·|ŵ‖_{ℓ²} ‖ŵ‖_{ℓ¹}` by Cauchy–Schwarz and Young
(`OddViscousNS/Young.lean`), with `‖ŵ‖_{ℓ¹} ≤ c₄‖w‖₂` (`wiener_le`).
-/

open scoped ENNReal ComplexConjugate
open MeasureTheory Set

namespace OVNS

private lemma det3_eq (a b c : V3) : det3 a b c = (a 1 * b 2 - a 2 * b 1) * c 0 +
    (a 2 * b 0 - a 0 * b 2) * c 1 + (a 0 * b 1 - a 1 * b 0) * c 2 := by
  simp [det3, dotV, cross, Fin.sum_univ_three]

private lemma det3_cyc (a b c : V3) : det3 b c a = det3 a b c := by
  rw [det3_eq, det3_eq]; ring

private lemma det3_swap12 (a b c : V3) : det3 b a c = -det3 a b c := by
  rw [det3_eq, det3_eq]; ring

private lemma det3_swap23 (a b c : V3) : det3 a c b = -det3 a b c := by
  rw [det3_eq, det3_eq]; ring

private lemma curlS_apply (j : Mode) (v : V3) :
    curlS j v 0 = Complex.I * ((j 1 : ℂ) * v 2 - (j 2 : ℂ) * v 1) ∧
    curlS j v 1 = Complex.I * ((j 2 : ℂ) * v 0 - (j 0 : ℂ) * v 2) ∧
    curlS j v 2 = Complex.I * ((j 0 : ℂ) * v 1 - (j 1 : ℂ) * v 0) := by
  simp [curlS, cross, modeVec]

private lemma det3_curlS (p : Mode) (a b c : V3) :
    det3 (curlS p a) b c = Complex.I * (dotM b p * dotV a c - dotV a b * dotM c p) := by
  obtain ⟨h0, h1, h2⟩ := curlS_apply p a
  rw [det3_eq, h0, h1, h2]
  simp only [dotM, dotV, Fin.sum_univ_three]
  ring

private lemma inner_eq_dotV (x y : V3) : inner ℂ x y = dotV (conjV x) y := by
  simp [dotV, conjV, PiLp.inner_apply, mul_comm]

private lemma norm_det3_le {x y z : V3} {X Y Z : ℝ} (hx : ∀ i, ‖x i‖ ≤ X) (hy : ∀ i, ‖y i‖ ≤ Y)
    (hz : ∀ i, ‖z i‖ ≤ Z) : ‖det3 x y z‖ ≤ 6 * X * Y * Z := by
  have hX : 0 ≤ X := (norm_nonneg _).trans (hx 0)
  have hY : 0 ≤ Y := (norm_nonneg _).trans (hy 0)
  have hZ : 0 ≤ Z := (norm_nonneg _).trans (hz 0)
  have key : ∀ i j k : Fin 3, ∀ i' j' : Fin 3,
      ‖(x i * y j - x i' * y j') * z k‖ ≤ 2 * X * Y * Z := by
    intro i j k i' j'
    rw [norm_mul]
    have h1 : ‖x i * y j - x i' * y j'‖ ≤ 2 * X * Y := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      nlinarith [mul_le_mul (hx i) (hy j) (norm_nonneg _) hX,
        mul_le_mul (hx i') (hy j') (norm_nonneg _) hX]
    have := mul_le_mul h1 (hz k) (norm_nonneg _) (by positivity)
    linarith
  rw [det3_eq]
  refine (norm_add_le _ _).trans ?_
  have := norm_add_le ((x 1 * y 2 - x 2 * y 1) * z 0) ((x 2 * y 0 - x 0 * y 2) * z 1)
  linarith [key 1 2 0 2 1, key 2 0 1 0 2, key 0 1 2 1 0]

private lemma norm_curlS_apply_le (j : Mode) (v : V3) (i : Fin 3) :
    ‖curlS j v i‖ ≤ 2 * absk j * ‖v‖ := by
  have hc : ∀ m : Fin 3, ‖((j m : ℤ) : ℂ)‖ ≤ absk j := fun m => by
    rw [Complex.norm_intCast]; exact_mod_cast abs_coord_le_absk j m
  have hv : ∀ m : Fin 3, ‖v m‖ ≤ ‖v‖ := fun m => PiLp.norm_apply_le v m
  have key : ∀ a b c d : Fin 3, ‖Complex.I * ((j a : ℂ) * v b - (j c : ℂ) * v d)‖ ≤
      2 * absk j * ‖v‖ := by
    intro a b c d
    rw [norm_mul, Complex.norm_I, one_mul]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    nlinarith [mul_le_mul (hc a) (hv b) (norm_nonneg _) (absk_nonneg j),
      mul_le_mul (hc c) (hv d) (norm_nonneg _) (absk_nonneg j)]
  obtain ⟨h0, h1, h2⟩ := curlS_apply j v
  fin_cases i
  · simpa [h0] using key 1 2 2 1
  · simpa [h1] using key 2 0 0 2
  · simpa [h2] using key 0 1 1 0

private lemma norm_det3_curlS_le (j : Mode) (a b c : V3) :
    ‖det3 (curlS j a) b c‖ ≤ 12 * absk j * ‖a‖ * ‖b‖ * ‖c‖ := by
  have := norm_det3_le (norm_curlS_apply_le j a) (fun i => PiLp.norm_apply_le b i)
    (fun i => PiLp.norm_apply_le c i)
  linarith

private lemma hm_nonneg (j : Mode) : 0 ≤ hm j := by
  unfold hm
  rcases Nat.eq_zero_or_pos (nsq j) with h | h
  · simp [h, hmet]
  · exact (hmet_pos h).le

private lemma hm_le (j : Mode) : hm j ≤ absSq j := by
  unfold hm; rw [← nsq_cast]; exact hmet_upper _

private lemma hm_neg (j : Mode) : hm (-j) = hm j := by
  simp [hm, nsq]

private lemma nsq_neg (j : Mode) : nsq (-j) = nsq j := by
  simp [nsq]

private lemma abs_hm_sub_le (i j : Mode) : |hm i - hm j| ≤ absSq i + absSq j := by
  rw [abs_le]; constructor <;>
    linarith [hm_nonneg i, hm_nonneg j, hm_le i, hm_le j]

private lemma lamVals_pos (i : ℕ) : 0 < lamVals.getD i 100000 := by
  rcases lt_or_ge i 24 with h | h
  · interval_cases i <;> decide
  · rw [List.getD_eq_default]; · norm_num
    simpa [lamVals] using h

private lemma lamW_pos (j : ℕ) : 0 < lamW j := by
  unfold lamW
  split
  · have := lamVals_pos ‹ℕ›
    positivity
  · norm_num

/-- The real part of the curl-form summand on the triple `(p, l, q)`. -/
private noncomputable def Dt (u : Field) (p l q : Mode) : ℝ := (det3 (curlS p (u p)) (u l) (u q)).re

/-- The weighted curl-form summand `h_q Re det(S_p u_p, u_l, u_q)`. -/
private noncomputable def Pt (u : Field) (p l q : Mode) : ℝ := hm q * Dt u p l q

/-- The real part of the triad form on the triple `(p, l, q)`. -/
private noncomputable def Trt (u : Field) (p l q : Mode) : ℝ := (triT p l q (u p) (u l) (u q)).re

/-- The cyclic weight attached to the third slot. -/
private noncomputable def Wt (p l q : Mode) : ℝ :=
  3 * lamW (nsq q) / (lamW (nsq p) + lamW (nsq l) + lamW (nsq q))

private lemma Trt_eq (u : Field) (p l q : Mode) : Trt u p l q =
    Pt u p l q + Pt u p q l + Pt u l q p + Pt u l p q + Pt u q p l + Pt u q l p := by
  have e1 := det3_swap23 (curlS p (u p)) (u l) (u q)
  have e2 := det3_cyc (u p) (curlS l (u l)) (u q)
  have e3 := det3_swap12 (u p) (curlS l (u l)) (u q)
  have e4 := det3_cyc (curlS q (u q)) (u p) (u l)
  have e5 : det3 (curlS q (u q)) (u l) (u p) = -det3 (u p) (u l) (curlS q (u q)) := by
    rw [det3_swap23, e4]
  simp only [Trt, triT, Pt, Dt, e1, e2, e3, ← e4, e5, Complex.add_re, Complex.re_ofReal_mul,
    Complex.neg_re]
  ring

private lemma Wt_cyc (p l q : Mode) : Wt p l q + Wt l q p + Wt q p l = 3 := by
  have h1 := lamW_pos (nsq p)
  have h2 := lamW_pos (nsq l)
  have h3 := lamW_pos (nsq q)
  simp only [Wt]
  field_simp
  ring

private lemma Wt_nonneg (p l q : Mode) : 0 ≤ Wt p l q := by
  have h1 := lamW_pos (nsq p)
  have h2 := lamW_pos (nsq l)
  have h3 := lamW_pos (nsq q)
  unfold Wt; positivity

private lemma Wt_le (p l q : Mode) : Wt p l q ≤ 3 := by
  have h1 := lamW_pos (nsq p)
  have h2 := lamW_pos (nsq l)
  have h3 := lamW_pos (nsq q)
  unfold Wt
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- The sum over ordered triples `p + l + q = 0`, parametrized by `(k, p) ↦ (p, k - p, -k)`. -/
private noncomputable def tS (Φ : Mode → Mode → Mode → ℝ) : ℝ :=
  ∑' kp : Mode × Mode, Φ kp.2 (kp.1 - kp.2) (-kp.1)

/-- Summability of a triple family. -/
private def tSm (Φ : Mode → Mode → Mode → ℝ) : Prop :=
  Summable fun kp : Mode × Mode => Φ kp.2 (kp.1 - kp.2) (-kp.1)

private lemma tS_perm (σ : Mode × Mode ≃ Mode × Mode) {Φ Ψ : Mode → Mode → Mode → ℝ}
    (h : ∀ kp : Mode × Mode, Ψ kp.2 (kp.1 - kp.2) (-kp.1) =
      Φ (σ kp).2 ((σ kp).1 - (σ kp).2) (-(σ kp).1)) :
    tS Ψ = tS Φ ∧ (tSm Ψ ↔ tSm Φ) := by
  have hf : (fun kp : Mode × Mode => Ψ kp.2 (kp.1 - kp.2) (-kp.1)) =
      (fun kp : Mode × Mode => Φ kp.2 (kp.1 - kp.2) (-kp.1)) ∘ σ := funext h
  refine ⟨?_, ?_⟩
  · unfold tS; rw [hf]; exact σ.tsum_eq (fun kp : Mode × Mode => Φ kp.2 (kp.1 - kp.2) (-kp.1))
  · unfold tSm; rw [hf]; exact σ.summable_iff

private def e12 : Mode × Mode ≃ Mode × Mode where
  toFun kp := (kp.1, kp.1 - kp.2)
  invFun kp := (kp.1, kp.1 - kp.2)
  left_inv kp := by ext <;> simp
  right_inv kp := by ext <;> simp

private def e23 : Mode × Mode ≃ Mode × Mode where
  toFun kp := (kp.2 - kp.1, kp.2)
  invFun kp := (kp.2 - kp.1, kp.2)
  left_inv kp := by ext <;> simp
  right_inv kp := by ext <;> simp

private def eCyc : Mode × Mode ≃ Mode × Mode where
  toFun kp := (-kp.2, kp.1 - kp.2)
  invFun kp := (kp.2 - kp.1, -kp.1)
  left_inv kp := by ext <;> simp
  right_inv kp := by ext <;> simp

private def eCyc2 : Mode × Mode ≃ Mode × Mode where
  toFun kp := (kp.2 - kp.1, -kp.1)
  invFun kp := (-kp.2, kp.1 - kp.2)
  left_inv kp := by ext <;> simp
  right_inv kp := by ext <;> simp

private def e13 : Mode × Mode ≃ Mode × Mode where
  toFun kp := (-kp.2, -kp.1)
  invFun kp := (-kp.2, -kp.1)
  left_inv kp := by ext <;> simp
  right_inv kp := by ext <;> simp

private lemma tS_12 (Φ : Mode → Mode → Mode → ℝ) :
    tS (fun p l q => Φ l p q) = tS Φ ∧ (tSm (fun p l q => Φ l p q) ↔ tSm Φ) :=
  tS_perm e12 fun kp => by simp [e12]

private lemma tS_23 (Φ : Mode → Mode → Mode → ℝ) :
    tS (fun p l q => Φ p q l) = tS Φ ∧ (tSm (fun p l q => Φ p q l) ↔ tSm Φ) :=
  tS_perm e23 fun kp => by simp [e23]

private lemma tS_cyc (Φ : Mode → Mode → Mode → ℝ) :
    tS (fun p l q => Φ l q p) = tS Φ ∧ (tSm (fun p l q => Φ l q p) ↔ tSm Φ) :=
  tS_perm eCyc fun kp => by
    simp only [eCyc, Equiv.coe_fn_mk, neg_neg,
      show ∀ a b : Mode, -b - (a - b) = -a from fun a b => by abel]

private lemma tS_cyc2 (Φ : Mode → Mode → Mode → ℝ) :
    tS (fun p l q => Φ q p l) = tS Φ ∧ (tSm (fun p l q => Φ q p l) ↔ tSm Φ) :=
  tS_perm eCyc2 fun kp => by simp [eCyc2]

private lemma tS_13 (Φ : Mode → Mode → Mode → ℝ) :
    tS (fun p l q => Φ q l p) = tS Φ ∧ (tSm (fun p l q => Φ q l p) ↔ tSm Φ) :=
  tS_perm e13 fun kp => by
    simp only [e13, Equiv.coe_fn_mk, neg_neg,
      show ∀ a b : Mode, -b - -a = a - b from fun a b => by abel]

private lemma summable_conv3 {a b c : Mode → ℝ} (ha0 : ∀ k, 0 ≤ a k) (hb0 : ∀ k, 0 ≤ b k)
    (hc0 : ∀ k, 0 ≤ c k) (ha : Summable fun k => a k ^ 2) (hb : Summable fun k => b k ^ 2)
    (hc : Summable c) (σ : Mode → Mode ≃ Mode) :
    Summable fun xy : Mode × Mode => c xy.1 * (a xy.2 * b (σ xy.1 xy.2)) := by
  have hb' : ∀ x, Summable fun y => b (σ x y) ^ 2 := fun x =>
    (σ x).summable_iff.2 hb
  have hamgm : ∀ x y, a y * b (σ x y) ≤ (a y ^ 2 + b (σ x y) ^ 2) / 2 := fun x y => by
    nlinarith [sq_nonneg (a y - b (σ x y))]
  have hin : ∀ x, Summable fun y => a y * b (σ x y) := fun x =>
    Summable.of_nonneg_of_le (fun y => mul_nonneg (ha0 _) (hb0 _)) (hamgm x)
      ((ha.add (hb' x)).div_const 2)
  have htsum : ∀ x, ∑' y, a y * b (σ x y) ≤ ((∑' y, a y ^ 2) + ∑' y, b y ^ 2) / 2 := by
    intro x
    have h1 := (hin x).tsum_le_tsum (hamgm x) ((ha.add (hb' x)).div_const 2)
    rw [tsum_div_const, (ha).tsum_add (hb' x),
      (σ x).tsum_eq (fun y => b y ^ 2)] at h1
    exact h1
  rw [summable_prod_of_nonneg (fun xy => mul_nonneg (hc0 _) (mul_nonneg (ha0 _) (hb0 _)))]
  refine ⟨fun x => (hin x).mul_left (c x), ?_⟩
  refine Summable.of_nonneg_of_le (fun x => tsum_nonneg fun y =>
    mul_nonneg (hc0 _) (mul_nonneg (ha0 _) (hb0 _))) (fun x => ?_)
    (hc.mul_right (((∑' y, a y ^ 2) + ∑' y, b y ^ 2) / 2))
  show ∑' y, c x * (a y * b (σ x y)) ≤ _
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (htsum x) (hc0 x)

/-- The weight `|j|² ‖u_j‖`. -/
private noncomputable def wt (u : Field) (j : Mode) : ℝ := absSq j * ‖u j‖

private lemma wt_nonneg (u : Field) (j : Mode) : 0 ≤ wt u j :=
  mul_nonneg (absSq_nonneg j) (norm_nonneg _)

private lemma norm_le_wt {u : Field} (hu0 : u 0 = 0) (j : Mode) : ‖u j‖ ≤ wt u j := by
  by_cases hj : j = 0
  · subst hj; simp [wt, hu0]
  · unfold wt
    nlinarith [one_le_absSq hj, norm_nonneg (u j)]

private lemma absk_mul_le_wt {u : Field} (hu0 : u 0 = 0) (j : Mode) :
    absk j * ‖u j‖ ≤ wt u j := by
  by_cases hj : j = 0
  · subst hj; simp [wt, hu0]
  · unfold wt
    have h1 := one_le_absk hj
    have h2 : absSq j = absk j * absk j := by rw [← absk_sq]; ring
    rw [h2]
    have := mul_le_mul_of_nonneg_left h1 (mul_nonneg (absk_nonneg j) (norm_nonneg (u j)))
    nlinarith [norm_nonneg (u j)]

private lemma summable_wt_sq {u : Field} (hu : Adm 2 u) : Summable fun j => wt u j ^ 2 := by
  refine hu.inH.congr fun j => ?_
  by_cases hj : j = 0
  · subst hj; simp [wt, hu.mean]
  · simp only [sobWeight, hj, ↓reduceIte, wt]
    rw [show (2 : ℝ) * 2 = (4 : ℕ) by norm_num, Real.rpow_natCast,
      show absk j ^ 4 = (absk j ^ 2) ^ 2 by ring, absk_sq]
    ring

private lemma norm_neg_eq {u : Field} (hu : Adm 2 u) (k : Mode) : ‖u (-k)‖ = ‖u k‖ := by
  rw [hu.real k, norm_conjV]

/-- The symmetric majorant of all triple summands. -/
private noncomputable def M3 (u : Field) (p l q : Mode) : ℝ :=
  (absSq p * absSq l + absSq p * absSq q + absSq l * absSq q) * (‖u p‖ * ‖u l‖ * ‖u q‖)

private def eAdd : Mode × Mode ≃ Mode × Mode where
  toFun mp := (mp.1 + mp.2, mp.2)
  invFun kp := (kp.1 - kp.2, kp.2)
  left_inv kp := by ext <;> simp
  right_inv kp := by ext <;> simp

private lemma tSm_M3 {u : Field} (hu : Adm 2 u) : tSm (M3 u) := by
  have hw0 := wt_nonneg u
  have hv0 : ∀ k, 0 ≤ ‖u k‖ := fun k => norm_nonneg _
  have hw := summable_wt_sq hu
  have hv := summable_wiener hu.inH
  have h1 := summable_conv3 hw0 hw0 hv0 hw hw hv (fun k => Equiv.subLeft k)
  have h2 := summable_conv3 hw0 hw0 hv0 hw hw hv (fun m => Equiv.addLeft m)
  have h3 := summable_conv3 hw0 hw0 hv0 hw hw hv (fun p => Equiv.subRight p)
  have h2' : Summable fun kp : Mode × Mode => ‖u (kp.1 - kp.2)‖ * (wt u kp.2 * wt u kp.1) := by
    rw [← eAdd.summable_iff]
    refine h2.congr fun mp => ?_
    simp [eAdd]
  have h3' : Summable fun kp : Mode × Mode => ‖u kp.2‖ * (wt u kp.1 * wt u (kp.1 - kp.2)) := by
    rw [← (Equiv.prodComm Mode Mode).summable_iff]
    exact h3
  refine ((h1.add h2').add h3').congr fun kp => ?_
  simp only [M3, wt, absSq_neg, norm_neg_eq hu, Equiv.subLeft_apply]
  ring

private lemma norm_det3_curlS_u {u : Field} (hu0 : u 0 = 0) (j : Mode) (x y : V3) :
    ‖det3 (curlS j (u j)) x y‖ ≤ 12 * (absSq j * ‖u j‖) * ‖x‖ * ‖y‖ := by
  have h := norm_det3_curlS_le j (u j) x y
  have h2 := absk_mul_le_wt hu0 j
  unfold wt at h2
  have := mul_le_mul_of_nonneg_right h2 (mul_nonneg (norm_nonneg x) (norm_nonneg y))
  nlinarith

private lemma norm_triT_le {u : Field} (hu0 : u 0 = 0) (p l q : Mode) :
    ‖triT p l q (u p) (u l) (u q)‖ ≤ 24 * M3 u p l q := by
  have h1 := norm_det3_curlS_u hu0 p (u l) (u q)
  have h2 := norm_det3_curlS_u hu0 l (u p) (u q)
  have h3 := norm_det3_curlS_u hu0 q (u p) (u l)
  rw [det3_swap12, norm_neg] at h2
  rw [← det3_cyc] at h3
  have d1 := abs_hm_sub_le q l
  have d2 := abs_hm_sub_le p q
  have d3 := abs_hm_sub_le l p
  unfold triT
  refine (norm_add₃_le).trans ?_
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hp := norm_nonneg (u p)
  have hl := norm_nonneg (u l)
  have hq := norm_nonneg (u q)
  have Ap := absSq_nonneg p
  have Al := absSq_nonneg l
  have Aq := absSq_nonneg q
  have e1 := mul_le_mul d1 h1 (norm_nonneg _) (by positivity)
  have e2 := mul_le_mul d2 h2 (norm_nonneg _) (by positivity)
  have e3 := mul_le_mul d3 h3 (norm_nonneg _) (by positivity)
  unfold M3
  nlinarith

private lemma tSm_of_le {u : Field} (hu : Adm 2 u) {Φ : Mode → Mode → Mode → ℝ} (C : ℝ)
    (h : ∀ p l q, |Φ p l q| ≤ C * M3 u p l q) : tSm Φ :=
  Summable.of_norm_bounded ((show Summable _ from tSm_M3 hu).mul_left C) fun _ => h _ _ _

private lemma abs_Pt_le {u : Field} (hu0 : u 0 = 0) (p l q : Mode) :
    |Pt u p l q| ≤ 12 * M3 u p l q := by
  have h1 := norm_det3_curlS_u hu0 p (u l) (u q)
  have h2 : |Dt u p l q| ≤ ‖det3 (curlS p (u p)) (u l) (u q)‖ := Complex.abs_re_le_norm _
  have h3 := hm_le q
  have h4 := hm_nonneg q
  have hp := norm_nonneg (u p)
  have hl := norm_nonneg (u l)
  have hq := norm_nonneg (u q)
  have Ap := absSq_nonneg p
  have Al := absSq_nonneg l
  have Aq := absSq_nonneg q
  unfold Pt M3
  rw [abs_mul, abs_of_nonneg h4]
  have := mul_le_mul h3 (h2.trans h1) (abs_nonneg _) Aq
  nlinarith [mul_nonneg (mul_nonneg Ap Al) (mul_nonneg (mul_nonneg hp hl) hq),
    mul_nonneg (mul_nonneg Al Aq) (mul_nonneg (mul_nonneg hp hl) hq)]

private lemma abs_Trt_le {u : Field} (hu0 : u 0 = 0) (p l q : Mode) :
    |Trt u p l q| ≤ 24 * M3 u p l q :=
  (Complex.abs_re_le_norm _).trans (norm_triT_le hu0 p l q)

private lemma M3_nonneg (u : Field) (p l q : Mode) : 0 ≤ M3 u p l q := by
  have := absSq_nonneg p
  have := absSq_nonneg l
  have := absSq_nonneg q
  unfold M3; positivity

private lemma abs_WTrt_le {u : Field} (hu0 : u 0 = 0) (p l q : Mode) :
    |Wt p l q * Trt u p l q| ≤ 72 * M3 u p l q := by
  rw [abs_mul, abs_of_nonneg (Wt_nonneg p l q)]
  have := mul_le_mul (Wt_le p l q) (abs_Trt_le hu0 p l q) (abs_nonneg _) (by norm_num)
  linarith

private lemma Trt_cyc (u : Field) (p l q : Mode) : Trt u l q p = Trt u p l q := by
  rw [Trt_eq, Trt_eq]; ring

private lemma Trt_cyc2 (u : Field) (p l q : Mode) : Trt u q p l = Trt u p l q := by
  rw [Trt_eq, Trt_eq]; ring

private lemma tS_Trt {u : Field} (hu : Adm 2 u) : tS (Trt u) = 6 * tS (Pt u) := by
  have hP : tSm (Pt u) := tSm_of_le hu 12 (abs_Pt_le hu.mean)
  have s1 := (tS_23 (Pt u)).2.2 hP
  have s2 := (tS_cyc (Pt u)).2.2 hP
  have s3 := (tS_12 (Pt u)).2.2 hP
  have s4 := (tS_cyc2 (Pt u)).2.2 hP
  have s5 := (tS_13 (Pt u)).2.2 hP
  have e1 := (tS_23 (Pt u)).1
  have e2 := (tS_cyc (Pt u)).1
  have e3 := (tS_12 (Pt u)).1
  have e4 := (tS_cyc2 (Pt u)).1
  have e5 := (tS_13 (Pt u)).1
  unfold tS tSm at *
  have h := (((((hP.hasSum.add s1.hasSum).add s2.hasSum).add s3.hasSum).add s4.hasSum).add
    s5.hasSum).tsum_eq
  simp only [← Trt_eq] at h
  rw [h, e1, e2, e3, e4, e5]
  ring

private lemma tS_WTrt {u : Field} (hu : Adm 2 u) :
    tS (fun p l q => Wt p l q * Trt u p l q) = tS (Trt u) := by
  set Φ : Mode → Mode → Mode → ℝ := fun p l q => Wt p l q * Trt u p l q with hΦ
  have h0 : tSm Φ := tSm_of_le hu 72 (abs_WTrt_le hu.mean)
  have s1 := (tS_cyc Φ).2.2 h0
  have s2 := (tS_cyc2 Φ).2.2 h0
  have e1 := (tS_cyc Φ).1
  have e2 := (tS_cyc2 Φ).1
  unfold tS tSm at *
  have h := ((h0.hasSum.add s1.hasSum).add s2.hasSum).tsum_eq
  rw [e1, e2] at h
  have h' : ∑' kp : Mode × Mode, (Φ kp.2 (kp.1 - kp.2) (-kp.1) +
      Φ (kp.1 - kp.2) (-kp.1) kp.2 + Φ (-kp.1) kp.2 (kp.1 - kp.2)) =
      ∑' kp : Mode × Mode, 3 * Trt u kp.2 (kp.1 - kp.2) (-kp.1) := by
    refine tsum_congr fun kp => ?_
    simp only [hΦ]
    rw [Trt_cyc u kp.2 (kp.1 - kp.2) (-kp.1), Trt_cyc2 u kp.2 (kp.1 - kp.2) (-kp.1)]
    rw [← Wt_cyc kp.2 (kp.1 - kp.2) (-kp.1)]
    ring
  rw [h', tsum_mul_left] at h
  linarith

private lemma dotV_eq_inner (a b : V3) : dotV a b = inner ℂ (conjV a) b := by
  simp [dotV, conjV, PiLp.inner_apply, mul_comm]

private lemma norm_dotV_le (a b : V3) : ‖dotV a b‖ ≤ ‖a‖ * ‖b‖ := by
  rw [dotV_eq_inner, ← norm_conjV a]; exact norm_inner_le_norm _ _

private lemma dotV_comm (a b : V3) : dotV a b = dotV b a := by
  simp only [dotV, mul_comm]

private lemma dotM_add_sub (c : V3) (k p : Mode) : dotM c p + dotM c (k - p) = dotM c k := by
  simp only [dotM, ← Finset.sum_add_distrib, Pi.sub_apply, Int.cast_sub]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

private lemma dotM_conjV' (v : V3) (k : Mode) : dotM (conjV v) k = conj (dotM v k) := by
  simp [dotM, conjV, map_sum]

private lemma inner_leray {u : Field} (hu : Adm 2 u) (k : Mode) (v : V3) :
    inner ℂ (u k) (leray k v) = inner ℂ (u k) v := by
  unfold leray
  split_ifs with hk
  · subst hk; simp [hu.mean]
  · have h0 : inner ℂ (u k) (modeVec k) = 0 := by
      rw [inner_eq_dotV, dotV_comm]
      have : dotV (modeVec k) (conjV (u k)) = dotM (conjV (u k)) k := by
        simp [dotV, dotM, modeVec, mul_comm]
      rw [this, dotM_conjV', hu.sol k, map_zero]
    rw [inner_sub_right, inner_smul_right, h0, mul_zero, sub_zero]

private lemma summable_mul_sub {X Y : Mode → ℝ} (hX0 : ∀ k, 0 ≤ X k) (hY0 : ∀ k, 0 ≤ Y k)
    (hX : Summable fun k => X k ^ 2) (hY : Summable fun k => Y k ^ 2) (k : Mode) :
    Summable fun p => X p * Y (k - p) := by
  have hY' : Summable fun p => Y (k - p) ^ 2 :=
    (Equiv.subLeft k).summable_iff.2 hY
  refine Summable.of_nonneg_of_le (fun p => mul_nonneg (hX0 _) (hY0 _)) (fun p => ?_)
    ((hX.add hY').div_const 2)
  nlinarith [sq_nonneg (X p - Y (k - p))]

private lemma summable_norm_sq {u : Field} (hu : Adm 2 u) : Summable fun k => ‖u k‖ ^ 2 :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun k => pow_le_pow_left₀ (norm_nonneg _) (norm_le_wt hu.mean k) 2) (summable_wt_sq hu)

private lemma summable_wt_mul {u : Field} (hu : Adm 2 u) (k : Mode) :
    Summable fun p => wt u p * ‖u (k - p)‖ :=
  summable_mul_sub (wt_nonneg u) (fun _ => norm_nonneg _) (summable_wt_sq hu)
    (summable_norm_sq hu) k

private lemma summable_mul_wt {u : Field} (hu : Adm 2 u) (k : Mode) :
    Summable fun p => ‖u p‖ * wt u (k - p) :=
  summable_mul_sub (fun _ => norm_nonneg _) (wt_nonneg u) (summable_norm_sq hu)
    (summable_wt_sq hu) k

private lemma sum_swap_identity {u : Field} (hu : Adm 2 u) (k : Mode) :
    ∑' p, Complex.I * dotM (u p) (k - p) * dotV (u (k - p)) (conjV (u k)) =
      ∑' p, det3 (curlS p (u p)) (u (k - p)) (conjV (u k)) := by
  set c := conjV (u k) with hcdef
  have hc : dotM c k = 0 := by rw [hcdef, dotM_conjV', hu.sol k, map_zero]
  set g : Mode → ℂ := fun p => dotM (u (k - p)) p * dotV (u p) c with hgdef
  set h : Mode → ℂ := fun p => dotV (u p) (u (k - p)) * dotM c p with hhdef
  have hB := (summable_wt_mul hu k).mul_left ‖c‖
  have hwt := absk_mul_le_wt hu.mean
  have hg : Summable g := by
    refine Summable.of_norm_bounded hB fun p => ?_
    simp only [hgdef, norm_mul]
    have h1 := norm_dotM_le (u (k - p)) p
    have h2 := norm_dotV_le (u p) c
    have h3 := hwt p
    have := norm_nonneg (u (k - p))
    have := norm_nonneg c
    have := norm_nonneg (u p)
    have := absk_nonneg p
    calc ‖dotM (u (k - p)) p‖ * ‖dotV (u p) c‖ ≤ (‖u (k - p)‖ * absk p) * (‖u p‖ * ‖c‖) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = ‖c‖ * ((absk p * ‖u p‖) * ‖u (k - p)‖) := by ring
      _ ≤ ‖c‖ * (wt u p * ‖u (k - p)‖) := by gcongr
  have hh : Summable h := by
    refine Summable.of_norm_bounded hB fun p => ?_
    simp only [hhdef, norm_mul]
    have h1 := norm_dotM_le c p
    have h2 := norm_dotV_le (u p) (u (k - p))
    have h3 := hwt p
    have := norm_nonneg (u (k - p))
    have := norm_nonneg c
    have := norm_nonneg (u p)
    have := absk_nonneg p
    calc ‖dotV (u p) (u (k - p))‖ * ‖dotM c p‖ ≤ (‖u p‖ * ‖u (k - p)‖) * (‖c‖ * absk p) :=
          mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
      _ = ‖c‖ * ((absk p * ‖u p‖) * ‖u (k - p)‖) := by ring
      _ ≤ ‖c‖ * (wt u p * ‖u (k - p)‖) := by gcongr
  have hgσ : ∑' p, g (k - p) = ∑' p, g p := (Equiv.subLeft k).tsum_eq g
  have hhσ : ∑' p, h (k - p) = ∑' p, h p := (Equiv.subLeft k).tsum_eq h
  have hh' : Summable fun p => h (k - p) := (Equiv.subLeft k).summable_iff.2 hh
  have hh0 : ∑' p, h p = 0 := by
    have e : ∑' p, (h p + h (k - p)) = 0 := by
      rw [← tsum_zero]
      refine tsum_congr fun p => ?_
      simp only [hhdef, sub_sub_cancel, dotV_comm (u (k - p)) (u p)]
      rw [← mul_add, dotM_add_sub, hc, mul_zero]
    rw [hh.tsum_add hh', hhσ] at e
    linear_combination e / 2
  have lhs : ∀ p, Complex.I * dotM (u p) (k - p) * dotV (u (k - p)) c =
      Complex.I * g (k - p) := fun p => by
    simp only [hgdef, sub_sub_cancel]; ring
  have rhs : ∀ p, det3 (curlS p (u p)) (u (k - p)) c = Complex.I * (g p - h p) := fun p => by
    rw [det3_curlS]
  simp only [lhs, rhs]
  rw [tsum_mul_left, tsum_mul_left, hg.tsum_sub hh, hh0, hgσ, sub_zero]

private lemma inner_convec_eq {u : Field} (hu : Adm 2 u) (k : Mode) :
    inner ℂ (u k) (convec u k) = ∑' p, det3 (curlS p (u p)) (u (k - p)) (conjV (u k)) := by
  have hf : Summable fun p => (Complex.I * dotM (u p) (k - p)) • u (k - p) := by
    refine Summable.of_norm_bounded (summable_mul_wt hu k) fun p => ?_
    rw [norm_smul, norm_mul, Complex.norm_I, one_mul]
    have h1 := norm_dotM_le (u p) (k - p)
    have h2 := absk_mul_le_wt hu.mean (k - p)
    have := norm_nonneg (u p)
    have := norm_nonneg (u (k - p))
    calc ‖dotM (u p) (k - p)‖ * ‖u (k - p)‖ ≤ (‖u p‖ * absk (k - p)) * ‖u (k - p)‖ := by gcongr
      _ = ‖u p‖ * (absk (k - p) * ‖u (k - p)‖) := by ring
      _ ≤ ‖u p‖ * wt u (k - p) := by gcongr
  rw [convec, inner_leray hu, advect, ← sum_swap_identity hu k]
  have := (innerSL ℂ (u k)).map_tsum hf
  simp only [innerSL_apply_apply] at this
  rw [this]
  refine tsum_congr fun p => ?_
  rw [inner_smul_right, inner_eq_dotV, dotV_comm]

private lemma cubic_term_eq {u : Field} (hu : Adm 2 u) (k : Mode) :
    hm k * (inner ℂ (u k) (convec u k)).re = ∑' p, Pt u p (k - p) (-k) := by
  have hs : Summable fun p => det3 (curlS p (u p)) (u (k - p)) (conjV (u k)) := by
    refine Summable.of_norm_bounded ((summable_wt_mul hu k).mul_right (12 * ‖conjV (u k)‖))
      fun p => ?_
    have := norm_det3_curlS_u hu.mean p (u (k - p)) (conjV (u k))
    unfold wt; linarith
  have hre := Complex.reCLM.map_tsum hs
  simp only [Complex.reCLM_apply] at hre
  rw [inner_convec_eq hu, hre, ← tsum_mul_left]
  refine tsum_congr fun p => ?_
  simp only [Pt, Dt, hm_neg, hu.real k]

private lemma cubic_eq_tS {u : Field} (hu : Adm 2 u) : cubic u = tS (Pt u) := by
  have hP : tSm (Pt u) := tSm_of_le hu 12 (abs_Pt_le hu.mean)
  unfold cubic tS
  rw [show (fun kp : Mode × Mode => Pt u kp.2 (kp.1 - kp.2) (-kp.1)) =
      fun kp => (fun k p => Pt u p (k - p) (-k)) kp.1 kp.2 from rfl, hP.tsum_prod]
  exact tsum_congr fun k => cubic_term_eq hu k

/-- Absolute convergence of the (fixed-output) triad sum for `H²` fields. -/
theorem summable_triad {u : Field} (hu : Adm 2 u) :
    Summable fun kp : Mode × Mode =>
      ‖triT kp.2 (kp.1 - kp.2) (-kp.1) (u kp.2) (u (kp.1 - kp.2)) (conjV (u kp.1))‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun kp => ?_)
    ((show Summable _ from tSm_M3 hu).mul_left 24)
  rw [← hu.real kp.1]
  exact norm_triT_le hu.mean _ _ _

/-- The weighted triad identity, fixed-output form. -/
theorem cubic_eq_triad {u : Field} (hu : Adm 2 u) :
    cubic u = (1 / 6) * ∑' k, ∑' p,
      Wk lamW k p * (triT p (k - p) (-k) (u p) (u (k - p)) (conjV (u k))).re := by
  have hΦ : tSm (fun p l q => Wt p l q * Trt u p l q) := tSm_of_le hu 72 (abs_WTrt_le hu.mean)
  have key : tS (fun p l q => Wt p l q * Trt u p l q) = ∑' k, ∑' p,
      Wk lamW k p * (triT p (k - p) (-k) (u p) (u (k - p)) (conjV (u k))).re := by
    unfold tS
    rw [show (fun kp : Mode × Mode => Wt kp.2 (kp.1 - kp.2) (-kp.1) *
        Trt u kp.2 (kp.1 - kp.2) (-kp.1)) = fun kp => (fun k p => Wt p (k - p) (-k) *
        Trt u p (k - p) (-k)) kp.1 kp.2 from rfl, hΦ.tsum_prod]
    refine tsum_congr fun k => tsum_congr fun p => ?_
    simp only [Wt, Wk, Trt, nsq_neg, hu.real k]
  rw [cubic_eq_tS hu, ← key, tS_WTrt hu, tS_Trt hu]
  ring

end OVNS
