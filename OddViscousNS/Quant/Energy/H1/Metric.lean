import OddViscousNS.Quant.Energy.H1.Identity

/-!
# E5 — the two `X₁` operator bounds (Body 12 §2, §4, §6)

`X1bil_le_proved` and `X1op_slow_le_proved` are the statements `X1bil_le`, `X1op_slow_le` of
`Bounds.lean`, verbatim.  Their proved constants are `24 c₄ ≤ 192 < 2⁸` and `12 c₄ ≤ 96 < 2⁹`.

## The route
Fix `p` slow, `q` fast, `k = p + q`, `n = q₃ = k₃`, helicities `a, b, c`, and put `l = aP`,
`u = bQ`, `v = cK`, with `P, Q, K` the three lengths.  The term of `pair 1 G (X1op S F)` at
`(p, q)` and the conjugate of the term of `pair 1 F (X1op S G)` at `(-p, k)` are matched by the
relabelling `flipE`; this is where `S_{-p} = conj S_p` is used.  On a helical triad the vertex is
`½(l - u) [A, B, C]` (`vert_hel`), and the reverse edge carries the same triple product `[A, B, C]`
with the opposite sign (`conj_inner_rev`) and the same multiplier (`conj_metM_flip`).  So the pair
is `m · ½(K²(l-u) - Q²(l-v)) [A, B, C]`, and
`K²(l-u) - Q²(l-v) = (v-u)[l(v+u) - uv]`, the Hermitian numerator of the TeX.  Since
`δ = Φ = n(u-v)`, `|n| ≥ 1`, the resolvent `1/(-Σ + irδ)` absorbs `v - u` at the price `1/q`
(`numer_le`), which leaves the positive kernel `(PK + PQ + KQ) ‖S_p‖ ‖F_q‖ ‖G_k‖`
(`norm_paired_le`).

The source then uses the paired Schur lemma (§2), to keep the block norm.  The file bounds the eight
helicity patterns one by one instead, which costs a constant factor and needs no matrix argument.

The two convolution envelopes (§4, §6) are `kern_sum_two` and `kern_sum_one`:
* `H²` direction: `PK ≤ ½(KQ + P²K/Q)`, `PQ ≤ ½(KQ + P²Q/K)`.
* `H¹` direction: `KQ ≤ KQ(K+Q)/P` (triangle) and `P(K+Q) ≤ KQ(K+Q)/P + P(Q³+K³)/(KQ)`, since their
  difference is `(K+Q)(K²Q² + P²(Q-K)²)/(PKQ)`.  This replaces the comparable/separated split.

The lattice constant `c₄² = ∑_{k≠0} |k|⁻⁴ ≤ 52` is `c4_sq_le`, by the sup-norm shells (§4), so
`c₄ ≤ 8` and the source's `√104` is not needed.

The projections `PiS S = S`, `PiF F = F`, `PiF G = G` are not used: the mask of `metM` already
restricts to slow `p` and fast `q`.  They stay in the statements, which are verbatim.
-/

open scoped ComplexConjugate

noncomputable section

namespace OVNS

/-! ### A. The lattice constant -/

/-- `∑_{n=1}^{R} n⁻² ≤ 2`. -/
private lemma sum_Icc_inv_sq_le (R : ℕ) : ∑ n ∈ Finset.Icc 1 R, ((n : ℝ) ^ 2)⁻¹ ≤ 2 := by
  have key : ∀ m : ℕ, ∑ n ∈ Finset.Icc 1 (m + 1), ((n : ℝ) ^ 2)⁻¹ ≤ 2 - ((m : ℝ) + 1)⁻¹ := by
    intro m
    induction m with
    | zero => simp; norm_num
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have h1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have h2 : (((m + 1 + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤ ((m : ℝ) + 1)⁻¹ - ((m : ℝ) + 1 + 1)⁻¹ := by
        push_cast
        rw [inv_sub_inv (by positivity) (by positivity), ← one_div]
        apply div_le_div₀ (by linarith) (by linarith) (by positivity)
        nlinarith
      push_cast at h2 ih ⊢
      linarith
  rcases R with _ | m
  · simp
  · have h3 : (0 : ℝ) ≤ ((m : ℝ) + 1)⁻¹ := by positivity
    linarith [key m]

/-- `∑_{0 < ‖p‖_∞ ≤ R} |p|⁻⁴ ≤ 52` (Body 12 §4: "summing `26/m²` already gives `≤ 52`"). -/
private lemma sum_inv4_le (R : ℕ) : ∑ p ∈ (Quant.modeBox R).erase 0, (absSq p)⁻¹ ^ 2 ≤ 52 := by
  classical
  have hmaps : ∀ p ∈ (Quant.modeBox R).erase 0, Quant.supNorm p ∈ Finset.Icc 1 R := by
    intro p hp
    rw [Finset.mem_erase, Quant.mem_modeBox_iff_supNorm_le] at hp
    exact Finset.mem_Icc.2 ⟨Quant.one_le_supNorm hp.1, hp.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hterm : ∀ n ∈ Finset.Icc 1 R,
      ∑ p ∈ ((Quant.modeBox R).erase 0).filter (fun p => Quant.supNorm p = n), (absSq p)⁻¹ ^ 2 ≤
        26 * ((n : ℝ) ^ 2)⁻¹ := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hnR : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    have hcard : (((Quant.modeBox R).erase 0).filter (fun p => Quant.supNorm p = n)).card ≤
        24 * n ^ 2 + 2 := by
      refine le_trans (Finset.card_le_card ?_) (Quant.card_shell_le (R := R) hn1)
      intro p hp
      rw [Finset.mem_filter, Finset.mem_erase] at hp
      exact Finset.mem_filter.2 ⟨hp.1.2, hp.2⟩
    calc ∑ p ∈ ((Quant.modeBox R).erase 0).filter (fun p => Quant.supNorm p = n), (absSq p)⁻¹ ^ 2
        ≤ ∑ p ∈ ((Quant.modeBox R).erase 0).filter (fun p => Quant.supNorm p = n),
            (((n : ℝ) ^ 2)⁻¹) ^ 2 := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hp' := (Finset.mem_filter.1 hp).2
          have := Quant.sq_supNorm_le_absSq p
          rw [hp'] at this
          exact pow_le_pow_left₀ (inv_nonneg.2 (absSq_nonneg p)) (inv_anti₀ hnR this) 2
      _ = ((((Quant.modeBox R).erase 0).filter (fun p => Quant.supNorm p = n)).card : ℝ) *
            (((n : ℝ) ^ 2)⁻¹) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((24 * n ^ 2 + 2 : ℕ) : ℝ) * (((n : ℝ) ^ 2)⁻¹) ^ 2 := by
          gcongr
      _ ≤ 26 * ((n : ℝ) ^ 2)⁻¹ := by
          push_cast
          have h3 : ((n : ℝ) ^ 2)⁻¹ * (n : ℝ) ^ 2 = 1 := inv_mul_cancel₀ hnR.ne'
          have h4 : (0 : ℝ) < ((n : ℝ) ^ 2)⁻¹ := inv_pos.2 hnR
          have h5 : ((n : ℝ) ^ 2)⁻¹ ≤ 1 := by
            rw [inv_le_one_iff₀]
            right
            nlinarith
          nlinarith
  calc ∑ n ∈ Finset.Icc 1 R, ∑ p ∈ ((Quant.modeBox R).erase 0).filter
        (fun p => Quant.supNorm p = n), (absSq p)⁻¹ ^ 2
      ≤ ∑ n ∈ Finset.Icc 1 R, 26 * ((n : ℝ) ^ 2)⁻¹ := Finset.sum_le_sum hterm
    _ = 26 * ∑ n ∈ Finset.Icc 1 R, ((n : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ 52 := by linarith [sum_Icc_inv_sq_le R]

/-- `c₄² = ∑_{k≠0} |k|⁻⁴ ≤ 52`. -/
private lemma c4_sq_le : c4 ^ 2 ≤ 52 := by
  classical
  have h0 : ∀ k : Mode, 0 ≤ if k = 0 then (0 : ℝ) else (absSq k)⁻¹ ^ 2 := fun k => by
    split_ifs
    · exact le_rfl
    · exact sq_nonneg _
  have hkey : ∀ s : Finset Mode, ∑ k ∈ s, (if k = 0 then (0 : ℝ) else (absSq k)⁻¹ ^ 2) ≤ 52 := by
    intro s
    set R := s.sup Quant.supNorm with hR
    have hsub : s ⊆ Quant.modeBox R := fun k hk =>
      Quant.mem_modeBox_iff_supNorm_le.2 (Finset.le_sup hk)
    have e : ∑ k ∈ Quant.modeBox R, (if k = 0 then (0 : ℝ) else (absSq k)⁻¹ ^ 2) =
        ∑ k ∈ (Quant.modeBox R).erase 0, (absSq k)⁻¹ ^ 2 := by
      rw [← Finset.sum_erase (a := (0 : Mode)) _ (by simp)]
      exact Finset.sum_congr rfl fun k hk => by simp [(Finset.mem_erase.1 hk).1]
    calc ∑ k ∈ s, (if k = 0 then (0 : ℝ) else (absSq k)⁻¹ ^ 2)
        ≤ ∑ k ∈ Quant.modeBox R, (if k = 0 then (0 : ℝ) else (absSq k)⁻¹ ^ 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => h0 k
      _ ≤ 52 := e ▸ sum_inv4_le R
  have hle := Real.tsum_le_of_sum_le h0 hkey
  rw [c4, Real.sq_sqrt (tsum_nonneg h0)]
  exact hle

/-- `c₄ ≤ 8`. -/
private lemma c4_le_eight : c4 ≤ 8 := by
  have h := c4_sq_le
  nlinarith [c4_pos]

/-! ### B. Weighted `ℓ¹` bounds and the three positions of the `ℓ¹` factor -/

/-- `∑ ‖F_k‖/|k| ≤ c₄ ‖F‖₁` (Cauchy–Schwarz against `|k|⁻²`; Body 12 §4: "`‖z/Q²‖_{ℓ¹} ≤
√104 ‖z‖₂`", "the comparable slow sequence `|h_p|/P` has `ℓ¹ ≤ √104 ‖h‖₁`"). -/
private lemma summable_div_absk {F : Field} (hF : MZ 1 F) :
    Summable (fun k => ‖F k‖ / absk k) ∧ ∑' k, ‖F k‖ / absk k ≤ c4 * hnorm 1 F := by
  classical
  set w : Mode → ℝ := fun k => if k = 0 then 0 else (absSq k)⁻¹ with hw
  have hw0 : ∀ k, 0 ≤ w k := fun k => by
    simp only [hw]
    split_ifs
    · exact le_rfl
    · exact inv_nonneg.2 (absSq_nonneg k)
  have hw2 : (fun k => w k ^ 2) = fun k : Mode => if k = 0 then (0 : ℝ) else (absSq k)⁻¹ ^ 2 := by
    funext k
    simp only [hw]
    split_ifs <;> simp
  have hg : Summable fun k => (absk k * ‖F k‖) ^ 2 :=
    hF.inH.congr fun k => by rw [sobWeight_one, mul_pow, absk_sq]
  obtain ⟨hs, hb⟩ := Quant.cs_tsum_nonneg' (a := fun k => absk k * ‖F k‖) (b := w)
    (fun k => mul_nonneg (absk_nonneg k) (norm_nonneg _)) hw0 hg (by rw [hw2]; exact summable_inv4)
  have e : (fun k => absk k * ‖F k‖ * w k) = fun k => ‖F k‖ / absk k := by
    funext k
    by_cases hk : k = 0
    · simp [hk, hF.mean]
    · have h1 : absk k ≠ 0 := absk_eq_zero.not.2 hk
      simp only [hw, ite_eq_right hk, ← absk_sq]
      field_simp
  rw [e] at hs hb
  refine ⟨hs, hb.trans (le_of_eq ?_)⟩
  rw [Quant.sqrt_tsum_grad_sq, hw2, mul_comm]
  rfl

/-- Young with the `ℓ¹` factor in the middle slot. -/
private lemma triple_mid {a b c : Mode → ℝ} (ha0 : ∀ k, 0 ≤ a k) (hb0 : ∀ k, 0 ≤ b k)
    (hc0 : ∀ k, 0 ≤ c k) (ha : Summable fun k => a k ^ 2) (hb : Summable b)
    (hc : Summable fun k => c k ^ 2) :
    Summable (fun x : Mode × Mode => a x.1 * b x.2 * c (x.1 + x.2)) ∧
      ∑' x : Mode × Mode, a x.1 * b x.2 * c (x.1 + x.2) ≤
        (∑' k, b k) * (Real.sqrt (∑' k, a k ^ 2) * Real.sqrt (∑' k, c k ^ 2)) := by
  obtain ⟨hs, hle⟩ := triple_bound hb0 ha0 hc0 hb ha hc
  have e : ∀ x : Mode × Mode, b x.swap.1 * a x.swap.2 * c (x.swap.1 + x.swap.2) =
      a x.1 * b x.2 * c (x.1 + x.2) := fun x => by
    simp only [Prod.fst_swap, Prod.snd_swap, add_comm x.2 x.1]
    ring
  have hs' := (Equiv.prodComm Mode Mode).summable_iff.mpr hs
  have ht := (Equiv.prodComm Mode Mode).tsum_eq fun x : Mode × Mode =>
    b x.1 * a x.2 * c (x.1 + x.2)
  simp only [Equiv.prodComm_apply, e] at ht
  refine ⟨hs'.congr fun x => (e x).symm ▸ rfl, ?_⟩
  rw [ht]
  exact hle

/-- The relabelling `(k, t) ↦ (k + t, -t)`. -/
private def shearE : Equiv.Perm (Mode × Mode) :=
  Function.Involutive.toPerm (fun x => (x.1 + x.2, -x.2)) fun x => Prod.ext (by simp) (by simp)

/-- Young with the `ℓ¹` factor on the output. -/
private lemma triple_right {a b c : Mode → ℝ} (ha0 : ∀ k, 0 ≤ a k) (hb0 : ∀ k, 0 ≤ b k)
    (hc0 : ∀ k, 0 ≤ c k) (ha : Summable fun k => a k ^ 2) (hb : Summable fun k => b k ^ 2)
    (hc : Summable c) :
    Summable (fun x : Mode × Mode => a x.1 * b x.2 * c (x.1 + x.2)) ∧
      ∑' x : Mode × Mode, a x.1 * b x.2 * c (x.1 + x.2) ≤
        (∑' k, c k) * (Real.sqrt (∑' k, a k ^ 2) * Real.sqrt (∑' k, b k ^ 2)) := by
  have hb' : Summable fun k => b (-k) ^ 2 := (Equiv.neg Mode).summable_iff.mpr hb
  obtain ⟨hs, hle⟩ := triple_bound (a := fun k => b (-k)) hc0 (fun k => hb0 _) ha0 hc hb' ha
  have hbe : ∑' k, b (-k) ^ 2 = ∑' k, b k ^ 2 := (Equiv.neg Mode).tsum_eq fun k => b k ^ 2
  rw [hbe] at hle
  have e : ∀ x : Mode × Mode,
      a (shearE x).1 * b (shearE x).2 * c ((shearE x).1 + (shearE x).2) =
        c x.1 * b (-x.2) * a (x.1 + x.2) := fun x => by
    have h1 : (shearE x).1 = x.1 + x.2 := rfl
    have h2 : (shearE x).2 = -x.2 := rfl
    have h3 : x.1 + x.2 + -x.2 = x.1 := by abel
    rw [h1, h2, h3]
    ring
  have hs' : Summable fun x : Mode × Mode => a x.1 * b x.2 * c (x.1 + x.2) := by
    rw [← shearE.summable_iff]
    exact hs.congr fun x => (e x).symm
  refine ⟨hs', ?_⟩
  have ht := shearE.tsum_eq fun x : Mode × Mode => a x.1 * b x.2 * c (x.1 + x.2)
  rw [← ht, tsum_congr e]
  calc ∑' x : Mode × Mode, c x.1 * b (-x.2) * a (x.1 + x.2)
      ≤ _ := hle
    _ = _ := by ring

/-- `(|k|²‖f_k‖)` is `ℓ²` with norm `‖f‖₂`. -/
private lemma hess_l2 {f : Field} (hf : MZ 2 f) :
    (Summable fun k => (absSq k * ‖f k‖) ^ 2) ∧
      Real.sqrt (∑' k, (absSq k * ‖f k‖) ^ 2) = hnorm 2 f := by
  have e : ∀ k, sobWeight 2 k * ‖f k‖ ^ 2 = (absSq k * ‖f k‖) ^ 2 := fun k => by
    rw [sobWeight_two, mul_pow]
  refine ⟨hf.inH.congr e, ?_⟩
  unfold hnorm
  rw [tsum_congr e]

/-- `(|k|‖f_k‖)` is `ℓ²`. -/
private lemma grad_l2 {f : Field} (hf : MZ 1 f) : Summable fun k => (absk k * ‖f k‖) ^ 2 :=
  hf.inH.congr fun k => by rw [sobWeight_one, mul_pow, absk_sq]

/-- `‖f_k‖` is `ℓ²`. -/
private lemma coeff_l2 {f : Field} (hf : MZ 1 f) : Summable fun k => ‖f k‖ ^ 2 :=
  summable_norm_sq_of_inH (hf.inH.mono (by norm_num))

/-- A nonzero coefficient of a mean-zero field sits at a nonzero mode. -/
private lemma pos_of_ne {f : Field} (h0 : f 0 = 0) {k : Mode} (h : ‖f k‖ ≠ 0) : 0 < absk k := by
  have hk : k ≠ 0 := fun e => h (by rw [e, h0, norm_zero])
  exact lt_of_lt_of_le one_pos (one_le_absk hk)

/-! ### C. The kernel of the paired form and its two convolution estimates -/

/-- The weight `|p||k| + |p||q| + |k||q|` of the Hermitian numerator `l(v+u) - uv`. -/
private def legW (p q : Mode) : ℝ :=
  absk p * absk (p + q) + absk p * absk q + absk (p + q) * absk q

/-- The positive kernel of the paired form. -/
private def kernT (S F G : Field) (x : Mode × Mode) : ℝ :=
  legW x.1 x.2 * (‖S x.1‖ * ‖F x.2‖ * ‖G (x.1 + x.2)‖)

/-- The weight of the numerator is nonnegative. -/
private lemma legW_nonneg (p q : Mode) : 0 ≤ legW p q := by
  have := absk_nonneg p
  have := absk_nonneg q
  have := absk_nonneg (p + q)
  unfold legW
  positivity

/-- The kernel is nonnegative. -/
private lemma kernT_nonneg (S F G : Field) (x : Mode × Mode) : 0 ≤ kernT S F G x :=
  mul_nonneg (legW_nonneg _ _) (by positivity)

/-- The pointwise envelope of the `H²` direction: Young in `P/Q ≤ ½(1 + P²/Q²)`. -/
private lemma kern_envelope_two {P Q K s f g : ℝ} (hQ : 0 < Q) (hK : 0 < K) (hs : 0 ≤ s)
    (hf : 0 ≤ f) (hg : 0 ≤ g) :
    (P * K + P * Q + K * Q) * (s * f * g) ≤
      2 * (s * (Q * f) * (K * g)) + 1 / 2 * (P ^ 2 * s * (f / Q) * (K * g)) +
        1 / 2 * (P ^ 2 * s * (Q * f) * (g / K)) := by
  have e : 2 * (s * (Q * f) * (K * g)) + 1 / 2 * (P ^ 2 * s * (f / Q) * (K * g)) +
      1 / 2 * (P ^ 2 * s * (Q * f) * (g / K)) =
      (2 * K * Q + 1 / 2 * (P ^ 2 * K / Q) + 1 / 2 * (P ^ 2 * Q / K)) * (s * f * g) := by
    field_simp
  rw [e]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have h1 : P * K ≤ 1 / 2 * (K * Q) + 1 / 2 * (P ^ 2 * K / Q) := by
    have : 1 / 2 * (K * Q) + 1 / 2 * (P ^ 2 * K / Q) - P * K = K * (P - Q) ^ 2 / (2 * Q) := by
      field_simp
      ring
    have h : 0 ≤ K * (P - Q) ^ 2 / (2 * Q) := by positivity
    linarith
  have h2 : P * Q ≤ 1 / 2 * (K * Q) + 1 / 2 * (P ^ 2 * Q / K) := by
    have : 1 / 2 * (K * Q) + 1 / 2 * (P ^ 2 * Q / K) - P * Q = Q * (P - K) ^ 2 / (2 * K) := by
      field_simp
      ring
    have h : 0 ≤ Q * (P - K) ^ 2 / (2 * K) := by positivity
    linarith
  linarith

/-- The pointwise envelope of the genuine `H¹` direction: one derivative on each exterior leg, in
both orientations (Body 12 §4, §6, without the comparable/separated split). -/
private lemma kern_envelope_one {P Q K s f g : ℝ} (hP : 0 < P) (hQ : 0 < Q) (hK : 0 < K)
    (htri : P ≤ K + Q) (hs : 0 ≤ s) (hf : 0 ≤ f) (hg : 0 ≤ g) :
    (P * K + P * Q + K * Q) * (s * f * g) ≤
      2 * (s / P * (Q ^ 2 * f) * (K * g)) + 2 * (s / P * (Q * f) * (K ^ 2 * g)) +
        P * s * (Q ^ 2 * f) * (g / K) + P * s * (f / Q) * (K ^ 2 * g) := by
  have e : 2 * (s / P * (Q ^ 2 * f) * (K * g)) + 2 * (s / P * (Q * f) * (K ^ 2 * g)) +
      P * s * (Q ^ 2 * f) * (g / K) + P * s * (f / Q) * (K ^ 2 * g) =
      (2 * (Q ^ 2 * K / P) + 2 * (Q * K ^ 2 / P) + P * Q ^ 2 / K + P * K ^ 2 / Q) *
        (s * f * g) := by
    field_simp
  rw [e]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have h1 : K * Q ≤ Q ^ 2 * K / P + Q * K ^ 2 / P := by
    have : Q ^ 2 * K / P + Q * K ^ 2 / P - K * Q = K * Q * (K + Q - P) / P := by
      field_simp
      ring
    have h : 0 ≤ K * Q * (K + Q - P) / P := by
      have : 0 ≤ K + Q - P := by linarith
      positivity
    linarith
  have h2 : P * K + P * Q ≤ Q ^ 2 * K / P + Q * K ^ 2 / P + P * Q ^ 2 / K + P * K ^ 2 / Q := by
    have : Q ^ 2 * K / P + Q * K ^ 2 / P + P * Q ^ 2 / K + P * K ^ 2 / Q - (P * K + P * Q) =
        (K + Q) * (K ^ 2 * Q ^ 2 + P ^ 2 * (Q - K) ^ 2) / (P * K * Q) := by
      field_simp
      ring
    have h : 0 ≤ (K + Q) * (K ^ 2 * Q ^ 2 + P ^ 2 * (Q - K) ^ 2) / (P * K * Q) := by positivity
    linarith
  linarith

/-- The `H²`-direction convolution envelope (Body 12 §4, (6)):
`∑ kernT ≤ 3 c₄ ‖S‖₂ ‖F‖₁ ‖G‖₁`. -/
private lemma kern_sum_two {S F G : Field} (hS : MZ 2 S) (hF : MZ 1 F) (hG : MZ 1 G) :
    Summable (kernT S F G) ∧
      ∑' x, kernT S F G x ≤ 3 * c4 * (hnorm 2 S * hnorm 1 F * hnorm 1 G) := by
  have hg1 : ∀ {f : Field} (k : Mode), 0 ≤ absk k * ‖f k‖ := fun k =>
    mul_nonneg (absk_nonneg k) (norm_nonneg _)
  have hg2 : ∀ {f : Field} (k : Mode), 0 ≤ absSq k * ‖f k‖ := fun k =>
    mul_nonneg (absSq_nonneg k) (norm_nonneg _)
  have hd : ∀ {f : Field} (k : Mode), 0 ≤ ‖f k‖ / absk k := fun k =>
    div_nonneg (norm_nonneg _) (absk_nonneg k)
  obtain ⟨hA, hAle⟩ := triple_bound (b := fun k => ‖S k‖) (a := fun k => absk k * ‖F k‖)
    (c := fun k => absk k * ‖G k‖) (fun _ => norm_nonneg _) hg1 hg1 (summable_wiener hS.inH)
    (grad_l2 hF) (grad_l2 hG)
  obtain ⟨hB, hBle⟩ := triple_mid (a := fun k => absSq k * ‖S k‖) (b := fun k => ‖F k‖ / absk k)
    (c := fun k => absk k * ‖G k‖) hg2 hd hg1 (hess_l2 hS).1 (summable_div_absk hF).1 (grad_l2 hG)
  obtain ⟨hC, hCle⟩ := triple_right (a := fun k => absSq k * ‖S k‖) (b := fun k => absk k * ‖F k‖)
    (c := fun k => ‖G k‖ / absk k) hg2 hg1 hd (hess_l2 hS).1 (grad_l2 hF) (summable_div_absk hG).1
  rw [Quant.sqrt_tsum_grad_sq, Quant.sqrt_tsum_grad_sq] at hAle
  rw [(hess_l2 hS).2, Quant.sqrt_tsum_grad_sq] at hBle hCle
  set A : Mode × Mode → ℝ := fun x => ‖S x.1‖ * (absk x.2 * ‖F x.2‖) *
    (absk (x.1 + x.2) * ‖G (x.1 + x.2)‖) with hAdef
  set B : Mode × Mode → ℝ := fun x => absSq x.1 * ‖S x.1‖ * (‖F x.2‖ / absk x.2) *
    (absk (x.1 + x.2) * ‖G (x.1 + x.2)‖) with hBdef
  set C : Mode × Mode → ℝ := fun x => absSq x.1 * ‖S x.1‖ * (absk x.2 * ‖F x.2‖) *
    (‖G (x.1 + x.2)‖ / absk (x.1 + x.2)) with hCdef
  have hA0 : ∀ x, 0 ≤ A x := fun x =>
    mul_nonneg (mul_nonneg (norm_nonneg _) (hg1 _)) (hg1 _)
  have hB0 : ∀ x, 0 ≤ B x := fun x => mul_nonneg (mul_nonneg (hg2 _) (hd _)) (hg1 _)
  have hC0 : ∀ x, 0 ≤ C x := fun x => mul_nonneg (mul_nonneg (hg2 _) (hg1 _)) (hd _)
  have hpt : ∀ x, kernT S F G x ≤ 2 * A x + (1 / 2 * B x + 1 / 2 * C x) := fun x => by
    have hR : 0 ≤ 2 * A x + (1 / 2 * B x + 1 / 2 * C x) := by
      have := hA0 x
      have := hB0 x
      have := hC0 x
      positivity
    by_cases hf : ‖F x.2‖ = 0
    · simpa [kernT, hf] using hR
    by_cases hg : ‖G (x.1 + x.2)‖ = 0
    · simpa [kernT, hg] using hR
    have h := kern_envelope_two (P := absk x.1) (hs := norm_nonneg (S x.1))
      (hf := norm_nonneg (F x.2)) (hg := norm_nonneg (G (x.1 + x.2))) (pos_of_ne hF.mean hf)
      (pos_of_ne hG.mean hg)
    rw [absk_sq] at h
    exact h.trans_eq (add_assoc _ _ _)
  have hsum := (hA.mul_left 2).add ((hB.mul_left (1 / 2)).add (hC.mul_left (1 / 2)))
  refine ⟨Summable.of_nonneg_of_le (kernT_nonneg S F G) hpt hsum, ?_⟩
  have hle := (Summable.of_nonneg_of_le (kernT_nonneg S F G) hpt hsum).tsum_le_tsum hpt hsum
  rw [(hA.mul_left 2).tsum_add ((hB.mul_left (1 / 2)).add (hC.mul_left (1 / 2))),
    (hB.mul_left (1 / 2)).tsum_add (hC.mul_left (1 / 2)), tsum_mul_left, tsum_mul_left,
    tsum_mul_left] at hle
  have hw1 := (summable_div_absk hF).2
  have hw2 := (summable_div_absk hG).2
  have hw3 := wiener_le hS
  have hnS := hnorm_nonneg 2 S
  have hnF := hnorm_nonneg 1 F
  have hnG := hnorm_nonneg 1 G
  have hc := c4_pos
  have h1 : ∑' x, A x ≤ c4 * hnorm 2 S * (hnorm 1 F * hnorm 1 G) :=
    hAle.trans (mul_le_mul_of_nonneg_right hw3 (by positivity))
  have h2 : ∑' x, B x ≤ c4 * hnorm 1 F * (hnorm 2 S * hnorm 1 G) :=
    hBle.trans (mul_le_mul_of_nonneg_right hw1 (by positivity))
  have h3 : ∑' x, C x ≤ c4 * hnorm 1 G * (hnorm 2 S * hnorm 1 F) :=
    hCle.trans (mul_le_mul_of_nonneg_right hw2 (by positivity))
  have e : 3 * c4 * (hnorm 2 S * hnorm 1 F * hnorm 1 G) =
      2 * (c4 * hnorm 2 S * (hnorm 1 F * hnorm 1 G)) +
        (1 / 2 * (c4 * hnorm 1 F * (hnorm 2 S * hnorm 1 G)) +
          1 / 2 * (c4 * hnorm 1 G * (hnorm 2 S * hnorm 1 F))) := by
    ring
  linarith

/-- The genuine `H¹`-direction convolution envelope (Body 12 §4, §6, (7), (14)):
`∑ kernT ≤ 3 c₄ ‖S‖₁ (‖F‖₂‖G‖₁ + ‖F‖₁‖G‖₂)`. -/
private lemma kern_sum_one {S F G : Field} (hS : MZ 1 S) (hF : MZ 2 F) (hG : MZ 2 G) :
    Summable (kernT S F G) ∧
      ∑' x, kernT S F G x ≤
        3 * c4 * (hnorm 1 S * (hnorm 2 F * hnorm 1 G + hnorm 1 F * hnorm 2 G)) := by
  have hF1 : MZ 1 F := ⟨hF.inH.mono (by norm_num), hF.mean⟩
  have hG1 : MZ 1 G := ⟨hG.inH.mono (by norm_num), hG.mean⟩
  have hg1 : ∀ {f : Field} (k : Mode), 0 ≤ absk k * ‖f k‖ := fun k =>
    mul_nonneg (absk_nonneg k) (norm_nonneg _)
  have hg2 : ∀ {f : Field} (k : Mode), 0 ≤ absSq k * ‖f k‖ := fun k =>
    mul_nonneg (absSq_nonneg k) (norm_nonneg _)
  have hd : ∀ {f : Field} (k : Mode), 0 ≤ ‖f k‖ / absk k := fun k =>
    div_nonneg (norm_nonneg _) (absk_nonneg k)
  obtain ⟨hA, hAle⟩ := triple_bound (b := fun k => ‖S k‖ / absk k)
    (a := fun k => absSq k * ‖F k‖) (c := fun k => absk k * ‖G k‖) hd hg2 hg1
    (summable_div_absk hS).1 (hess_l2 hF).1 (grad_l2 hG1)
  obtain ⟨hB, hBle⟩ := triple_bound (b := fun k => ‖S k‖ / absk k)
    (a := fun k => absk k * ‖F k‖) (c := fun k => absSq k * ‖G k‖) hd hg1 hg2
    (summable_div_absk hS).1 (grad_l2 hF1) (hess_l2 hG).1
  obtain ⟨hC, hCle⟩ := triple_right (a := fun k => absk k * ‖S k‖)
    (b := fun k => absSq k * ‖F k‖) (c := fun k => ‖G k‖ / absk k) hg1 hg2 hd
    (grad_l2 hS) (hess_l2 hF).1 (summable_div_absk hG1).1
  obtain ⟨hD, hDle⟩ := triple_mid (a := fun k => absk k * ‖S k‖)
    (b := fun k => ‖F k‖ / absk k) (c := fun k => absSq k * ‖G k‖) hg1 hd hg2
    (grad_l2 hS) (summable_div_absk hF1).1 (hess_l2 hG).1
  rw [(hess_l2 hF).2, Quant.sqrt_tsum_grad_sq] at hAle
  rw [(hess_l2 hG).2, Quant.sqrt_tsum_grad_sq] at hBle
  rw [(hess_l2 hF).2, Quant.sqrt_tsum_grad_sq] at hCle
  rw [(hess_l2 hG).2, Quant.sqrt_tsum_grad_sq] at hDle
  set A : Mode × Mode → ℝ := fun x => ‖S x.1‖ / absk x.1 * (absSq x.2 * ‖F x.2‖) *
    (absk (x.1 + x.2) * ‖G (x.1 + x.2)‖) with hAdef
  set B : Mode × Mode → ℝ := fun x => ‖S x.1‖ / absk x.1 * (absk x.2 * ‖F x.2‖) *
    (absSq (x.1 + x.2) * ‖G (x.1 + x.2)‖) with hBdef
  set C : Mode × Mode → ℝ := fun x => absk x.1 * ‖S x.1‖ * (absSq x.2 * ‖F x.2‖) *
    (‖G (x.1 + x.2)‖ / absk (x.1 + x.2)) with hCdef
  set D : Mode × Mode → ℝ := fun x => absk x.1 * ‖S x.1‖ * (‖F x.2‖ / absk x.2) *
    (absSq (x.1 + x.2) * ‖G (x.1 + x.2)‖) with hDdef
  have hA0 : ∀ x, 0 ≤ A x := fun x => mul_nonneg (mul_nonneg (hd _) (hg2 _)) (hg1 _)
  have hB0 : ∀ x, 0 ≤ B x := fun x => mul_nonneg (mul_nonneg (hd _) (hg1 _)) (hg2 _)
  have hC0 : ∀ x, 0 ≤ C x := fun x => mul_nonneg (mul_nonneg (hg1 _) (hg2 _)) (hd _)
  have hD0 : ∀ x, 0 ≤ D x := fun x => mul_nonneg (mul_nonneg (hg1 _) (hd _)) (hg2 _)
  have hpt : ∀ x, kernT S F G x ≤ 2 * A x + 2 * B x + C x + D x := fun x => by
    have hR : 0 ≤ 2 * A x + 2 * B x + C x + D x := by
      have := hA0 x
      have := hB0 x
      have := hC0 x
      have := hD0 x
      positivity
    by_cases hs : ‖S x.1‖ = 0
    · simpa [kernT, hs] using hR
    by_cases hf : ‖F x.2‖ = 0
    · simpa [kernT, hf] using hR
    by_cases hg : ‖G (x.1 + x.2)‖ = 0
    · simpa [kernT, hg] using hR
    have htri : absk x.1 ≤ absk (x.1 + x.2) + absk x.2 := by
      have := absk_sub_le (x.1 + x.2) x.2
      rwa [add_sub_cancel_right] at this
    have h := kern_envelope_one (hs := norm_nonneg (S x.1)) (hf := norm_nonneg (F x.2))
      (hg := norm_nonneg (G (x.1 + x.2))) (pos_of_ne hS.mean hs) (pos_of_ne hF.mean hf)
      (pos_of_ne hG.mean hg) htri
    rw [absk_sq, absk_sq] at h
    exact h
  have hsum := (((hA.mul_left 2).add (hB.mul_left 2)).add hC).add hD
  have hkS := Summable.of_nonneg_of_le (kernT_nonneg S F G) hpt hsum
  refine ⟨hkS, ?_⟩
  have hle := hkS.tsum_le_tsum hpt hsum
  rw [(((hA.mul_left 2).add (hB.mul_left 2)).add hC).tsum_add hD,
    ((hA.mul_left 2).add (hB.mul_left 2)).tsum_add hC, (hA.mul_left 2).tsum_add (hB.mul_left 2),
    tsum_mul_left, tsum_mul_left] at hle
  have hw1 := (summable_div_absk hS).2
  have hw2 := (summable_div_absk hG1).2
  have hw3 := (summable_div_absk hF1).2
  have hnS := hnorm_nonneg 1 S
  have hnF := hnorm_nonneg 1 F
  have hnG := hnorm_nonneg 1 G
  have hbF := hnorm_nonneg 2 F
  have hbG := hnorm_nonneg 2 G
  have hc := c4_pos
  have h1 : ∑' x, A x ≤ c4 * hnorm 1 S * (hnorm 2 F * hnorm 1 G) :=
    hAle.trans (mul_le_mul_of_nonneg_right hw1 (by positivity))
  have h2 : ∑' x, B x ≤ c4 * hnorm 1 S * (hnorm 1 F * hnorm 2 G) :=
    hBle.trans (mul_le_mul_of_nonneg_right hw1 (by positivity))
  have h3 : ∑' x, C x ≤ c4 * hnorm 1 G * (hnorm 1 S * hnorm 2 F) :=
    hCle.trans (mul_le_mul_of_nonneg_right hw2 (by positivity))
  have h4 : ∑' x, D x ≤ c4 * hnorm 1 F * (hnorm 1 S * hnorm 2 G) :=
    hDle.trans (mul_le_mul_of_nonneg_right hw3 (by positivity))
  have e : 3 * c4 * (hnorm 1 S * (hnorm 2 F * hnorm 1 G + hnorm 1 F * hnorm 2 G)) =
      2 * (c4 * hnorm 1 S * (hnorm 2 F * hnorm 1 G)) +
        2 * (c4 * hnorm 1 S * (hnorm 1 F * hnorm 2 G)) +
        c4 * hnorm 1 G * (hnorm 1 S * hnorm 2 F) + c4 * hnorm 1 F * (hnorm 1 S * hnorm 2 G) := by
    ring
  linarith

/-! ### D. The edge form of the pairing -/

/-- The fixed-triad summand of `⟨Z_k, Q^♯_m(X,Y)_k⟩`.  Unlike `tripT`, this needs no reality of
`Z`: the fast fields of `X1bil_le` are not assumed real. -/
private def edgeT (m : Mult) (X Y Z : Field) (p q : Mode) : ℂ :=
  ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, m a b c p q *
    inner ℂ (Z (p + q)) (hel c (p + q) (vert p q (hel a p (X p)) (hel b q (Y q))))

/-- `⟨Z_k, Q^♯_m(X,Y)_k⟩ = ∑_p edgeT m X Y Z p (k-p)`, given the convergence of the `p`-sum. -/
private lemma inner_Qm_edge {m : Mult} {X Y : Field} (Z : Field) (k : Mode)
    (hs : Summable fun p => ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, m a b c p (k - p) •
      hel c k (vert p (k - p) (hel a p (X p)) (hel b (k - p) (Y (k - p))))) :
    inner ℂ (Z k) (Qm m X Y k) = ∑' p, edgeT m X Y Z p (k - p) := by
  rw [Qm, inner_tsum _ hs]
  refine tsum_congr fun p => ?_
  have hk : p + (k - p) = k := by abel
  simp only [inner_sum, inner_smul_right, edgeT, hk]

/-- `|metM| ≤ 1/(|p|²+|q|²+|p+q|²)`. -/
private lemma norm_metM_le_triHeat (r τ : ℝ) (a b c : Sgn) {p q : Mode} (hk : p + q ≠ 0) :
    ‖metM r τ a b c p q‖ ≤ 1 / triHeat p q := by
  unfold metM
  split_ifs with h
  · exact norm_metSym_le r τ a b c hk
  · rw [norm_zero]
    exact div_nonneg zero_le_one (by linarith [one_le_triHeat hk])

/-- The direct bound of an edge term (no cancellation). -/
private lemma norm_edgeT_le (r τ : ℝ) (X Y Z : Field) {p q : Mode} (hk : p + q ≠ 0) :
    ‖edgeT (metM r τ) X Y Z p q‖ ≤
      8 * (1 / triHeat p q * ((absk p + absk q) * (‖X p‖ * ‖Y q‖ * ‖Z (p + q)‖))) := by
  set E := 1 / triHeat p q * ((absk p + absk q) * (‖X p‖ * ‖Y q‖ * ‖Z (p + q)‖)) with hE
  have hT : 0 ≤ 1 / triHeat p q := div_nonneg zero_le_one (by linarith [one_le_triHeat hk])
  have hpq : 0 ≤ absk p + absk q := add_nonneg (absk_nonneg p) (absk_nonneg q)
  have hterm : ∀ a b c, ‖metM r τ a b c p q * inner ℂ (Z (p + q))
      (hel c (p + q) (vert p q (hel a p (X p)) (hel b q (Y q))))‖ ≤ E := by
    intro a b c
    have h1 := norm_metM_le_triHeat r τ a b c hk
    have h3 : ‖hel c (p + q) (vert p q (hel a p (X p)) (hel b q (Y q)))‖ ≤
        (absk p + absk q) * (‖X p‖ * ‖Y q‖) := by
      refine (norm_hel_le _ _ _).trans ((norm_vert_le₁ _ _ _ _).trans ?_)
      have h4 : ‖hel a p (X p)‖ * ‖hel b q (Y q)‖ ≤ ‖X p‖ * ‖Y q‖ :=
        mul_le_mul (norm_hel_le _ _ _) (norm_hel_le _ _ _) (norm_nonneg _) (norm_nonneg _)
      have h5 : 0 ≤ (absk p + absk q) * (‖X p‖ * ‖Y q‖) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h4 hpq]
    have h2 : ‖inner ℂ (Z (p + q)) (hel c (p + q) (vert p q (hel a p (X p)) (hel b q (Y q))))‖ ≤
        (absk p + absk q) * (‖X p‖ * ‖Y q‖ * ‖Z (p + q)‖) := by
      refine (norm_inner_le_norm _ _).trans ?_
      calc ‖Z (p + q)‖ * ‖hel c (p + q) (vert p q (hel a p (X p)) (hel b q (Y q)))‖
          ≤ ‖Z (p + q)‖ * ((absk p + absk q) * (‖X p‖ * ‖Y q‖)) :=
            mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
        _ = _ := by ring
    rw [norm_mul, hE]
    exact mul_le_mul h1 h2 (norm_nonneg _) hT
  have hbd : ‖edgeT (metM r τ) X Y Z p q‖ ≤ ∑ _a : Sgn, ∑ _b : Sgn, ∑ _c : Sgn, E :=
    norm_sum_le_of_le _ fun a _ => norm_sum_le_of_le _ fun b _ =>
      norm_sum_le_of_le _ fun c _ => hterm a b c
  refine hbd.trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
  push_cast
  ring

/-- Summability of the weighted edge family, output in `H¹`, input in the Wiener algebra. -/
private lemma summable_edge_one (r τ : ℝ) {X Y Z : Field} (hX : MZ 1 X) (hY : MZ 2 Y)
    (hZ : MZ 1 Z) :
    Summable fun x : Mode × Mode =>
      (sobWeight 1 (x.1 + x.2) : ℂ) * edgeT (metM r τ) X Y Z x.1 x.2 := by
  obtain ⟨hA, -⟩ := triple_mid (a := fun k => absk k * ‖X k‖) (b := fun k => ‖Y k‖)
    (c := fun k => absk k * ‖Z k‖) (fun k => mul_nonneg (absk_nonneg k) (norm_nonneg _))
    (fun _ => norm_nonneg _) (fun k => mul_nonneg (absk_nonneg k) (norm_nonneg _)) (grad_l2 hX)
    (summable_wiener hY.inH) (grad_l2 hZ)
  refine Summable.of_norm_bounded (hA.mul_left 8) fun x => ?_
  rw [norm_mul, Complex.norm_real, sobWeight_one, Real.norm_of_nonneg (absSq_nonneg _)]
  set p := x.1
  set q := x.2
  by_cases hk : p + q = 0
  · have h0 : absSq (p + q) = 0 := by rw [hk]; simp [absSq]
    rw [h0, zero_mul]
    have := mul_nonneg (mul_nonneg (mul_nonneg (absk_nonneg p) (norm_nonneg (X p)))
      (norm_nonneg (Y q))) (mul_nonneg (absk_nonneg (p + q)) (norm_nonneg (Z (p + q))))
    linarith
  by_cases hx : ‖X p‖ = 0
  · have h0 : ‖edgeT (metM r τ) X Y Z p q‖ ≤ 0 := by
      have := norm_edgeT_le r τ X Y Z hk
      simpa [hx] using this
    have h1 := mul_le_mul_of_nonneg_left h0 (absSq_nonneg (p + q))
    simp only [hx, mul_zero, zero_mul] at h1 ⊢
    linarith
  have hP : 1 ≤ absk p := one_le_absk fun e => hx (by rw [e, hX.mean, norm_zero])
  have hK := absk_nonneg (p + q)
  have hQ := absk_nonneg q
  have hT : 0 < triHeat p q := by linarith [one_le_triHeat hk]
  have hTe : triHeat p q = absk p ^ 2 + absk q ^ 2 + absk (p + q) ^ 2 := by
    simp only [triHeat, absk_sq]
  have hkern : absSq (p + q) * (1 / triHeat p q * (absk p + absk q)) ≤
      absk p * absk (p + q) := by
    rw [← absk_sq, ← mul_assoc, mul_one_div, div_mul_eq_mul_div, div_le_iff₀ hT, hTe]
    nlinarith [sq_nonneg (absk (p + q) - absk p), sq_nonneg (absk (p + q) - absk q),
      mul_nonneg hK (sq_nonneg (absk (p + q) - absk p)),
      mul_nonneg hK (sq_nonneg (absk (p + q) - absk q)),
      mul_nonneg hK (mul_nonneg (sub_nonneg.2 hP) (add_nonneg (sq_nonneg (absk p))
        (add_nonneg (sq_nonneg (absk q)) (sq_nonneg (absk (p + q))))))]
  have hxyz : 0 ≤ ‖X p‖ * ‖Y q‖ * ‖Z (p + q)‖ := by positivity
  calc absSq (p + q) * ‖edgeT (metM r τ) X Y Z p q‖
      ≤ absSq (p + q) * (8 * (1 / triHeat p q * ((absk p + absk q) *
          (‖X p‖ * ‖Y q‖ * ‖Z (p + q)‖)))) :=
        mul_le_mul_of_nonneg_left (norm_edgeT_le r τ X Y Z hk) (absSq_nonneg _)
    _ = 8 * ((absSq (p + q) * (1 / triHeat p q * (absk p + absk q))) *
          (‖X p‖ * ‖Y q‖ * ‖Z (p + q)‖)) := by ring
    _ ≤ 8 * ((absk p * absk (p + q)) * (‖X p‖ * ‖Y q‖ * ‖Z (p + q)‖)) := by
        gcongr
    _ = 8 * (absk p * ‖X p‖ * ‖Y q‖ * (absk (p + q) * ‖Z (p + q)‖)) := by ring

/-- Summability of the weighted edge family, output in the Wiener algebra. -/
private lemma summable_edge_two (r τ : ℝ) {X Y Z : Field} (hX : MZ 1 X) (hY : MZ 1 Y)
    (hZ : MZ 2 Z) :
    Summable fun x : Mode × Mode =>
      (sobWeight 1 (x.1 + x.2) : ℂ) * edgeT (metM r τ) X Y Z x.1 x.2 := by
  obtain ⟨hA, -⟩ := triple_right (a := fun k => absk k * ‖X k‖) (b := fun k => ‖Y k‖)
    (c := fun k => ‖Z k‖) (fun k => mul_nonneg (absk_nonneg k) (norm_nonneg _))
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) (grad_l2 hX) (coeff_l2 hY)
    (summable_wiener hZ.inH)
  obtain ⟨hB, -⟩ := triple_right (a := fun k => ‖X k‖) (b := fun k => absk k * ‖Y k‖)
    (c := fun k => ‖Z k‖) (fun _ => norm_nonneg _)
    (fun k => mul_nonneg (absk_nonneg k) (norm_nonneg _)) (fun _ => norm_nonneg _) (coeff_l2 hX)
    (grad_l2 hY) (summable_wiener hZ.inH)
  refine Summable.of_norm_bounded ((hA.add hB).mul_left 8) fun x => ?_
  rw [norm_mul, Complex.norm_real, sobWeight_one, Real.norm_of_nonneg (absSq_nonneg _)]
  set p := x.1
  set q := x.2
  have hRe : 8 * (absk p * ‖X p‖ * ‖Y q‖ * ‖Z (p + q)‖ +
      ‖X p‖ * (absk q * ‖Y q‖) * ‖Z (p + q)‖) =
      8 * ((absk p + absk q) * (‖X p‖ * ‖Y q‖ * ‖Z (p + q)‖)) := by ring
  rw [hRe]
  have hR0 : 0 ≤ (absk p + absk q) * (‖X p‖ * ‖Y q‖ * ‖Z (p + q)‖) := by
    have := absk_nonneg p
    have := absk_nonneg q
    positivity
  by_cases hk : p + q = 0
  · have h0 : absSq (p + q) = 0 := by rw [hk]; simp [absSq]
    rw [h0, zero_mul]
    linarith
  have hT : 0 < triHeat p q := by linarith [one_le_triHeat hk]
  have hkern : absSq (p + q) * (1 / triHeat p q) ≤ 1 := by
    rw [mul_one_div, div_le_one hT]
    exact absSq_le_triHeat p q
  calc absSq (p + q) * ‖edgeT (metM r τ) X Y Z p q‖
      ≤ absSq (p + q) * (8 * (1 / triHeat p q * ((absk p + absk q) *
          (‖X p‖ * ‖Y q‖ * ‖Z (p + q)‖)))) :=
        mul_le_mul_of_nonneg_left (norm_edgeT_le r τ X Y Z hk) (absSq_nonneg _)
    _ = 8 * ((absSq (p + q) * (1 / triHeat p q)) * ((absk p + absk q) *
          (‖X p‖ * ‖Y q‖ * ‖Z (p + q)‖))) := by ring
    _ ≤ 8 * (1 * ((absk p + absk q) * (‖X p‖ * ‖Y q‖ * ‖Z (p + q)‖))) := by
        gcongr
    _ = _ := by ring

/-- The pairing with the `H¹` weight as a sum over triads. -/
private lemma pair_eq_edge {r τ : ℝ} {X Y Z : Field} (hX : MZ 1 X) (hY : MZ 1 Y)
    (hT : Summable fun x : Mode × Mode =>
      (sobWeight 1 (x.1 + x.2) : ℂ) * edgeT (metM r τ) X Y Z x.1 x.2) :
    pair 1 Z (X1op r τ X Y) =
      (∑' x : Mode × Mode, (sobWeight 1 (x.1 + x.2) : ℂ) * edgeT (metM r τ) X Y Z x.1 x.2).re :=
  pair_eq_tsum (edgeT (metM r τ) X Y Z)
    (fun k => inner_Qm_edge Z k (summable_Qm_term_gain (norm_metM_le_absSq r τ) k
      (summable_vertex_fixed k (coeff_l2 hX) (coeff_l2 hY) (Or.inl (grad_l2 hX))))) hT

/-! ### E. The Hermitian pairing of the two couplings -/

/-- Conjugation of a triple product. -/
private lemma conj_bd_cross (x y z : V3) :
    conj (bd (conjV x) (cross (conjV y) z)) = bd x (cross y (conjV z)) := by
  simp only [bd, cross_apply_zero, cross_apply_one, cross_apply_two, conjV_apply, map_add, map_sub,
    map_mul, Complex.conj_conj]

/-- Antisymmetry of the triple product in its outer slots. -/
private lemma bd_cross_swap (x y z : V3) : bd x (cross y z) = -bd z (cross y x) := by
  simp only [bd, cross_apply_zero, cross_apply_one, cross_apply_two]
  ring

/-- The vertex against an arbitrary test vector, on helical inputs (`vert_hel`). -/
private lemma inner_hel_vert (Z X Y : V3) (a b c : Sgn) {p q : Mode} (hk : p + q ≠ 0) :
    inner ℂ Z (hel c (p + q) (vert p q (hel a p X) (hel b q Y))) =
      (((sg a * absk p - sg b * absk q) / 2 : ℝ) : ℂ) *
        bd (conjV (hel c (p + q) Z)) (cross (hel a p X) (hel b q Y)) := by
  have hC : dotM (conjV (hel c (p + q) Z)) (p + q) = 0 := by
    rw [conjV_hel]
    exact dotM_hel_neg c _ _
  rw [inner_hel_right, inner_eq_bd, vert_hel, bd_smul_right, bd_leray hk hC]

/-- The helical triple product of the triad `(p, q, -(p+q))`. -/
private def trQ (S F G : Field) (a b c : Sgn) (p q : Mode) : ℂ :=
  bd (conjV (hel c (p + q) (G (p + q)))) (cross (hel a p (S p)) (hel b q (F q)))

/-- `|[A, B, C]| ≤ ‖A‖ ‖B‖ ‖C‖` on the triad. -/
private lemma norm_trQ_le (S F G : Field) (a b c : Sgn) (p q : Mode) :
    ‖trQ S F G a b c p q‖ ≤ ‖S p‖ * ‖F q‖ * ‖G (p + q)‖ := by
  unfold trQ
  refine (norm_bd_le _ _).trans ?_
  rw [norm_conjV]
  calc ‖hel c (p + q) (G (p + q))‖ * ‖cross (hel a p (S p)) (hel b q (F q))‖
      ≤ ‖G (p + q)‖ * (‖S p‖ * ‖F q‖) :=
        mul_le_mul (norm_hel_le _ _ _)
          ((norm_cross_le _ _).trans (mul_le_mul (norm_hel_le _ _ _) (norm_hel_le _ _ _)
            (norm_nonneg _) (norm_nonneg _))) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by ring

/-- The reverse edge `k → q` through `S_{-p} = conj S_p`, conjugated: the same triple product. -/
private lemma conj_inner_rev {S : Field} (hS : IsReal S) (F G : Field) (a b c : Sgn) (p : Mode)
    {q : Mode} (hq : q ≠ 0) :
    conj (inner ℂ (F q) (hel b q (vert (-p) (p + q) (hel a (-p) (S (-p)))
        (hel c (p + q) (G (p + q)))))) =
      -(((sg a * absk p - sg c * absk (p + q)) / 2 : ℝ) : ℂ) * trQ S F G a b c p q := by
  have e : -p + (p + q) = q := by abel
  have h := inner_hel_vert (F q) (S (-p)) (G (p + q)) a c b (p := -p) (q := p + q) (by rwa [e])
  rw [e, absk_neg, hS p, ← conjV_hel] at h
  rw [hS p, ← conjV_hel, h, map_mul, Complex.conj_ofReal, conj_bd_cross, bd_cross_swap]
  unfold trQ
  ring

/-- The reversed edge has the opposite phase. -/
private lemma Phi_flip (a b c : Sgn) {p : Mode} (hp : p 2 = 0) (q : Mode) :
    Phi a c b (-p) (p + q) = -Phi a b c p q := by
  have e : -p + (p + q) = q := by abel
  simp only [Phi, e, lam_neg, lam_slow hp]
  ring

/-- The reversed edge has the same three-leg heat. -/
private lemma triHeat_flip (p q : Mode) : triHeat (-p) (p + q) = triHeat p q := by
  have e : -p + (p + q) = q := by abel
  simp only [triHeat, e, absSq_neg]
  ring

/-- The reversed edge has the same mask. -/
private lemma slowFast_flip (a b c : Sgn) (p q : Mode) :
    SlowFast a c b (-p) (p + q) ↔ SlowFast a b c p q := by
  unfold SlowFast
  by_cases hp : p 2 = 0
  · rw [Phi_flip a b c hp q, neg_ne_zero]
    simp [hp]
  · simp [hp]

/-- `m(-δ) = conj m(δ)` for the `X₁` symbol, on a slow leg. -/
private lemma metSym_flip (r τ : ℝ) (a b c : Sgn) {p : Mode} (hp : p 2 = 0) (q : Mode) :
    conj (metSym r τ a c b (-p) (p + q)) = metSym r τ a b c p q := by
  have hph : conj (phaseM τ a c b (-p) (p + q)) = phaseM τ a b c p q := by
    simp only [phaseM, Phi_flip a b c hp q]
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  rw [metSym, map_mul, hph, Quant.conj_resolv, triHeat_flip, Phi_flip a b c hp, mul_neg, neg_neg,
    metSym]

/-- The two edges of a triad carry the same multiplier, up to conjugation. -/
private lemma conj_metM_flip (r τ : ℝ) (a b c : Sgn) (p q : Mode) :
    conj (metM r τ a c b (-p) (p + q)) = metM r τ a b c p q := by
  unfold metM
  by_cases h : SlowFast a b c p q
  · rw [ite_eq_left ((slowFast_flip a b c p q).2 h), ite_eq_left h]
    exact metSym_flip r τ a b c h.1 q
  · rw [ite_eq_right (fun h' => h ((slowFast_flip a b c p q).1 h')), ite_eq_right h, map_zero]

/-- `|metSym| ≤ 1/(q|Φ|)`, the phase gain of the resolvent. -/
private lemma norm_metSym_mul_Phi_le (r τ : ℝ) (a b c : Sgn) (p q : Mode) :
    ‖metSym r τ a b c p q‖ * (|r| * |Phi a b c p q|) ≤ 1 := by
  rw [metSym, norm_mul, Quant.norm_resolv_sgn (Or.inr rfl), ← abs_mul]
  set z := r * Phi a b c p q
  set T := triHeat p q
  have h1 : |z| ≤ Real.sqrt (T ^ 2 + z ^ 2) :=
    Real.abs_le_sqrt (by nlinarith [sq_nonneg T])
  have h2 : 1 / Real.sqrt (T ^ 2 + z ^ 2) * |z| ≤ 1 := by
    rw [one_div_mul_eq_div]
    exact div_le_one_of_le₀ h1 (Real.sqrt_nonneg _)
  have h3 := phaseM_bdd τ a b c p q
  have h4 : 0 ≤ 1 / Real.sqrt (T ^ 2 + z ^ 2) * |z| := by positivity
  calc ‖phaseM τ a b c p q‖ * (1 / Real.sqrt (T ^ 2 + z ^ 2)) * |z|
      = ‖phaseM τ a b c p q‖ * (1 / Real.sqrt (T ^ 2 + z ^ 2) * |z|) := by ring
    _ ≤ 1 * 1 := mul_le_mul h3 h2 h4 zero_le_one
    _ = 1 := one_mul 1

/-- `|a| = 1` for a helicity sign. -/
private lemma abs_sg (a : Sgn) : |sg a| = 1 := by
  cases a <;> simp [sg]

/-- `a² = 1` for a helicity sign. -/
private lemma sg_sq (a : Sgn) : sg a ^ 2 = 1 := by
  cases a <;> simp [sg]

/-- **The collapse**: `K²(l-u) - Q²(l-v) = (v-u)[l(v+u) - uv]`, and `(v-u)/(-Σ + irδ)` is
`≤ 1/q` since `δ = n(u-v)`, `|n| ≥ 1`. -/
private lemma numer_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) (a b c : Sgn) (p q : Mode) :
    ‖metM r τ a b c p q‖ * |absSq (p + q) * ((sg a * absk p - sg b * absk q) / 2) -
        absSq q * ((sg a * absk p - sg c * absk (p + q)) / 2)| ≤ legW p q / (2 * |r|) := by
  have hr' : 0 < |r| := abs_pos.2 hr
  have hW := legW_nonneg p q
  unfold metM
  split_ifs with h
  swap
  · rw [norm_zero, zero_mul]
    positivity
  have hm := norm_metSym_mul_Phi_le r τ a b c p q
  obtain ⟨hp, hq, -⟩ := h
  set m := ‖metSym r τ a b c p q‖ with hmdef
  have hm0 : 0 ≤ m := norm_nonneg _
  set l := sg a * absk p with hl
  set u := sg b * absk q with hu
  set v := sg c * absk (p + q) with hv
  have hk2 : (((p + q) 2 : ℤ) : ℝ) = (q 2 : ℝ) := by simp [hp]
  have hΦ : Phi a b c p q = (q 2 : ℝ) * (u - v) := by
    rw [Phi, lam_slow hp, lam, lam, hk2, hu, hv]
    ring
  have hn : 1 ≤ |(q 2 : ℝ)| := by
    have : (1 : ℤ) ≤ |q 2| := Int.one_le_abs hq
    exact_mod_cast this
  have hQ2 : absSq q = u ^ 2 := by
    rw [hu, mul_pow, sg_sq, one_mul, absk_sq]
  have hK2 : absSq (p + q) = v ^ 2 := by
    rw [hv, mul_pow, sg_sq, one_mul, absk_sq]
  have hnum : absSq (p + q) * ((l - u) / 2) - absSq q * ((l - v) / 2) =
      (v - u) * (l * (v + u) - u * v) / 2 := by
    rw [hQ2, hK2]
    ring
  rw [hnum, abs_div, abs_mul, abs_two]
  have habs_l : |l| = absk p := by rw [hl, abs_mul, abs_sg, one_mul, abs_of_nonneg (absk_nonneg p)]
  have habs_u : |u| = absk q := by rw [hu, abs_mul, abs_sg, one_mul, abs_of_nonneg (absk_nonneg q)]
  have habs_v : |v| = absk (p + q) := by
    rw [hv, abs_mul, abs_sg, one_mul, abs_of_nonneg (absk_nonneg _)]
  have hX : |l * (v + u) - u * v| ≤ legW p q := by
    calc |l * (v + u) - u * v| ≤ |l * (v + u)| + |u * v| := abs_sub _ _
      _ = |l| * |v + u| + |u| * |v| := by rw [abs_mul l, abs_mul u]
      _ ≤ |l| * (|v| + |u|) + |u| * |v| := by
          gcongr
          exact abs_add_le _ _
      _ = legW p q := by
          rw [habs_l, habs_u, habs_v, legW]
          ring
  have hvu : |v - u| = |u - v| := abs_sub_comm v u
  have hmr : m * |u - v| ≤ 1 / |r| := by
    rw [le_div_iff₀ hr']
    rw [hΦ, abs_mul] at hm
    have h1 : 0 ≤ m * |r| * |u - v| := by positivity
    calc m * |u - v| * |r| = m * |r| * |u - v| := by ring
      _ ≤ m * |r| * |u - v| * |(q 2 : ℝ)| := le_mul_of_one_le_right h1 hn
      _ = m * (|r| * (|(q 2 : ℝ)| * |u - v|)) := by ring
      _ ≤ 1 := hm
  rw [hvu]
  calc m * (|u - v| * |l * (v + u) - u * v| / 2)
      = (m * |u - v|) * |l * (v + u) - u * v| / 2 := by ring
    _ ≤ (1 / |r|) * legW p q / 2 := by
        gcongr
    _ = legW p q / (2 * |r|) := by
        field_simp

/-- **The paired block estimate**: the coupling `q → k` through `S_p` and the conjugated coupling
`k → q` through `S_{-p}` combine, on each triad, to `4/|r| · (|p||k| + |p||q| + |k||q|) ‖S_p‖ ‖F_q‖
‖G_k‖`: the term `K²(l-u) - Q²(l-v)` carries the factor `v - u`, `δ = n(u - v)`.  The eight helicity
patterns are bounded one by one, so the paired Schur lemma of Body 12 §2 is not used: this costs a
constant factor, paid by the room in `2⁸`, `2⁹`. -/
private lemma norm_paired_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {S : Field} (hS : IsReal S)
    (F G : Field) (p q : Mode) :
    ‖(absSq (p + q) : ℂ) * edgeT (metM r τ) S F G p q +
        (absSq q : ℂ) * conj (edgeT (metM r τ) S G F (-p) (p + q))‖ ≤
      4 / |r| * (legW p q * (‖S p‖ * ‖F q‖ * ‖G (p + q)‖)) := by
  have hr' : 0 < |r| := abs_pos.2 hr
  have hR : 0 ≤ legW p q * (‖S p‖ * ‖F q‖ * ‖G (p + q)‖) :=
    mul_nonneg (legW_nonneg p q) (by positivity)
  by_cases hmask : p 2 = 0 ∧ q 2 ≠ 0
  · obtain ⟨hp, hq⟩ := hmask
    have hk : p + q ≠ 0 := fun h => hq (by
      have := congrFun h 2
      simpa [hp] using this)
    have hq0 : q ≠ 0 := fun h => hq (by simp [h])
    have e1 : edgeT (metM r τ) S F G p q = ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, metM r τ a b c p q *
        (((sg a * absk p - sg b * absk q) / 2 : ℝ) * trQ S F G a b c p q) := by
      unfold edgeT
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun c _ => ?_
      rw [inner_hel_vert _ _ _ _ _ _ hk]
      rfl
    have e2 : conj (edgeT (metM r τ) S G F (-p) (p + q)) =
        ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, metM r τ a b c p q *
          (-((sg a * absk p - sg c * absk (p + q)) / 2 : ℝ) * trQ S F G a b c p q) := by
      have e3 : -p + (p + q) = q := by abel
      unfold edgeT
      rw [e3]
      simp only [map_sum, map_mul]
      rw [sum3_swap]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun c _ => ?_
      rw [conj_metM_flip, conj_inner_rev hS _ _ _ _ _ _ hq0]
    have e4 : (absSq (p + q) : ℂ) * edgeT (metM r τ) S F G p q +
        (absSq q : ℂ) * conj (edgeT (metM r τ) S G F (-p) (p + q)) =
        ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, metM r τ a b c p q *
          (((absSq (p + q) * ((sg a * absk p - sg b * absk q) / 2) -
            absSq q * ((sg a * absk p - sg c * absk (p + q)) / 2) : ℝ) : ℂ) *
              trQ S F G a b c p q) := by
      rw [e1, e2]
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun c _ => ?_
      push_cast
      ring
    rw [e4]
    set E := legW p q / (2 * |r|) * (‖S p‖ * ‖F q‖ * ‖G (p + q)‖) with hE
    have hterm : ∀ a b c, ‖metM r τ a b c p q *
        (((absSq (p + q) * ((sg a * absk p - sg b * absk q) / 2) -
            absSq q * ((sg a * absk p - sg c * absk (p + q)) / 2) : ℝ) : ℂ) *
              trQ S F G a b c p q)‖ ≤ E := by
      intro a b c
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, ← mul_assoc]
      exact mul_le_mul (numer_le hr τ a b c p q) (norm_trQ_le S F G a b c p q) (norm_nonneg _)
        (div_nonneg (legW_nonneg p q) (by positivity))
    refine (norm_sum_le_of_le _ fun a _ => norm_sum_le_of_le _ fun b _ =>
      norm_sum_le_of_le _ fun c _ => hterm a b c).trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul, hE]
    push_cast
    field_simp
    ring
  · have h1 : ∀ a b c, metM r τ a b c p q = 0 := fun a b c => by
      unfold metM
      exact ite_eq_right fun h => hmask ⟨h.1, h.2.1⟩
    have h2 : ∀ a b c, metM r τ a b c (-p) (p + q) = 0 := fun a b c => by
      have := conj_metM_flip r τ a c b p q
      rw [h1] at this
      exact (map_eq_zero _).1 this
    simp only [edgeT, h1, h2, zero_mul, Finset.sum_const_zero, map_zero, mul_zero, add_zero,
      norm_zero]
    positivity

/-! ### F. The two bounds -/

/-- The relabelling `(p, q) ↦ (-p, p + q)`: the coupling `q → k` through `p` against the coupling
`k → q` through `-p`. -/
private def flipE : Equiv.Perm (Mode × Mode) :=
  Function.Involutive.toPerm (fun x => (-x.1, x.1 + x.2)) fun x => Prod.ext (by simp) (by simp)

/-- The paired form against the positive kernel. -/
private lemma abs_pair_add_pair_le {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {S F G : Field} (hS : MZ 1 S)
    (hSr : IsReal S) (hF : MZ 2 F) (hG : MZ 1 G) (hk : Summable (kernT S F G)) :
    |pair 1 G (X1op r τ S F) + pair 1 F (X1op r τ S G)| ≤ 4 / |r| * ∑' x, kernT S F G x := by
  have hF1 : MZ 1 F := ⟨hF.inH.mono (by norm_num), hF.mean⟩
  set U : Mode × Mode → ℂ := fun x =>
    (sobWeight 1 (x.1 + x.2) : ℂ) * edgeT (metM r τ) S F G x.1 x.2 with hU
  set V : Mode × Mode → ℂ := fun x =>
    (sobWeight 1 (x.1 + x.2) : ℂ) * edgeT (metM r τ) S G F x.1 x.2 with hV
  have hUs : Summable U := summable_edge_one r τ hS hF hG
  have hVs : Summable V := summable_edge_two r τ hS hG hF
  have e1 : pair 1 G (X1op r τ S F) = (∑' x, U x).re := pair_eq_edge hS hF1 hUs
  have e2 : pair 1 F (X1op r τ S G) = (∑' x, V x).re := pair_eq_edge hS hG hVs
  have hVf : Summable fun x => V (flipE x) := flipE.summable_iff.mpr hVs
  have e3 : ∑' x, V (flipE x) = ∑' x, V x := flipE.tsum_eq V
  have hVc : Summable fun x => conj (V (flipE x)) := hVf.star
  have e4 : ∑' x, conj (V (flipE x)) = conj (∑' x, V (flipE x)) := (Complex.conj_tsum _).symm
  have hpt : ∀ x, ‖U x + conj (V (flipE x))‖ ≤ 4 / |r| * kernT S F G x := by
    rintro ⟨p, q⟩
    have h := norm_paired_le hr τ hSr F G p q
    have e7 : -p + (p + q) = q := by abel
    show ‖((sobWeight 1 (p + q) : ℝ) : ℂ) * edgeT (metM r τ) S F G p q +
        conj (((sobWeight 1 (-p + (p + q)) : ℝ) : ℂ) * edgeT (metM r τ) S G F (-p) (p + q))‖ ≤
      4 / |r| * kernT S F G (p, q)
    rw [e7, sobWeight_one, sobWeight_one, map_mul, Complex.conj_ofReal]
    exact h
  have e8 : pair 1 G (X1op r τ S F) + pair 1 F (X1op r τ S G) =
      (∑' x, (U x + conj (V (flipE x)))).re := by
    rw [hUs.tsum_add hVc, e1, e2, Complex.add_re, e4, e3, Complex.conj_re]
  rw [e8]
  refine (Complex.abs_re_le_norm _).trans ?_
  exact tsum_of_norm_bounded ((hk.mul_left _).hasSum.trans_eq (by rw [tsum_mul_left])) hpt

/-- **The `X₁` operator bound, polarized** (Body 12 §6 eq. (12); `X1bil_le` of `Bounds.lean`,
verbatim): `|⟨z_F, X₁ z_G⟩| ≤ 2⁸ B_S ‖F‖₁‖G‖₁/q` for a real slow `S ∈ H²`, fast `F ∈ H²`, fast
`G ∈ H¹`.  The proof gives the better constant `24 c₄ ≤ 192`. -/
theorem X1bil_le_proved {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {S F G : Field} (hS : MZ 2 S) (hSr : IsReal S)
    (hS' : PiS S = S)
    (hF : MZ 2 F) (hF' : PiF F = F) (hG : MZ 1 G) (hG' : PiF G = G) :
    |X1bil r τ S F G| ≤ 2 ^ 8 * hnorm 2 S * hnorm 1 F * hnorm 1 G / |r| := by
  have _ := hS'
  have _ := hF'
  have _ := hG'
  have hr' : 0 < |r| := abs_pos.2 hr
  have hS1 : MZ 1 S := ⟨hS.inH.mono (by norm_num), hS.mean⟩
  have hF1 : MZ 1 F := ⟨hF.inH.mono (by norm_num), hF.mean⟩
  obtain ⟨hk, hle⟩ := kern_sum_two hS hF1 hG
  have h := abs_pair_add_pair_le hr τ hS1 hSr hF hG hk
  have hW0 : 0 ≤ hnorm 2 S * hnorm 1 F * hnorm 1 G :=
    mul_nonneg (mul_nonneg (hnorm_nonneg _ _) (hnorm_nonneg _ _)) (hnorm_nonneg _ _)
  have e : X1bil r τ S F G = 2 * (pair 1 G (X1op r τ S F) + pair 1 F (X1op r τ S G)) := by
    unfold X1bil
    ring
  have hc : 3 * c4 ≤ 24 := by linarith [c4_le_eight]
  rw [e, abs_mul, abs_two]
  calc 2 * |pair 1 G (X1op r τ S F) + pair 1 F (X1op r τ S G)|
      ≤ 2 * (4 / |r| * ∑' x, kernT S F G x) := by gcongr
    _ ≤ 2 * (4 / |r| * (3 * c4 * (hnorm 2 S * hnorm 1 F * hnorm 1 G))) := by gcongr
    _ ≤ 2 * (4 / |r| * (24 * (hnorm 2 S * hnorm 1 F * hnorm 1 G))) := by gcongr
    _ ≤ 2 ^ 8 * (hnorm 2 S * hnorm 1 F * hnorm 1 G) / |r| := by
        rw [le_div_iff₀ hr']
        have e' : 2 * (4 / |r| * (24 * (hnorm 2 S * hnorm 1 F * hnorm 1 G))) * |r| =
            192 * (hnorm 2 S * hnorm 1 F * hnorm 1 G) := by
          field_simp
          ring
        rw [e']
        nlinarith
    _ = 2 ^ 8 * hnorm 2 S * hnorm 1 F * hnorm 1 G / |r| := by ring

/-- **The genuine `H¹`-direction form of `X₁`** (Body 12 §6 eq. (14); `X1op_slow_le` of
`Bounds.lean`, verbatim): `|⟨AF, X₁[h]F⟩| ≤ 2⁹ ‖h‖₁ ‖F‖₁‖F‖₂/q` for a real slow `h ∈ H¹` and a
fast `F ∈ H²`.  The proof gives the better constant `12 c₄ ≤ 96`. -/
theorem X1op_slow_le_proved {r : ℝ} (hr : r ≠ 0) (τ : ℝ) {h F : Field} (hh : MZ 1 h)
    (hhr : IsReal h)
    (hh' : PiS h = h)
    (hF : MZ 2 F) (hF' : PiF F = F) :
    |pair 1 F (X1op r τ h F)| ≤ 2 ^ 9 * hnorm 1 h * hnorm 1 F * hnorm 2 F / |r| := by
  have _ := hh'
  have _ := hF'
  have hr' : 0 < |r| := abs_pos.2 hr
  have hF1 : MZ 1 F := ⟨hF.inH.mono (by norm_num), hF.mean⟩
  obtain ⟨hk, hle⟩ := kern_sum_one hh hF hF
  have hb := abs_pair_add_pair_le hr τ hh hhr hF hF1 hk
  have hW0 : 0 ≤ hnorm 1 h * hnorm 1 F * hnorm 2 F :=
    mul_nonneg (mul_nonneg (hnorm_nonneg _ _) (hnorm_nonneg _ _)) (hnorm_nonneg _ _)
  have e : pair 1 F (X1op r τ h F) + pair 1 F (X1op r τ h F) = 2 * pair 1 F (X1op r τ h F) := by
    ring
  have hc : 3 * c4 ≤ 24 := by linarith [c4_le_eight]
  rw [e, abs_mul, abs_two] at hb
  have hle' : ∑' x, kernT h F F x ≤ 24 * (2 * (hnorm 1 h * hnorm 1 F * hnorm 2 F)) := by
    refine hle.trans ?_
    have e' : hnorm 1 h * (hnorm 2 F * hnorm 1 F + hnorm 1 F * hnorm 2 F) =
        2 * (hnorm 1 h * hnorm 1 F * hnorm 2 F) := by
      ring
    rw [e']
    gcongr
  have hb' : 2 * |pair 1 F (X1op r τ h F)| ≤
      4 / |r| * (24 * (2 * (hnorm 1 h * hnorm 1 F * hnorm 2 F))) :=
    hb.trans (by gcongr)
  have e' : 4 / |r| * (24 * (2 * (hnorm 1 h * hnorm 1 F * hnorm 2 F))) =
      2 * (96 * (hnorm 1 h * hnorm 1 F * hnorm 2 F) / |r|) := by
    ring
  have h96 : 96 * (hnorm 1 h * hnorm 1 F * hnorm 2 F) / |r| ≤
      2 ^ 9 * hnorm 1 h * hnorm 1 F * hnorm 2 F / |r| := by
    rw [show 2 ^ 9 * hnorm 1 h * hnorm 1 F * hnorm 2 F =
      2 ^ 9 * (hnorm 1 h * hnorm 1 F * hnorm 2 F) by ring]
    gcongr
    norm_num
  rw [e'] at hb'
  linarith

end OVNS
