import OddViscousNS.Quant.Joint.Quartic.Hi

/-!
# The source of the quartic is the near differential (step J5, node N11)

J3-v2 §3: "Insert the high mixed product in each of its three differentiated slots".

* `src_eq_nearD`: `Re J4F j (S, F, F, F) = D_j^N(F; Q_hi(S, F))`, the near differential of
  `Native/Defs.lean`, for real fields.  Each triad term of `nearD` splits over the slow label `s`;
  the phase of the source edge moves `Φ` to the total phase `Ψ` (`hel_edge`): "the intermediate phase
  canceled and the slow dispersion zero".
* `nearD_add`, `nearD_neg`: the near differential is additive in its direction.
-/

open scoped ENNReal ComplexConjugate

open private nearTriadTerm_degen from OddViscousNS.Quant.Energy.Native.TriadBound

noncomputable section

namespace OVNS.Quant.Quartic

open OVNS.Quant.Metric

variable {S F : Field} {τ r : ℝ} {j : ℕ}

/-! ### A. The phase of the edge -/

lemma hiM_cov (τ : ℝ) : Cov τ (hiM 0) (hiM τ) := fun a b c p q => by
  simp only [hiM, phaseM]
  simp only [zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  ring

/-- **The source edge at time `τ`**, on a channel: the phase of the output and of the input. -/
lemma hel_edge {s p l : Mode} (hs : s 2 = 0) (hk : s + l = p) (τ : ℝ) (a : Sgn) (v w : V3) :
    hel a p (blk (hiM τ) s p l v w) = ∑ d : Sgn,
      Complex.exp (Complex.I * (τ * (lam d l - lam a p) : ℝ)) •
        hel a p (blk (hiM 0) s p l v (hel d l w)) := by
  rw [blk_cov (hiM_cov τ) hs hk v w, hel_rotL, rotL_apply, map_sum, hel_sum_distrib,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_smul, hel_smul, smul_smul, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The cyclic sum sees its first vector through its helicity. -/
lemma cyc3_hel {j : ℕ} {ε z : ℝ} {ℓ0 ℓ1 ℓ2 : Mode} {s0 s1 s2 : Sgn} (a v1 v2 : V3) :
    cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 (hel s0 ℓ0 a) v1 v2 = cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 a v1 v2 := by
  simp only [cyc3, hel_idem]

/-- The cyclic sum as an operator of its first vector. -/
def cycL (j : ℕ) (ε z : ℝ) (ℓ0 ℓ1 ℓ2 : Mode) (s0 s1 s2 : Sgn) (v1 v2 : V3) : V3 →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a => cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 a v1 v2
      map_add' := fun a a' => cyc3_add₀ a a' v1 v2
      map_smul' := fun c a => cyc3_smul₀ c a v1 v2 }

@[simp] lemma cycL_apply (j : ℕ) (ε z : ℝ) (ℓ0 ℓ1 ℓ2 : Mode) (s0 s1 s2 : Sgn) (a v1 v2 : V3) :
    cycL j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 v1 v2 a = cyc3 j ε z ℓ0 ℓ1 ℓ2 s0 s1 s2 a v1 v2 := rfl

/-- One channel of the source label. -/
lemma channel_eq {x : L4} (hs : x.2.2 2 = 0) (a b c : Sgn) (z : ℝ) (t w u v : V3) :
    phaseM τ a b c x.1 x.2.1 * cyc3 j (-1) z x.1 x.2.1 (outE x) a b c
        (blk (hiM τ) x.2.2 x.1 (inL x) t w) u v =
      ∑ d : Sgn, chQ τ d b c x * cyc3 j (-1) z x.1 x.2.1 (outE x) a b c (edgeQ x d t w) u v := by
  rw [← cyc3_hel, hel_edge hs (p_eq x) τ a t w, ← cycL_apply, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_smul, smul_eq_mul, cycL_apply, cyc3_hel, ← mul_assoc]
  congr 1
  rw [phaseM, chQ, ← Complex.exp_add, psi_eq d a b c x]
  congr 1
  push_cast
  ring

/-! ### B. A triad -/

lemma srcQ_swap (j : ℕ) (r : ℝ) (x : L4) (τ : ℝ) (t w u v : V3) :
    srcQ j r x τ t w u v = ∑ a : Sgn, ∑ b : Sgn, ∑ c : Sgn, ∑ d : Sgn,
      chQ τ d b c x * coreQ j r x d a b c t w u v := by
  unfold srcQ
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]

open scoped Classical in
/-- **A nondegenerate triad of the near differential is the sum over `s` of the source labels.** -/
theorem triad_hasSum (hS2 : Summable fun k => ‖S k‖ ^ 2) (hF2 : Summable fun k => ‖F k‖ ^ 2)
    (hS' : PiS S = S) (p q : Mode) (hp : p ≠ 0) (hq : q ≠ 0) (hk : p + q ≠ 0) :
    HasSum (fun s => srcQ j r (p, q, s) τ (S s) (F (p - s)) (F q) (F (-(p + q))))
      (nearTriadTerm j (-1) r τ F (Qhi τ S F) (p, q)) := by
  have hb := (blk_norm_summable (hiM_bdd τ) hS2 hF2 p).of_norm
  have hG : HasSum (fun s => blk (hiM τ) s p (p - s) (S s) (F (p - s))) (Qhi τ S F p) := by
    have e := Qm_eq_tsum_blk (hiM τ) S F p
    rw [Qhi, e]
    exact hb.hasSum
  rw [nearTriadTerm_eq j (-1) r τ F (Qhi τ S F) hp hq hk]
  simp only [srcQ_swap]
  refine hasSum_sum fun a _ => hasSum_sum fun b _ => hasSum_sum fun c _ => ?_
  by_cases hN : NearT a b c p q
  · simp only [hN, ite_true]
    have h1 := (hG.mapL (cycL j (-1) (r * Phi a b c p q) p q (-(p + q)) a b c (F q)
      (F (-(p + q))))).mul_left (phaseM τ a b c p q)
    simp only [cycL_apply] at h1
    have e : (fun s => ∑ d : Sgn, chQ τ d b c (p, q, s) * coreQ j r (p, q, s) d a b c (S s)
        (F (p - s)) (F q) (F (-(p + q)))) = fun s => phaseM τ a b c p q *
        cyc3 j (-1) (r * Phi a b c p q) p q (-(p + q)) a b c
          (blk (hiM τ) s p (p - s) (S s) (F (p - s))) (F q) (F (-(p + q))) := by
      funext s
      by_cases hs : s 2 = 0
      · have h2 := channel_eq (j := j) (τ := τ) (x := (p, q, s)) hs a b c (r * Phi a b c p q)
          (S s) (F (p - s)) (F q) (F (-(p + q)))
        simp only [coreQ, hN, ite_true]
        exact h2.symm
      · have hS0 := slow_zero hS' hs
        simp only [coreQ, hN, ite_true, hS0, blk_zero_leaf, zero_apply, edgeQ_zero_l,
          cyc3_zero₀, mul_zero, Finset.sum_const_zero]
    rw [e]
    exact h1
  · simp only [hN, ite_false, coreQ, mul_zero, Finset.sum_const_zero]
    exact hasSum_zero

/-- **The source form is the sum of the triad terms.** -/
theorem J4F_eq_tsum (hS2 : Summable fun k => ‖S k‖ ^ 2) (hF2 : Summable fun k => ‖F k‖ ^ 2)
    (hS' : PiS S = S) (hF' : PiF F = F)
    (hs : Summable fun x : L4 => srcQ j r x τ (S x.2.2) (F (inL x)) (F x.2.1) (F (outE x))) :
    J4F j r τ S F F F = ∑' i : Mode × Mode, nearTriadTerm j (-1) r τ F (Qhi τ S F) i := by
  set f : L4 → ℂ := fun x => srcQ j r x τ (S x.2.2) (F (inL x)) (F x.2.1) (F (outE x)) with hf
  have hslots : Slots S F F F := ⟨hS', hF', hF', hF'⟩
  have e0 : J4F j r τ S F F F = ∑' z : (Mode × Mode) × Mode, f (l4Equiv.symm z) :=
    (l4Equiv.symm.tsum_eq f).symm
  have hz : Summable fun z : (Mode × Mode) × Mode => f (l4Equiv.symm z) :=
    l4Equiv.symm.summable_iff.2 hs
  rw [e0, hz.tsum_prod]
  refine tsum_congr fun i => ?_
  obtain ⟨p, q⟩ := i
  by_cases hd : p = 0 ∨ q = 0 ∨ p + q = 0
  · rw [nearTriadTerm_degen j (-1) r τ F (Qhi τ S F) hd]
    refine (tsum_congr fun s => ?_).trans tsum_zero
    refine hslots.src_zero fun hx => ?_
    rcases hd with h0 | h0 | h0
    · have h1 := hx.l
      have h2 := hx.s
      simp only [l4Equiv, Equiv.coe_fn_symm_mk, inL] at h1 h2
      simp [h0, h2] at h1
    · exact hx.ne_q h0
    · exact hx.ne_k h0
  · push Not at hd
    exact (triad_hasSum hS2 hF2 hS' p q hd.1 hd.2.1 hd.2.2).tsum_eq

/-- **The source is the near differential in the direction `Q_hi`** (J3-v2 §3). -/
theorem src_eq_nearD (hS : Adm 2 S) (hS' : PiS S = S) (hF : Adm 2 F) (hF' : PiF F = F)
    (hj : j = 1 ∨ j = 2) (hFm : MZ ((j : ℝ) + 1) F) (hG : MZ j (Qhi τ S F))
    (hs : Summable fun x : L4 => srcQ j r x τ (S x.2.2) (F (inL x)) (F x.2.1) (F (outE x))) :
    (J4F j r τ S F F F).re = nearD j (-1) r τ F (Qhi τ S F) := by
  have hS2 := summable_norm_sq_of_inH (hS.inH.mono (by norm_num : (0 : ℝ) ≤ 2))
  have hF2 := summable_norm_sq_of_inH (hF.inH.mono (by norm_num : (0 : ℝ) ≤ 2))
  have h1 := (nearD_eq_tsum_triad hj (Or.inr rfl) r τ hFm hF.real hG (isReal_Qhi τ hS hF)).2
  rw [PiF_Qhi hS' hF'] at h1
  rw [h1, J4F_eq_tsum hS2 hF2 hS' hF' hs]

/-! ### C. The near differential is additive -/

section Add

variable {ε : ℝ} {h₁ h₂ : Field}

lemma nearTriadTerm_add (j : ℕ) (ε r τ : ℝ) (F G₁ G₂ : Field) (x : Mode × Mode) :
    nearTriadTerm j ε r τ F (G₁ + G₂) x =
      nearTriadTerm j ε r τ F G₁ x + nearTriadTerm j ε r τ F G₂ x := by
  simp only [nearTriadTerm, nearTri, tripT, Pi.add_apply, hel_add, tau_add₁, tau_add₂, tau_add₃,
    mul_add, Finset.sum_add_distrib]
  ring

lemma nearTriadTerm_zero (j : ℕ) (ε r τ : ℝ) (F : Field) (x : Mode × Mode) :
    nearTriadTerm j ε r τ F 0 x = 0 := by
  simp only [nearTriadTerm, nearTri, tripT, Pi.zero_apply, hel_zero_right, tau_zero_left,
    tau_zero_mid, tau_zero_right, mul_zero, Finset.sum_const_zero, add_zero]

lemma nearTriadTerm_neg (j : ℕ) (ε r τ : ℝ) (F G : Field) (x : Mode × Mode) :
    nearTriadTerm j ε r τ F (-G) x = -nearTriadTerm j ε r τ F G x := by
  have h := nearTriadTerm_add j ε r τ F G (-G) x
  rw [add_neg_cancel, nearTriadTerm_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

lemma PiF_add'' (u v : Field) : PiF (u + v) = PiF u + PiF v := by
  funext k
  by_cases hk : k 2 = 0 <;> simp [PiF, hk]

lemma PiF_neg'' (u : Field) : PiF (-u) = -PiF u := by
  funext k
  by_cases hk : k 2 = 0 <;> simp [PiF, hk]

lemma IsReal.add'' {u v : Field} (hu : IsReal u) (hv : IsReal v) : IsReal (u + v) := fun k => by
  simp only [Pi.add_apply, hu k, hv k]
  ext i
  simp [conjV]

/-- **The near differential is additive in the direction.** -/
theorem nearD_add {j : ℕ} (hj : j = 1 ∨ j = 2) (hε : ε = 1 ∨ ε = -1) (r τ : ℝ)
    (hF : MZ ((j : ℝ) + 1) F) (hFr : IsReal F) (m1 : MZ j h₁) (m2 : MZ j h₂) (r1 : IsReal h₁)
    (r2 : IsReal h₂) :
    nearD j ε r τ F (h₁ + h₂) = nearD j ε r τ F h₁ + nearD j ε r τ F h₂ := by
  have hh : MZ j (h₁ + h₂) := ⟨m1.inH.add m2.inH, by simp [m1.mean, m2.mean]⟩
  obtain ⟨s1, e1⟩ := nearD_eq_tsum_triad hj hε r τ hF hFr m1 r1
  obtain ⟨s2, e2⟩ := nearD_eq_tsum_triad hj hε r τ hF hFr m2 r2
  obtain ⟨-, e3⟩ := nearD_eq_tsum_triad hj hε r τ hF hFr hh (IsReal.add'' r1 r2)
  have e : ∑' x, nearTriadTerm j ε r τ F (PiF (h₁ + h₂)) x =
      ∑' x, (nearTriadTerm j ε r τ F (PiF h₁) x + nearTriadTerm j ε r τ F (PiF h₂) x) := by
    rw [PiF_add'']
    exact tsum_congr fun x => nearTriadTerm_add j ε r τ F _ _ x
  rw [e3, e1, e2, e, s1.tsum_add s2, Complex.add_re]

/-- The near differential in the opposite direction. -/
theorem nearD_neg {j : ℕ} (hj : j = 1 ∨ j = 2) (hε : ε = 1 ∨ ε = -1) (r τ : ℝ)
    (hF : MZ ((j : ℝ) + 1) F) (hFr : IsReal F) (m1 : MZ j h₁) (r1 : IsReal h₁) :
    nearD j ε r τ F (-h₁) = -nearD j ε r τ F h₁ := by
  have hh : MZ j (-h₁) := ⟨m1.inH.neg, by simp [m1.mean]⟩
  obtain ⟨-, e1⟩ := nearD_eq_tsum_triad hj hε r τ hF hFr m1 r1
  obtain ⟨-, e3⟩ := nearD_eq_tsum_triad hj hε r τ hF hFr hh (IsReal.neg' r1)
  have e : ∑' x, nearTriadTerm j ε r τ F (PiF (-h₁)) x =
      ∑' x, -nearTriadTerm j ε r τ F (PiF h₁) x := by
    rw [PiF_neg'']
    exact tsum_congr fun x => nearTriadTerm_neg j ε r τ F _ x
  rw [e3, e1, e, tsum_neg, Complex.neg_re]

end Add

end OVNS.Quant.Quartic

end
