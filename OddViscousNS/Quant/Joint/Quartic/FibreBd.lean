import OddViscousNS.Quant.Joint.Quartic.Fibre

/-!
# The fibre norm of a field (step J5, node N11)

Bodies 20, 34, 35, 46.  For a fast `V`, with `j(a) = (a, 1)`, so that `|j(a)| ≤ |(a, n)|` for
`n ≠ 0`:
* `lhB_two`: `L_h(V) ≤ √17 ‖V‖₂` ("horizontal Cauchy and the two-dimensional inverse-fourth sum");
* `lhB_eps`: `L_h(|l|^{−ε} V) ≤ √(9 + 4/ε) ‖V‖₁` (Body 35, with Body 43's constant `ε^{−1/2}`);
* `lhB_log`: `L_h(V) ≤ √(9 + 8 ln D) ‖V‖₁ + (5/D) ‖V‖₂`, every `D ≥ 1` (Body 20, `L(a, b)`).

For a slow `S`:
* `l1B_gr_log`: `W₁(S) = ∑|s||Ŝ_s| ≤ √(9 + 8 ln D) ‖S‖₂ + (5/D) ‖S‖₃` (Body 46).
-/

noncomputable section

namespace OVNS.Quant.Quartic

open OVNS.Quant.Metric

variable {α β γ : Mode → ℝ} {A L Z : ℝ}

/-! ### A. The horizontal sums -/

lemma absSq_md_zero (a : ℤ × ℤ) : absSq (md a 0) = (a.1 : ℝ) ^ 2 + (a.2 : ℝ) ^ 2 := by
  simp [absSq, Fin.sum_univ_three, md]

lemma absSq_md (a : ℤ × ℤ) (n : ℤ) :
    absSq (md a n) = (a.1 : ℝ) ^ 2 + (a.2 : ℝ) ^ 2 + (n : ℝ) ^ 2 := by
  simp [absSq, Fin.sum_univ_three, md]

/-- The reference point of the fibre over `a`. -/
def jm (a : ℤ × ℤ) : Mode := md a 1

/-- `|j(a)| ≤ |(a, n)|` on a fast fibre. -/
lemma absk_jm_le {a : ℤ × ℤ} {n : ℤ} (hn : n ≠ 0) : absk (jm a) ≤ absk (md a n) := by
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ n ^ 2 := by
      have := sq_nonneg n
      have h : n ^ 2 ≠ 0 := pow_ne_zero 2 hn
      omega
    exact_mod_cast this
  have h2 : absk (jm a) ^ 2 ≤ absk (md a n) ^ 2 := by
    rw [absk_sq, absk_sq, jm, absSq_md, absSq_md]
    push_cast
    linarith
  exact (pow_le_pow_iff_left₀ (absk_nonneg _) (absk_nonneg _) two_ne_zero).1 h2

lemma absk_jm_pos (a : ℤ × ℤ) : 1 ≤ absk (jm a) := by
  have h : jm a ≠ 0 := fun h0 => by
    have := congrFun h0 2
    simp [jm] at this
  exact one_le_absk h

/-- The sum over a horizontal plane, in horizontal labels. -/
lemma Fib.hor {w : Mode → ℝ} (h : Fib w Z) (h0 : ∀ k, 0 ≤ w k) :
    SB (fun a : ℤ × ℤ => w (jm a)) Z := by
  have h1 := h (md 0 1)
  have hi : Function.Injective fun a : ℤ × ℤ => md (-a) 0 := fun a b hab => by
    have := (md_inj hab).1
    exact neg_injective this
  refine (SB.comp_inj h1 (fun b => ?_) hi).of_le (fun a => h0 _) fun a => ?_
  · split_ifs
    · exact h0 _
    · exact le_rfl
  · have e : md 0 1 - md (-a) 0 = jm a := by
      rw [md_sub]
      simp [jm]
    simp only [md_two, ite_true, e]
    exact le_rfl

/-! ### B. Two weights -/

/-- The two-weight form of `LhB.of_weight`: each fibre is paid by one of two weights. -/
theorem LhB.of_weight₂ {ρ₁ ρ₂ : ℤ × ℤ → ℝ} {γ₁ γ₂ : Mode → ℝ} {Z₁ Z₂ A₁ A₂ : ℝ}
    (hβ0 : ∀ k, 0 ≤ β k) (h1 : ∀ a, 0 ≤ ρ₁ a) (h2 : ∀ a, 0 ≤ ρ₂ a)
    (hρ₁ : SB (fun a => ρ₁ a ^ 2) Z₁) (hρ₂ : SB (fun a => ρ₂ a ^ 2) Z₂)
    (hγ₁ : L2B γ₁ A₁) (hγ₂ : L2B γ₂ A₂)
    (hle : ∀ a, (∀ n, β (md a n) ≤ ρ₁ a * γ₁ (md a n)) ∧ ρ₂ a = 0 ∨
      (∀ n, β (md a n) ≤ ρ₂ a * γ₂ (md a n)) ∧ ρ₁ a = 0) :
    LhB β (Real.sqrt Z₁ * A₁ + Real.sqrt Z₂ * A₂) := by
  obtain ⟨hf₁, hS₁⟩ := l2b_fib_sq hγ₁
  obtain ⟨hf₂, hS₂⟩ := l2b_fib_sq hγ₂
  have hZ₁ : 0 ≤ Z₁ := (tsum_nonneg fun a => sq_nonneg _).trans hρ₁.2
  have hZ₂ : 0 ≤ Z₂ := (tsum_nonneg fun a => sq_nonneg _).trans hρ₂.2
  have hP₁ : SB (fun a => ρ₁ a ^ 2) (Real.sqrt Z₁ ^ 2) := by rwa [Real.sq_sqrt hZ₁]
  have hP₂ : SB (fun a => ρ₂ a ^ 2) (Real.sqrt Z₂ ^ 2) := by rwa [Real.sq_sqrt hZ₂]
  have hc₁ := SB.cs h1 (fibN_nonneg γ₁) (Real.sqrt_nonneg _) hγ₁.bd_nonneg hP₁ hS₁
  have hc₂ := SB.cs h2 (fibN_nonneg γ₂) (Real.sqrt_nonneg _) hγ₂.bd_nonneg hP₂ hS₂
  have hpt : ∀ a, (Summable fun n : ℤ => β (md a n) ^ 2) ∧
      fibN β a ≤ ρ₁ a * fibN γ₁ a + ρ₂ a * fibN γ₂ a := fun a => by
    rcases hle a with ⟨h, h0⟩ | ⟨h, h0⟩
    · obtain ⟨s, b⟩ := fibN_le (β := β) (fun n => hβ0 _) (h1 a) (hf₁ a) h
      refine ⟨s, ?_⟩
      rw [h0, zero_mul, add_zero]
      exact b
    · obtain ⟨s, b⟩ := fibN_le (β := β) (fun n => hβ0 _) (h2 a) (hf₂ a) h
      refine ⟨s, ?_⟩
      rw [h0, zero_mul, zero_add]
      exact b
  exact ⟨hβ0, fun a => (hpt a).1, (hc₁.add hc₂).of_le (fibN_nonneg β) fun a => (hpt a).2⟩

/-- A smaller sequence has a smaller fibre norm. -/
lemma LhB.of_le (h : LhB β L) (h0 : ∀ k, 0 ≤ γ k) (hle : ∀ k, γ k ≤ β k) : LhB γ L := by
  have hpt : ∀ a, _ := fun a => fibN_le (β := γ) (γ := β) (a := a) (c := 1) (fun n => h0 _)
    zero_le_one (h.fib a) (fun n => by rw [one_mul]; exact hle _)
  refine ⟨h0, fun a => (hpt a).1, h.sum.of_le (fibN_nonneg γ) fun a => ?_⟩
  simpa using (hpt a).2

lemma fibN_add_le {β₁ β₂ : Mode → ℝ} (h1 : ∀ k, 0 ≤ β₁ k) (h2 : ∀ k, 0 ≤ β₂ k) {a : ℤ × ℤ}
    (s1 : Summable fun n : ℤ => β₁ (md a n) ^ 2) (s2 : Summable fun n : ℤ => β₂ (md a n) ^ 2) :
    (Summable fun n : ℤ => (β₁ (md a n) + β₂ (md a n)) ^ 2) ∧
      fibN (fun k => β₁ k + β₂ k) a ≤ fibN β₁ a + fibN β₂ a := by
  have h := Real.Lp_add_le_tsum_of_nonneg (p := 2) one_le_two
    (f := fun n : ℤ => β₁ (md a n)) (g := fun n : ℤ => β₂ (md a n))
    (fun n => h1 _) (fun n => h2 _) (by simpa only [Real.rpow_two] using s1)
    (by simpa only [Real.rpow_two] using s2)
  simpa only [Real.rpow_two, Real.sqrt_eq_rpow, fibN] using h

/-- The triangle inequality of `L_h`. -/
theorem LhB.add {β₁ β₂ : Mode → ℝ} {L₁ L₂ : ℝ} (h1 : LhB β₁ L₁) (h2 : LhB β₂ L₂) :
    LhB (fun k => β₁ k + β₂ k) (L₁ + L₂) := by
  have hpt : ∀ a, _ := fun a => fibN_add_le (a := a) h1.nn h2.nn (h1.fib a) (h2.fib a)
  exact ⟨fun k => add_nonneg (h1.nn k) (h2.nn k), fun a => (hpt a).1,
    (h1.sum.add h2.sum).of_le (fibN_nonneg _) fun a => (hpt a).2⟩

lemma LhB.const_mul (h : LhB β L) {c : ℝ} (hc : 0 ≤ c) : LhB (fun k => c * β k) (c * L) := by
  have hpt : ∀ a, _ := fun a => fibN_le (β := fun k => c * β k) (γ := β) (a := a) (c := c)
    (fun n => mul_nonneg hc (h.nn _)) hc (h.fib a) (fun n => le_rfl)
  exact ⟨fun k => mul_nonneg hc (h.nn k), fun a => (hpt a).1,
    (h.sum.const_mul hc).of_le (fibN_nonneg _) fun a => (hpt a).2⟩

/-! ### C. A fast field -/

variable {V : Field}

lemma fast_md_zero (hV : PiF V = V) (a : ℤ × ℤ) : V (md a 0) = 0 :=
  fast_zero hV (md_two a 0)

/-- **`L_h(V) ≤ √17 ‖V‖₂`**, for fast `V`. -/
theorem lhB_two (hV : InH 2 V) (hF : PiF V = V) : LhB (nrm V) (Real.sqrt 17 * hnorm 2 V) := by
  have hw := Fib.hor fib_w4 (fun k => pow_nonneg (inv_nonneg.2 (absk_nonneg k)) 4)
  have hρ : SB (fun a : ℤ × ℤ => ((absk (jm a))⁻¹ ^ 2) ^ 2) 17 := by
    refine hw.of_le (fun a => sq_nonneg _) fun a => le_of_eq ?_
    simp only [w4]
    ring
  refine LhB.of_weight (fun k => norm_nonneg _) (fun a => by positivity) hρ (l2B_up hV)
    fun a n => ?_
  by_cases hn : n = 0
  · subst hn
    have h0 := fast_md_zero hF a
    have h2 : 0 ≤ up (nrm V) (md a 0) := mul_nonneg (absSq_nonneg _) (norm_nonneg _)
    have e : nrm V (md a 0) = 0 := by simp [nrm, h0]
    rw [e]
    exact mul_nonneg (by positivity) h2
  · have h1 := absk_jm_le (a := a) hn
    have h2 := absk_jm_pos a
    have h3 : (1 : ℝ) ≤ (absk (jm a))⁻¹ ^ 2 * absSq (md a n) := by
      rw [← absk_sq, inv_pow, inv_mul_eq_div, one_le_div (by positivity)]
      exact pow_le_pow_left₀ (by linarith) h1 2
    simp only [nrm, up]
    have h4 := norm_nonneg (V (md a n))
    nlinarith only [mul_le_mul_of_nonneg_right h3 h4]

/-- **The weighted fibre** (Body 35; Body 43 for the constant): `L_h(|l|^{−ε} V) ≤ √(9 + 4/ε) ‖V‖₁`. -/
theorem lhB_eps {ε : ℝ} (hε : 0 < ε) (hV : InH 1 V) (hF : PiF V = V) :
    LhB (fun k => (absk k)⁻¹ ^ ε * ‖V k‖) (Real.sqrt (9 + 4 / ε) * hnorm 1 V) := by
  have hw := Fib.hor (fib_eps hε) (wr_nonneg _)
  have hρ : SB (fun a : ℤ × ℤ => ((absk (jm a))⁻¹ ^ (1 + ε)) ^ 2) (9 + 4 / ε) := by
    refine hw.of_le (fun a => sq_nonneg _) fun a => le_of_eq ?_
    simp only [wr]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.2 (absk_nonneg _))]
    congr 1
    push_cast
    ring
  have hnn : ∀ k : Mode, 0 ≤ (absk k)⁻¹ ^ ε * ‖V k‖ := fun k =>
    mul_nonneg (Real.rpow_nonneg (inv_nonneg.2 (absk_nonneg k)) _) (norm_nonneg _)
  refine LhB.of_weight hnn (fun a => Real.rpow_nonneg (inv_nonneg.2 (absk_nonneg _)) _) hρ
    (l2B_gr hV) fun a n => ?_
  by_cases hn : n = 0
  · subst hn
    have h0 := fast_md_zero hF a
    simp only [h0, norm_zero, mul_zero]
    exact mul_nonneg (Real.rpow_nonneg (inv_nonneg.2 (absk_nonneg _)) _)
      (mul_nonneg (absk_nonneg _) (norm_nonneg _))
  · have h1 := absk_jm_le (a := a) hn
    have h2 := absk_jm_pos a
    have hk : 0 < absk (md a n) := by linarith
    have hj : 0 < absk (jm a) := by linarith
    have h3 : (absk (md a n))⁻¹ ^ ε ≤ (absk (jm a))⁻¹ ^ (1 + ε) * absk (md a n) := by
      have h4 : (absk (md a n))⁻¹ ^ (1 + ε) ≤ (absk (jm a))⁻¹ ^ (1 + ε) :=
        Real.rpow_le_rpow (inv_nonneg.2 hk.le) (inv_anti₀ hj h1) (by linarith)
      have h5 : (absk (md a n))⁻¹ ^ ε = (absk (md a n))⁻¹ ^ (1 + ε) * absk (md a n) := by
        rw [Real.rpow_add (inv_pos.2 hk), Real.rpow_one]
        field_simp
      rw [h5]
      exact mul_le_mul_of_nonneg_right h4 hk.le
    simp only [gr]
    have h4 := norm_nonneg (V (md a n))
    calc _ ≤ (absk (jm a))⁻¹ ^ (1 + ε) * absk (md a n) * ‖V (md a n)‖ :=
          mul_le_mul_of_nonneg_right h3 h4
      _ = _ := by ring

/-! ### D. The logarithmic bound and the first weight of a slow field -/

/-- `∑_{D < |j|} |j|⁻⁴ ≤ (5/D)²`. -/
lemma sb_tail {D : ℝ} (hD : 1 ≤ D) :
    SB (fun a : ℤ × ℤ => (if D < absk (jm a) then (absk (jm a))⁻¹ ^ 2 else 0) ^ 2) ((5 / D) ^ 2) := by
  have hD0 : 0 < D := by linarith
  obtain ⟨hs, hle⟩ := slow_lattice_sum_le (sq_nonneg D)
  have h1 : SB (fun k => 4 * slowResW (D ^ 2) k ^ 2) (4 * (25 / (4 * D ^ 2 + 1))) :=
    SB.const_mul ⟨hs, hle⟩ (by norm_num)
  have h2 := SB.comp_inj h1 (fun k => by positivity) md0_inj
  refine (h2.mono_bd ?_).of_le (fun a => sq_nonneg _) fun a => ?_
  · have hp : 0 < D ^ 2 := by positivity
    have h3 : 25 / (4 * D ^ 2 + 1) ≤ 25 / (4 * D ^ 2) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
    calc 4 * (25 / (4 * D ^ 2 + 1)) ≤ 4 * (25 / (4 * D ^ 2)) := by linarith
      _ = (5 / D) ^ 2 := by
          field_simp
          ring
  · split_ifs with h
    · have hj := absk_jm_pos a
      have hne : md a 0 ≠ 0 := fun h0 => by
        have e1 : a = (0, 0) := by
          have h01 := congrFun h0 0
          have h11 := congrFun h0 1
          simp only [md_zero, md_one, Pi.zero_apply] at h01 h11
          exact Prod.ext h01 h11
        have e2 : absk (jm a) ≤ 1 := by
          subst e1
          have : absSq (jm (0, 0)) = 1 := by
            simp [jm, absSq_md]
          have h3 : absk (jm (0, 0)) ^ 2 = 1 := by rw [absk_sq, this]
          nlinarith only [h3, absk_nonneg (jm (0, 0))]
        linarith
      have e : slowResW (D ^ 2) (md a 0) = (D ^ 2 + absSq (md a 0))⁻¹ :=
        slowResW_of_slow (md_two a 0) hne
      rw [e]
      have hA := absSq_nonneg (md a 0)
      set J := absk (jm a)
      have hJ0 : 0 < J := by linarith
      have hJ2 : absSq (md a 0) + 1 = J ^ 2 := by
        simp only [J, jm]
        rw [absk_sq, absSq_md, absSq_md]
        push_cast
        ring
      have hDJ : D ^ 2 ≤ J ^ 2 := pow_le_pow_left₀ hD0.le h.le 2
      have hle2 : D ^ 2 + absSq (md a 0) ≤ 2 * J ^ 2 := by linarith
      have hpos : 0 < D ^ 2 + absSq (md a 0) := by positivity
      have h4 : (J⁻¹ ^ 2) ^ 2 = 1 / (J ^ 2) ^ 2 := by
        field_simp
      have h5 : 4 * ((D ^ 2 + absSq (md a 0))⁻¹) ^ 2 = 4 / (D ^ 2 + absSq (md a 0)) ^ 2 := by
        field_simp
      rw [h4, h5, div_le_div_iff₀ (by positivity) (by positivity)]
      have h6 := pow_le_pow_left₀ hpos.le hle2 2
      nlinarith only [h6]
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      positivity

/-- **The logarithmic fibre bound** (Body 20, `L(a, b)`): for fast `V ∈ H²`, every `D ≥ 1`. -/
theorem lhB_log {D : ℝ} (hD : 1 ≤ D) (hV : InH 2 V) (hF : PiF V = V) :
    LhB (nrm V) (Real.sqrt (9 + 8 * Real.log D) * hnorm 1 V + 5 / D * hnorm 2 V) := by
  have hD0 : 0 < D := by linarith
  have hV1 : InH 1 V := hV.mono (by norm_num)
  have hb := Fib.hor (fib_band hD) (fun k => sq_nonneg _)
  have ht := sb_tail hD
  have hR : Real.sqrt ((5 / D) ^ 2) = 5 / D := Real.sqrt_sq (by positivity)
  have h := LhB.of_weight₂ (β := nrm V) (ρ₁ := fun a => bandW D (jm a))
    (ρ₂ := fun a => if D < absk (jm a) then (absk (jm a))⁻¹ ^ 2 else 0) (γ₁ := gr V)
    (γ₂ := up (nrm V)) (fun k => norm_nonneg _) (fun a => bandW_nonneg D _)
    (fun a => by split_ifs <;> positivity) hb ht (l2B_gr hV1) (l2B_up hV) fun a => ?_
  · rwa [hR] at h
  · by_cases ha : D < absk (jm a)
    · right
      have e0 : bandW D (jm a) = 0 := by
        simp only [bandW, not_le.2 ha, ite_false]
      refine ⟨fun n => ?_, e0⟩
      rw [ite_eq_left ha]
      by_cases hn : n = 0
      · subst hn
        have e : nrm V (md a 0) = 0 := by simp [nrm, fast_md_zero hF a]
        rw [e]
        exact mul_nonneg (by positivity) (mul_nonneg (absSq_nonneg _) (norm_nonneg _))
      · have h1 := absk_jm_le (a := a) hn
        have h2 := absk_jm_pos a
        have h3 : (1 : ℝ) ≤ (absk (jm a))⁻¹ ^ 2 * absSq (md a n) := by
          rw [← absk_sq, inv_pow, inv_mul_eq_div, one_le_div (by positivity)]
          exact pow_le_pow_left₀ (by linarith) h1 2
        have h4 := norm_nonneg (V (md a n))
        simp only [nrm, up]
        nlinarith only [mul_le_mul_of_nonneg_right h3 h4]
    · left
      have hle : absk (jm a) ≤ D := not_lt.1 ha
      refine ⟨fun n => ?_, ite_eq_right ha⟩
      by_cases hn : n = 0
      · subst hn
        have e : nrm V (md a 0) = 0 := by simp [nrm, fast_md_zero hF a]
        rw [e]
        exact mul_nonneg (bandW_nonneg D _) (mul_nonneg (absk_nonneg _) (norm_nonneg _))
      · have h1 := absk_jm_le (a := a) hn
        have h2 := absk_jm_pos a
        have e : bandW D (jm a) = (absk (jm a))⁻¹ := by simp only [bandW, hle, ite_true]
        rw [e]
        have h3 : (1 : ℝ) ≤ (absk (jm a))⁻¹ * absk (md a n) := by
          rw [inv_mul_eq_div, one_le_div (by linarith)]
          exact h1
        have h4 := norm_nonneg (V (md a n))
        simp only [nrm, gr]
        nlinarith only [mul_le_mul_of_nonneg_right h3 h4]

/-- **The first weight of a slow field** (Body 46): `W₁(S) ≤ √(9 + 8 ln D) ‖S‖₂ + (5/D) ‖S‖₃`.  The
two lattice sums are `∑_{|s| ≤ D} |s|⁻² ≤ 9 + 8 ln D` and `∑_{|s| > D} |s|⁻⁴ ≤ (5/D)²`. -/
theorem l1B_gr_log {D : ℝ} (hD : 1 ≤ D) {S : Field} (hS : MZ 3 S) (hS' : PiS S = S) :
    L1B (gr S) (Real.sqrt (9 + 8 * Real.log D) * hnorm 2 S + 5 / D * hnorm 3 S) := by
  have hD0 : 0 < D := by linarith
  have hS2 : MZ 2 S := hS.mono' (by norm_num)
  have hZ0 : 0 ≤ 9 + 8 * Real.log D := by
    have := Real.log_nonneg hD
    linarith
  set ρ₁ : Mode → ℝ := fun k => if k 2 = 0 then bandW D k else 0 with hρ₁
  set ρ₂ : Mode → ℝ := fun k => if k 2 = 0 ∧ D < absk k then (absk k)⁻¹ ^ 2 else 0 with hρ₂
  have h1 : ∀ k, 0 ≤ ρ₁ k := fun k => by
    simp only [hρ₁]
    split_ifs
    · exact bandW_nonneg D k
    · exact le_rfl
  have h2 : ∀ k, 0 ≤ ρ₂ k := fun k => by
    simp only [hρ₂]
    split_ifs
    · positivity
    · exact le_rfl
  have hs1 : SB (fun k => ρ₁ k ^ 2) (Real.sqrt (9 + 8 * Real.log D) ^ 2) := by
    rw [Real.sq_sqrt hZ0]
    refine (fib_band hD 0).of_le (fun k => sq_nonneg _) fun k => ?_
    simp only [hρ₁]
    by_cases hk : k 2 = 0
    · have e : bandW D (0 - k) = bandW D k := by
        rw [zero_sub]
        simp only [bandW, absk_neg]
      simp only [hk, ite_true, e]
      exact le_rfl
    · simp [hk]
  have hs2 : SB (fun k => ρ₂ k ^ 2) ((5 / D) ^ 2) := by
    obtain ⟨hs, hle⟩ := slow_lattice_sum_le (sq_nonneg D)
    have h3 : SB (fun k => 4 * slowResW (D ^ 2) k ^ 2) (4 * (25 / (4 * D ^ 2 + 1))) :=
      SB.const_mul ⟨hs, hle⟩ (by norm_num)
    refine (h3.mono_bd ?_).of_le (fun k => sq_nonneg _) fun k => ?_
    · have hp : 0 < D ^ 2 := by positivity
      have h4 : 25 / (4 * D ^ 2 + 1) ≤ 25 / (4 * D ^ 2) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
      calc 4 * (25 / (4 * D ^ 2 + 1)) ≤ 4 * (25 / (4 * D ^ 2)) := by linarith
        _ = (5 / D) ^ 2 := by
            field_simp
            ring
    · simp only [hρ₂]
      split_ifs with h
      · obtain ⟨hk, hlt⟩ := h
        have hne : k ≠ 0 := fun h0 => by
          rw [h0, show absk 0 = 0 from absk_eq_zero.2 rfl] at hlt
          linarith
        rw [slowResW_of_slow hk hne]
        have hA := one_le_absSq hne
        set J := absk k
        have hJ0 : 0 < J := by linarith
        have hJ2 : absSq k = J ^ 2 := (absk_sq k).symm
        have hDJ : D ^ 2 ≤ J ^ 2 := pow_le_pow_left₀ hD0.le hlt.le 2
        have hpos : 0 < D ^ 2 + absSq k := by positivity
        have hle2 : D ^ 2 + absSq k ≤ 2 * J ^ 2 := by linarith
        have e1 : (J⁻¹ ^ 2) ^ 2 = 1 / (J ^ 2) ^ 2 := by
          field_simp
        have e2 : 4 * ((D ^ 2 + absSq k)⁻¹) ^ 2 = 4 / (D ^ 2 + absSq k) ^ 2 := by
          field_simp
        rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
        have h6 := pow_le_pow_left₀ hpos.le hle2 2
        nlinarith only [h6]
      · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        positivity
  have hU := l2B_up hS2.inH
  have hU3 := l2B_up_gr hS
  have c1 := SB.cs h1 hU.nn (Real.sqrt_nonneg _) hU.bd_nonneg hs1 (L2B.sq hU)
  have c2 := SB.cs h2 hU3.nn (by positivity) hU3.bd_nonneg hs2 (L2B.sq hU3)
  have hpt : ∀ k, gr S k ≤ ρ₁ k * up (nrm S) k + ρ₂ k * up (gr S) k := fun k => by
    by_cases hk : k 2 = 0
    · by_cases h0 : k = 0
      · subst h0
        have e : gr S 0 = 0 := by simp [gr, hS.mean]
        rw [e]
        exact add_nonneg (mul_nonneg (h1 _) (hU.nn _)) (mul_nonneg (h2 _) (hU3.nn _))
      have hA := one_le_absk h0
      have hJ0 : 0 < absk k := by linarith
      by_cases hlt : D < absk k
      · have e1 : ρ₂ k * up (gr S) k = gr S k := by
          simp only [hρ₂, hk, hlt, and_self, ite_true, up, gr, ← absk_sq]
          field_simp
        have := mul_nonneg (h1 k) (hU.nn k)
        linarith
      · have e1 : ρ₁ k * up (nrm S) k = gr S k := by
          simp only [hρ₁, hk, ite_true, bandW, not_lt.1 hlt, up, nrm, gr, ← absk_sq]
          field_simp
        have := mul_nonneg (h2 k) (hU3.nn k)
        linarith
    · have e : gr S k = 0 := by
        have : S k = 0 := slow_zero hS' hk
        simp [gr, this]
      rw [e]
      exact add_nonneg (mul_nonneg (h1 _) (hU.nn _)) (mul_nonneg (h2 _) (hU3.nn _))
  have hsum := (c1.add c2).of_le (gr_nonneg S) hpt
  exact ⟨gr_nonneg S, hsum.1, hsum.2⟩

end OVNS.Quant.Quartic

end
