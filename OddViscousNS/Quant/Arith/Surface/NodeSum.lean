import OddViscousNS.Quant.Arith.Surface.NodeDet
import OddViscousNS.Quant.Arith.Surface.Mertens

/-!
# The sum over primes at a node (second half of route L10)

For the rows `J`, values `m j ≠ 0`, `|m j| ≤ Mb`, primes in `(P₀, x]` off `Bad`:
`primes_lower`:  `Σ_p n_p log p ≥ c₀ E^{3/2} (log x − log P₀ − C₄)`, as soon as
`n_p ≥ c₀ E_p^{3/2}/√(p²+18p) − 2E_p`, `x² ≤ E`, `log Mb ≤ P₀`.

Here `E − E_p` counts the rows with `p ∣ m`, and `Σ_p (E − E_p) log p / p ≤ E log Mb / P₀`.
-/

open Finset

namespace OVNS.Quant.Surf

/-- `c₀ = 2√2/3`. -/
noncomputable def c0 : ℝ := 2 * Real.sqrt 2 / 3

lemma c0_pos : 0 < c0 := by unfold c0; positivity

lemma rpow_three_halves {x : ℝ} (hx : 0 ≤ x) : x ^ ((3 : ℝ) / 2) = Real.sqrt x ^ 3 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- `(E − b)^{3/2} ≥ E^{3/2} − (3/2) b √E`. -/
lemma rpow_sub_ge {E b : ℝ} (hb : 0 ≤ b) (hbE : b ≤ E) :
    E ^ ((3 : ℝ) / 2) - 3 / 2 * b * Real.sqrt E ≤ (E - b) ^ ((3 : ℝ) / 2) := by
  have hE : 0 ≤ E := hb.trans hbE
  have hEb : 0 ≤ E - b := by linarith
  rw [rpow_three_halves hE, rpow_three_halves hEb]
  set u := Real.sqrt E with hu
  set v := Real.sqrt (E - b) with hv
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = E := Real.sq_sqrt hE
  have hv2 : v ^ 2 = E - b := Real.sq_sqrt hEb
  have hbe : b = u ^ 2 - v ^ 2 := by rw [hu2, hv2]; ring
  rw [hbe]
  nlinarith [mul_nonneg (sq_nonneg (u - v)) (by positivity : 0 ≤ u + 2 * v)]

/-- `1/√(p²+18p) ≥ (1/p)(1 − 9/p)`. -/
lemma inv_sqrt_ge {p : ℝ} (hp : 18 ≤ p) :
    1 / p - 9 / p ^ 2 ≤ 1 / Real.sqrt (p ^ 2 + 18 * p) := by
  have hp0 : 0 < p := by linarith
  have hpos : 0 < p ^ 2 + 18 * p := by positivity
  have hs : 0 < Real.sqrt (p ^ 2 + 18 * p) := Real.sqrt_pos.2 hpos
  have h1 : Real.sqrt (p ^ 2 + 18 * p) ≤ p ^ 2 / (p - 9) := by
    have hp9 : 0 < p - 9 := by linarith
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    rw [div_pow, le_div_iff₀ (by positivity)]
    nlinarith [mul_pos hp0 hp0, mul_nonneg hp0.le (sub_nonneg.2 hp), sq_nonneg p]
  have e : 1 / p - 9 / p ^ 2 = (p - 9) / p ^ 2 := by field_simp
  rw [e, div_le_div_iff₀ (by positivity) hs]
  have hp9 : 0 < p - 9 := by linarith
  have := (le_div_iff₀ hp9).1 h1
  linarith

/-- The contribution of one prime. -/
lemma term_lower {p E b n w : ℝ} (hp : 18 ≤ p) (hb : 0 ≤ b) (hbE : b ≤ E) (hw : 0 ≤ w)
    (hn : c0 * (E - b) ^ ((3 : ℝ) / 2) / Real.sqrt (p ^ 2 + 18 * p) - 2 * (E - b) ≤ n) :
    c0 * E ^ ((3 : ℝ) / 2) * (w / p - 9 * (w / p ^ 2)) - c0 * (3 / 2) * Real.sqrt E * (b * (w / p))
      - 2 * E * w ≤ n * w := by
  have hp0 : 0 < p := by linarith
  have hc := c0_pos
  set A := (E - b) ^ ((3 : ℝ) / 2) with hA
  have hA0 : 0 ≤ A := by
    have : 0 ≤ E - b := by linarith
    positivity
  have h1 := rpow_sub_ge hb hbE
  have h2 := inv_sqrt_ge hp
  set T := 1 / p - 9 / p ^ 2 with hT
  have hT0 : 0 ≤ T := by
    have e : T = (p - 9) / p ^ 2 := by rw [hT]; field_simp
    rw [e]
    have : 0 ≤ p - 9 := by linarith
    positivity
  have hT1 : T ≤ 1 / p := by
    have : 0 ≤ 9 / p ^ 2 := by positivity
    rw [hT]; linarith
  have hE0 : 0 ≤ E := hb.trans hbE
  have hsE : 0 ≤ Real.sqrt E := Real.sqrt_nonneg _
  have h3 : A * T ≤ A / Real.sqrt (p ^ 2 + 18 * p) := by
    have := mul_le_mul_of_nonneg_left h2 hA0
    rwa [mul_one_div] at this
  have h4 : (E ^ ((3 : ℝ) / 2) - 3 / 2 * b * Real.sqrt E) * T ≤ A * T :=
    mul_le_mul_of_nonneg_right h1 hT0
  have h5 : 3 / 2 * b * Real.sqrt E * T ≤ 3 / 2 * b * Real.sqrt E * (1 / p) :=
    mul_le_mul_of_nonneg_left hT1 (by positivity)
  have h6 : E ^ ((3 : ℝ) / 2) * T - 3 / 2 * b * Real.sqrt E * (1 / p) ≤
      A / Real.sqrt (p ^ 2 + 18 * p) := by
    nlinarith
  have h7 : c0 * (E ^ ((3 : ℝ) / 2) * T - 3 / 2 * b * Real.sqrt E * (1 / p)) - 2 * E ≤ n := by
    have := mul_le_mul_of_nonneg_left h6 hc.le
    have e : c0 * (A / Real.sqrt (p ^ 2 + 18 * p)) = c0 * A / Real.sqrt (p ^ 2 + 18 * p) := by ring
    rw [e] at this
    nlinarith
  have h8 := mul_le_mul_of_nonneg_right h7 hw
  refine le_trans (le_of_eq ?_) h8
  have e2 : w / p - 9 * (w / p ^ 2) = w * T := by rw [hT]; ring
  rw [e2]
  ring

/-- Primes in a set dividing `m ≠ 0`. -/
lemma sum_log_dvd_le (m : ℤ) (hm : m ≠ 0) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hd : ∀ p ∈ S, (p : ℤ) ∣ m) : ∑ p ∈ S, Real.log p ≤ Real.log |(m : ℝ)| := by
  have := sum_log_le_log_abs m hm S hS (fun _ => 1) (fun p hp => by simpa using hd p hp)
  simpa using this

lemma log_abs_le {m : ℤ} {Mb : ℝ} (hm : m ≠ 0) (h : |(m : ℝ)| ≤ Mb) :
    Real.log |(m : ℝ)| ≤ Real.log Mb :=
  Real.log_le_log (abs_pos.2 (by exact_mod_cast hm)) h

/-- `∑_{p∈S, p ∣ m} log p / p ≤ log|m| / P₀` for primes `p > P₀`. -/
lemma sum_div_dvd_le {m : ℤ} {Mb : ℝ} (hm : m ≠ 0) (hMb : |(m : ℝ)| ≤ Mb) (P₀ : ℕ) (hP₀ : 0 < P₀)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ P₀ < p) (hd : ∀ p ∈ S, (p : ℤ) ∣ m) :
    ∑ p ∈ S, Real.log p / p ≤ Real.log Mb / P₀ := by
  have hP : (0 : ℝ) < P₀ := by exact_mod_cast hP₀
  have h1 : ∑ p ∈ S, Real.log p / p ≤ ∑ p ∈ S, Real.log p / P₀ := by
    refine sum_le_sum fun p hp => ?_
    have h2 : (P₀ : ℝ) ≤ p := by exact_mod_cast (hS p hp).2.le
    exact div_le_div_of_nonneg_left (log_nonneg_prime (hS p hp).1) hP h2
  refine h1.trans ?_
  rw [← Finset.sum_div]
  refine div_le_div_of_nonneg_right ?_ hP.le
  exact (sum_log_dvd_le m hm S (fun p hp => (hS p hp).1) hd).trans (log_abs_le hm hMb)

/-- The bad rows, summed over primes. -/
lemma sum_bad_rows_le {J : Type*} [Fintype J] (m : J → ℤ) (hm : ∀ j, m j ≠ 0) {Mb : ℝ}
    (hMb : ∀ j, |(m j : ℝ)| ≤ Mb) (P₀ : ℕ) (hP₀ : 0 < P₀) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ P₀ < p) :
    ∑ p ∈ S, (((univ.filter fun j => (p : ℤ) ∣ m j).card : ℕ) : ℝ) * (Real.log p / p) ≤
      (Fintype.card J : ℝ) * (Real.log Mb / P₀) := by
  classical
  have e : ∀ p : ℕ, (((univ.filter fun j => (p : ℤ) ∣ m j).card : ℕ) : ℝ) * (Real.log p / p) =
      ∑ j, if (p : ℤ) ∣ m j then Real.log p / p else 0 := by
    intro p
    rw [card_filter]
    push_cast
    rw [Finset.sum_mul]
    refine sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun p _ => e p, Finset.sum_comm]
  have h1 : ∀ j, ∑ p ∈ S, (if (p : ℤ) ∣ m j then Real.log p / p else 0) ≤ Real.log Mb / P₀ := by
    intro j
    rw [← Finset.sum_filter]
    exact sum_div_dvd_le (hm j) (hMb j) P₀ hP₀ _ (fun p hp => hS p (mem_filter.1 hp).1)
      fun p hp => (mem_filter.1 hp).2
  calc _ ≤ ∑ _j : J, Real.log Mb / P₀ := sum_le_sum fun j _ => h1 j
    _ = _ := by simp [Finset.card_univ]

/-- The tail `∑ log p / p²`. -/
lemma sum_log_sq_le (S : Finset ℕ) (x : ℕ) (hS : ∀ p ∈ S, p ≤ x ∧ p.Prime) :
    ∑ p ∈ S, Real.log p / (p : ℝ) ^ 2 ≤ C0 := by
  have hsub : S ⊆ PL x := fun p hp => mem_PL.2 (hS p hp)
  have h1 : ∑ p ∈ S, Real.log p / (p : ℝ) ^ 2 ≤ ∑ p ∈ PL x, Real.log p / (p * (p - 1)) := by
    refine (sum_le_sum fun p hp => ?_).trans (sum_le_sum_of_subset_of_nonneg hsub ?_)
    · have hpp := (hS p hp).2
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
      refine div_le_div_of_nonneg_left (log_nonneg_prime hpp) (by nlinarith) (by nlinarith)
    · intro p hp _
      have hpp := (mem_PL.1 hp).2
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
      exact div_nonneg (log_nonneg_prime hpp) (by nlinarith)
  exact h1.trans (tail_sum x)

/-- The theta bound on a set of primes. -/
lemma sum_log_theta_le (S : Finset ℕ) (x : ℕ) (hS : ∀ p ∈ S, p ≤ x ∧ p.Prime) :
    ∑ p ∈ S, Real.log p ≤ x * Real.log 4 := by
  have hsub : S ⊆ PL x := fun p hp => mem_PL.2 (hS p hp)
  refine (sum_le_sum_of_subset_of_nonneg hsub ?_).trans (theta_PL x)
  intro p hp _
  exact log_nonneg_prime (mem_PL.1 hp).2

/-- The primes used at a node. -/
noncomputable def nodePrimes (Bad : ℤ) (P₀ x : ℕ) : Finset ℕ := by
  classical
  exact ((Ioc P₀ x).filter Nat.Prime).filter fun p => ¬ (p : ℤ) ∣ Bad

lemma mem_nodePrimes {Bad : ℤ} {P₀ x p : ℕ} :
    p ∈ nodePrimes Bad P₀ x ↔ (P₀ < p ∧ p ≤ x) ∧ p.Prime ∧ ¬ (p : ℤ) ∣ Bad := by
  classical
  simp only [nodePrimes, mem_filter, mem_Ioc, and_assoc]

/-- **Lower bound for the sum over primes.** -/
theorem primes_lower : ∃ C₄ : ℝ, 0 ≤ C₄ ∧ ∀ {J : Type} [Fintype J] (m : J → ℤ) (Bad : ℤ)
    (Mb : ℝ) (P₀ x : ℕ) (n : ℕ → ℕ),
    (∀ j, m j ≠ 0) → (∀ j, |(m j : ℝ)| ≤ Mb) → Bad ≠ 0 → |(Bad : ℝ)| ≤ Mb →
    Real.log Mb ≤ P₀ → 18 ≤ P₀ → 1 ≤ x → x ^ 2 ≤ Fintype.card J →
    (∀ p ∈ nodePrimes Bad P₀ x,
      c0 * (((univ.filter fun j => ¬ (p : ℤ) ∣ m j).card : ℕ) : ℝ) ^ ((3 : ℝ) / 2) /
          Real.sqrt ((p : ℝ) ^ 2 + 18 * p)
        - 2 * (((univ.filter fun j => ¬ (p : ℤ) ∣ m j).card : ℕ) : ℝ) ≤ n p) →
    c0 * (Fintype.card J : ℝ) ^ ((3 : ℝ) / 2) * (Real.log x - Real.log P₀ - C₄) ≤
      ∑ p ∈ nodePrimes Bad P₀ x, (n p : ℝ) * Real.log p := by
  classical
  obtain ⟨CM, hCM, hM⟩ := mertens_window
  have hC0 : 0 ≤ C0 := tsum_nonneg fun m => by positivity
  have hc := c0_pos
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨CM + 1 + 9 * C0 + 3 / 2 + 2 * Real.log 4 / c0, by positivity, ?_⟩
  intro J _ m Bad Mb P₀ x n hm hMb hBad hBadMb hlogMb hP₀ hx1 hxE hn
  set E : ℝ := (Fintype.card J : ℝ) with hE
  have hE0 : 0 ≤ E := Nat.cast_nonneg _
  set C₄ := CM + 1 + 9 * C0 + 3 / 2 + 2 * Real.log 4 / c0 with hC₄
  have hP₀0 : (18 : ℝ) ≤ P₀ := by exact_mod_cast hP₀
  have hE32 : 0 ≤ E ^ ((3 : ℝ) / 2) := by positivity
  rcases lt_or_ge x P₀ with hlt | hge
  · -- no primes
    have hempty : nodePrimes Bad P₀ x = ∅ := by
      ext p
      simp only [mem_nodePrimes, notMem_empty, iff_false]
      rintro ⟨⟨h1, h2⟩, -⟩
      omega
    rw [hempty, Finset.sum_empty]
    have hlogle : Real.log x ≤ Real.log P₀ :=
      Real.log_le_log (by exact_mod_cast hx1) (by exact_mod_cast hlt.le)
    have : Real.log x - Real.log P₀ - C₄ ≤ 0 := by
      have : 0 ≤ C₄ := by positivity
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) this
  set S := nodePrimes Bad P₀ x with hS
  have hSmem : ∀ p ∈ S, (P₀ < p ∧ p ≤ x) ∧ p.Prime ∧ ¬ (p : ℤ) ∣ Bad := fun p hp =>
    mem_nodePrimes.1 hp
  set b : ℕ → ℝ := fun p => (((univ.filter fun j => (p : ℤ) ∣ m j).card : ℕ) : ℝ) with hb
  have hcompl : ∀ p : ℕ, (((univ.filter fun j => ¬ (p : ℤ) ∣ m j).card : ℕ) : ℝ) = E - b p := by
    intro p
    have := card_filter_add_card_filter_not (s := (univ : Finset J)) (fun j => (p : ℤ) ∣ m j)
    rw [Finset.card_univ] at this
    have h : (((univ.filter fun j => (p : ℤ) ∣ m j).card : ℕ) : ℝ) +
        (((univ.filter fun j => ¬ (p : ℤ) ∣ m j).card : ℕ) : ℝ) = E := by
      rw [hE]; exact_mod_cast this
    simp only [hb]
    linarith
  -- term by term
  have hterm : ∀ p ∈ S, c0 * E ^ ((3 : ℝ) / 2) * (Real.log p / p - 9 * (Real.log p / (p : ℝ) ^ 2))
      - c0 * (3 / 2) * Real.sqrt E * (b p * (Real.log p / p)) - 2 * E * Real.log p ≤
      (n p : ℝ) * Real.log p := by
    intro p hp
    obtain ⟨⟨h1, h2⟩, h3, -⟩ := hSmem p hp
    have hbp : 0 ≤ b p := Nat.cast_nonneg _
    have hbE : b p ≤ E := by
      have := hcompl p
      have h0 : (0 : ℝ) ≤ (((univ.filter fun j => ¬ (p : ℤ) ∣ m j).card : ℕ) : ℝ) :=
        Nat.cast_nonneg _
      linarith
    have hp18 : (18 : ℝ) ≤ p := by
      have : 18 ≤ p := by omega
      exact_mod_cast this
    have hn' := hn p hp
    rw [hcompl p] at hn'
    exact term_lower hp18 hbp hbE (log_nonneg_prime h3) hn'
  have hsum := sum_le_sum hterm
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  set a₁ := ∑ p ∈ S, Real.log p / p with ha₁
  set a₂ := ∑ p ∈ S, Real.log p / (p : ℝ) ^ 2 with ha₂
  set a₃ := ∑ p ∈ S, b p * (Real.log p / p) with ha₃
  set a₄ := ∑ p ∈ S, Real.log p with ha₄
  have hP0pos : 0 < P₀ := by omega
  have hPR : (0 : ℝ) < P₀ := by exact_mod_cast hP0pos
  have hratio : Real.log Mb / P₀ ≤ 1 := (div_le_one hPR).2 hlogMb
  have hA : a₃ ≤ E := by
    have h1 : a₃ ≤ E * (Real.log Mb / P₀) :=
      sum_bad_rows_le m hm hMb P₀ hP0pos S (fun p hp => ⟨(hSmem p hp).2.1, (hSmem p hp).1.1⟩)
    have h2 : E * (Real.log Mb / P₀) ≤ E * 1 := mul_le_mul_of_nonneg_left hratio hE0
    linarith
  have hB : a₂ ≤ C0 := sum_log_sq_le S x fun p hp => ⟨(hSmem p hp).1.2, (hSmem p hp).2.1⟩
  have hD : a₄ ≤ x * Real.log 4 :=
    sum_log_theta_le S x fun p hp => ⟨(hSmem p hp).1.2, (hSmem p hp).2.1⟩
  have hC : Real.log x - Real.log P₀ - CM - 1 ≤ a₁ := by
    have h1 := hM P₀ x hP0pos hge
    set Pr := (Ioc P₀ x).filter Nat.Prime with hPr
    have h2 : ∑ p ∈ Pr, Real.log (p : ℝ) / (p : ℝ) = a₁ +
        ∑ p ∈ Pr.filter (fun p : ℕ => (p : ℤ) ∣ Bad), Real.log (p : ℝ) / (p : ℝ) := by
      rw [← Finset.sum_filter_add_sum_filter_not Pr (fun p : ℕ => (p : ℤ) ∣ Bad), add_comm]
      have hSeq : Pr.filter (fun p : ℕ => ¬ (p : ℤ) ∣ Bad) = S := by
        ext p
        simp only [hS, mem_nodePrimes, hPr, mem_filter, mem_Ioc]
        tauto
      rw [hSeq]
    have h3 : ∑ p ∈ Pr.filter (fun p : ℕ => (p : ℤ) ∣ Bad), Real.log (p : ℝ) / (p : ℝ) ≤
        Real.log Mb / P₀ := by
      refine sum_div_dvd_le hBad hBadMb P₀ hP0pos _ (fun p hp => ?_) fun p hp =>
        (mem_filter.1 hp).2
      have := mem_filter.1 (mem_filter.1 hp).1
      exact ⟨this.2, (mem_Ioc.1 this.1).1⟩
    linarith
  -- the three error terms
  have hsE : 0 ≤ Real.sqrt E := Real.sqrt_nonneg _
  have hE2 : Real.sqrt E ^ 2 = E := Real.sq_sqrt hE0
  have hE3 : E ^ ((3 : ℝ) / 2) = E * Real.sqrt E := by
    rw [rpow_three_halves hE0]
    nlinarith
  have hxs : (x : ℝ) ≤ Real.sqrt E := by
    refine Real.le_sqrt_of_sq_le ?_
    rw [hE]
    exact_mod_cast hxE
  set R := E ^ ((3 : ℝ) / 2) with hR
  have hR0 : 0 ≤ R := hE32
  have e1 : c0 * R * (Real.log x - Real.log P₀ - CM - 1 - 9 * C0) ≤ c0 * R * (a₁ - 9 * a₂) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have e2 : c0 * (3 / 2) * Real.sqrt E * a₃ ≤ c0 * (3 / 2) * R := by
    have := mul_le_mul_of_nonneg_left hA (by positivity : 0 ≤ c0 * (3 / 2) * Real.sqrt E)
    rw [hE3]
    nlinarith
  have e3 : 2 * E * a₄ ≤ c0 * R * (2 * Real.log 4 / c0) := by
    have h1 : 2 * E * a₄ ≤ 2 * E * (x * Real.log 4) :=
      mul_le_mul_of_nonneg_left hD (by positivity)
    have h2 : 2 * E * (x * Real.log 4) ≤ 2 * E * (Real.sqrt E * Real.log 4) := by
      have : (x : ℝ) * Real.log 4 ≤ Real.sqrt E * Real.log 4 :=
        mul_le_mul_of_nonneg_right hxs hlog4
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have h3 : c0 * R * (2 * Real.log 4 / c0) = 2 * R * Real.log 4 := by
      field_simp
    rw [h3, hE3]
    nlinarith
  have efinal : c0 * R * (Real.log x - Real.log P₀ - C₄) =
      c0 * R * (Real.log x - Real.log P₀ - CM - 1 - 9 * C0) - c0 * (3 / 2) * R -
        c0 * R * (2 * Real.log 4 / c0) := by
    rw [hC₄]
    ring
  rw [efinal]
  linarith

end OVNS.Quant.Surf
