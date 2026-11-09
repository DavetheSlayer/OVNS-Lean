import OddViscousNS.Quant.Arith.Resonant.Regroup
import OddViscousNS.Quant.Arith.Resonant.Cauchy

/-!
# Proposition quant-resonant (conditional on the weighted count)

With `σ = θ = 281/1000` and `b₀ = 2σ = 281/500 > p*`, the weighted count gives
`W(n) ≤ C_W |n|^{b₀}`.  `H¹`: the `γ`-sum is bounded through the fixed-output Cauchy
(`√W(n) ≤ √C_W |n|^{σ}`, split as `|n|^{σ/2} |n|^{σ/2}` with `|n|^σ ≤ 2^σ |k|^σ` on the fibre),
the output Cauchy with `c_n = |n|^{σ/2} u_n`, `a = u`, `b_k = |k|^{σ/2} u_k`, and the interpolation
`‖F‖²_{1+σ/2} ≤ ‖F‖₁^{2−σ} ‖F‖₂^σ`: `C_s = 6 · 2^{σ/2} √C_W`.  `H²`: `|h₂| ≤ 6 K N` and the
weights `|m|^θ, |k|², |n|³` make the fibre factor `6 γ N^{−θ}`, uniform since `2θ = b₀`:
`C_H = 36 √C_W`.
-/

namespace OVNS.Quant

/-! ### Fibre sums -/

private lemma sfib_summable (n : Mode) (g : Mode → ℝ) :
    Summable fun k => if SFib n k then g k else 0 := by
  refine summable_of_ne_finset_zero (s := (finite_ball (absk n)).toFinset) fun k hk => ?_
  exact ite_eq_right_iff.mpr fun h => absurd (by simpa using h.2.1) hk

private lemma sfib_tsum_le {n : Mode} {g h : Mode → ℝ} (hgh : ∀ k, SFib n k → g k ≤ h k) :
    (∑' k, if SFib n k then g k else 0) ≤ ∑' k, if SFib n k then h k else 0 :=
  (sfib_summable n g).tsum_le_tsum
    (fun k => by split_ifs with hk; exacts [hgh k hk, le_rfl]) (sfib_summable n h)

private lemma sqrt_W_le {CW σ : ℝ} (hCW : 0 ≤ CW) {n : Mode}
    (hW : Wfib n ≤ CW * absk n ^ (2 * σ)) :
    Real.sqrt (Wfib n) ≤ Real.sqrt CW * absk n ^ σ := by
  calc Real.sqrt (Wfib n) ≤ Real.sqrt (CW * absk n ^ (2 * σ)) := Real.sqrt_le_sqrt hW
    _ = _ := by
      rw [Real.sqrt_mul hCW, show 2 * σ = σ * 2 by ring, Real.rpow_mul (absk_nonneg n),
        Real.rpow_two, Real.sqrt_sq (Real.rpow_nonneg (absk_nonneg n) _)]

/-- The squared fibre sum `∑_{k ∈ fibre} a(−k−n)² b(k)²`. -/
private noncomputable def fibG (a b : Mode → ℝ) (n : Mode) : ℝ :=
  ∑' k, if SFib n k then a (-k - n) ^ 2 * b k ^ 2 else 0

private lemma fibre_step {CW σ L : ℝ} (hCW : 0 ≤ CW) (hL : 0 ≤ L) {n : Mode} (hn : 0 < absk n)
    (hW : Wfib n ≤ CW * absk n ^ (2 * σ)) {a b c h : Mode → ℝ} (ha : ∀ k, 0 ≤ a k)
    (hb : ∀ k, 0 ≤ b k) (hc : ∀ k, 0 ≤ c k)
    (hterm : ∀ k, SFib n k →
      absk n ^ σ * h k ≤ L * c n * (gammaR ![-k - n, k, n] * a (-k - n) * b k)) :
    (∑' k, if SFib n k then h k else 0) ≤ L * Real.sqrt CW * (c n * Real.sqrt (fibG a b n)) := by
  have hp : 0 < absk n ^ σ := Real.rpow_pos_of_pos hn σ
  have hG := fibre_cauchy n ha hb (sfib_summable n _)
  have h1 : absk n ^ σ * (∑' k, if SFib n k then h k else 0) ≤
      L * c n * ∑' k, (if SFib n k then gammaR ![-k - n, k, n] * a (-k - n) * b k else 0) := by
    rw [← tsum_mul_left, ← tsum_mul_left]
    simp only [mul_ite, mul_zero]
    exact sfib_tsum_le hterm
  have hLc : 0 ≤ L * c n := mul_nonneg hL (hc n)
  have h2 : L * c n * ∑' k, (if SFib n k then gammaR ![-k - n, k, n] * a (-k - n) * b k else 0)
      ≤ absk n ^ σ * (L * Real.sqrt CW * (c n * Real.sqrt (fibG a b n))) := by
    calc _ ≤ L * c n * (Real.sqrt (Wfib n) * Real.sqrt (fibG a b n)) :=
          mul_le_mul_of_nonneg_left hG hLc
      _ ≤ L * c n * (Real.sqrt CW * absk n ^ σ * Real.sqrt (fibG a b n)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (sqrt_W_le hCW hW) (Real.sqrt_nonneg _)) hLc
      _ = _ := by ring
  exact le_of_mul_le_mul_left (h1.trans h2) hp

private lemma fibre_step' {CW σ L : ℝ} (hCW : 0 ≤ CW) (hL : 0 ≤ L)
    (hWn : ∀ n : Mode, n ≠ 0 → Wfib n ≤ CW * absk n ^ (2 * σ)) (n : Mode) {a b c h : Mode → ℝ}
    (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (hc : ∀ k, 0 ≤ c k)
    (hterm : ∀ k, SFib n k →
      absk n ^ σ * h k ≤ L * c n * (gammaR ![-k - n, k, n] * a (-k - n) * b k)) :
    (∑' k, if SFib n k then h k else 0) ≤ L * Real.sqrt CW * (c n * Real.sqrt (fibG a b n)) := by
  by_cases hn2 : n 2 = 0
  · have hno : ∀ k, ¬ SFib n k := fun k hk => hk.2.2.1 hn2
    simp only [hno, ↓reduceIte, tsum_zero]
    exact mul_nonneg (mul_nonneg hL (Real.sqrt_nonneg _))
      (mul_nonneg (hc n) (Real.sqrt_nonneg _))
  · have hn0 : n ≠ 0 := fun h => hn2 (by simp [h])
    exact fibre_step hCW hL (lt_of_lt_of_le one_pos (one_le_absk hn0)) (hWn n hn0) ha hb hc
      hterm

private lemma total_le {f : Mode × Mode → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hfs : Summable f)
    (hsym : ∀ x, f (rho x) = f x ∧ f (iota x) = f x)
    (hfast : ∀ x, (∃ j, legs x j 2 = 0) → f x = 0) {a b c : Mode → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (hc : ∀ k, 0 ≤ c k)
    (hsa : Summable fun k => a k ^ 2) (hsb : Summable fun k => b k ^ 2)
    (hsc : Summable fun k => c k ^ 2)
    (hT : ∀ n, (∑' k, if SFib n k then f (-k - n, k) else 0) ≤
      K * (c n * Real.sqrt (fibG a b n))) :
    ∑' x, f x ≤ 6 * K * (Real.sqrt (∑' k, c k ^ 2) * Real.sqrt (∑' k, a k ^ 2) *
      Real.sqrt (∑' k, b k ^ 2)) := by
  refine (sorted_sum_le hf0 hfs hsym hfast).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine tsum_le_of_sum_le' (by positivity) fun s => ?_
  have hc' : ∀ k, 0 ≤ (if k ∈ s then c k else 0) := fun k => by
    split_ifs
    exacts [hc k, le_rfl]
  have hsc' : Summable fun k => (if k ∈ s then c k else 0) ^ 2 :=
    summable_of_ne_finset_zero (s := s) fun k hk => by simp [hk]
  calc ∑ n ∈ s, (∑' k, if SFib n k then f (-k - n, k) else 0)
      ≤ ∑ n ∈ s, K * (c n * Real.sqrt (fibG a b n)) := Finset.sum_le_sum fun n _ => hT n
    _ = K * ∑' n, (if n ∈ s then c n else 0) * Real.sqrt (fibG a b n) := by
        rw [← Finset.mul_sum, tsum_eq_sum (s := s) (fun n hn => by simp [hn])]
        congr 1
        exact Finset.sum_congr rfl fun n hn => by simp [hn]
    _ ≤ K * (Real.sqrt (∑' k, (if k ∈ s then c k else 0) ^ 2) * Real.sqrt (∑' k, a k ^ 2) *
          Real.sqrt (∑' k, b k ^ 2)) :=
        mul_le_mul_of_nonneg_left (output_cauchy ha hb hc' hsa hsb hsc') hK
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ hK
        have hle := hsc'.tsum_le_tsum (fun k => by split_ifs <;> simp [sq_nonneg]) hsc
        gcongr


/-! ### Symmetry of the coefficients under relabelling the legs -/

/-- The cyclic permutation of the legs induced by `rho`. -/
private def piR : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

private lemma piR_0 : piR 0 = 1 := by decide
private lemma piR_1 : piR 1 = 2 := by decide
private lemma piR_2 : piR 2 = 0 := by decide

private lemma legs_rho (x : Mode × Mode) : legs (rho x) = fun j => legs x (piR j) := by
  obtain ⟨p, q⟩ := x
  funext j
  fin_cases j <;> simp [legs, rho, piR_0, piR_1, piR_2]

private lemma legs_iota (x : Mode × Mode) :
    legs (iota x) = fun j => legs x (Equiv.swap 1 2 j) := by
  obtain ⟨p, q⟩ := x
  funext j
  fin_cases j <;> simp [legs, iota, Equiv.swap_apply_def]

private lemma sum_res_comp (π : Equiv.Perm (Fin 3)) (ℓ : Fin 3 → Mode)
    (G G' : (Fin 3 → Sgn) → ℝ) (hG : ∀ t, G' (fun j => t (π j)) = G t) :
    (∑ s, if ResPat (fun j => ℓ (π j)) s then G' s else 0) =
      ∑ s, if ResPat ℓ s then G s else 0 := by
  refine Fintype.sum_equiv (Equiv.arrowCongr π (Equiv.refl Sgn)) _ _ fun s => ?_
  have hR : ResPat (fun j => ℓ (π j)) s ↔ ResPat ℓ (fun j => s (π.symm j)) := by
    unfold ResPat
    rw [← Equiv.sum_comp π (fun j => lam (s (π.symm j)) (ℓ j))]
    simp only [Equiv.symm_apply_apply]
  have hG' : G' s = G (fun j => s (π.symm j)) := by
    rw [← hG]
    simp only [Equiv.symm_apply_apply]
  exact if_congr hR hG' rfl

private lemma crossZ_rho (p q : Mode) : crossZ q (-(p + q)) = crossZ p q := by
  funext i
  fin_cases i <;> simp [crossZ] <;> ring

private lemma crossZ_iota (p q : Mode) : crossZ p (-(p + q)) = -crossZ p q := by
  funext i
  fin_cases i <;> simp [crossZ] <;> ring

private lemma abs_alt_rho (y0 y1 y2 : ℝ) :
    |(y1 + y2 + y0) * (y1 - y2) * (y2 - y0) * (y0 - y1)| =
      |(y0 + y1 + y2) * (y0 - y1) * (y1 - y2) * (y2 - y0)| := by
  ring_nf

private lemma abs_alt_iota (y0 y1 y2 : ℝ) :
    |(y0 + y2 + y1) * (y0 - y2) * (y2 - y1) * (y1 - y0)| =
      |(y0 + y1 + y2) * (y0 - y1) * (y1 - y2) * (y2 - y0)| := by
  rw [← abs_neg]
  ring_nf

private lemma gammaC_rho (x : Mode × Mode) (t : Fin 3 → Sgn) :
    gammaC (fun j => legs x (piR j)) (fun j => t (piR j)) = gammaC (legs x) t := by
  unfold gammaC areaM sl
  simp only [piR_0, piR_1, piR_2]
  have h : crossZ (legs x 1) (legs x 2) = crossZ (legs x 0) (legs x 1) := crossZ_rho x.1 x.2
  rw [h, abs_alt_rho]
  ring

private lemma gammaC_iota (x : Mode × Mode) (t : Fin 3 → Sgn) :
    gammaC (fun j => legs x (Equiv.swap 1 2 j)) (fun j => t (Equiv.swap 1 2 j)) =
      gammaC (legs x) t := by
  unfold gammaC areaM sl
  have e0 : Equiv.swap (1 : Fin 3) 2 0 = 0 := by decide
  have e1 : Equiv.swap (1 : Fin 3) 2 1 = 2 := by decide
  have e2 : Equiv.swap (1 : Fin 3) 2 2 = 1 := by decide
  simp only [e0, e1, e2]
  have h : crossZ (legs x 0) (legs x 2) = -crossZ (legs x 0) (legs x 1) := crossZ_iota x.1 x.2
  rw [h, absk_neg, abs_alt_iota]
  ring

private lemma h2C_rho (x : Mode × Mode) (t : Fin 3 → Sgn) :
    h2C (fun j => legs x (piR j)) (fun j => t (piR j)) = h2C (legs x) t := by
  unfold h2C sl
  simp only [piR_0, piR_1, piR_2]
  ring

private lemma h2C_iota (x : Mode × Mode) (t : Fin 3 → Sgn) :
    h2C (fun j => legs x (Equiv.swap 1 2 j)) (fun j => t (Equiv.swap 1 2 j)) = h2C (legs x) t := by
  unfold h2C sl
  have e0 : Equiv.swap (1 : Fin 3) 2 0 = 0 := by decide
  have e1 : Equiv.swap (1 : Fin 3) 2 1 = 2 := by decide
  have e2 : Equiv.swap (1 : Fin 3) 2 2 = 1 := by decide
  simp only [e0, e1, e2]
  ring

private lemma gammaR_sym (x : Mode × Mode) :
    gammaR (legs (rho x)) = gammaR (legs x) ∧ gammaR (legs (iota x)) = gammaR (legs x) := by
  unfold gammaR
  rw [legs_rho, legs_iota, sum_res_comp piR (legs x) _ _ (gammaC_rho x),
    sum_res_comp (Equiv.swap 1 2) (legs x) _ _ (gammaC_iota x)]
  exact ⟨rfl, rfl⟩

private lemma gammaR2_sym (x : Mode × Mode) :
    gammaR2 (legs (rho x)) = gammaR2 (legs x) ∧ gammaR2 (legs (iota x)) = gammaR2 (legs x) := by
  unfold gammaR2
  rw [legs_rho, legs_iota,
    sum_res_comp piR (legs x) _ _ (fun t => by rw [gammaC_rho x, h2C_rho x]),
    sum_res_comp (Equiv.swap 1 2) (legs x) _ _ (fun t => by rw [gammaC_iota x, h2C_iota x])]
  exact ⟨rfl, rfl⟩

/-! ### The triad summand -/

/-- The triad summand `g(ℓ) ∏_j u_{ℓ_j}`. -/
private noncomputable def fT (g : (Fin 3 → Mode) → ℝ) (F : Field) (x : Mode × Mode) : ℝ :=
  g (legs x) * ∏ j, uAmp F (legs x j)

private lemma uAmp_nonneg (F : Field) (k : Mode) : 0 ≤ uAmp F k :=
  mul_nonneg (absk_nonneg k) (norm_nonneg _)

private lemma fT_nonneg {g : (Fin 3 → Mode) → ℝ} (hg : ∀ ℓ, 0 ≤ g ℓ) (F : Field)
    (x : Mode × Mode) : 0 ≤ fT g F x :=
  mul_nonneg (hg _) (Finset.prod_nonneg fun _ _ => uAmp_nonneg F _)

private lemma fT_sym {g : (Fin 3 → Mode) → ℝ}
    (hg : ∀ x, g (legs (rho x)) = g (legs x) ∧ g (legs (iota x)) = g (legs x)) (F : Field)
    (x : Mode × Mode) : fT g F (rho x) = fT g F x ∧ fT g F (iota x) = fT g F x := by
  unfold fT
  refine ⟨?_, ?_⟩
  · rw [(hg x).1, legs_rho]
    congr 1
    exact Equiv.prod_comp piR (fun j => uAmp F (legs x j))
  · rw [(hg x).2, legs_iota]
    congr 1
    exact Equiv.prod_comp (Equiv.swap 1 2) (fun j => uAmp F (legs x j))

private lemma fT_fast {g : (Fin 3 → Mode) → ℝ} {F : Field} (hF' : PiF F = F) (x : Mode × Mode)
    (hx : ∃ j, legs x j 2 = 0) : fT g F x = 0 := by
  obtain ⟨j, hj⟩ := hx
  have h0 : F (legs x j) = 0 := by
    have := congrFun hF' (legs x j)
    simp only [PiF, hj, ↓reduceIte] at this
    exact this.symm
  unfold fT
  rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [uAmp, h0]), mul_zero]

private lemma fT_fib (g : (Fin 3 → Mode) → ℝ) (F : Field) (n k : Mode) :
    fT g F (-k - n, k) = g ![-k - n, k, n] * (uAmp F (-k - n) * uAmp F k * uAmp F n) := by
  have hl : legs (-k - n, k) = ![-k - n, k, n] := by
    funext j
    fin_cases j <;> simp [legs]
  unfold fT
  rw [hl, Fin.prod_univ_three]
  rfl

private lemma absk_zero' : absk 0 = 0 := by simp [absk, absSq]

private lemma wsq {t : ℝ} (ht : t ≠ 0) (F : Field) (j : Mode) :
    (absk j ^ t * ‖F j‖) ^ 2 = sobWeight t j * ‖F j‖ ^ 2 := by
  unfold sobWeight
  split_ifs with hj
  · subst hj
    simp [absk_zero', Real.zero_rpow ht]
  · rw [mul_pow, mul_comm 2 t, Real.rpow_mul (absk_nonneg j), Real.rpow_two]

/-! ### The two chains -/

private lemma H1_term {σ : ℝ} (h0 : 0 < σ) (F : Field) {n k : Mode} (hk : SFib n k) :
    absk n ^ σ * fT gammaR F (-k - n, k) ≤ 2 ^ (σ / 2) * (absk n ^ (σ / 2) * uAmp F n) *
      (gammaR ![-k - n, k, n] * uAmp F (-k - n) * (absk k ^ (σ / 2) * uAmp F k)) := by
  obtain ⟨hnk, -, hkpos, hn⟩ := fibre_norm_le hk
  rw [fT_fib]
  have e : absk n ^ σ = absk n ^ (σ / 2) * absk n ^ (σ / 2) := by
    rw [← Real.rpow_add hn]
    ring_nf
  have hle : absk n ^ (σ / 2) ≤ 2 ^ (σ / 2) * absk k ^ (σ / 2) := by
    rw [← Real.mul_rpow (by norm_num) hkpos.le]
    exact Real.rpow_le_rpow (absk_nonneg n) hnk (by linarith)
  have hX : 0 ≤ gammaR ![-k - n, k, n] * uAmp F (-k - n) * uAmp F k * uAmp F n *
      absk n ^ (σ / 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (gammaR_nonneg _) (uAmp_nonneg F _))
      (uAmp_nonneg F _)) (uAmp_nonneg F _)) (Real.rpow_nonneg (absk_nonneg n) _)
  calc absk n ^ σ * (gammaR ![-k - n, k, n] * (uAmp F (-k - n) * uAmp F k * uAmp F n))
      = (gammaR ![-k - n, k, n] * uAmp F (-k - n) * uAmp F k * uAmp F n *
          absk n ^ (σ / 2)) * absk n ^ (σ / 2) := by rw [e]; ring
    _ ≤ (gammaR ![-k - n, k, n] * uAmp F (-k - n) * uAmp F k * uAmp F n *
          absk n ^ (σ / 2)) * (2 ^ (σ / 2) * absk k ^ (σ / 2)) :=
        mul_le_mul_of_nonneg_left hle hX
    _ = _ := by ring

private lemma H1_gen {σ CW : ℝ} (h0 : 0 < σ) (h1 : σ ≤ 1) (hCW : 0 ≤ CW)
    (hWn : ∀ n : Mode, n ≠ 0 → Wfib n ≤ CW * absk n ^ (2 * σ)) {F : Field} (hF : Adm 2 F)
    (hF' : PiF F = F) :
    |pair 1 F (Qres F F)| ≤
      6 * 2 ^ (σ / 2) * Real.sqrt CW * hnorm 1 F ^ (3 - σ) * hnorm 2 F ^ σ := by
  obtain ⟨hs, hle⟩ := pair1_le_gamma_sum hF hF'
  set c : Mode → ℝ := fun j => absk j ^ (σ / 2) * uAmp F j with hc_def
  have hc0 : ∀ j, 0 ≤ c j := fun j =>
    mul_nonneg (Real.rpow_nonneg (absk_nonneg j) _) (uAmp_nonneg F j)
  have hcsq : ∀ j, c j ^ 2 = sobWeight (1 + σ / 2) j * ‖F j‖ ^ 2 := fun j => by
    rw [← wsq (by linarith)]
    simp only [hc_def, uAmp]
    rw [Real.rpow_add' (absk_nonneg j) (by linarith), Real.rpow_one]
    ring
  have husq : ∀ j, uAmp F j ^ 2 = sobWeight 1 j * ‖F j‖ ^ 2 := fun j => by
    rw [← wsq one_ne_zero, Real.rpow_one]
    rfl
  have hsc : Summable fun k => c k ^ 2 := by
    simp only [hcsq]
    exact hF.inH.mono (by linarith)
  have hsu : Summable fun k => uAmp F k ^ 2 := by
    simp only [husq]
    exact hF.inH.mono (by norm_num)
  have hL : (0 : ℝ) ≤ 2 ^ (σ / 2) := by positivity
  have hT := fun n => fibre_step' (h := fun k => fT gammaR F (-k - n, k)) hCW hL hWn n
    (uAmp_nonneg F) hc0 hc0 (fun k hk => H1_term h0 F hk)
  have htot := total_le (fT_nonneg gammaR_nonneg F) hs (fT_sym gammaR_sym F) (fT_fast hF')
    (mul_nonneg hL (Real.sqrt_nonneg CW)) (uAmp_nonneg F) hc0 hc0 hsu hsc hsc hT
  have ec : Real.sqrt (∑' k, c k ^ 2) = hnorm (1 + σ / 2) F := by
    simp only [hcsq]
    rfl
  have eu : Real.sqrt (∑' k, uAmp F k ^ 2) = hnorm 1 F := by
    simp only [husq]
    rfl
  rw [ec, eu] at htot
  have hint := hnorm_interp h0.le h1 hF.inH
  have hB := hnorm_nonneg 1 F
  have h6 : 0 ≤ 6 * (2 ^ (σ / 2) * Real.sqrt CW) := by positivity
  calc |pair 1 F (Qres F F)| ≤ _ := hle
    _ ≤ _ := htot
    _ = 6 * (2 ^ (σ / 2) * Real.sqrt CW) * hnorm (1 + σ / 2) F ^ 2 * hnorm 1 F := by ring
    _ ≤ 6 * (2 ^ (σ / 2) * Real.sqrt CW) * (hnorm 1 F ^ (2 - σ) * hnorm 2 F ^ σ) *
          hnorm 1 F := by gcongr
    _ = _ := by
        rw [show 3 - σ = (2 - σ) + 1 by ring, Real.rpow_add' hB (by linarith), Real.rpow_one]
        ring

private lemma gammaR2_le {n k : Mode} (hk : SFib n k) :
    gammaR2 ![-k - n, k, n] ≤ 6 * absk k * absk n * gammaR ![-k - n, k, n] := by
  obtain ⟨-, hm, -, -⟩ := fibre_norm_le hk
  obtain ⟨hMK, hKN, -, -, -⟩ := hk
  have hNMK : absk n ≤ absk (-k - n) + absk k := by
    have e : n = -((-k - n) + k) := by abel
    calc absk n = absk ((-k - n) + k) := by rw [e, absk_neg]; congr 1; abel
      _ ≤ absk (-k - n) + absk k := absk_add_le _ _
  unfold gammaR2 gammaR
  calc (1 / 2 : ℝ) * ∑ s : Fin 3 → Sgn, (if ResPat ![-k - n, k, n] s then
        gammaC ![-k - n, k, n] s * |h2C ![-k - n, k, n] s| else 0)
      ≤ (1 / 2 : ℝ) * ∑ s : Fin 3 → Sgn, (if ResPat ![-k - n, k, n] s then
        6 * absk k * absk n * gammaC ![-k - n, k, n] s else 0) := by
        gcongr with s
        split_ifs
        · rw [mul_comm]
          exact mul_le_mul_of_nonneg_right (h2C_le ![-k - n, k, n] s hm hMK hKN hNMK)
            (gammaC_nonneg _ s)
        · exact le_rfl
    _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        split_ifs <;> ring

private lemma H2_term {σ : ℝ} (h1 : σ ≤ 1) (F : Field) {n k : Mode}
    (hk : SFib n k) :
    absk n ^ σ * fT gammaR2 F (-k - n, k) ≤ 6 * (absk n ^ (3 : ℝ) * ‖F n‖) *
      (gammaR ![-k - n, k, n] * (absk (-k - n) ^ σ * ‖F (-k - n)‖) *
        (absk k ^ (2 : ℝ) * ‖F k‖)) := by
  have hg := gammaR2_le hk
  obtain ⟨-, hm, hkpos, hn⟩ := fibre_norm_le hk
  obtain ⟨hMK, hKN, -, -, -⟩ := hk
  rw [fT_fib]
  set M := absk (-k - n)
  set K := absk k
  set N := absk n
  set γ := gammaR ![-k - n, k, n]
  have hγ : 0 ≤ γ := gammaR_nonneg _
  have hp : M ^ (1 - σ) ≤ N ^ (1 - σ) := Real.rpow_le_rpow hm.le (hMK.trans hKN) (by linarith)
  have key : N ^ σ * M ≤ N * M ^ σ := by
    calc N ^ σ * M = (N ^ σ * M ^ σ) * M ^ (1 - σ) := by
          rw [mul_assoc, ← Real.rpow_add hm]
          simp
      _ ≤ (N ^ σ * M ^ σ) * N ^ (1 - σ) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = N * M ^ σ := by
          rw [mul_comm (N ^ σ), mul_assoc, ← Real.rpow_add hn]
          simp only [add_sub_cancel, Real.rpow_one]
          ring
  have hu : 0 ≤ uAmp F (-k - n) * uAmp F k * uAmp F n :=
    mul_nonneg (mul_nonneg (uAmp_nonneg F _) (uAmp_nonneg F _)) (uAmp_nonneg F _)
  have hX : 0 ≤ 6 * γ * ‖F (-k - n)‖ * ‖F k‖ * ‖F n‖ * K ^ 2 * N ^ 2 := by positivity
  have e3 : N ^ (3 : ℝ) = N ^ 3 := by exact_mod_cast Real.rpow_natCast N 3
  have e2 : K ^ (2 : ℝ) = K ^ 2 := by exact_mod_cast Real.rpow_natCast K 2
  calc N ^ σ * (gammaR2 ![-k - n, k, n] * (uAmp F (-k - n) * uAmp F k * uAmp F n))
      ≤ N ^ σ * (6 * K * N * γ * (uAmp F (-k - n) * uAmp F k * uAmp F n)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hg hu) (by positivity)
    _ = (6 * γ * ‖F (-k - n)‖ * ‖F k‖ * ‖F n‖ * K ^ 2 * N ^ 2) * (N ^ σ * M) := by
        simp only [uAmp]
        ring
    _ ≤ (6 * γ * ‖F (-k - n)‖ * ‖F k‖ * ‖F n‖ * K ^ 2 * N ^ 2) * (N * M ^ σ) :=
        mul_le_mul_of_nonneg_left key hX
    _ = _ := by
        rw [e3, e2]
        ring

private lemma H2_gen {σ CW : ℝ} (h0 : 0 < σ) (h1 : σ ≤ 1) (hCW : 0 ≤ CW)
    (hWn : ∀ n : Mode, n ≠ 0 → Wfib n ≤ CW * absk n ^ (2 * σ)) {F : Field} (hF : Adm 3 F)
    (hF' : PiF F = F) :
    |pair 2 F (Qres F F)| ≤ 6 * (6 * Real.sqrt CW) * hnorm σ F * hnorm 2 F * hnorm 3 F := by
  obtain ⟨hs, hle⟩ := pair2_le_gamma_sum hF hF'
  set a : Mode → ℝ := fun j => absk j ^ σ * ‖F j‖ with ha_def
  set b : Mode → ℝ := fun j => absk j ^ (2 : ℝ) * ‖F j‖ with hb_def
  set c : Mode → ℝ := fun j => absk j ^ (3 : ℝ) * ‖F j‖ with hc_def
  have ha0 : ∀ j, 0 ≤ a j := fun j =>
    mul_nonneg (Real.rpow_nonneg (absk_nonneg j) _) (norm_nonneg _)
  have hb0 : ∀ j, 0 ≤ b j := fun j =>
    mul_nonneg (Real.rpow_nonneg (absk_nonneg j) _) (norm_nonneg _)
  have hc0 : ∀ j, 0 ≤ c j := fun j =>
    mul_nonneg (Real.rpow_nonneg (absk_nonneg j) _) (norm_nonneg _)
  have hasq : ∀ j, a j ^ 2 = sobWeight σ j * ‖F j‖ ^ 2 := fun j => wsq h0.ne' F j
  have hbsq : ∀ j, b j ^ 2 = sobWeight 2 j * ‖F j‖ ^ 2 := fun j => wsq (by norm_num) F j
  have hcsq : ∀ j, c j ^ 2 = sobWeight 3 j * ‖F j‖ ^ 2 := fun j => wsq (by norm_num) F j
  have hsa : Summable fun k => a k ^ 2 := by
    simp only [hasq]
    exact hF.inH.mono (by linarith)
  have hsb : Summable fun k => b k ^ 2 := by
    simp only [hbsq]
    exact hF.inH.mono (by norm_num)
  have hsc : Summable fun k => c k ^ 2 := by
    simp only [hcsq]
    exact hF.inH
  have hL : (0 : ℝ) ≤ 6 := by norm_num
  have hT := fun n => fibre_step' (h := fun k => fT gammaR2 F (-k - n, k)) hCW hL hWn n
    ha0 hb0 hc0 (fun k hk => H2_term h1 F hk)
  have htot := total_le (fT_nonneg gammaR2_nonneg F) hs (fT_sym gammaR2_sym F) (fT_fast hF')
    (mul_nonneg hL (Real.sqrt_nonneg CW)) ha0 hb0 hc0 hsa hsb hsc hT
  have ea : Real.sqrt (∑' k, a k ^ 2) = hnorm σ F := by
    simp only [hasq]
    rfl
  have eb : Real.sqrt (∑' k, b k ^ 2) = hnorm 2 F := by
    simp only [hbsq]
    rfl
  have ec : Real.sqrt (∑' k, c k ^ 2) = hnorm 3 F := by
    simp only [hcsq]
    rfl
  rw [ea, eb, ec] at htot
  calc |pair 2 F (Qres F F)| ≤ _ := hle
    _ ≤ _ := htot
    _ = _ := by ring

/-- The weighted count at `b₀ = 2σ`, `σ = 281/1000`. -/
private lemma weighted_b0 (hW : WeightedCount) : ∃ CW : ℝ, 0 ≤ CW ∧
    ∀ n : Mode, n ≠ 0 → Wfib n ≤ CW * absk n ^ (2 * ((281 : ℝ) / 1000)) := by
  obtain ⟨CW, hCW, hC⟩ := hW (281 / 500 - pStar) (by linarith [pStar_bounds.2.1])
  refine ⟨CW, hCW, fun n hn => ?_⟩
  have h := hC n hn
  rwa [show pStar + (281 / 500 - pStar) = 2 * ((281 : ℝ) / 1000) by ring] at h

/-- The `H¹` resonant energy inequality. -/
theorem resonant_H1 (hW : WeightedCount) : ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ F : Field, Adm 2 F → PiF F = F →
    |pair 1 F (Qres F F)| ≤
      Cs * hnorm 1 F ^ (3 - (281 : ℝ) / 1000) * hnorm 2 F ^ ((281 : ℝ) / 1000) := by
  obtain ⟨CW, hCW, hWn⟩ := weighted_b0 hW
  exact ⟨6 * 2 ^ ((281 : ℝ) / 1000 / 2) * Real.sqrt CW, by positivity,
    fun F hF hF' => H1_gen (by norm_num) (by norm_num) hCW hWn hF hF'⟩

/-- The `H²` resonant energy inequality. -/
theorem resonant_H2 (hW : WeightedCount) : ∃ CH : ℝ, 0 ≤ CH ∧ ∀ F : Field, Adm 3 F → PiF F = F →
    |pair 2 F (Qres F F)| ≤ CH * hnorm ((281 : ℝ) / 1000) F * hnorm 2 F * hnorm 3 F := by
  obtain ⟨CW, hCW, hWn⟩ := weighted_b0 hW
  exact ⟨6 * (6 * Real.sqrt CW), by positivity,
    fun F hF hF' => H2_gen (by norm_num) (by norm_num) hCW hWn hF hF'⟩

/-- `β = (2 − σ)/(1 − σ) = 1719/719` and `7β − 3 = 9876/719`. -/
theorem beta_eq : (2 - (281 : ℝ) / 1000) / (1 - 281 / 1000) = 1719 / 719 ∧
    7 * ((1719 : ℝ) / 719) - 3 = 9876 / 719 := by
  constructor <;> norm_num

end OVNS.Quant
