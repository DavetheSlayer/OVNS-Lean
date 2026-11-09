import OddViscousNS.Quant.Arith.Weighted.SurfaceCover
import OddViscousNS.Quant.Arith.Weighted.CaseTable
import OddViscousNS.Quant.Arith.Weighted.Factor
import OddViscousNS.Quant.Arith.Divisor
import OddViscousNS.Quant.Arith.Gamma

/-!
# Lemma quant-weighted, from its inputs, and the glue to `WeightedCount`

`quant_weighted`: `W(n) ≤ C_η |n|^{p* + η}` from `PlaneCurveCount`, `ShellBound` and
`QuadraticNormCount`, by the gcd seam: `W_g` for small `g`, the fixed-`t` count for large `g`, and the
shell bound on the intermediate shells.  All three inputs are proved, so `quant_weighted'`
(`Arith/Surface/QuantWeighted.lean`) has no hypotheses.
`weightedCount_of_quantWeighted`: the one-pattern sorted count `Wfib` of the resonant layer is at
most the eight-pattern count `WfibA`, so `QuantWeighted → WeightedCount`.
-/

namespace OVNS.Quant

/-- Lagrange's identity: `|m × k| = crossAbs m k`. -/
private theorem areaM_eq_crossAbs (m k : Mode) : areaM m k = crossAbs m k := by
  rw [areaM, crossAbs, absk_eq_sqrt_nsqZ]
  congr 2
  simp only [nsqZ, dotZ, crossZ, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

private theorem nsqZ_nonneg (k : Mode) : 0 ≤ nsqZ k :=
  Finset.sum_nonneg fun i _ => sq_nonneg (k i)

private theorem absk_le_iff (k l : Mode) : absk k ≤ absk l ↔ nsqZ k ≤ nsqZ l := by
  rw [absk_eq_sqrt_nsqZ, absk_eq_sqrt_nsqZ,
    Real.sqrt_le_sqrt_iff (by exact_mod_cast nsqZ_nonneg l)]
  exact Int.cast_le

private theorem mem_modeBox_of_nsqZ {k n : Mode} (h : nsqZ k ≤ nsqZ n) :
    k ∈ modeBox (Nat.sqrt (nsqZ n).toNat) := by
  simp only [modeBox, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have hi : k i ^ 2 ≤ nsqZ k := by
    simp only [nsqZ]
    exact Finset.single_le_sum (f := fun j => k j ^ 2) (fun j _ => sq_nonneg (k j))
      (Finset.mem_univ i)
  have h1 : (k i).natAbs ^ 2 ≤ (nsqZ n).toNat := by
    have : (((k i).natAbs ^ 2 : ℕ) : ℤ) ≤ ((nsqZ n).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg (nsqZ_nonneg n)]; push_cast
      rw [sq_abs]; linarith
    exact_mod_cast this
  have h2 : (k i).natAbs ≤ Nat.sqrt (nsqZ n).toNat := Nat.le_sqrt'.mpr h1
  have h3 : |k i| ≤ (Nat.sqrt (nsqZ n).toNat : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast h2
  exact abs_le.mp h3

private theorem sFib_iff (n k : Mode) : SFib n k ↔ (-k - n, k) ∈ sortedFibre n := by
  classical
  simp only [SFib, sortedFibre, Finset.mem_filter, Finset.mem_product, absk_le_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨mem_modeBox_of_nsqZ (h1.trans h2), mem_modeBox_of_nsqZ h2⟩, by abel, h1, h2, h5, h4,
      h3⟩
  · rintro ⟨-, -, h1, h2, h5, h4, h3⟩
    exact ⟨h1, h2, h3, h4, h5⟩

private theorem resPat_iff (m k n : Mode) (s : Fin 3 → Sgn) :
    ResPat ![m, k, n] s ↔ phase3 (s 0) (s 1) (s 2) m k n = 0 := by
  simp only [ResPat, phase3, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

private theorem gammaC_eq (m k n : Mode) (s : Fin 3 → Sgn) :
    gammaC ![m, k, n] s = gammaCoef (s 0) (s 1) (s 2) m k n := by
  simp only [gammaC, gammaCoef, sl, areaM_eq_crossAbs, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- Patterns as triples. -/
private def patEquiv : (Fin 3 → Sgn) ≃ Sgn × Sgn × Sgn where
  toFun s := (s 0, s 1, s 2)
  invFun t := ![t.1, t.2.1, t.2.2]
  left_inv s := by
    funext j; fin_cases j <;> rfl
  right_inv _ := rfl

private theorem sg_not' (a : Sgn) : sg (!a) = -sg a := by cases a <;> simp [sg]

private theorem resPat_neg' (ℓ : Fin 3 → Mode) (s : Fin 3 → Sgn) :
    ResPat ℓ (fun j => !s j) ↔ ResPat ℓ s := by
  have h : ∑ j, lam (!s j) (ℓ j) = -∑ j, lam (s j) (ℓ j) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [lam, sg_not']; ring
  unfold ResPat
  rw [h, neg_eq_zero]

private theorem gammaC_neg' (ℓ : Fin 3 → Mode) (s : Fin 3 → Sgn) :
    gammaC ℓ (fun j => !s j) = gammaC ℓ s := by
  simp only [gammaC, sl, sg_not']
  congr 3
  ring

private theorem pat_aux' (t0 t1 t2 : ℝ) (h0 : t0 ≠ 0) (h1 : t1 ≠ 0) (h2 : t2 ≠ 0)
    (a0 a1 a2 b0 b1 b2 : Bool)
    (ha : sg a0 * t0 + sg a1 * t1 + sg a2 * t2 = 0)
    (hb : sg b0 * t0 + sg b1 * t1 + sg b2 * t2 = 0) :
    (b0 = a0 ∧ b1 = a1 ∧ b2 = a2) ∨ (b0 = !a0 ∧ b1 = !a1 ∧ b2 = !a2) := by
  cases a0 <;> cases a1 <;> cases a2 <;> cases b0 <;> cases b1 <;> cases b2 <;>
    simp only [sg, ↓reduceIte, Bool.false_eq_true] at ha hb <;> simp <;>
    first
    | exact h0 (by linarith)
    | exact h1 (by linarith)
    | exact h2 (by linarith)

private theorem resPat_unique' (ℓ : Fin 3 → Mode) (hfast : ∀ j, ℓ j 2 ≠ 0)
    {s s' : Fin 3 → Sgn} (hs : ResPat ℓ s) (hs' : ResPat ℓ s') :
    s' = s ∨ s' = fun j => !s j := by
  have ht : ∀ j, (ℓ j 2 : ℝ) * absk (ℓ j) ≠ 0 := by
    intro j
    have hj : ℓ j ≠ 0 := fun h => hfast j (by simp [h])
    have : 0 < absk (ℓ j) := lt_of_lt_of_le one_pos (one_le_absk hj)
    exact mul_ne_zero (by exact_mod_cast hfast j) this.ne'
  unfold ResPat lam at hs hs'
  simp only [Fin.sum_univ_three, mul_assoc] at hs hs'
  rcases pat_aux' _ _ _ (ht 0) (ht 1) (ht 2) _ _ _ _ _ _ hs hs' with h | h
  · left
    funext j
    fin_cases j
    exacts [h.1, h.2.1, h.2.2]
  · right
    funext j
    fin_cases j
    exacts [h.1, h.2.1, h.2.2]

private theorem gammaR_sq_le (n k : Mode) (hk : SFib n k) :
    gammaR ![-k - n, k, n] ^ 2 ≤ ∑ s : Sgn × Sgn × Sgn,
      if phase3 s.1 s.2.1 s.2.2 (-k - n) k n = 0 then
        gammaCoef s.1 s.2.1 s.2.2 (-k - n) k n ^ 2 else 0 := by
  classical
  set ℓ : Fin 3 → Mode := ![-k - n, k, n] with hℓ
  set a : (Fin 3 → Sgn) → ℝ := fun s => if ResPat ℓ s then gammaC ℓ s else 0 with ha
  have hRHS : (∑ s : Sgn × Sgn × Sgn,
      if phase3 s.1 s.2.1 s.2.2 (-k - n) k n = 0 then
        gammaCoef s.1 s.2.1 s.2.2 (-k - n) k n ^ 2 else 0) = ∑ s, a s ^ 2 := by
    refine (Fintype.sum_equiv patEquiv _ _ fun s => ?_).symm
    change _ = if phase3 (s 0) (s 1) (s 2) (-k - n) k n = 0 then
      gammaCoef (s 0) (s 1) (s 2) (-k - n) k n ^ 2 else 0
    simp only [ha, hℓ, resPat_iff, gammaC_eq]
    split_ifs <;> simp
  rw [hRHS]
  have hnn : 0 ≤ ∑ s, a s ^ 2 := Finset.sum_nonneg fun s _ => sq_nonneg _
  by_cases h : ∃ s, ResPat ℓ s
  · obtain ⟨s0, hs0⟩ := h
    have hfast : ∀ j, ℓ j 2 ≠ 0 := by
      intro j; fin_cases j
      exacts [hk.2.2.2.2, hk.2.2.2.1, hk.2.2.1]
    have hne : (fun j => !s0 j) ≠ s0 := by
      intro he; have := congrFun he 0; cases h0 : s0 0 <;> simp [h0] at this
    have hpair : ({s0, fun j => !s0 j} : Finset (Fin 3 → Sgn)) ⊆ Finset.univ :=
      Finset.subset_univ _
    have hsum : ∑ s, a s = ∑ s ∈ {s0, fun j => !s0 j}, a s := by
      refine (Finset.sum_subset hpair fun s _ hs => ?_).symm
      simp only [ha]
      refine ite_eq_right_iff.mpr fun hs' => ?_
      rcases resPat_unique' ℓ hfast hs0 hs' with h | h <;> simp [h] at hs
    have hneg : a (fun j => !s0 j) = a s0 := by
      simp only [ha, resPat_neg', gammaC_neg']
    have hg : gammaR ℓ = a s0 := by
      rw [gammaR, hsum, Finset.sum_pair hne.symm, hneg]; ring
    have h2 : ∑ s ∈ {s0, fun j => !s0 j}, a s ^ 2 ≤ ∑ s, a s ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hpair fun s _ _ => sq_nonneg _
    rw [Finset.sum_pair hne.symm, hneg] at h2
    rw [hg]; nlinarith [sq_nonneg (a s0)]
  · push Not at h
    have hg : gammaR ℓ = 0 := by
      rw [gammaR]; simp [h]
    rw [hg]; simpa using hnn

private theorem fst_eq_of_mem {n : Mode} {p : Mode × Mode} (hp : p ∈ sortedFibre n) :
    p.1 = -p.2 - n := by
  classical
  simp only [sortedFibre, Finset.mem_filter] at hp
  have h := hp.2.1
  rw [← sub_eq_zero, ← h]; abel

/-- The resonant-layer count is dominated by the eight-pattern count. -/
theorem Wfib_le_WfibA (n : Mode) : Wfib n ≤ WfibA n := by
  classical
  set S : Finset Mode := (sortedFibre n).image Prod.snd with hS
  have hmemS : ∀ k, k ∈ S → SFib n k := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    rw [sFib_iff, ← fst_eq_of_mem hp]
    exact hp
  have hW : Wfib n = ∑ k ∈ S, if SFib n k then gammaR ![-k - n, k, n] ^ 2 else 0 := by
    rw [Wfib]
    refine tsum_eq_sum fun k hk => ite_eq_right_iff.mpr fun h => absurd ?_ hk
    exact Finset.mem_image.mpr ⟨_, (sFib_iff n k).mp h, rfl⟩
  have hA : WfibA n = ∑ k ∈ S, ∑ s : Sgn × Sgn × Sgn,
      if phase3 s.1 s.2.1 s.2.2 (-k - n) k n = 0 then
        gammaCoef s.1 s.2.1 s.2.2 (-k - n) k n ^ 2 else 0 := by
    rw [WfibA, hS, Finset.sum_image]
    · refine Finset.sum_congr rfl fun p hp => ?_
      rw [fst_eq_of_mem hp]
    · intro p hp q hq hpq
      exact Prod.ext (by rw [fst_eq_of_mem hp, fst_eq_of_mem hq, hpq]) hpq
  rw [hW, hA]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [ite_eq_left_iff.mpr fun h => absurd (hmemS k hk) h]
  exact gammaR_sq_le n k (hmemS k hk)

/-! ### Bookkeeping for `quant_weighted` -/

private theorem mem_sortedFibre' {n m k : Mode} (hp : (m, k) ∈ sortedFibre n) :
    m + k + n = 0 ∧ nsqZ m ≤ nsqZ k ∧ nsqZ k ≤ nsqZ n ∧ m 2 ≠ 0 ∧ k 2 ≠ 0 ∧ n 2 ≠ 0 := by
  classical
  simp only [sortedFibre, Finset.mem_filter] at hp
  exact hp.2

private theorem abs_sg_mul (a : Sgn) (x : ℝ) (hx : 0 ≤ x) : |sg a * x| = x := by
  cases a <;> simp [sg, abs_of_nonneg hx]

/-- The coefficient of a sorted fast triad is at most `2`. -/
private theorem gammaCoef_sq_le (a b c : Sgn) {m k n : Mode} (hp : (m, k) ∈ sortedFibre n) :
    gammaCoef a b c m k n ^ 2 ≤ 4 := by
  obtain ⟨hsum, hmk, hkn, hm3, -, -⟩ := mem_sortedFibre' hp
  have hm0 : m ≠ 0 := fun h => hm3 (by simp [h])
  have hX : 0 < absk m := lt_of_lt_of_le one_pos (one_le_absk hm0)
  have hXY : absk m ≤ absk k := (absk_le_iff m k).mpr hmk
  have hYZ : absk k ≤ absk n := (absk_le_iff k n).mpr hkn
  have hn : n = -(m + k) := by rw [← sub_eq_zero, ← hsum]; abel
  have hZ : absk n ≤ absk m + absk k := by rw [hn, absk_neg]; exact absk_add_le m k
  have hD0 : 0 ≤ crossAbs m k := Real.sqrt_nonneg _
  have hD : crossAbs m k ≤ absk m * absk k := by
    rw [crossAbs, absk_eq_sqrt_nsqZ, absk_eq_sqrt_nsqZ,
      ← Real.sqrt_mul (by exact_mod_cast nsqZ_nonneg m)]
    refine Real.sqrt_le_sqrt ?_
    push_cast
    nlinarith [sq_nonneg (dotZ m k : ℝ)]
  have key := gamma_bound hX hXY hYZ hZ hD0 hD (abs_sg_mul a _ (absk_nonneg m))
    (abs_sg_mul b _ (absk_nonneg k)) (abs_sg_mul c _ (absk_nonneg n))
  have hP : 0 < (absk m * absk k * absk n) ^ 2 := by
    have : 0 < absk k := hX.trans_le hXY
    have : 0 < absk n := this.trans_le hYZ
    positivity
  have hs : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hg0 : 0 ≤ gammaCoef a b c m k n := by
    simp only [gammaCoef]; positivity
  have hg2 : gammaCoef a b c m k n ≤ 2 := by
    simp only [gammaCoef]
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith

/-- The `g`-decomposition of the weighted fibre. -/
private theorem WfibA_eq_sum_Wg (Δ : ℕ) (n : Mode) (hn : n 2 ≠ 0) :
    WfibA n = ∑ g ∈ (n 2).natAbs.divisors, Wg Δ n g := by
  classical
  simp only [WfibA, Wg]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp_rw [ite_and]
  rw [Finset.sum_ite_irrel]
  split_ifs with h
  · rw [Finset.sum_ite_eq, ite_eq_left_iff.mpr fun h' => absurd (Nat.mem_divisors.mpr
      ⟨Nat.gcd_dvd_left _ _, Int.natAbs_ne_zero.mpr hn⟩) h']
  · simp


/-- Active middle legs with relative signs `(s₂, s₃)` and `gcd(v, t) = g`. -/
private noncomputable def gPts (Δ : ℕ) (n : Mode) (s2 s3 : ℤ) (g : ℕ) : Finset Mode := by
  classical
  exact (activePts n s2 s3).filter fun k => Nat.gcd (n 2).natAbs (tOf Δ s2 n k).natAbs = g

private theorem mem_activePts {n k : Mode} {s2 s3 : ℤ} :
    k ∈ activePts n s2 s3 ↔ k ∈ modeBox (Nat.sqrt (nsqZ n).toNat) ∧
      (-k - n, k) ∈ sortedFibre n ∧ ∃ a b c : Sgn, sgZ a * sgZ b = s2 ∧ sgZ c * sgZ b = s3 ∧
        phase3 a b c (-k - n) k n = 0 ∧ gammaCoef a b c (-k - n) k n ≠ 0 := by
  classical
  simp only [activePts, Finset.mem_filter]

/-- `W_g` is at most `4` times the number of active points with `gcd(v, t) = g`. -/
private theorem Wg_le_card (Δ : ℕ) (n : Mode) (g : ℕ) :
    Wg Δ n g ≤ 4 * ∑ s : Sgn × Sgn × Sgn,
      ((gPts Δ n (sgZ s.1 * sgZ s.2.1) (sgZ s.2.2 * sgZ s.2.1) g).card : ℝ) := by
  classical
  simp only [Wg]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ => ?_
  set G := gPts Δ n (sgZ s.1 * sgZ s.2.1) (sgZ s.2.2 * sgZ s.2.1) g with hG
  calc _ ≤ ∑ p ∈ sortedFibre n, if p.2 ∈ G then (4 : ℝ) else 0 := by
        refine Finset.sum_le_sum fun p hp => ?_
        split_ifs with h1 h2 h2
        · exact gammaCoef_sq_le _ _ _ hp
        · have hp' : (-p.2 - n, p.2) ∈ sortedFibre n := by rw [← fst_eq_of_mem hp]; exact hp
          rw [fst_eq_of_mem hp] at h1
          by_cases hγ : gammaCoef s.1 s.2.1 s.2.2 p.1 p.2 n = 0
          · rw [hγ]; norm_num
          · exfalso; apply h2
            rw [fst_eq_of_mem hp] at hγ
            simp only [hG, gPts, Finset.mem_filter, mem_activePts]
            refine ⟨⟨?_, hp', s.1, s.2.1, s.2.2, rfl, rfl, h1.1, hγ⟩, h1.2⟩
            have := hp
            simp only [sortedFibre, Finset.mem_filter, Finset.mem_product] at this
            exact this.1.2
        · norm_num
        · exact le_rfl
    _ = 4 * ((sortedFibre n).filter fun p => p.2 ∈ G).card := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ 4 * (G.card : ℝ) := by
        gcongr
        refine Finset.card_le_card_of_injOn Prod.snd (fun p hp => ?_) (fun p hp q hq hpq => ?_)
        · exact (Finset.mem_filter.mp hp).2
        · have hp' := (Finset.mem_filter.mp hp).1
          have hq' := (Finset.mem_filter.mp hq).1
          exact Prod.ext (by rw [fst_eq_of_mem hp', fst_eq_of_mem hq', hpq]) hpq

private theorem xOf_mono (Δ : ℕ) {k l : Mode} (h : nsqZ k ≤ nsqZ l) : xOf Δ k ≤ xOf Δ l := by
  unfold xOf
  exact_mod_cast Nat.sqrt_le_sqrt (Nat.div_le_div_right (Int.toNat_le_toNat h))

private theorem xOf_eq (Δ z : ℕ) (hΔ : 0 < Δ) {n : Mode} (hn : nsqZ n = Δ * z ^ 2) :
    xOf Δ n = z := by
  unfold xOf
  have : (nsqZ n).toNat = Δ * z ^ 2 := by rw [hn]; exact_mod_cast Int.toNat_natCast _
  rw [this, Nat.mul_div_cancel_left _ hΔ, Nat.sqrt_eq']

/-- `0 ≤ t ≤ 2z` on the active points. -/
private theorem tOf_bounds {Δ z : ℕ} (hΔ : 0 < Δ) {n k : Mode} (hn : nsqZ n = Δ * z ^ 2)
    {s2 s3 : ℤ} (hk : k ∈ activePts n s2 s3) :
    0 ≤ tOf Δ s2 n k ∧ tOf Δ s2 n k ≤ 2 * z := by
  obtain ⟨-, hp, a, b, c, hs2, -⟩ := mem_activePts.mp hk
  obtain ⟨-, hmk, hkn, -⟩ := mem_sortedFibre' hp
  have h1 := xOf_mono Δ hmk
  have h2 := xOf_mono Δ hkn
  rw [xOf_eq Δ z hΔ hn] at h2
  have h0 : (0 : ℤ) ≤ xOf Δ (-k - n) := Int.natCast_nonneg _
  have hs : s2 = 1 ∨ s2 = -1 := by
    rw [← hs2]; cases a <;> cases b <;> simp [sgZ]
  unfold tOf
  rcases hs with rfl | rfl <;> constructor <;> linarith

private theorem card_filter_mem_le {α β : Type*} [DecidableEq β] (s : Finset α) (f : α → β)
    (A : Finset β) (M : ℝ) (hM : ∀ t ∈ A, ((s.filter fun x => f x = t).card : ℝ) ≤ M) :
    ((s.filter fun x => f x ∈ A).card : ℝ) ≤ A.card * M := by
  classical
  have hsub : (s.filter fun x => f x ∈ A) ⊆ A.biUnion fun t => s.filter fun x => f x = t := by
    intro x hx
    simp only [Finset.mem_filter] at hx
    exact Finset.mem_biUnion.mpr ⟨f x, hx.2, Finset.mem_filter.mpr ⟨hx.1, rfl⟩⟩
  calc ((s.filter fun x => f x ∈ A).card : ℝ)
      ≤ ((A.biUnion fun t => s.filter fun x => f x = t).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ t ∈ A, ((s.filter fun x => f x = t).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ t ∈ A, M := Finset.sum_le_sum hM
    _ = A.card * M := by rw [Finset.sum_const, nsmul_eq_mul]

/-- Multiples of `g` in an integer interval. -/
private theorem card_multiples_le (a b : ℤ) (g : ℕ) (hg : 0 < g) (hab : a ≤ b) :
    (((Finset.Icc a b).filter fun t => (g : ℤ) ∣ t).card : ℝ) ≤ (b - a) / g + 2 := by
  have hg' : (0 : ℤ) < g := by exact_mod_cast hg
  have hc : ((Finset.Icc a b).filter fun t => (g : ℤ) ∣ t).card ≤
      (Finset.Icc (a / g) (b / g)).card := by
    refine Finset.card_le_card_of_injOn (fun t => t / g) (fun t ht => ?_) (fun t ht u hu htu => ?_)
    · simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at ht
      simp only [Finset.coe_Icc, Set.mem_Icc]
      exact ⟨Int.ediv_le_ediv hg' ht.1.1, Int.ediv_le_ediv hg' ht.1.2⟩
    · simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at ht hu
      simp only at htu
      rw [← Int.ediv_mul_cancel ht.2, ← Int.ediv_mul_cancel hu.2, htu]
  have hq : a / g ≤ b / g := Int.ediv_le_ediv hg' hab
  rw [Int.card_Icc] at hc
  have h1 := Int.mul_ediv_add_emod a g
  have h2 := Int.mul_ediv_add_emod b g
  have h3 := Int.emod_nonneg a hg'.ne'
  have h4 := Int.emod_lt_of_pos a hg'
  have h5 := Int.emod_nonneg b hg'.ne'
  have key : ((g : ℤ) : ℝ) * ((b / g : ℤ) - (a / g : ℤ)) < (b - a) + g := by
    have : (g : ℤ) * (b / g - a / g) < b - a + g := by nlinarith
    exact_mod_cast this
  have hcR : (((Finset.Icc a b).filter fun t => (g : ℤ) ∣ t).card : ℝ) ≤
      ((b / g : ℤ) : ℝ) + 1 - (a / g : ℤ) := by
    have : ((((Finset.Icc a b).filter fun t => (g : ℤ) ∣ t).card : ℕ) : ℤ) ≤ b / g + 1 - a / g := by
      have := Int.toNat_of_nonneg (show 0 ≤ b / g + 1 - a / g by omega)
      omega
    exact_mod_cast this
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have : ((b / g : ℤ) : ℝ) - (a / g : ℤ) < (b - a) / g + 1 := by
    rw [div_add_one hgR.ne', lt_div_iff₀ hgR]
    push_cast at key ⊢
    linarith
  linarith

private theorem gPts_sub (Δ : ℕ) (n : Mode) (s2 s3 : ℤ) (g : ℕ) :
    gPts Δ n s2 s3 g ⊆ activePts n s2 s3 := by
  classical
  intro k hk
  simp only [gPts, Finset.mem_filter] at hk
  exact hk.1

private theorem n2_ne_of_active {n k : Mode} {s2 s3 : ℤ} (hk : k ∈ activePts n s2 s3) :
    n 2 ≠ 0 := by
  obtain ⟨-, hp, -⟩ := mem_activePts.mp hk
  exact (mem_sortedFibre' hp).2.2.2.2.2

/-- The parabolic part: at most two `t`, each costing `N^{1/2+ε}`. -/
private theorem parabolic_part (hP : PlaneCurveCount) : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (n : Mode) (Δ z : ℕ) (s2 s3 : ℤ) (g : ℕ), Squarefree Δ → nsqZ n = Δ * z ^ 2 →
      (((gPts Δ n s2 s3 g).filter fun k => caOf Δ z (n 2) (tOf Δ s2 n k) = 0).card : ℝ) ≤
        2 * (C * max 2 (absk n) ^ ((1 : ℝ) / 2 + ε)) := by
  classical
  intro ε hε
  obtain ⟨C, hC0, hC⟩ := parabolic_t_count hP ε hε
  refine ⟨C, hC0, fun n Δ z s2 s3 g hΔ hn => ?_⟩
  have hΔ0 : 0 < Δ := Nat.pos_of_ne_zero hΔ.ne_zero
  set A : Finset ℤ := (Finset.Icc (1 : ℤ) (2 * z)).filter fun t =>
    -((Δ : ℤ) * t ^ 2) ^ 2 + ((Δ : ℤ) * (z : ℤ) ^ 2 - 3 * n 2 ^ 2) * ((Δ : ℤ) * t ^ 2) -
      (Δ : ℤ) * (z : ℤ) ^ 2 * n 2 ^ 2 = 0 with hA
  have hAc : A.card ≤ 2 := parabolic_card (Δ : ℤ) (z : ℤ) (n 2) (by exact_mod_cast hΔ0)
  have hsub : ((gPts Δ n s2 s3 g).filter fun k => caOf Δ z (n 2) (tOf Δ s2 n k) = 0) ⊆
      (gPts Δ n s2 s3 g).filter fun k => tOf Δ s2 n k ∈ A := by
    intro k hk
    simp only [Finset.mem_filter] at hk ⊢
    refine ⟨hk.1, ?_⟩
    have hact := gPts_sub Δ n s2 s3 g hk.1
    obtain ⟨h0, h1⟩ := tOf_bounds hΔ0 hn hact
    have hn2 := n2_ne_of_active hact
    have hca := hk.2
    simp only [caOf] at hca
    have hz : (0 : ℤ) < z := by
      rcases Nat.eq_zero_or_pos z with h | h
      · exfalso
        have : nsqZ n = 0 := by rw [hn, h]; simp
        have h2 : n 2 ^ 2 ≤ nsqZ n := by
          simp only [nsqZ, Fin.sum_univ_three]; nlinarith [sq_nonneg (n 0), sq_nonneg (n 1)]
        have : n 2 ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
        exact hn2 (pow_eq_zero_iff two_ne_zero |>.mp this)
      · exact_mod_cast h
    rw [hA, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, h1⟩, by linarith⟩
    by_contra ht
    have ht0 : tOf Δ s2 n k = 0 := by omega
    rw [ht0] at hca
    have : (Δ : ℤ) * (z : ℤ) ^ 2 * n 2 ^ 2 = 0 := by linarith
    have hΔz : (0 : ℤ) < (Δ : ℤ) * (z : ℤ) ^ 2 * n 2 ^ 2 := by
      have : (0 : ℤ) < Δ := by exact_mod_cast hΔ0
      positivity
    linarith
  calc _ ≤ (((gPts Δ n s2 s3 g).filter fun k => tOf Δ s2 n k ∈ A).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ A.card * (C * max 2 (absk n) ^ ((1 : ℝ) / 2 + ε)) := by
        refine card_filter_mem_le _ _ _ _ fun t _ => ?_
        refine le_trans ?_ (hC n Δ (z : ℤ) t s2 s3 hΔ (by rw [hn]))
        exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (gPts_sub _ _ _ _ _))
    _ ≤ 2 * (C * max 2 (absk n) ^ ((1 : ℝ) / 2 + ε)) := by
        have : (A.card : ℝ) ≤ 2 := by exact_mod_cast hAc
        have : 0 ≤ C * max 2 (absk n) ^ ((1 : ℝ) / 2 + ε) := by positivity
        nlinarith

/-- The non-parabolic part over a set `A` of values of `t`. -/
private theorem nonpar_part (hQ : QuadraticNormCount) : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 ≤ K ∧
    ∀ (n : Mode) (Δ z : ℕ) (s2 s3 : ℤ) (g : ℕ) (A : Finset ℤ), Squarefree Δ →
      nsqZ n = Δ * z ^ 2 →
      (((gPts Δ n s2 s3 g).filter fun k => tOf Δ s2 n k ∈ A ∧
        caOf Δ z (n 2) (tOf Δ s2 n k) ≠ 0).card : ℝ) ≤ A.card * (K * (nsqZ n : ℝ) ^ ε) := by
  classical
  intro ε hε
  obtain ⟨K, hK0, hK⟩ := fixed_t_count hQ ε hε
  refine ⟨K, hK0, fun n Δ z s2 s3 g A hΔ hn => ?_⟩
  have hM : 0 ≤ K * (nsqZ n : ℝ) ^ ε :=
    mul_nonneg hK0 (Real.rpow_nonneg (by exact_mod_cast nsqZ_nonneg n) _)
  calc _ ≤ (((gPts Δ n s2 s3 g).filter fun k =>
          tOf Δ s2 n k ∈ A.filter fun t => caOf Δ z (n 2) t ≠ 0).card : ℝ) := by
        refine le_of_eq ?_
        congr 2
        ext k; simp only [Finset.mem_filter]
    _ ≤ (A.filter fun t => caOf Δ z (n 2) t ≠ 0).card * (K * (nsqZ n : ℝ) ^ ε) := by
        refine card_filter_mem_le _ _ _ _ fun t ht => ?_
        refine le_trans ?_ (hK n Δ (z : ℤ) t s2 s3 hΔ (by rw [hn])
          (Finset.mem_filter.mp ht).2)
        exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (gPts_sub _ _ _ _ _))
    _ ≤ A.card * (K * (nsqZ n : ℝ) ^ ε) := by
        gcongr
        exact Finset.filter_subset _ _

private theorem z_le_absk {n : Mode} {Δ z : ℕ} (hΔ : 0 < Δ) (hn : nsqZ n = Δ * z ^ 2) :
    (z : ℝ) ≤ absk n := by
  rw [absk_eq_sqrt_nsqZ, hn]
  refine Real.le_sqrt_of_sq_le ?_
  push_cast
  have : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  nlinarith [sq_nonneg (z : ℝ)]

private theorem nsqZ_eq_sq (n : Mode) : (nsqZ n : ℝ) = absk n ^ 2 := by
  rw [absk_eq_sqrt_nsqZ, Real.sq_sqrt (by exact_mod_cast nsqZ_nonneg n)]

private theorem mem_gPts_facts {Δ z : ℕ} (hΔ : 0 < Δ) {n k : Mode} (hn : nsqZ n = Δ * z ^ 2)
    {s2 s3 : ℤ} {g : ℕ} (hk : k ∈ gPts Δ n s2 s3 g) :
    (g : ℤ) ∣ tOf Δ s2 n k ∧ 0 ≤ tOf Δ s2 n k ∧ tOf Δ s2 n k ≤ 2 * z := by
  classical
  have hk' := hk
  simp only [gPts, Finset.mem_filter] at hk'
  obtain ⟨h0, h1⟩ := tOf_bounds hΔ hn hk'.1
  refine ⟨?_, h0, h1⟩
  rw [← hk'.2]
  exact Int.natCast_dvd.mpr (Nat.gcd_dvd_right _ _)

/-- The shell bound: the count of active points on an intermediate shell.  It is proved by
`shell_surface_bound'` (`Arith/Surface/ShellBound.lean`). -/
def ShellBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (n : Mode) (Δ z : ℕ) (s2 s3 : ℤ) (g T : ℕ), Squarefree Δ → nsqZ n = Δ * z ^ 2 →
      g ∣ (n 2).natAbs → 1 ≤ T → T ≤ 2 * z → absk n ^ (pStar - 1 / 4) < g →
      absk n ^ pStar < (T : ℝ) / g →
      ((((activePts n s2 s3).filter fun k =>
          Nat.gcd (n 2).natAbs (tOf Δ s2 n k).natAbs = g).filter fun k =>
        (T : ℤ) ≤ tOf Δ s2 n k ∧ tOf Δ s2 n k < 2 * T ∧
          caOf Δ z (n 2) (tOf Δ s2 n k) ≠ 0).card : ℝ) ≤ C * absk n ^ (pStar + ε)

/-- The count of active points with `gcd(v, t) = g`, for `g > N^{p*−1/4}`. -/
private theorem gPts_card_le (hP : PlaneCurveCount) (hB : ShellBound)
    (hQ : QuadraticNormCount) : ∀ ε : ℝ, 0 < ε →
    ∃ Cp K Cs : ℝ, 0 ≤ Cp ∧ 0 ≤ K ∧ 0 ≤ Cs ∧
    ∀ (n : Mode) (Δ z : ℕ) (s2 s3 : ℤ) (g : ℕ), Squarefree Δ → nsqZ n = Δ * z ^ 2 → 1 ≤ z →
      g ∣ (n 2).natAbs → absk n ^ (pStar - 1 / 4) < g →
      ((gPts Δ n s2 s3 g).card : ℝ) ≤ 2 * (Cp * max 2 (absk n) ^ ((1 : ℝ) / 2 + ε)) +
        ((Nat.log 2 (2 * z) : ℝ) + 2) * ((2 * absk n ^ pStar + 2) * (K * (nsqZ n : ℝ) ^ ε) +
          Cs * absk n ^ (pStar + ε)) := by
  classical
  intro ε hε
  obtain ⟨Cp, hCp0, hCp⟩ := parabolic_part hP ε hε
  obtain ⟨K, hK0, hK⟩ := nonpar_part hQ ε hε
  obtain ⟨Cs, hCs0, hCs⟩ := hB ε hε
  refine ⟨Cp, K, Cs, hCp0, hK0, hCs0, fun n Δ z s2 s3 g hΔ hn hz hg hgl => ?_⟩
  have hΔ0 : 0 < Δ := Nat.pos_of_ne_zero hΔ.ne_zero
  set G := gPts Δ n s2 s3 g with hG
  set N := absk n with hN
  set Q := K * (nsqZ n : ℝ) ^ ε with hQdef
  set R := (2 * N ^ pStar + 2) * Q + Cs * N ^ (pStar + ε) with hR
  have hzN : (z : ℝ) ≤ N := z_le_absk hΔ0 hn
  have hN1 : 1 ≤ N := le_trans (by exact_mod_cast hz) hzN
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN1
  have hQ0 : 0 ≤ Q := mul_nonneg hK0 (Real.rpow_nonneg (by exact_mod_cast nsqZ_nonneg n) _)
  have hNp0 : 0 ≤ N ^ pStar := Real.rpow_nonneg hN0.le _
  have hQR : (2 * N ^ pStar + 2) * Q ≤ R := by
    have : 0 ≤ Cs * N ^ (pStar + ε) := mul_nonneg hCs0 (Real.rpow_nonneg hN0.le _)
    linarith
  have hR0 : 0 ≤ R := le_trans (by positivity) hQR
  have hg0 : (0 : ℝ) < g := lt_of_le_of_lt (Real.rpow_nonneg hN0.le _) hgl
  have hg0' : 0 < g := by exact_mod_cast hg0
  -- multiples of `g` in `[a, b]` cost `((b - a)/g + 2) Q`
  have hmult : ∀ a b : ℕ, a ≤ b → (b - a : ℝ) / g ≤ 2 * N ^ pStar →
      ((G.filter fun k => (a : ℤ) ≤ tOf Δ s2 n k ∧ tOf Δ s2 n k ≤ b ∧
        caOf Δ z (n 2) (tOf Δ s2 n k) ≠ 0).card : ℝ) ≤ R := by
    intro a b hab hb
    set A := (Finset.Icc (a : ℤ) b).filter fun t => (g : ℤ) ∣ t
    have hsub : (G.filter fun k => (a : ℤ) ≤ tOf Δ s2 n k ∧ tOf Δ s2 n k ≤ b ∧
        caOf Δ z (n 2) (tOf Δ s2 n k) ≠ 0) ⊆ G.filter fun k => tOf Δ s2 n k ∈ A ∧
        caOf Δ z (n 2) (tOf Δ s2 n k) ≠ 0 := by
      intro k hk
      simp only [Finset.mem_filter] at hk ⊢
      refine ⟨hk.1, ?_, hk.2.2.2⟩
      simp only [A, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hk.2.1, hk.2.2.1⟩, (mem_gPts_facts hΔ0 hn hk.1).1⟩
    have hA := card_multiples_le (a : ℤ) b g hg0' (by exact_mod_cast hab)
    push_cast at hA
    calc _ ≤ ((G.filter fun k => tOf Δ s2 n k ∈ A ∧
          caOf Δ z (n 2) (tOf Δ s2 n k) ≠ 0).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ A.card * Q := hK n Δ z s2 s3 g A hΔ hn
      _ ≤ (2 * N ^ pStar + 2) * Q := by
          gcongr; linarith
      _ ≤ R := hQR
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := G) (fun k => caOf Δ z (n 2) (tOf Δ s2 n k) = 0)
  have hpar := hCp n Δ z s2 s3 g hΔ hn
  have hnp : ((G.filter fun k => ¬ caOf Δ z (n 2) (tOf Δ s2 n k) = 0).card : ℝ) ≤
      ((Nat.log 2 (2 * z) : ℝ) + 2) * R := by
    have hL0 : (0 : ℝ) ≤ Nat.log 2 (2 * z) := Nat.cast_nonneg _
    by_cases hbig : N ^ (1 - pStar) ≤ g
    · have hsub : (G.filter fun k => ¬ caOf Δ z (n 2) (tOf Δ s2 n k) = 0) ⊆
          G.filter fun k => ((0 : ℕ) : ℤ) ≤ tOf Δ s2 n k ∧ tOf Δ s2 n k ≤ ((2 * z : ℕ) : ℤ) ∧
            caOf Δ z (n 2) (tOf Δ s2 n k) ≠ 0 := by
        intro k hk
        simp only [Finset.mem_filter] at hk ⊢
        obtain ⟨-, h0, h1⟩ := mem_gPts_facts hΔ0 hn hk.1
        exact ⟨hk.1, by simpa using h0, by push_cast; exact h1, hk.2⟩
      have hb : ((2 * z : ℕ) - (0 : ℕ) : ℝ) / g ≤ 2 * N ^ pStar := by
        rw [div_le_iff₀ hg0]
        have : N = N ^ pStar * N ^ (1 - pStar) := by
          rw [← Real.rpow_add hN0]; simp
        push_cast
        nlinarith [mul_le_mul_of_nonneg_left hbig hNp0]
      calc _ ≤ _ := by exact_mod_cast Finset.card_le_card hsub
        _ ≤ R := hmult 0 (2 * z) (Nat.zero_le _) hb
        _ ≤ ((Nat.log 2 (2 * z) : ℝ) + 2) * R := by nlinarith
    · set J := Nat.log 2 (2 * z) + 1 with hJ
      set X : ℕ → Finset Mode := fun j => G.filter fun k =>
        ((2 ^ j : ℕ) : ℤ) ≤ tOf Δ s2 n k ∧ tOf Δ s2 n k < 2 * ((2 ^ j : ℕ) : ℤ) ∧
          caOf Δ z (n 2) (tOf Δ s2 n k) ≠ 0 with hX
      set X0 := G.filter fun k => tOf Δ s2 n k ∈ ({0} : Finset ℤ) ∧
          caOf Δ z (n 2) (tOf Δ s2 n k) ≠ 0 with hX0
      have hcov : (G.filter fun k => ¬ caOf Δ z (n 2) (tOf Δ s2 n k) = 0) ⊆
          X0 ∪ (Finset.range J).biUnion X := by
        intro k hk
        simp only [Finset.mem_filter] at hk
        obtain ⟨-, h0, h1⟩ := mem_gPts_facts hΔ0 hn hk.1
        rw [Finset.mem_union]
        by_cases ht : tOf Δ s2 n k = 0
        · left
          simp only [hX0, Finset.mem_filter, Finset.mem_singleton]
          exact ⟨hk.1, ht, hk.2⟩
        · right
          set m := (tOf Δ s2 n k).toNat with hm
          have hmt : (m : ℤ) = tOf Δ s2 n k := Int.toNat_of_nonneg h0
          have hm0 : m ≠ 0 := by omega
          have hm2 : m ≤ 2 * z := by omega
          refine Finset.mem_biUnion.mpr ⟨Nat.log 2 m, ?_, ?_⟩
          · rw [Finset.mem_range, hJ]
            exact Nat.lt_succ_of_le (Nat.log_mono_right hm2)
          · simp only [hX, Finset.mem_filter]
            refine ⟨hk.1, ?_, ?_, hk.2⟩
            · rw [← hmt]; exact_mod_cast Nat.pow_log_le_self 2 hm0
            · rw [← hmt]
              have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) m
              rw [pow_succ] at this
              push_cast
              linarith [(by exact_mod_cast this : (m : ℤ) < 2 ^ Nat.log 2 m * 2)]
      have hX0c : (X0.card : ℝ) ≤ Q := by
        have := hK n Δ z s2 s3 g {0} hΔ hn
        rw [Finset.card_singleton, Nat.cast_one, one_mul] at this
        exact this
      have hXj : ∀ j ∈ Finset.range J, ((X j).card : ℝ) ≤ R := by
        intro j hj
        have hjl : j ≤ Nat.log 2 (2 * z) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hT2z : 2 ^ j ≤ 2 * z :=
          le_trans (Nat.pow_le_pow_right (by norm_num) hjl) (Nat.pow_log_le_self 2 (by omega))
        by_cases hT : ((2 ^ j : ℕ) : ℝ) / g ≤ N ^ pStar
        · have hsub : X j ⊆ G.filter fun k => ((2 ^ j : ℕ) : ℤ) ≤ tOf Δ s2 n k ∧
              tOf Δ s2 n k ≤ ((2 * 2 ^ j : ℕ) : ℤ) ∧ caOf Δ z (n 2) (tOf Δ s2 n k) ≠ 0 := by
            intro k hk
            simp only [hX, Finset.mem_filter] at hk ⊢
            refine ⟨hk.1, hk.2.1, ?_, hk.2.2.2⟩
            push_cast at hk ⊢
            linarith [hk.2.2.1]
          have hb : (((2 * 2 ^ j : ℕ) : ℝ) - ((2 ^ j : ℕ) : ℝ)) / g ≤ 2 * N ^ pStar := by
            have : ((2 * 2 ^ j : ℕ) : ℝ) - ((2 ^ j : ℕ) : ℝ) = ((2 ^ j : ℕ) : ℝ) := by
              push_cast; ring
            rw [this]; linarith
          calc _ ≤ _ := by exact_mod_cast Finset.card_le_card hsub
            _ ≤ R := hmult _ _ (by omega) hb
        · have := hCs n Δ z s2 s3 g (2 ^ j) hΔ hn hg Nat.one_le_two_pow hT2z hgl
            (lt_of_not_ge hT)
          have h2 : 0 ≤ (2 * N ^ pStar + 2) * Q := by positivity
          calc ((X j).card : ℝ) ≤ Cs * N ^ (pStar + ε) := this
            _ ≤ R := by linarith
      calc _ ≤ ((X0 ∪ (Finset.range J).biUnion X).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hcov
        _ ≤ (X0.card : ℝ) + ∑ j ∈ Finset.range J, ((X j).card : ℝ) := by
            have h1 := Finset.card_union_le X0 ((Finset.range J).biUnion X)
            have h2 := Finset.card_biUnion_le (s := Finset.range J) (t := X)
            have : ((X0 ∪ (Finset.range J).biUnion X).card : ℝ) ≤
                (X0.card : ℝ) + (((Finset.range J).biUnion X).card : ℝ) := by exact_mod_cast h1
            have h2' : (((Finset.range J).biUnion X).card : ℝ) ≤
                ∑ j ∈ Finset.range J, ((X j).card : ℝ) := by exact_mod_cast h2
            linarith
        _ ≤ Q + J * R := by
            gcongr
            calc ∑ j ∈ Finset.range J, ((X j).card : ℝ) ≤ ∑ _j ∈ Finset.range J, R :=
                  Finset.sum_le_sum hXj
              _ = J * R := by simp
        _ ≤ ((Nat.log 2 (2 * z) : ℝ) + 2) * R := by
            have : Q ≤ R := le_trans (by nlinarith) hQR
            rw [hJ]; push_cast; nlinarith
  have : (G.card : ℝ) = ((G.filter fun k => caOf Δ z (n 2) (tOf Δ s2 n k) = 0).card : ℝ) +
      ((G.filter fun k => ¬ caOf Δ z (n 2) (tOf Δ s2 n k) = 0).card : ℝ) := by
    exact_mod_cast hsplit.symm
  rw [this]
  exact add_le_add hpar hnp

private theorem max2_rpow_le {N a : ℝ} (hN : 1 ≤ N) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    max 2 N ^ a ≤ 2 * N ^ a := by
  have hN0 : 0 ≤ N := by linarith
  calc max 2 N ^ a ≤ (2 * N) ^ a :=
        Real.rpow_le_rpow (by positivity) (max_le (by linarith) (by linarith)) ha0
    _ = 2 ^ a * N ^ a := Real.mul_rpow (by norm_num) hN0
    _ ≤ 2 * N ^ a := by
        gcongr
        calc (2 : ℝ) ^ a ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) ha1
          _ = 2 := Real.rpow_one 2

/-- Logarithmically many dyadic shells. -/
private theorem log_shells_le {ε : ℝ} (hε : 0 < ε) : ∃ CL : ℝ, 0 ≤ CL ∧
    ∀ (z : ℕ) (N : ℝ), 1 ≤ z → (z : ℝ) ≤ N → (Nat.log 2 (2 * z) : ℝ) + 2 ≤ CL * N ^ ε := by
  refine ⟨4 * 2 ^ ε / ε + 2, by positivity, fun z N hz hzN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (by exact_mod_cast hz) hzN
  have hN0 : 0 < N := by linarith
  have hNe : 1 ≤ N ^ ε := Real.one_le_rpow hN1 hε.le
  set L := Nat.log 2 (2 * z)
  have hpow : ((2 : ℝ) ^ L) ≤ 2 * z := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have hlog : (L : ℝ) * Real.log 2 ≤ Real.log (2 * z) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hpow
  have h2 := Real.log_le_rpow_div (x := 2 * (z : ℝ)) (by positivity) hε
  have h3 : (2 * (z : ℝ)) ^ ε ≤ 2 ^ ε * N ^ ε := by
    rw [Real.mul_rpow (by norm_num) (by positivity)]
    gcongr
  have hl2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hL : (L : ℝ) ≤ 2 * (2 ^ ε * N ^ ε / ε) := by
    have : (L : ℝ) * (1 / 2) ≤ 2 ^ ε * N ^ ε / ε := by
      have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
      calc (L : ℝ) * (1 / 2) ≤ L * Real.log 2 := by gcongr
        _ ≤ (2 * (z : ℝ)) ^ ε / ε := hlog.trans h2
        _ ≤ 2 ^ ε * N ^ ε / ε := by gcongr
    linarith
  have : 2 * (2 ^ ε * N ^ ε / ε) = (4 * 2 ^ ε / ε) * N ^ ε / 2 := by ring
  have h4 : 0 ≤ 4 * 2 ^ ε / ε * N ^ ε := by positivity
  nlinarith

/-- The per-`g` bound `W_g ≤ M N^{p* + 3ε}` (the three ranges of `g`). -/
private theorem Wg_le_main (hP : PlaneCurveCount) (hB : ShellBound)
    (hQ : QuadraticNormCount) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 8) : ∃ M : ℝ, 0 ≤ M ∧
    ∀ (n : Mode) (Δ z : ℕ) (g : ℕ), Squarefree Δ → nsqZ n = Δ * z ^ 2 → 1 ≤ z →
      g ∣ (n 2).natAbs → Wg Δ n g ≤ M * absk n ^ (pStar + 3 * ε) := by
  obtain ⟨Cw, hCw0, hCw⟩ := Wg_bound hP ε hε
  obtain ⟨Cp, K, Cs, hCp0, hK0, hCs0, hG⟩ := gPts_card_le hP hB hQ ε hε
  obtain ⟨CL, hCL0, hCL⟩ := log_shells_le hε
  have hp := pStar_bounds
  refine ⟨2 * Cw + 32 * (4 * Cp + CL * (4 * K + Cs)), by positivity,
    fun n Δ z g hΔ hn hz hg => ?_⟩
  have hΔ0 : 0 < Δ := Nat.pos_of_ne_zero hΔ.ne_zero
  set N := absk n with hN
  have hzN : (z : ℝ) ≤ N := z_le_absk hΔ0 hn
  have hN1 : 1 ≤ N := le_trans (by exact_mod_cast hz) hzN
  have hN0 : 0 < N := by linarith
  have hmono : ∀ a b : ℝ, a ≤ b → N ^ a ≤ N ^ b := fun a b h =>
    Real.rpow_le_rpow_of_exponent_le hN1 h
  have hE0 : 0 ≤ N ^ (pStar + 3 * ε) := Real.rpow_nonneg hN0.le _
  by_cases hsmall : (g : ℝ) ≤ N ^ (pStar - 1 / 4)
  · -- range (R1): `W_g ≤ C N^{1/4+ε} g`
    have h1 := hCw n Δ z g hΔ (by rw [hn])
    have h2 : max 2 N ^ ((1 : ℝ) / 4 + ε) ≤ 2 * N ^ ((1 : ℝ) / 4 + ε) :=
      max2_rpow_le hN1 (by positivity) (by linarith)
    have h3 : N ^ ((1 : ℝ) / 4 + ε) * N ^ (pStar - 1 / 4) ≤ N ^ (pStar + 3 * ε) := by
      rw [← Real.rpow_add hN0]; exact hmono _ _ (by linarith)
    have hm0 : 0 ≤ max 2 N ^ ((1 : ℝ) / 4 + ε) := by positivity
    have hW : Wg Δ n g ≤ 2 * Cw * N ^ (pStar + 3 * ε) := by
      calc Wg Δ n g ≤ Cw * max 2 N ^ ((1 : ℝ) / 4 + ε) * g := h1
        _ ≤ Cw * (2 * N ^ ((1 : ℝ) / 4 + ε)) * N ^ (pStar - 1 / 4) := by gcongr
        _ = 2 * Cw * (N ^ ((1 : ℝ) / 4 + ε) * N ^ (pStar - 1 / 4)) := by ring
        _ ≤ 2 * Cw * N ^ (pStar + 3 * ε) := by gcongr
    have : 0 ≤ 32 * (4 * Cp + CL * (4 * K + Cs)) * N ^ (pStar + 3 * ε) := by positivity
    nlinarith
  · push Not at hsmall
    -- ranges (R2) and (R3): count the active points
    have hB : ∀ s2 s3 : ℤ, ((gPts Δ n s2 s3 g).card : ℝ) ≤
        (4 * Cp + CL * (4 * K + Cs)) * N ^ (pStar + 3 * ε) := by
      intro s2 s3
      have h := hG n Δ z s2 s3 g hΔ hn hz hg hsmall
      have hL := hCL z N hz hzN
      have hpar : max 2 N ^ ((1 : ℝ) / 2 + ε) ≤ 2 * N ^ (pStar + 3 * ε) :=
        (max2_rpow_le hN1 (by positivity) (by linarith)).trans
          (by have := hmono ((1 : ℝ) / 2 + ε) (pStar + 3 * ε) (by linarith); linarith)
      have hnsq : (nsqZ n : ℝ) ^ ε = N ^ (2 * ε) := by
        rw [nsqZ_eq_sq, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
      have hp1 : 2 * N ^ pStar + 2 ≤ 4 * N ^ pStar := by
        have : 1 ≤ N ^ pStar := Real.one_le_rpow hN1 (by linarith)
        linarith
      have hA : (2 * N ^ pStar + 2) * (K * (nsqZ n : ℝ) ^ ε) + Cs * N ^ (pStar + ε) ≤
          (4 * K + Cs) * N ^ (pStar + 2 * ε) := by
        rw [hnsq]
        have e1 : N ^ pStar * N ^ (2 * ε) = N ^ (pStar + 2 * ε) := (Real.rpow_add hN0 _ _).symm
        have e2 : N ^ (pStar + ε) ≤ N ^ (pStar + 2 * ε) := hmono _ _ (by linarith)
        have : 0 ≤ K * N ^ (2 * ε) := by positivity
        have : (2 * N ^ pStar + 2) * (K * N ^ (2 * ε)) ≤ 4 * K * N ^ (pStar + 2 * ε) := by
          rw [← e1]; nlinarith
        nlinarith
      have hA0 : 0 ≤ (2 * N ^ pStar + 2) * (K * (nsqZ n : ℝ) ^ ε) + Cs * N ^ (pStar + ε) := by
        have : 0 ≤ (nsqZ n : ℝ) ^ ε := Real.rpow_nonneg (by exact_mod_cast nsqZ_nonneg n) _
        have : 0 ≤ N ^ pStar := Real.rpow_nonneg hN0.le _
        positivity
      have e3 : N ^ ε * N ^ (pStar + 2 * ε) = N ^ (pStar + 3 * ε) := by
        rw [← Real.rpow_add hN0]; ring_nf
      have hNe : 0 ≤ N ^ ε := Real.rpow_nonneg hN0.le _
      calc ((gPts Δ n s2 s3 g).card : ℝ)
          ≤ 2 * (Cp * max 2 N ^ ((1 : ℝ) / 2 + ε)) + ((Nat.log 2 (2 * z) : ℝ) + 2) *
            ((2 * N ^ pStar + 2) * (K * (nsqZ n : ℝ) ^ ε) + Cs * N ^ (pStar + ε)) := h
        _ ≤ 2 * (Cp * (2 * N ^ (pStar + 3 * ε))) + (CL * N ^ ε) *
            ((4 * K + Cs) * N ^ (pStar + 2 * ε)) := by
            gcongr
        _ = (4 * Cp + CL * (4 * K + Cs)) * N ^ (pStar + 3 * ε) := by
            rw [← e3]; ring
    have h := Wg_le_card Δ n g
    have hsum : ∑ s : Sgn × Sgn × Sgn,
        ((gPts Δ n (sgZ s.1 * sgZ s.2.1) (sgZ s.2.2 * sgZ s.2.1) g).card : ℝ) ≤
        8 * ((4 * Cp + CL * (4 * K + Cs)) * N ^ (pStar + 3 * ε)) := by
      calc _ ≤ ∑ _s : Sgn × Sgn × Sgn, (4 * Cp + CL * (4 * K + Cs)) * N ^ (pStar + 3 * ε) :=
            Finset.sum_le_sum fun s _ => hB _ _
        _ = _ := by simp
    have : 0 ≤ 2 * Cw * N ^ (pStar + 3 * ε) := by positivity
    nlinarith

theorem weightedCount_of_quantWeighted (h : QuantWeighted) : WeightedCount := by
  intro η hη
  obtain ⟨C, hC, hb⟩ := h η hη
  exact ⟨C, hC, fun n _ => (Wfib_le_WfibA n).trans (hb n)⟩

/-- D7: Lemma quant-weighted, from its inputs. -/
theorem quant_weighted (hP : PlaneCurveCount) (hB : ShellBound) (hQ : QuadraticNormCount) :
    QuantWeighted := by
  intro η hη
  set ε := min (η / 8) (1 / 8) with hεdef
  have hε : 0 < ε := lt_min (by linarith) (by norm_num)
  have hε1 : ε ≤ 1 / 8 := min_le_right _ _
  have hε8 : ε ≤ η / 8 := min_le_left _ _
  obtain ⟨M, hM0, hM⟩ := Wg_le_main hP hB hQ hε hε1
  obtain ⟨Cτ, hCτ0, hCτ⟩ := divisor_bound hε
  refine ⟨Cτ * M, by positivity, fun n => ?_⟩
  have hE0 : 0 ≤ absk n ^ (pStar + η) := Real.rpow_nonneg (absk_nonneg n) _
  by_cases hn2 : n 2 = 0
  · have : WfibA n = 0 := by
      simp only [WfibA]
      refine Finset.sum_eq_zero fun p hp => absurd hn2 ?_
      exact (mem_sortedFibre' (m := p.1) (k := p.2) hp).2.2.2.2.2
    rw [this]; positivity
  · have h2 : n 2 ^ 2 ≤ nsqZ n := by
      simp only [nsqZ, Fin.sum_univ_three]; nlinarith [sq_nonneg (n 0), sq_nonneg (n 1)]
    have hpos : 0 < nsqZ n := lt_of_lt_of_le (by positivity) h2
    obtain ⟨Δ, z, hΔ0, hz0, hbz, hΔ⟩ := Nat.sq_mul_squarefree_of_pos (Int.lt_toNat.mpr hpos)
    have hn : nsqZ n = Δ * z ^ 2 := by
      rw [← Int.toNat_of_nonneg hpos.le, ← hbz]; push_cast; ring
    set N := absk n with hN
    have hzN : (z : ℝ) ≤ N := z_le_absk hΔ0 hn
    have hN1 : 1 ≤ N := le_trans (by exact_mod_cast hz0) hzN
    have hN0 : 0 < N := by linarith
    have hv : (((n 2).natAbs : ℕ) : ℝ) ≤ N := by
      rw [Nat.cast_natAbs, Int.cast_abs]; exact abs_coord_le_absk n 2
    have hv1 : 1 ≤ (n 2).natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hn2)
    have hτ := hCτ _ hv1
    have hτ' : ((n 2).natAbs.divisors.card : ℝ) ≤ Cτ * N ^ ε :=
      hτ.trans (by gcongr)
    rw [WfibA_eq_sum_Wg Δ n hn2]
    have hE : 0 ≤ N ^ (pStar + 3 * ε) := Real.rpow_nonneg hN0.le _
    calc ∑ g ∈ (n 2).natAbs.divisors, Wg Δ n g
        ≤ ∑ _g ∈ (n 2).natAbs.divisors, M * N ^ (pStar + 3 * ε) :=
          Finset.sum_le_sum fun g hg => hM n Δ z g hΔ hn hz0 (Nat.dvd_of_mem_divisors hg)
      _ = ((n 2).natAbs.divisors.card : ℝ) * (M * N ^ (pStar + 3 * ε)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Cτ * N ^ ε) * (M * N ^ (pStar + 3 * ε)) := by gcongr
      _ = Cτ * M * (N ^ ε * N ^ (pStar + 3 * ε)) := by ring
      _ = Cτ * M * N ^ (pStar + 4 * ε) := by
          rw [← Real.rpow_add hN0]; ring_nf
      _ ≤ Cτ * M * N ^ (pStar + η) := by
          gcongr
          linarith

end OVNS.Quant
