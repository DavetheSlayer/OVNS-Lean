import OddViscousNS.Quant.Joint.Metric.Positive

/-!
# The fibered positive layer of the signed metric (step J5, node N1)

The positive estimates of Bodies 33, 36, 38, 39 and LOCAL457 that the seven and thirteen classes of
`Positive.lean` do not cover: an **inverse-first-power exterior** `z/J`, which is not `ℓ¹` on `ℤ³`,
so the common fast vertical must be kept.

## No `ℓ^p ⋆ ℓ^q` Young is needed
The sources use `ℓ^{6/5}`, `ℓ^{16/15}`, `ℓ^{16/9}`, `ℓ^r`, `ℓ^p`.  **All of it but one rule (see
`FibreSub.lean`) is replaced by weighted Cauchy–Schwarz on the index set of the form, plus one
pointwise inequality**, as `sob_conv` replaced `ℓ^{4/3}` in `Joint/Kinetic/GN.lean`.  Two groupings
are enough:
* `cs_out`, output against the rest: `∑ α_l p(l,a,b) u_a v_b β_j ≤ √Z ‖α‖ ‖u‖ ‖v‖ ‖β‖` as soon as
  `∑_{a,b} p(l,a,b)² ≤ Z` for every `l`.  This is `‖u ⋆ v ⋆ β‖`-Young in disguise.
* `cs_mid`, around the intermediate label: `(α_l, u_a)` against `(β_j, v_b)`.

The only thing that remains of the Young exponents is **a kernel sum**, and it is elementary:
the largest of the three lengths can be discarded.  For `x, y, z ≥ 0` the inequality
`(xyz)² ≤ (xy)³ + (xz)³ + (yz)³` (`three_cube_le`, with `x = |a|⁻¹` …) gives
`∑_{a,b} |a|⁻²|b|⁻²|j|⁻² ≤ 3 · 17²`, the `ℓ^{6/5} ⋆ ℓ^{6/5} ⋆ ℓ^{6/5} ⊂ ℓ²` of Body 36.  In the same
way `|a|⁻²|b|^{−2ε} ≤ |a|^{−2−2ε} + |b|^{−2−2ε}` gives the `ℓ^{16/15} ⋆ ℓ^{16/9}` of LOCAL457
(`ε = 1/4`) and the `ℓ^r ⋆ ℓ^p`, `1/r = 1 − η/2`, `1/p = (1 + η)/2` of Bodies 38, 39, with the
sources' constant `ε^{−1/2}`.

## The fibre sums
`Fib w Z`: the sum of `w` along every horizontal plane of `ℤ³` is at most `Z`.  This is uniform in
the vertical, including the vertical `0`, so one lemma pays slow leaves and fast exteriors:
* `fib_w3`: `∑ |j|⁻³ ≤ 17`, Body 36 "the two-dimensional inverse-cubic sum";
* `fib_w4`: `∑ |j|⁻⁴ ≤ 17`, "the uniform inverse-fourth sum";
* `fib_band`: `∑_{|j| ≤ D} |j|⁻² ≤ 9 + 8 ln D`, "the fixed-vertical two-dimensional inverse-square
  shell sum is logarithmic".
The method is the square shells of `Slow/Lattice2D.lean`.
-/

open Finset

noncomputable section

namespace OVNS.Quant.Metric

variable {α β u v f₁ f₂ : Mode → ℝ} {A B U V U₁ U₂ Z Z₁ Z₂ : ℝ}

/-! ### A. Nonnegative families -/

lemma L2B.sq (h : L2B f₁ A) : SB (fun k => f₁ k ^ 2) (A ^ 2) := by
  refine ⟨h.s, ?_⟩
  have h0 : 0 ≤ ∑' k, f₁ k ^ 2 := tsum_nonneg fun k => sq_nonneg _
  calc ∑' k, f₁ k ^ 2 = Real.sqrt (∑' k, f₁ k ^ 2) ^ 2 := (Real.sq_sqrt h0).symm
    _ ≤ A ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h.le 2

/-- **Cauchy–Schwarz** for a nonnegative family, on any index set. -/
lemma SB.cs {ι : Type*} {P Q : ι → ℝ} (hP0 : ∀ x, 0 ≤ P x) (hQ0 : ∀ x, 0 ≤ Q x) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hP : SB (fun x => P x ^ 2) (A ^ 2)) (hQ : SB (fun x => Q x ^ 2) (B ^ 2)) :
    SB (fun x => P x * Q x) (A * B) := by
  have h := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
    hP0 hQ0 (by simpa only [Real.rpow_two] using hP.1) (by simpa only [Real.rpow_two] using hQ.1)
  simp only [Real.rpow_two] at h
  refine ⟨h.1, h.2.trans ?_⟩
  simp only [← Real.sqrt_eq_rpow]
  exact mul_le_mul (Real.sqrt_le_iff.2 ⟨hA, hP.2⟩) (Real.sqrt_le_iff.2 ⟨hB, hQ.2⟩)
    (Real.sqrt_nonneg _) hA

/-- **Tonelli**, for a bound. -/
lemma SB.prod {ι κ : Type*} {H : ι × κ → ℝ} {c : ι → ℝ} {C : ℝ} (h0 : ∀ x, 0 ≤ H x)
    (h1 : ∀ i, SB (fun k => H (i, k)) (c i)) (h2 : SB c C) : SB H C := by
  have hs : Summable H := (summable_prod_of_nonneg h0).2 ⟨fun i => (h1 i).1,
    Summable.of_nonneg_of_le (fun i => tsum_nonneg fun k => h0 _) (fun i => (h1 i).2) h2.1⟩
  refine ⟨hs, ?_⟩
  rw [hs.tsum_prod]
  exact (Summable.tsum_le_tsum (fun i => (h1 i).2) hs.prod h2.1).trans h2.2

/-- Reindexing by a bijection between index types. -/
lemma SB.equiv' {ι κ : Type*} {F : κ → ℝ} {G : ι → ℝ} {C : ℝ} (e : ι ≃ κ) (hF : SB F C)
    (h : ∀ x, G x = F (e x)) : SB G C := by
  have hG : G = fun x => F (e x) := funext h
  rw [hG]
  exact ⟨e.summable_iff.2 hF.1, (e.tsum_eq F).le.trans hF.2⟩

/-- A double sum, the inner one uniformly bounded. -/
lemma SB.prod_mul {a : Mode → ℝ} {K : Mode → Mode → ℝ} {A₁ : ℝ} (ha : SB a A₁) (ha0 : ∀ k, 0 ≤ a k)
    (hK0 : ∀ i k, 0 ≤ K i k) (hK : ∀ i, SB (K i) Z) (hZ : 0 ≤ Z) :
    SB (fun y : Mode × Mode => a y.1 * K y.1 y.2) (A₁ * Z) := by
  have hc : SB (fun i => a i * Z) (A₁ * Z) := by
    refine ⟨ha.1.mul_right Z, ?_⟩
    rw [tsum_mul_right]
    exact mul_le_mul_of_nonneg_right ha.2 hZ
  exact SB.prod (fun y => mul_nonneg (ha0 _) (hK0 _ _)) (fun i => (hK i).const_mul (ha0 i)) hc

/-- Three nested sums, the last one uniformly bounded. -/
lemma SB.tri {a₁ a₂ : Mode → ℝ} {K : I3 → ℝ} {A₁ A₂ : ℝ} (h1 : SB a₁ A₁) (h2 : SB a₂ A₂)
    (h10 : ∀ k, 0 ≤ a₁ k) (h20 : ∀ k, 0 ≤ a₂ k) (hK0 : ∀ x, 0 ≤ K x)
    (hK : ∀ l a, SB (fun b => K (l, a, b)) Z) :
    SB (fun x : I3 => a₁ x.1 * a₂ x.2.1 * K x) (A₁ * A₂ * Z) := by
  have hZ : 0 ≤ Z := (tsum_nonneg fun b => hK0 (0, 0, b)).trans (hK 0 0).2
  have hA2 : 0 ≤ A₂ := (tsum_nonneg h20).trans h2.2
  refine SB.prod (c := fun l => a₁ l * (A₂ * Z))
    (fun x => mul_nonneg (mul_nonneg (h10 _) (h20 _)) (hK0 _)) (fun l => ?_) ?_
  · have e : ∀ y : Mode × Mode, a₁ l * a₂ y.1 * K (l, y.1, y.2) =
        a₁ l * (a₂ y.1 * K (l, y.1, y.2)) := fun y => by ring
    simp only [e]
    refine SB.const_mul ?_ (h10 l)
    refine SB.prod (c := fun a => a₂ a * Z) (fun y => mul_nonneg (h20 _) (hK0 _)) (fun a => ?_) ?_
    · exact (hK l a).const_mul (h20 a)
    · exact ⟨h2.1.mul_right Z, by
        rw [tsum_mul_right]
        exact mul_le_mul_of_nonneg_right h2.2 hZ⟩
  · exact ⟨h1.1.mul_right _, by
      rw [tsum_mul_right, mul_assoc]
      exact mul_le_mul_of_nonneg_right h1.2 (mul_nonneg hA2 hZ)⟩

/-! ### B. The sum along a horizontal plane -/

/-- `w` has fibre sums at most `Z`: `∑_{b slow} w(t − b) ≤ Z` for every `t`.  Slow `b` run over the
horizontal plane through `t`, so this is uniform in the vertical. -/
def Fib (w : Mode → ℝ) (Z : ℝ) : Prop :=
  ∀ t : Mode, SB (fun b : Mode => if b 2 = 0 then w (t - b) else 0) Z

lemma Fib.mono {w w' : Mode → ℝ} (h : Fib w Z) (h0 : ∀ k, 0 ≤ w' k) (hle : ∀ k, w' k ≤ w k) :
    Fib w' Z := fun t =>
  (h t).of_le (fun b => by split_ifs <;> simp [h0]) fun b => by
    split_ifs
    · exact hle _
    · exact le_rfl

/-- The same sum with `+ a` in place of `− b`. -/
lemma Fib.add {w : Mode → ℝ} (h : Fib w Z) (t : Mode) :
    SB (fun a : Mode => if a 2 = 0 then w (t + a) else 0) Z :=
  SB.equiv' (Equiv.neg Mode) (h t) fun a => by
    simp only [Equiv.neg_apply, Pi.neg_apply, neg_eq_zero, sub_neg_eq_add]

lemma slowBox_zero : slowBox 0 = {(0 : Mode)} := by
  ext k
  rw [mem_slowBox, Finset.mem_singleton]
  constructor
  · rintro ⟨h2, h0, h1⟩
    funext i
    fin_cases i
    · simpa using abs_nonpos_iff.1 (by simpa using h0)
    · simpa using abs_nonpos_iff.1 (by simpa using h1)
    · simpa using h2
  · rintro rfl
    simp

/-- The sum over a slow square, by shells. -/
lemma sum_slowBox_shell {φ : Mode → ℝ} {ψ : ℕ → ℝ}
    (h : ∀ (n : ℕ) (k : Mode), k 2 = 0 → k ≠ 0 → ((n : ℝ) + 1) ^ 2 ≤ absSq k → φ k ≤ ψ n)
    (N : ℕ) :
    ∑ k ∈ slowBox N, φ k ≤ φ 0 + ∑ n ∈ Finset.range N, 8 * ((n : ℝ) + 1) * ψ n := by
  induction N with
  | zero => simp [slowBox_zero]
  | succ n ih =>
    rw [← Finset.sum_sdiff (slowBox_mono (Nat.le_succ n)), Finset.sum_range_succ]
    have hsh : ∑ k ∈ slowBox (n + 1) \ slowBox n, φ k ≤ 8 * ((n : ℝ) + 1) * ψ n := by
      have h1 := Finset.sum_le_card_nsmul (slowBox (n + 1) \ slowBox n) φ (ψ n) fun k hk => by
        obtain ⟨a, b, c⟩ := shell_spec hk
        exact h n k a b c
      rw [card_shell, nsmul_eq_mul] at h1
      refine h1.trans (le_of_eq ?_)
      push_cast
      ring
    linarith

/-- The vertical part of a mode. -/
def vPart (t : Mode) : Mode := ![0, 0, t 2]

/-- The horizontal part of a mode. -/
def hPart (t : Mode) : Mode := t - vPart t

lemma hPart_two (t : Mode) : hPart t 2 = 0 := by
  simp [hPart, vPart]

/-- Adding a vertical to a slow mode does not decrease the length. -/
lemma absSq_le_vPart (t : Mode) {p : Mode} (hp : p 2 = 0) : absSq p ≤ absSq (vPart t + p) := by
  simp only [absSq, Fin.sum_univ_three, vPart, Pi.add_apply, hp]
  simp only [Matrix.cons_val]
  push_cast
  nlinarith [sq_nonneg (t 2 : ℝ)]

/-- **Fibre sums from a shell bound**: `w ≤ ψ₀`, and `w ≤ ψ n` outside the ball of radius
`n + 1`. -/
theorem fib_of_shell {w : Mode → ℝ} {ψ₀ : ℝ} {ψ : ℕ → ℝ} (h0 : ∀ k, 0 ≤ w k) (h1 : ∀ k, w k ≤ ψ₀)
    (h2 : ∀ (n : ℕ) (k : Mode), ((n : ℝ) + 1) ^ 2 ≤ absSq k → w k ≤ ψ n)
    (h3 : ∀ N, ψ₀ + ∑ n ∈ Finset.range N, 8 * ((n : ℝ) + 1) * ψ n ≤ Z) : Fib w Z := by
  intro t
  set φ : Mode → ℝ := fun p => if p 2 = 0 then w (vPart t + p) else 0 with hφ
  have hφ0 : ∀ p, 0 ≤ φ p := fun p => by
    simp only [hφ]
    split_ifs
    · exact h0 _
    · exact le_rfl
  have key : ∀ s : Finset Mode, ∑ k ∈ s, φ k ≤ Z := by
    intro s
    obtain ⟨M, hM⟩ := (s.image fun k : Mode => |k 0| ⊔ |k 1|).exists_le
    set n : ℕ := M.toNat with hn
    have hsub : s.filter (fun k : Mode => k 2 = 0) ⊆ slowBox n := by
      intro k hk
      rw [Finset.mem_filter] at hk
      have h := hM _ (Finset.mem_image_of_mem (fun k : Mode => |k 0| ⊔ |k 1|) hk.1)
      have hMn : M ≤ (n : ℤ) := Int.self_le_toNat M
      rw [mem_slowBox]
      exact ⟨hk.2, (le_sup_left.trans h).trans hMn, (le_sup_right.trans h).trans hMn⟩
    have hfilt : ∑ k ∈ s.filter (fun k : Mode => k 2 = 0), φ k = ∑ k ∈ s, φ k := by
      refine Finset.sum_filter_of_ne fun k _ hk => ?_
      by_contra h2'
      exact hk (by simp [hφ, h2'])
    rw [← hfilt]
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => hφ0 k).trans ?_
    have hbox := sum_slowBox_shell (φ := φ) (ψ := ψ) (fun m k hk _ hle => by
      simp only [hφ, hk, ite_true]
      exact h2 m _ (hle.trans (absSq_le_vPart t hk))) n
    have hz : φ 0 ≤ ψ₀ := by
      simp only [hφ]
      simpa using h1 _
    linarith [h3 n]
  have hs : SB φ Z := ⟨summable_of_sum_le hφ0 key, Real.tsum_le_of_sum_le hφ0 key⟩
  refine SB.equiv' (Equiv.subLeft (hPart t)) hs fun b => ?_
  simp only [Equiv.subLeft_apply, hφ, Pi.sub_apply, hPart_two, zero_sub, neg_eq_zero]
  have e : vPart t + (hPart t - b) = t - b := by
    simp only [hPart]
    abel
  rw [e]

/-! ### C. The three lattice sums -/

/-- `∑_{n<N} (n+1)⁻² ≤ 2`. -/
lemma sum_range_inv_sq_le (N : ℕ) : ∑ n ∈ Finset.range N, ((n : ℝ) + 1)⁻¹ ^ 2 ≤ 2 := by
  have key : ∀ m : ℕ, ∑ n ∈ Finset.range (m + 1), ((n : ℝ) + 1)⁻¹ ^ 2 ≤ 2 - ((m : ℝ) + 1)⁻¹ := by
    intro m
    induction m with
    | zero => simp; norm_num
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have h1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have h2 : ((((m + 1 : ℕ) : ℝ) + 1)⁻¹) ^ 2 ≤ ((m : ℝ) + 1)⁻¹ - ((m : ℝ) + 1 + 1)⁻¹ := by
        push_cast
        rw [inv_sub_inv (by positivity) (by positivity), inv_pow, ← one_div]
        apply div_le_div₀ (by linarith) (by linarith) (by positivity)
        nlinarith
      push_cast at h2 ih ⊢
      linarith
  rcases N with _ | m
  · simp
  · have h3 : (0 : ℝ) ≤ ((m : ℝ) + 1)⁻¹ := by positivity
    linarith [key m]

/-- `|k|⁻³`, zero at the origin. -/
def w3 (k : Mode) : ℝ := (absk k)⁻¹ ^ 3

lemma w3_nonneg (k : Mode) : 0 ≤ w3 k := pow_nonneg (inv_nonneg.2 (absk_nonneg k)) 3

lemma w3_neg (k : Mode) : w3 (-k) = w3 k := by simp only [w3, absk_neg]

lemma inv_absk_le_one (k : Mode) : (absk k)⁻¹ ≤ 1 := by
  by_cases hk : k = 0
  · subst hk
    simp [absk_eq_zero.2 rfl]
  · exact inv_le_one_of_one_le₀ (one_le_absk hk)

lemma inv_absk_le_of_sq {n : ℕ} {k : Mode} (h : ((n : ℝ) + 1) ^ 2 ≤ absSq k) :
    (absk k)⁻¹ ≤ ((n : ℝ) + 1)⁻¹ := by
  have h1 : (n : ℝ) + 1 ≤ absk k := by
    rw [← absk_sq k] at h
    exact (pow_le_pow_iff_left₀ (by positivity) (absk_nonneg k) two_ne_zero).1 h
  exact inv_anti₀ (by positivity) h1

/-- **The inverse-cubic sum** (Body 36: "the two-dimensional inverse-cubic sum"; Body 74: "the
convergent inverse-third lattice sum"). -/
theorem fib_w3 : Fib w3 17 := by
  refine fib_of_shell (ψ₀ := 1) (ψ := fun n => ((n : ℝ) + 1)⁻¹ ^ 3) w3_nonneg (fun k => ?_)
    (fun n k h => ?_) fun N => ?_
  · exact pow_le_one₀ (inv_nonneg.2 (absk_nonneg k)) (inv_absk_le_one k)
  · exact pow_le_pow_left₀ (inv_nonneg.2 (absk_nonneg k)) (inv_absk_le_of_sq h) 3
  · have e : ∀ n ∈ Finset.range N, 8 * ((n : ℝ) + 1) * ((n : ℝ) + 1)⁻¹ ^ 3 =
        8 * ((n : ℝ) + 1)⁻¹ ^ 2 := fun n _ => by
      have : ((n : ℝ) + 1) ≠ 0 := by positivity
      field_simp
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
    linarith [sum_range_inv_sq_le N]

/-- `|k|⁻⁴`, zero at the origin. -/
def w4 (k : Mode) : ℝ := (absk k)⁻¹ ^ 4

/-- **The inverse-fourth sum** (Body 36: "the uniform inverse-fourth sum"). -/
theorem fib_w4 : Fib w4 17 :=
  fib_w3.mono (fun k => pow_nonneg (inv_nonneg.2 (absk_nonneg k)) 4) fun k =>
    pow_le_pow_of_le_one (inv_nonneg.2 (absk_nonneg k)) (inv_absk_le_one k) (by norm_num)

open Classical in
/-- `|k|⁻¹` on the ball of radius `D`, zero outside and at the origin. -/
def bandW (D : ℝ) (k : Mode) : ℝ := if absk k ≤ D then (absk k)⁻¹ else 0

lemma bandW_nonneg (D : ℝ) (k : Mode) : 0 ≤ bandW D k := by
  unfold bandW
  split_ifs
  · exact inv_nonneg.2 (absk_nonneg k)
  · exact le_rfl

lemma bandW_le (D : ℝ) (k : Mode) : bandW D k ≤ (absk k)⁻¹ := by
  unfold bandW
  split_ifs
  · exact le_rfl
  · exact inv_nonneg.2 (absk_nonneg k)

lemma sum_band_inv_le {D : ℝ} (hD : 1 ≤ D) (N : ℕ) :
    ∑ n ∈ Finset.range N, (if (n : ℝ) + 1 ≤ D then ((n : ℝ) + 1)⁻¹ else 0) ≤ 1 + Real.log D := by
  have hD0 : 0 ≤ D := by linarith
  rw [← Finset.sum_filter]
  have hsub : (Finset.range N).filter (fun n : ℕ => (n : ℝ) + 1 ≤ D) ⊆ Finset.range ⌊D⌋₊ := by
    intro n hn
    rw [Finset.mem_filter] at hn
    have h1 : n + 1 ≤ ⌊D⌋₊ := Nat.le_floor (by exact_mod_cast hn.2)
    exact Finset.mem_range.2 h1
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity).trans ?_
  have hh := harmonic_le_one_add_log ⌊D⌋₊
  have e : ((harmonic ⌊D⌋₊ : ℚ) : ℝ) = ∑ n ∈ Finset.range ⌊D⌋₊, ((n : ℝ) + 1)⁻¹ := by
    simp only [harmonic]
    push_cast
    rfl
  rw [e] at hh
  refine hh.trans ?_
  have h1 : (1 : ℝ) ≤ ⌊D⌋₊ := by exact_mod_cast Nat.le_floor (by simpa using hD)
  have h2 : Real.log ⌊D⌋₊ ≤ Real.log D :=
    Real.log_le_log (by linarith) (Nat.floor_le hD0)
  linarith

/-- **The logarithmic band sum** (Body 36: "`C √(1 + ln D)`, since `L, J ≤ D` on this sector and the
fixed-vertical two-dimensional inverse-square shell sum is logarithmic"). -/
theorem fib_band {D : ℝ} (hD : 1 ≤ D) : Fib (fun k => bandW D k ^ 2) (9 + 8 * Real.log D) := by
  refine fib_of_shell (ψ₀ := 1)
    (ψ := fun n => if (n : ℝ) + 1 ≤ D then ((n : ℝ) + 1)⁻¹ ^ 2 else 0) (fun k => sq_nonneg _)
    (fun k => ?_) (fun n k h => ?_) fun N => ?_
  · exact pow_le_one₀ (bandW_nonneg D k) ((bandW_le D k).trans (inv_absk_le_one k))
  · have h1 : (n : ℝ) + 1 ≤ absk k := by
      rw [← absk_sq k] at h
      exact (pow_le_pow_iff_left₀ (by positivity) (absk_nonneg k) two_ne_zero).1 h
    unfold bandW
    by_cases hk : absk k ≤ D
    · rw [ite_eq_left hk, ite_eq_left (h1.trans hk)]
      exact pow_le_pow_left₀ (inv_nonneg.2 (absk_nonneg k)) (inv_absk_le_of_sq h) 2
    · rw [ite_eq_right hk, zero_pow two_ne_zero]
      split_ifs
      · positivity
      · exact le_rfl
  · have e : ∀ n ∈ Finset.range N, 8 * ((n : ℝ) + 1) *
        (if (n : ℝ) + 1 ≤ D then ((n : ℝ) + 1)⁻¹ ^ 2 else 0) =
        8 * (if (n : ℝ) + 1 ≤ D then ((n : ℝ) + 1)⁻¹ else 0) := fun n _ => by
      have : ((n : ℝ) + 1) ≠ 0 := by positivity
      split_ifs
      · field_simp
      · simp
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
    linarith [sum_band_inv_le hD N]

end OVNS.Quant.Metric

end
