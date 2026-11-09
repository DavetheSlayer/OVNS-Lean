import OddViscousNS.Quant.Joint.Metric.Path3Main

/-!
# The fourth correction: the horizontal fibre norm (step J5, node N11)

Bodies 34, 35, 46: `L_h(V) = ∑_{l_h} (∑_n |V̂(l_h, n)|²)^{1/2}`, the horizontal `ℓ¹` of the vertical
`ℓ²` fibres (`LhB`), and the two things it does:

* `LhB.conv`: for a slow `α ∈ ℓ²`, `‖α ⋆ β‖_{ℓ²} ≤ ‖α‖ L_h(β)` (Body 34, "fix `l_h`, take the product
  of the slow weighted horizontal `ℓ²` norm and the fast vertical `ℓ²` norm, translate horizontal
  indices by `l_h`, and sum by Minkowski");
* `LhB.conv_l1`: for a slow `α ∈ ℓ¹`, `L_h(α ⋆ β) ≤ ‖α‖₁ L_h(β)` (Body 46).

The fibres are indexed by `a : ℤ × ℤ`, through `md a n = (a₁, a₂, n)`.  Minkowski in `ℓ²` for a
nonnegative family (`mink`) is a Schur test: `(∑ f_i)² ≤ (∑ c_i)(∑ f_i²/c_i)`, so no `ℓ²`-valued sum
is needed.
-/

noncomputable section

namespace OVNS.Quant.Quartic

open OVNS.Quant.Metric

/-! ### A. Minkowski for a nonnegative family -/

/-- **Minkowski in `ℓ²`**: a family of nonnegative sequences of `ℓ²` norms at most `c i`, `∑ c ≤ C`. -/
theorem mink {ι κ : Type*} {f : ι → κ → ℝ} {c : ι → ℝ} {C : ℝ} (h0 : ∀ i k, 0 ≤ f i k)
    (hc0 : ∀ i, 0 ≤ c i) (hf : ∀ i, SB (fun k => f i k ^ 2) (c i ^ 2)) (hc : SB c C) :
    (∀ k, Summable fun i => f i k) ∧ SB (fun k => (∑' i, f i k) ^ 2) (C ^ 2) := by
  have hC0 : 0 ≤ C := (tsum_nonneg hc0).trans hc.2
  have hle : ∀ i k, f i k ≤ c i := fun i k => by
    have h1 : f i k ^ 2 ≤ ∑' k, f i k ^ 2 :=
      (hf i).1.le_tsum k fun j _ => sq_nonneg _
    have h2 := h1.trans (hf i).2
    exact (pow_le_pow_iff_left₀ (h0 i k) (hc0 i) two_ne_zero).1 h2
  have hS : ∀ k, Summable fun i => f i k := fun k =>
    Summable.of_nonneg_of_le (fun i => h0 i k) (fun i => hle i k) hc.1
  refine ⟨hS, ?_⟩
  set H : ι × κ → ℝ := fun x => f x.1 x.2 ^ 2 / c x.1 with hH
  have hH0 : ∀ x, 0 ≤ H x := fun x => div_nonneg (sq_nonneg _) (hc0 _)
  have hHi : ∀ i, SB (fun k => H (i, k)) (c i) := fun i => by
    have e : ∀ k, H (i, k) = f i k ^ 2 * (c i)⁻¹ := fun k => by simp only [hH, div_eq_mul_inv]
    simp only [e]
    refine ⟨(hf i).1.mul_right _, ?_⟩
    rw [tsum_mul_right]
    by_cases h : c i = 0
    · simp [h]
    · have hp : 0 < c i := lt_of_le_of_ne (hc0 i) (Ne.symm h)
      calc _ ≤ c i ^ 2 * (c i)⁻¹ := mul_le_mul_of_nonneg_right (hf i).2 (inv_nonneg.2 hp.le)
        _ = c i := by field_simp
  have hHS : SB H C := SB.prod hH0 hHi hc
  obtain ⟨hswap, hsum⟩ := SB.fst_swap hHS
  have hfib : ∀ k, Summable fun i => H (i, k) := fun k => by
    have := hswap.prod_factor k
    exact this
  have hpt : ∀ k, (∑' i, f i k) ^ 2 ≤ C * ∑' i, H (i, k) := fun k => by
    have hP : SB (fun i => Real.sqrt (c i) ^ 2) (Real.sqrt C ^ 2) := by
      rw [Real.sq_sqrt hC0]
      refine ⟨hc.1.congr fun i => (Real.sq_sqrt (hc0 i)).symm, ?_⟩
      simpa only [Real.sq_sqrt (hc0 _)] using hc.2
    have hIn : 0 ≤ ∑' i, H (i, k) := tsum_nonneg fun i => hH0 _
    have hQ : SB (fun i => (f i k / Real.sqrt (c i)) ^ 2)
        (Real.sqrt (∑' i, H (i, k)) ^ 2) := by
      rw [Real.sq_sqrt hIn]
      have e : ∀ i, (f i k / Real.sqrt (c i)) ^ 2 = H (i, k) := fun i => by
        simp only [hH, div_pow, Real.sq_sqrt (hc0 i)]
      simp only [e]
      exact ⟨hfib k, le_rfl⟩
    have h1 := SB.cs (fun i => Real.sqrt_nonneg _)
      (fun i => div_nonneg (h0 i k) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _) hP hQ
    have e2 : ∀ i, Real.sqrt (c i) * (f i k / Real.sqrt (c i)) = f i k := fun i => by
      by_cases h : c i = 0
      · have : f i k = 0 := le_antisymm (by simpa [h] using hle i k) (h0 i k)
        simp [this]
      · have hp : 0 < Real.sqrt (c i) := Real.sqrt_pos.2 (lt_of_le_of_ne (hc0 i) (Ne.symm h))
        field_simp
    simp only [e2] at h1
    have h2 : ∑' i, f i k ≤ Real.sqrt C * Real.sqrt (∑' i, H (i, k)) := h1.2
    have h3 := pow_le_pow_left₀ (tsum_nonneg fun i => h0 i k) h2 2
    rw [mul_pow, Real.sq_sqrt hC0, Real.sq_sqrt hIn] at h3
    exact h3
  have hs2 : SB (fun k => C * ∑' i, H (i, k)) (C * C) := hsum.const_mul hC0
  have e3 : C * C = C ^ 2 := by ring
  rw [e3] at hs2
  exact hs2.of_le (fun k => sq_nonneg _) hpt

/-! ### B. The horizontal labels -/

/-- The mode `(a₁, a₂, n)`. -/
def md (a : ℤ × ℤ) (n : ℤ) : Mode := ![a.1, a.2, n]

@[simp] lemma md_zero (a : ℤ × ℤ) (n : ℤ) : md a n 0 = a.1 := rfl
@[simp] lemma md_one (a : ℤ × ℤ) (n : ℤ) : md a n 1 = a.2 := rfl
@[simp] lemma md_two (a : ℤ × ℤ) (n : ℤ) : md a n 2 = n := rfl

lemma mode_ext {p p' : Mode} (h0 : p 0 = p' 0) (h1 : p 1 = p' 1) (h2 : p 2 = p' 2) : p = p' := by
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- Every mode is an `md`. -/
lemma md_eta (p : Mode) : md (p 0, p 1) (p 2) = p := mode_ext rfl rfl rfl

/-- The modes as horizontal and vertical labels. -/
def mdEquiv : (ℤ × ℤ) × ℤ ≃ Mode where
  toFun z := md z.1 z.2
  invFun p := ((p 0, p 1), p 2)
  left_inv z := by
    obtain ⟨⟨a, b⟩, n⟩ := z
    rfl
  right_inv p := md_eta p

lemma md_inj {a b : ℤ × ℤ} {n m : ℤ} (h : md a n = md b m) : a = b ∧ n = m := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [md_zero, md_one, md_two] at h0 h1 h2
  exact ⟨Prod.ext h0 h1, h2⟩

lemma md_sub (a b : ℤ × ℤ) (n m : ℤ) : md a n - md b m = md (a - b) (n - m) :=
  mode_ext (by simp) (by simp) (by simp)

lemma md_add (a b : ℤ × ℤ) (n m : ℤ) : md a n + md b m = md (a + b) (n + m) :=
  mode_ext (by simp) (by simp) (by simp)

/-- A slow mode is `md c 0`. -/
lemma slow_eq_md {s : Mode} (hs : s 2 = 0) : s = md (s 0, s 1) 0 :=
  mode_ext rfl rfl hs

/-! ### C. The fibre norm -/

/-- The vertical `ℓ²` norm over the horizontal label `a`. -/
def fibN (β : Mode → ℝ) (a : ℤ × ℤ) : ℝ := Real.sqrt (∑' n : ℤ, β (md a n) ^ 2)

lemma fibN_nonneg (β : Mode → ℝ) (a : ℤ × ℤ) : 0 ≤ fibN β a := Real.sqrt_nonneg _

/-- `L_h(β) ≤ L`: the horizontal `ℓ¹` of the vertical `ℓ²` norms. -/
structure LhB (β : Mode → ℝ) (L : ℝ) : Prop where
  nn : ∀ k, 0 ≤ β k
  fib : ∀ a, Summable fun n : ℤ => β (md a n) ^ 2
  sum : SB (fibN β) L

variable {α β γ : Mode → ℝ} {A L Z : ℝ}

lemma LhB.bd_nonneg (h : LhB β L) : 0 ≤ L := (tsum_nonneg (fibN_nonneg β)).trans h.sum.2

lemma LhB.mono (h : LhB β L) {L' : ℝ} (hL : L ≤ L') : LhB β L' :=
  ⟨h.nn, h.fib, h.sum.mono_bd hL⟩

/-- The sum of the squares of the vertical fibres of an `ℓ²` sequence. -/
lemma l2b_fib_sq (h : L2B γ A) :
    (∀ a, Summable fun n : ℤ => γ (md a n) ^ 2) ∧ SB (fun a => fibN γ a ^ 2) (A ^ 2) := by
  have hs : Summable fun z : (ℤ × ℤ) × ℤ => γ (md z.1 z.2) ^ 2 :=
    mdEquiv.summable_iff.2 h.s
  have hf : ∀ a, Summable fun n : ℤ => γ (md a n) ^ 2 := fun a => hs.prod_factor a
  have e : ∀ a, fibN γ a ^ 2 = ∑' n, γ (md a n) ^ 2 := fun a =>
    Real.sq_sqrt (tsum_nonneg fun n => sq_nonneg _)
  refine ⟨hf, ?_⟩
  simp only [e]
  refine ⟨hs.prod, ?_⟩
  rw [← hs.tsum_prod]
  have e2 : ∑' z : (ℤ × ℤ) × ℤ, γ (md z.1 z.2) ^ 2 = ∑' k, γ k ^ 2 :=
    mdEquiv.tsum_eq fun k => γ k ^ 2
  rw [e2]
  have h0 : 0 ≤ ∑' k, γ k ^ 2 := tsum_nonneg fun k => sq_nonneg _
  calc ∑' k, γ k ^ 2 = Real.sqrt (∑' k, γ k ^ 2) ^ 2 := (Real.sq_sqrt h0).symm
    _ ≤ A ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h.le 2

/-- The monotonicity of a fibre under a scalar bound. -/
lemma fibN_le {a : ℤ × ℤ} {c : ℝ} (h0 : ∀ n, 0 ≤ β (md a n)) (hc : 0 ≤ c)
    (hγ : Summable fun n : ℤ => γ (md a n) ^ 2)
    (hle : ∀ n, β (md a n) ≤ c * γ (md a n)) :
    (Summable fun n : ℤ => β (md a n) ^ 2) ∧ fibN β a ≤ c * fibN γ a := by
  have hb : ∀ n, β (md a n) ^ 2 ≤ c ^ 2 * γ (md a n) ^ 2 := fun n => by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (h0 n) (hle n) 2
  have hs : Summable fun n : ℤ => c ^ 2 * γ (md a n) ^ 2 := hγ.mul_left _
  have hβ : Summable fun n : ℤ => β (md a n) ^ 2 :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) hb hs
  refine ⟨hβ, ?_⟩
  unfold fibN
  rw [← Real.sqrt_sq hc, ← Real.sqrt_mul (sq_nonneg c), ← tsum_mul_left]
  exact Real.sqrt_le_sqrt (hβ.tsum_le_tsum hb hs)

/-- **A weighted fibre bound**: if `β ≤ ρ_a γ` on the fibre over `a`, with `∑ ρ² ≤ Z`, `γ ∈ ℓ²`,
then `L_h(β) ≤ √Z ‖γ‖` (the horizontal Cauchy of Bodies 34, 35). -/
theorem LhB.of_weight {ρ : ℤ × ℤ → ℝ} (hβ0 : ∀ k, 0 ≤ β k) (hρ0 : ∀ a, 0 ≤ ρ a)
    (hρ : SB (fun a => ρ a ^ 2) Z) (hγ : L2B γ A)
    (hle : ∀ a n, β (md a n) ≤ ρ a * γ (md a n)) : LhB β (Real.sqrt Z * A) := by
  obtain ⟨hf, hS⟩ := l2b_fib_sq hγ
  have hZ0 : 0 ≤ Z := (tsum_nonneg fun a => sq_nonneg _).trans hρ.2
  have hA0 := hγ.bd_nonneg
  have hfib : ∀ a, _ := fun a => fibN_le (β := β) (a := a) (fun n => hβ0 _) (hρ0 a) (hf a) (hle a)
  have hP : SB (fun a => ρ a ^ 2) (Real.sqrt Z ^ 2) := by rwa [Real.sq_sqrt hZ0]
  have hcs := SB.cs hρ0 (fibN_nonneg γ) (Real.sqrt_nonneg _) hA0 hP hS
  refine ⟨hβ0, fun a => (hfib a).1, ?_⟩
  exact hcs.of_le (fibN_nonneg β) fun a => (hfib a).2

/-! ### D. The convolution with a slow sequence -/

/-- `α ⋆ β`. -/
def cvS (α β : Mode → ℝ) (p : Mode) : ℝ := ∑' s, α s * β (p - s)

/-- The labels of the sum: `s = p − md a (p 2)`, for slow `s`. -/
lemma cv_reindex {f : Mode → ℝ} (hf : ∀ s, s 2 ≠ 0 → f s = 0) (p : Mode) :
    ∑' a : ℤ × ℤ, f (p - md a (p 2)) = ∑' s, f s := by
  have hinj : Function.Injective fun a : ℤ × ℤ => p - md a (p 2) := fun a b h => by
    have h' : md a (p 2) = md b (p 2) := sub_right_injective h
    exact (md_inj h').1
  refine hinj.tsum_eq ?_
  intro s hs
  have hs2 : s 2 = 0 := by
    by_contra h
    exact hs (hf s h)
  refine ⟨((p - s) 0, (p - s) 1), ?_⟩
  have e : md ((p - s) 0, (p - s) 1) (p 2) = p - s :=
    mode_ext rfl rfl (by simp [hs2])
  simp only [e, sub_sub_cancel]

/-- A nonnegative sum along an injection. -/
lemma SB.comp_inj {ι κ : Type*} {F : κ → ℝ} {C : ℝ} (hF : SB F C) (h0 : ∀ k, 0 ≤ F k) {i : ι → κ}
    (hi : Function.Injective i) : SB (fun x => F (i x)) C :=
  ⟨hF.1.comp_injective hi, (tsum_comp_le_tsum_of_inj hF.1 h0 hi).trans hF.2⟩

/-- A product of two nonnegative sums. -/
lemma SB.mul_prod {ι κ : Type*} {u : ι → ℝ} {v : κ → ℝ} {A B : ℝ} (hu : SB u A) (hv : SB v B)
    (hu0 : ∀ i, 0 ≤ u i) (hv0 : ∀ k, 0 ≤ v k) : SB (fun z : ι × κ => u z.1 * v z.2) (A * B) := by
  have hB : 0 ≤ B := (tsum_nonneg hv0).trans hv.2
  refine SB.prod (c := fun i => u i * B) (fun z => mul_nonneg (hu0 _) (hv0 _))
    (fun i => hv.const_mul (hu0 i)) ?_
  refine ⟨hu.1.mul_right B, ?_⟩
  rw [tsum_mul_right]
  exact mul_le_mul_of_nonneg_right hu.2 hB

/-- `s ↦ md s 0` is injective. -/
lemma md0_inj : Function.Injective fun c : ℤ × ℤ => md c 0 := fun _ _ h => (md_inj h).1

/-- **The product of a slow `ℓ²` sequence and a fibre** (Body 34). -/
theorem LhB.conv (hα : L2B α A) (hαs : ∀ s, s 2 ≠ 0 → α s = 0) (hβ : LhB β L) :
    (∀ p, Summable fun s => α s * β (p - s)) ∧ L2B (cvS α β) (A * L) := by
  have hA0 := hα.bd_nonneg
  set f : ℤ × ℤ → Mode → ℝ := fun a p => α (p - md a (p 2)) * β (md a (p 2)) with hf
  have h0 : ∀ a p, 0 ≤ f a p := fun a p => mul_nonneg (hα.nn _) (hβ.nn _)
  have hsq := L2B.sq hα
  have hfa : ∀ a, SB (fun p => f a p ^ 2) ((A * fibN β a) ^ 2) := fun a => by
    have hu : SB (fun c : ℤ × ℤ => α (md (c - a) 0) ^ 2) (A ^ 2) := by
      have hi : Function.Injective fun c : ℤ × ℤ => md (c - a) 0 := fun c c' h => by
        exact sub_left_injective (md_inj h).1
      exact SB.comp_inj hsq (fun k => sq_nonneg _) hi
    have hv : SB (fun n : ℤ => β (md a n) ^ 2) (fibN β a ^ 2) := by
      have e : fibN β a ^ 2 = ∑' n, β (md a n) ^ 2 :=
        Real.sq_sqrt (tsum_nonneg fun n => sq_nonneg _)
      rw [e]
      exact ⟨hβ.fib a, le_rfl⟩
    have hP := SB.mul_prod hu hv (fun c => sq_nonneg _) (fun n => sq_nonneg _)
    have e2 : (A * fibN β a) ^ 2 = A ^ 2 * fibN β a ^ 2 := by ring
    rw [e2]
    refine SB.equiv' mdEquiv.symm hP fun p => ?_
    have e3 : p - md a (p 2) = md ((p 0, p 1) - a) 0 := by
      conv_lhs => rw [← md_eta p]
      rw [md_sub]
      simp
    have e4 : mdEquiv.symm p = ((p 0, p 1), p 2) := rfl
    simp only [hf, e3, e4, mul_pow]
  have hc : SB (fun a => A * fibN β a) (A * L) := hβ.sum.const_mul hA0
  obtain ⟨hS, hB⟩ := mink h0 (fun a => mul_nonneg hA0 (fibN_nonneg β a)) hfa hc
  have hval : ∀ p, ∑' a, f a p = ∑' s, α s * β (p - s) := fun p => by
    have h1 := cv_reindex (f := fun s => α s * β (p - s))
      (fun s hs => by simp only [hαs s hs, zero_mul]) p
    simp only [sub_sub_cancel] at h1
    exact h1
  have hinj : ∀ p : Mode, Function.Injective fun a : ℤ × ℤ => p - md a (p 2) := fun p a b h => by
    have h' : md a (p 2) = md b (p 2) := sub_right_injective h
    exact (md_inj h').1
  refine ⟨fun p => ?_, ?_⟩
  · have h1 : Summable ((fun s => α s * β (p - s)) ∘ fun a : ℤ × ℤ => p - md a (p 2)) := by
      refine (hS p).congr fun a => ?_
      simp only [Function.comp, sub_sub_cancel]
      rfl
    refine ((hinj p).summable_iff ?_).1 h1
    intro s hs
    by_cases hs2 : s 2 = 0
    · exfalso
      refine hs ⟨((p - s) 0, (p - s) 1), ?_⟩
      have e : md ((p - s) 0, (p - s) 1) (p 2) = p - s :=
        mode_ext rfl rfl (by simp [hs2])
      simp only [e, sub_sub_cancel]
    · simp only [hαs s hs2, zero_mul]
  · have e : ∀ p, cvS α β p ^ 2 = (∑' a, f a p) ^ 2 := fun p => by rw [hval p]; rfl
    refine ⟨fun p => tsum_nonneg fun s => mul_nonneg (hα.nn _) (hβ.nn _), ?_, ?_⟩
    · simpa only [e] using hB.1
    · have h2 : ∑' p, cvS α β p ^ 2 ≤ (A * L) ^ 2 := by
        simpa only [e] using hB.2
      exact Real.sqrt_le_iff.2 ⟨mul_nonneg hA0 hβ.bd_nonneg, h2⟩

/-- The value of the convolution on a fibre, in horizontal labels. -/
lemma cvS_md (hαs : ∀ s, s 2 ≠ 0 → α s = 0) (a : ℤ × ℤ) (n : ℤ) :
    cvS α β (md a n) = ∑' c : ℤ × ℤ, α (md c 0) * β (md (a - c) n) := by
  unfold cvS
  have hsupp : Function.support (fun s => α s * β (md a n - s)) ⊆
      Set.range fun c : ℤ × ℤ => md c 0 := fun s hs => by
    have hs2 : s 2 = 0 := by
      by_contra h
      exact hs (by simp only [hαs s h, zero_mul])
    exact ⟨(s 0, s 1), (slow_eq_md hs2).symm⟩
  rw [← md0_inj.tsum_eq hsupp]
  refine tsum_congr fun c => ?_
  rw [md_sub, sub_zero]

/-- The shear of the horizontal labels. -/
def shearH : (ℤ × ℤ) × (ℤ × ℤ) ≃ (ℤ × ℤ) × (ℤ × ℤ) where
  toFun z := (z.2, z.1 - z.2)
  invFun z := (z.1 + z.2, z.1)
  left_inv z := by simp
  right_inv z := by simp

/-- **The fibre norm of a product with a slow `ℓ¹` sequence** (Body 46: "at fixed `s_h` its output
fibre is the horizontal translate of the input fast fibre with the same nonzero vertical
coordinate", Minkowski in the sum over `s_h`). -/
theorem LhB.conv_l1 (hα : L1B α A) (hαs : ∀ s, s 2 ≠ 0 → α s = 0) (hβ : LhB β L) :
    LhB (cvS α β) (A * L) := by
  have hA0 := hα.bd_nonneg
  have ht : SB (fun c : ℤ × ℤ => α (md c 0)) A :=
    SB.comp_inj ⟨hα.s, hα.le⟩ hα.nn md0_inj
  have t0 : ∀ c : ℤ × ℤ, 0 ≤ α (md c 0) := fun c => hα.nn _
  have hP := SB.mul_prod ht hβ.sum t0 (fibN_nonneg β)
  set G : (ℤ × ℤ) × (ℤ × ℤ) → ℝ := fun z => α (md z.2 0) * fibN β (z.1 - z.2) with hG
  have hGs : SB G (A * L) := SB.equiv' shearH hP fun z => rfl
  have hGfib : ∀ a, Summable fun c => G (a, c) := fun a => hGs.1.prod_factor a
  have hGsum : SB (fun a => ∑' c, G (a, c)) (A * L) :=
    ⟨hGs.1.prod, by rw [← hGs.1.tsum_prod]; exact hGs.2⟩
  have hfib : ∀ a, (∀ n : ℤ, Summable fun c : ℤ × ℤ => α (md c 0) * β (md (a - c) n)) ∧
      SB (fun n : ℤ => (∑' c : ℤ × ℤ, α (md c 0) * β (md (a - c) n)) ^ 2)
        ((∑' c, G (a, c)) ^ 2) := fun a => by
    refine mink (f := fun (c : ℤ × ℤ) (n : ℤ) => α (md c 0) * β (md (a - c) n))
      (c := fun c => G (a, c)) (fun c n => mul_nonneg (t0 c) (hβ.nn _))
      (fun c => mul_nonneg (t0 c) (fibN_nonneg β _)) (fun c => ?_) ⟨hGfib a, le_rfl⟩
    have e : ∀ n : ℤ, (α (md c 0) * β (md (a - c) n)) ^ 2 =
        α (md c 0) ^ 2 * β (md (a - c) n) ^ 2 := fun n => by ring
    have e2 : G (a, c) ^ 2 = α (md c 0) ^ 2 * fibN β (a - c) ^ 2 := by
      simp only [hG]
      ring
    have e3 : fibN β (a - c) ^ 2 = ∑' n, β (md (a - c) n) ^ 2 :=
      Real.sq_sqrt (tsum_nonneg fun n => sq_nonneg _)
    simp only [e]
    rw [e2, e3]
    exact ⟨(hβ.fib _).mul_left _, by rw [tsum_mul_left]⟩
  have hval : ∀ a n, cvS α β (md a n) ^ 2 =
      (∑' c : ℤ × ℤ, α (md c 0) * β (md (a - c) n)) ^ 2 := fun a n => by rw [cvS_md hαs]
  have hnn : ∀ p, 0 ≤ cvS α β p := fun p =>
    tsum_nonneg fun s => mul_nonneg (hα.nn _) (hβ.nn _)
  refine ⟨hnn, fun a => ?_, ?_⟩
  · simpa only [hval] using (hfib a).2.1
  · refine hGsum.of_le (fibN_nonneg _) fun a => ?_
    refine Real.sqrt_le_iff.2 ⟨tsum_nonneg fun c => mul_nonneg (t0 c) (fibN_nonneg β _), ?_⟩
    simpa only [hval] using (hfib a).2.2

end OVNS.Quant.Quartic

end
