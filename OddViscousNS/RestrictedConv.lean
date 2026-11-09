import OddViscousNS.Mode

/-! # The restricted convolution lemma (`Lemma lem:rc`) -/

open scoped ENNReal
noncomputable section
namespace OVNS

/-- Cauchy-Schwarz for `ℝ≥0∞`-valued series, without any summability assumption. -/
private lemma tsum_mul_sq_le {ι : Type*} (f g : ι → ℝ≥0∞) :
    (∑' x, f x * g x) ^ 2 ≤ (∑' x, f x ^ 2) * ∑' x, g x ^ 2 := by
  let _ : MeasurableSpace ι := ⊤
  have _ : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq
    (MeasureTheory.Measure.count : MeasureTheory.Measure ι) Real.HolderConjugate.two_two
    (f := f) (g := g) measurable_from_top.aemeasurable measurable_from_top.aemeasurable
  simp only [Pi.mul_apply, MeasureTheory.lintegral_count, ENNReal.rpow_two] at h
  calc (∑' x, f x * g x) ^ 2
      ≤ ((∑' x, f x ^ 2) ^ (1 / 2 : ℝ) * (∑' x, g x ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = (∑' x, f x ^ 2) * ∑' x, g x ^ 2 := by
      rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
        ← ENNReal.rpow_mul]
      norm_num

/-- The dyadic index of a mode. -/
private def dy (k : Mode) : ℕ := Nat.log 2 ⌊absk k⌋₊

private lemma two_pow_dy_le {k : Mode} (hk : k ≠ 0) : (2 : ℝ) ^ dy k ≤ absk k := by
  have h1 : 1 ≤ absk k := one_le_absk hk
  have h2 : ⌊absk k⌋₊ ≠ 0 := by
    have : 1 ≤ ⌊absk k⌋₊ := Nat.le_floor (by simpa using h1)
    omega
  have h3 : 2 ^ dy k ≤ ⌊absk k⌋₊ := Nat.pow_log_le_self 2 h2
  have h4 : (2 : ℝ) ^ dy k ≤ (⌊absk k⌋₊ : ℝ) := by exact_mod_cast h3
  exact h4.trans (Nat.floor_le (absk_nonneg k))

private lemma lt_two_pow_dy (k : Mode) : absk k < 2 ^ (dy k + 1) := by
  have h3 : ⌊absk k⌋₊ < 2 ^ (dy k + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h4 : ⌊absk k⌋₊ + 1 ≤ 2 ^ (dy k + 1) := h3
  have h5 : ((⌊absk k⌋₊ : ℝ) + 1) ≤ 2 ^ (dy k + 1) := by exact_mod_cast h4
  exact (Nat.lt_floor_add_one _).trans_le h5

private lemma geom_le (N : ℕ) : ∑ i ∈ Finset.range (N + 1), (2 : ℝ) ^ i ≤ 2 * 2 ^ N := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have : (2 : ℝ) ^ (N + 1) = 2 * 2 ^ N := by ring
    have h : (2 : ℝ) ^ (N + 1 + 1) = 2 * 2 ^ (N + 1) := by ring
    linarith

open Classical in
/-- Sum of the inverse dyadic weights over the fibre of `n`, restricted to `|k| ≤ |n|`. -/
private lemma fibre_sum (T : Mode → Mode → Mode → Prop) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hne : ∀ k m n, T k m n → k ≠ 0 ∧ m ≠ 0 ∧ n ≠ 0)
    (hfib : ∀ (n : Mode) (i : ℕ),
      ({k | (2 : ℝ) ^ i ≤ absk k ∧ absk k < 2 ^ (i + 1) ∧ T k (-k - n) n}.encard : ℝ≥0∞) ≤
        ENNReal.ofReal (C₀ * 4 ^ i)) (n : Mode) (P : Mode → Prop)
    (hP : ∀ k, P k → T k (-k - n) n ∧ absk k ≤ absk n) :
    ∑' k, (if P k then ((2 : ℝ≥0∞) ^ dy k)⁻¹ else 0) ≤ ENNReal.ofReal (2 * C₀ * absk n) := by
  by_cases hn : n = 0
  · have : ∀ k, ¬ P k := fun k h => (hne _ _ _ (hP k h).1).2.2 hn
    simp [this]
  have h1 : ∀ k, (if P k then ((2 : ℝ≥0∞) ^ dy k)⁻¹ else 0) =
      ∑' i : ℕ, ((2 : ℝ≥0∞) ^ i)⁻¹ * (if dy k = i ∧ P k then 1 else 0) := by
    intro k
    rw [tsum_eq_single (dy k)]
    · by_cases h : P k <;> simp [h]
    · intro i hi
      have : ¬ (dy k = i ∧ P k) := fun h => hi h.1.symm
      simp [this]
  simp only [h1]
  rw [tsum_comm]
  simp only [ENNReal.tsum_mul_left]
  have h2 : ∀ i : ℕ, ((2 : ℝ≥0∞) ^ i)⁻¹ * ∑' k, (if dy k = i ∧ P k then (1 : ℝ≥0∞) else 0) ≤
      if i ∈ Finset.range (dy n + 1) then ENNReal.ofReal (C₀ * 2 ^ i) else 0 := by
    intro i
    have hset : ∑' k, (if dy k = i ∧ P k then (1 : ℝ≥0∞) else 0) =
        (({k | dy k = i ∧ P k} : Set Mode).encard : ℝ≥0∞) := by
      rw [← ENNReal.tsum_set_one, tsum_subtype ({k | dy k = i ∧ P k} : Set Mode)
        (fun _ => (1 : ℝ≥0∞))]
      refine tsum_congr fun k => ?_
      simp [Set.indicator_apply]
    rw [hset]
    split_ifs with hi
    · have hsub : ({k | dy k = i ∧ P k} : Set Mode) ⊆
          {k | (2 : ℝ) ^ i ≤ absk k ∧ absk k < 2 ^ (i + 1) ∧ T k (-k - n) n} := by
        rintro k ⟨rfl, hk⟩
        have h := (hP k hk).1
        exact ⟨two_pow_dy_le (hne _ _ _ h).1, lt_two_pow_dy k, h⟩
      have h3 : (({k | dy k = i ∧ P k} : Set Mode).encard : ℝ≥0∞) ≤
          ENNReal.ofReal (C₀ * 4 ^ i) := by
        refine le_trans ?_ (hfib n i)
        exact_mod_cast Set.encard_le_encard hsub
      have h4 : ((2 : ℝ≥0∞) ^ i)⁻¹ = ENNReal.ofReal (((2 : ℝ) ^ i)⁻¹) := by
        rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
        simp
      calc _ ≤ ENNReal.ofReal (((2 : ℝ) ^ i)⁻¹) * ENNReal.ofReal (C₀ * 4 ^ i) := by
            rw [h4]; gcongr
        _ = ENNReal.ofReal (C₀ * 2 ^ i) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            have : (4 : ℝ) ^ i = 2 ^ i * 2 ^ i := by rw [← mul_pow]; norm_num
            rw [this]
            field_simp
    · have hempty : ({k | dy k = i ∧ P k} : Set Mode) = ∅ := by
        ext k
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨rfl, hk⟩
        obtain ⟨h, hle⟩ := hP k hk
        apply hi
        have h5 : (2 : ℝ) ^ dy k < 2 ^ (dy n + 1) :=
          (two_pow_dy_le (hne _ _ _ h).1).trans_lt (hle.trans_lt (lt_two_pow_dy n))
        have := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 h5
        simpa using this
      simp [hempty]
  calc _ ≤ ∑' i : ℕ, (if i ∈ Finset.range (dy n + 1) then ENNReal.ofReal (C₀ * 2 ^ i) else 0) :=
        tsum_le_tsum h2
    _ = ∑ i ∈ Finset.range (dy n + 1), ENNReal.ofReal (C₀ * 2 ^ i) := by
        rw [tsum_eq_sum (s := Finset.range (dy n + 1)) (fun i hi => by simp [hi])]
        exact Finset.sum_congr rfl fun i hi => by simp only [hi, ite_true]
    _ = ENNReal.ofReal (∑ i ∈ Finset.range (dy n + 1), C₀ * 2 ^ i) :=
        (ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity).symm
    _ ≤ ENNReal.ofReal (2 * C₀ * absk n) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← Finset.mul_sum]
        have := geom_le (dy n)
        have h6 := two_pow_dy_le hn
        nlinarith [mul_le_mul_of_nonneg_left this hC₀, mul_le_mul_of_nonneg_left h6 hC₀]

open Classical in
/-- The ordered half of the sum, squared. -/
private lemma half_bound (T : Mode → Mode → Mode → Prop) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hne : ∀ k m n, T k m n → k ≠ 0 ∧ m ≠ 0 ∧ n ≠ 0)
    (hfib : ∀ (n : Mode) (i : ℕ),
      ({k | (2 : ℝ) ^ i ≤ absk k ∧ absk k < 2 ^ (i + 1) ∧ T k (-k - n) n}.encard : ℝ≥0∞) ≤
        ENNReal.ofReal (C₀ * 4 ^ i)) (v : Mode → ℝ≥0∞) (O : Mode × Mode → Prop)
    (hO : ∀ x, O x → T x.1 x.2 (-x.1 - x.2) ∧ absk x.1 ≤ absk (-x.1 - x.2)) :
    (∑' x : Mode × Mode, if O x then v x.1 * v x.2 * v (-x.1 - x.2) else 0) ^ 2 ≤
      (ENNReal.ofReal (2 * C₀) * ∑' k, ENNReal.ofReal (absk k) * v k ^ 2) *
        ((∑' k, ENNReal.ofReal (absk k) * v k ^ 2) * ∑' k, v k ^ 2) := by
  set ρ : Mode → ℝ≥0∞ := fun k => ENNReal.ofReal (Real.sqrt (2 ^ dy k)) with hρ
  have hρ2 : ∀ k, ρ k ^ 2 = 2 ^ dy k := by
    intro k
    rw [hρ]
    simp only
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity),
      ENNReal.ofReal_pow (by norm_num)]
    simp
  have hρ0 : ∀ k, ρ k ≠ 0 := by
    intro k h
    have := hρ2 k
    rw [h] at this
    simp at this
    exact absurd this.symm (by positivity)
  have hρt : ∀ k, ρ k ≠ ⊤ := fun _ => ENNReal.ofReal_ne_top
  have hsplit : ∀ x : Mode × Mode, (if O x then v x.1 * v x.2 * v (-x.1 - x.2) else 0) =
      (if O x then v (-x.1 - x.2) * (ρ x.1)⁻¹ else 0) *
        (if O x then v x.1 * v x.2 * ρ x.1 else 0) := by
    intro x
    by_cases h : O x
    · simp only [h, ite_true]
      calc v x.1 * v x.2 * v (-x.1 - x.2)
          = v x.1 * v x.2 * v (-x.1 - x.2) * ((ρ x.1)⁻¹ * ρ x.1) := by
            rw [ENNReal.inv_mul_cancel (hρ0 _) (hρt _), mul_one]
        _ = _ := by ring
    · simp [h]
  have hfirst : ∑' x : Mode × Mode, (if O x then v (-x.1 - x.2) * (ρ x.1)⁻¹ else 0) ^ 2 ≤
      ENNReal.ofReal (2 * C₀) * ∑' k, ENNReal.ofReal (absk k) * v k ^ 2 := by
    have hinv : Function.Involutive fun y : Mode × Mode => (y.1, -y.1 - y.2) := by
      intro y
      ext i <;> simp
    set e : Equiv.Perm (Mode × Mode) := Function.Involutive.toPerm _ hinv with he
    have he' : ∀ y, e y = (y.1, -y.1 - y.2) := fun _ => rfl
    rw [← e.tsum_eq]
    have hterm : ∀ y : Mode × Mode,
        (if O (e y) then v (-(e y).1 - (e y).2) * (ρ (e y).1)⁻¹ else 0) ^ 2 =
        v y.2 ^ 2 * (if O (y.1, -y.1 - y.2) then ((2 : ℝ≥0∞) ^ dy y.1)⁻¹ else 0) := by
      intro y
      have h3 : -y.1 - (-y.1 - y.2) = y.2 := by abel
      simp only [he', h3]
      by_cases h : O (y.1, -y.1 - y.2)
      · simp only [h, ite_true, mul_pow]
        rw [← ENNReal.inv_pow, hρ2]
      · simp [h]
    simp only [hterm]
    rw [tsum_prod', tsum_comm]
    simp only [ENNReal.tsum_mul_left]
    rw [← ENNReal.tsum_mul_left]
    refine tsum_le_tsum fun n => ?_
    have h4 := fibre_sum T C₀ hC₀ hne hfib n (fun k => O (k, -k - n)) (fun k hk => by
      have := hO _ hk
      have h3 : -k - (-k - n) = n := by abel
      simp only [h3] at this
      exact this)
    calc _ ≤ v n ^ 2 * ENNReal.ofReal (2 * C₀ * absk n) := by gcongr
      _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity)]
        ring
  have hsecond : ∑' x : Mode × Mode, (if O x then v x.1 * v x.2 * ρ x.1 else 0) ^ 2 ≤
      (∑' k, ENNReal.ofReal (absk k) * v k ^ 2) * ∑' k, v k ^ 2 := by
    rw [← ENNReal.tsum_mul_right]
    simp only [← ENNReal.tsum_mul_left]
    rw [← tsum_prod (f := fun i j => ENNReal.ofReal (absk i) * v i ^ 2 * v j ^ 2)]
    refine tsum_le_tsum fun x => ?_
    by_cases h : O x
    · simp only [h, ite_true, mul_pow, hρ2]
      have h5 : (2 : ℝ≥0∞) ^ dy x.1 ≤ ENNReal.ofReal (absk x.1) := by
        have h6 := ENNReal.ofReal_le_ofReal (two_pow_dy_le (hne _ _ _ (hO x h).1).1)
        rwa [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat] at h6
      calc v x.1 ^ 2 * v x.2 ^ 2 * 2 ^ dy x.1
          ≤ v x.1 ^ 2 * v x.2 ^ 2 * ENNReal.ofReal (absk x.1) := by gcongr
        _ = _ := by ring
    · simp [h]
  simp only [hsplit]
  exact (tsum_mul_sq_le _ _).trans (mul_le_mul' hfirst hsecond)

/-- `Lemma lem:rc`. `T k m n` is a permutation-invariant relation on zero-sum triples of nonzero
modes with dyadic fibres of size at most `C₀ 4^i`. The output is the sum over `(k,m)`, with
`n = -k-m`. -/
theorem restricted_conv (T : Mode → Mode → Mode → Prop) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hne : ∀ k m n, T k m n → k ≠ 0 ∧ m ≠ 0 ∧ n ≠ 0)
    (_hsum : ∀ k m n, T k m n → k + m + n = 0)
    (hswap₁ : ∀ k m n, T k m n → T m k n) (hswap₂ : ∀ k m n, T k m n → T k n m)
    (hfib : ∀ (n : Mode) (i : ℕ),
      ({k | (2 : ℝ) ^ i ≤ absk k ∧ absk k < 2 ^ (i + 1) ∧ T k (-k - n) n}.encard : ℝ≥0∞) ≤
        ENNReal.ofReal (C₀ * 4 ^ i))
    (u : Mode → ℝ) (hu0 : ∀ k, 0 ≤ u k)
    (hu1 : Summable fun k => absk k * u k ^ 2) (hu2 : Summable fun k => u k ^ 2) :
    open Classical in
    Summable (fun x : Mode × Mode =>
      if T x.1 x.2 (-x.1 - x.2) then u x.1 * u x.2 * u (-x.1 - x.2) else 0) ∧
    ∑' x : Mode × Mode, (if T x.1 x.2 (-x.1 - x.2) then u x.1 * u x.2 * u (-x.1 - x.2) else 0) ≤
      6 * Real.sqrt (2 * C₀) * (∑' k, absk k * u k ^ 2) * Real.sqrt (∑' k, u k ^ 2) := by
  classical
  set a : Mode × Mode → ℝ := fun x =>
    if T x.1 x.2 (-x.1 - x.2) then u x.1 * u x.2 * u (-x.1 - x.2) else 0 with ha
  set A : ℝ := ∑' k, absk k * u k ^ 2 with hA
  set B : ℝ := ∑' k, u k ^ 2 with hB
  have hA0 : 0 ≤ A := tsum_nonneg fun k => mul_nonneg (absk_nonneg k) (sq_nonneg _)
  have hB0 : 0 ≤ B := tsum_nonneg fun k => sq_nonneg _
  have ha0 : ∀ x, 0 ≤ a x := by
    intro x
    simp only [ha]
    split_ifs
    · exact mul_nonneg (mul_nonneg (hu0 _) (hu0 _)) (hu0 _)
    · exact le_rfl
  set v : Mode → ℝ≥0∞ := fun k => ENNReal.ofReal (u k) with hv
  have hAe : ∑' k, ENNReal.ofReal (absk k) * v k ^ 2 = ENNReal.ofReal A := by
    rw [hA, ENNReal.ofReal_tsum_of_nonneg
      (fun k => mul_nonneg (absk_nonneg k) (sq_nonneg _)) hu1]
    refine tsum_congr fun k => ?_
    rw [ENNReal.ofReal_mul (absk_nonneg k), ENNReal.ofReal_pow (hu0 k)]
  have hBe : ∑' k, v k ^ 2 = ENNReal.ofReal B := by
    rw [hB, ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) hu2]
    exact tsum_congr fun k => (ENNReal.ofReal_pow (hu0 k) 2).symm
  set R : ℝ := Real.sqrt (2 * C₀) * A * Real.sqrt B with hR
  have hR0 : 0 ≤ R := by positivity
  obtain ⟨O, hO⟩ : ∃ O : Mode × Mode → Prop,
      ∀ x, O x ↔ T x.1 x.2 (-x.1 - x.2) ∧ absk x.1 ≤ absk (-x.1 - x.2) :=
    ⟨_, fun _ => Iff.rfl⟩
  set G : Mode × Mode → ℝ≥0∞ := fun x =>
    if O x then v x.1 * v x.2 * v (-x.1 - x.2) else 0 with hG
  have hGle : ∑' x, G x ≤ ENNReal.ofReal R := by
    have h1 := half_bound T C₀ hC₀ hne hfib v O (fun x h => (hO x).1 h)
    rw [hAe, hBe, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hA0,
      ← ENNReal.ofReal_mul (by positivity)] at h1
    refine (ENNReal.pow_le_pow_left_iff two_ne_zero).1 (h1.trans (le_of_eq ?_))
    rw [← ENNReal.ofReal_pow hR0]
    congr 1
    rw [hR, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hB0]
    ring
  have hinv : Function.Involutive fun x : Mode × Mode => (-x.1 - x.2, x.2) := by
    intro x
    ext i <;> simp
  set e : Equiv.Perm (Mode × Mode) := Function.Involutive.toPerm _ hinv with he
  have he' : ∀ x, e x = (-x.1 - x.2, x.2) := fun _ => rfl
  have hle : ∀ x, ENNReal.ofReal (a x) ≤ G x + G (e x) := by
    intro x
    by_cases hT : T x.1 x.2 (-x.1 - x.2)
    · have h3 : -(-x.1 - x.2) - x.2 = x.1 := by abel
      have hval : ENNReal.ofReal (a x) = v x.1 * v x.2 * v (-x.1 - x.2) := by
        simp only [ha, hT, ite_true, hv]
        rw [ENNReal.ofReal_mul (mul_nonneg (hu0 _) (hu0 _)), ENNReal.ofReal_mul (hu0 _)]
      rcases le_total (absk x.1) (absk (-x.1 - x.2)) with h | h
      · have : O x := (hO x).2 ⟨hT, h⟩
        simp only [hval, hG, this, ite_true]
        exact le_self_add
      · have hT' : T (-x.1 - x.2) x.2 x.1 :=
          hswap₂ _ _ _ (hswap₁ _ _ _ (hswap₂ _ _ _ hT))
        have : O (e x) := by
          rw [hO, he']
          simp only [h3]
          exact ⟨hT', h⟩
        have h7 : G (e x) = v x.1 * v x.2 * v (-x.1 - x.2) := by
          simp only [hG, this, ite_true]
          simp only [he', h3]
          ring
        rw [hval, h7]
        exact le_add_self
    · simp [ha, hT]
  have hsumle : ∑' x, ENNReal.ofReal (a x) ≤ ENNReal.ofReal (2 * R) := by
    calc ∑' x, ENNReal.ofReal (a x) ≤ ∑' x, (G x + G (e x)) := tsum_le_tsum hle
      _ = ∑' x, G x + ∑' x, G (e x) := tsum_add
      _ = 2 * ∑' x, G x := by rw [e.tsum_eq, two_mul]
      _ ≤ 2 * ENNReal.ofReal R := by gcongr
      _ = ENNReal.ofReal (2 * R) := by
          rw [ENNReal.ofReal_mul (p := 2) (q := R) (by norm_num), ENNReal.ofReal_ofNat]
  have hfin : ∑' x, ENNReal.ofReal (a x) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsumle
  have hsummable : Summable a := by
    have := ENNReal.summable_toReal hfin
    refine this.congr fun x => ?_
    exact ENNReal.toReal_ofReal (ha0 x)
  refine ⟨hsummable, ?_⟩
  have h8 : ENNReal.ofReal (∑' x, a x) ≤ ENNReal.ofReal (2 * R) := by
    rwa [ENNReal.ofReal_tsum_of_nonneg ha0 hsummable]
  have h9 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h8
  have h10 : 2 * R ≤ 6 * Real.sqrt (2 * C₀) * A * Real.sqrt B := by
    rw [hR]
    have : 0 ≤ Real.sqrt (2 * C₀) * A * Real.sqrt B := by positivity
    nlinarith
  exact h9.trans h10

end OVNS
