import OddViscousNS.Quant.Energy.Near.NormForm
import OddViscousNS.Quant.Arith.NormCount

/-!
# E9: the centred count `#{p near : |D(p)| ≤ T} ≲_δ (K/|k₃|) K^δ T`

The arithmetic input of the near-moment bound (route report §2.1 step 2, reconstructed; the
volume states only the result `36 (K/|w|) 2^{ω(C)} Σ_∞(C) D_δ M^{2δ} T` and cites the MISSING
LOCAL266/267).  For a fast output `k` (`C = k₃²K² ≠ 0`), a pattern `(s₁, s₂)` and `T ≥ 0`, the
near legs `p` with `|D(p)| ≤ T` (`countSet`) are counted through the pair
`(d, y) = (D, A − B + C)` (`dyMap`):

1. `y² ≡ d (mod 4C)` since `D = y² − 4AC` (`sq_sub_normD`); on near triads `1 ≤ |d| ≤ T` and `y`
   lies in the window `|y − C| = |A − B| ≤ 4|k₃|K³` (`abs_legA_sub_le_of_near`);
2. the number of residues `y mod 4C` with `y² ≡ d`, summed over `1 ≤ |d| ≤ T`, is at most
   `2T τ(4C)³` (`sum_card_sqrt_le`): at most `4√gcd(d, p^e)` roots modulo each prime power
   (`card_sqrt_mod_prime_pow_le_sqrt_gcd`, the general-`d` form of
   `NormCount.lean`'s squarefree `card_sqrt_mod_prime_pow_le`), CRT (`card_sqrt_mul`, reused),
   `4^ω ≤ τ²`, and the gcd sum `Σ_{g ∣ n} √g · 2T/g ≤ 2Tτ(n)`;
3. each residue has at most `2W/(4C) + 1 ≤ 3K/|k₃|` lifts in the window
   (`card_residue_window_le`);
4. `(d, y)` fixes `A = (y² − d)/(4C)` and `B = A + C − y` (`fibre_dyMap_subset`), and the fibre
   `{p : A(p) = A, A(k − p) = B}` has `≤ C_δ K^δ` points (`card_fibre_le`): off-axis
   (`k_h ≠ 0`) `u = p₃` satisfies `u² ∣ A` (`≤ 2τ(A)` choices) and `p_h` lies on two circles
   with distinct centres (`≤ 2` points, `card_two_circles_le`); on-axis (`k_h = 0`) `u` is a root
   of a nonzero quintic (`≤ 5`, `card_axis_vertical_le`) and `p_h` lies on one circle
   (`r₂(n) ≤ C_δ n^δ`, from `sol_card_bound` at `a = −1`, `card_circle_le`).

Assembly (`near_count`): `#countSet ≤ Σ_{(d,y)} #fibre ≤ 2Tτ(4C)³ · (3K/|k₃|) · C_δK^δ`, and
`τ(4C)³ ≤ C_δ' K^δ` by `divisor_bound` (`4C ≤ 4K⁴`).  Numerically
`#/((K/|w|)T) ≤ 0.083` on the tested outputs (`count_check.py`).  The near condition is needed
only for step 1 (the window): without it the window is `O(K⁴)` and the lift count degrades to
`K²/k₃²`.
-/

noncomputable section

namespace OVNS.Quant

open Finset

/-! ### The count set -/

/-- The near legs of the output `k` and pattern `(s₁, s₂)` whose norm form has `|D| ≤ T`. -/
def countSet (s₁ s₂ : Sgn) (k : Mode) (T : ℝ) : Finset Mode :=
  (nearBox k).filter fun p => IsNear s₁ s₂ p k ∧ |(normD p k : ℝ)| ≤ T

theorem mem_countSet {s₁ s₂ : Sgn} {k p : Mode} {T : ℝ} :
    p ∈ countSet s₁ s₂ k T ↔ p ∈ nearBox k ∧ IsNear s₁ s₂ p k ∧ |(normD p k : ℝ)| ≤ T := by
  simp [countSet, Finset.mem_filter]

theorem countSet_mono (s₁ s₂ : Sgn) (k : Mode) {T T' : ℝ} (h : T ≤ T') :
    countSet s₁ s₂ k T ⊆ countSet s₁ s₂ k T' := by
  intro p hp
  rw [mem_countSet] at hp ⊢
  exact ⟨hp.1, hp.2.1, hp.2.2.trans h⟩

/-- Below `T = 1` the count set is empty (`1 ≤ |D|` on near triads). -/
theorem countSet_eq_empty_of_lt_one (s₁ s₂ : Sgn) (k : Mode) {T : ℝ} (hT : T < 1) :
    countSet s₁ s₂ k T = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro p hp
  obtain ⟨hp, hn, hT'⟩ := mem_countSet.1 hp
  linarith [one_le_abs_normD_of_near hp hn]

/-- The count set at the full range `T = 27K⁶` is the whole near set of the pattern. -/
theorem filter_isNear_subset_countSet (s₁ s₂ : Sgn) (k : Mode) :
    (nearBox k).filter (fun p => IsNear s₁ s₂ p k) ⊆ countSet s₁ s₂ k (27 * absk k ^ 6) := by
  intro p hp
  rw [Finset.mem_filter] at hp
  exact mem_countSet.2 ⟨hp.1, hp.2, abs_normD_le_pow_of_near hp.1 hp.2⟩

/-! ### Step 1: the pair `(d, y)` -/

/-- `(d, y) = (D(p), A − B + C)`. -/
def dyMap (p k : Mode) : ℤ × ℤ := (normD p k, legA p - legA (k - p) + legA k)

/-- `C = A(k) > 0` for a fast output. -/
theorem legA_pos {k : Mode} (hk : k 2 ≠ 0) : 0 < legA k := by
  have h1 : 0 < k 2 ^ 2 := by positivity
  have h2 : 0 < nsqZ k :=
    lt_of_lt_of_le h1 (sq_coord_le_nsqZ k 2)
  exact mul_pos h1 h2

/-- `(d, y)` determines `(A, B)`: `A = (y² − d)/(4C)` and `B = A + C − y`. -/
theorem legA_eq_of_dyMap {p k : Mode} (hk : k 2 ≠ 0) :
    legA p = ((legA p - legA (k - p) + legA k) ^ 2 - normD p k) / (4 * legA k) ∧
      legA (k - p) = ((legA p - legA (k - p) + legA k) ^ 2 - normD p k) / (4 * legA k)
        + legA k - (legA p - legA (k - p) + legA k) := by
  have hC : (4 * legA k) ≠ 0 := by have := legA_pos hk; omega
  have e : ((legA p - legA (k - p) + legA k) ^ 2 - normD p k) / (4 * legA k) = legA p := by
    rw [sq_sub_normD, show 4 * legA p * legA k = (4 * legA k) * legA p by ring]
    exact Int.mul_ediv_cancel_left _ hC
  rw [e]
  constructor
  · rfl
  · ring

/-- The fibre of `(A, B)`: the box legs with `A(p) = A` and `A(k − p) = B`. -/
def fibre (k : Mode) (A B : ℤ) : Finset Mode :=
  (nearBox k).filter fun p => legA p = A ∧ legA (k - p) = B

/-- The fibres of `dyMap` on the count set are contained in the fibres of `(A, B)`. -/
theorem fibre_dyMap_subset (s₁ s₂ : Sgn) {k : Mode} (hk : k 2 ≠ 0) (T : ℝ) (d y : ℤ) :
    (countSet s₁ s₂ k T).filter (fun p => dyMap p k = (d, y)) ⊆
      fibre k ((y ^ 2 - d) / (4 * legA k)) ((y ^ 2 - d) / (4 * legA k) + legA k - y) := by
  intro p hp
  rw [Finset.mem_filter, mem_countSet] at hp
  obtain ⟨⟨hbox, -, -⟩, hdy⟩ := hp
  simp only [dyMap, Prod.mk.injEq] at hdy
  obtain ⟨rfl, rfl⟩ := hdy
  rw [fibre, Finset.mem_filter]
  exact ⟨hbox, legA_eq_of_dyMap hk⟩

/-- On the count set: `1 ≤ |d| ≤ T`, `y` in the window `|y − C| ≤ 4|k₃|K³`, and
`y² ≡ d (mod 4C)`. -/
theorem dyMap_mem {s₁ s₂ : Sgn} {k p : Mode} {T : ℝ} (hp : p ∈ countSet s₁ s₂ k T) :
    (normD p k ≠ 0 ∧ |(normD p k : ℝ)| ≤ T) ∧
      |((legA p - legA (k - p) + legA k - legA k : ℤ) : ℝ)| ≤ 4 * |(k 2 : ℝ)| * absk k ^ 3 ∧
      ((legA p - legA (k - p) + legA k : ℤ) : ZMod (4 * legA k).natAbs) ^ 2 = normD p k := by
  obtain ⟨hbox, hn, hT⟩ := mem_countSet.1 hp
  refine ⟨⟨normD_ne_zero_of_near hbox hn, hT⟩, ?_, ?_⟩
  · have := abs_legA_sub_le_of_near hbox hn
    rwa [show legA p - legA (k - p) + legA k - legA k = legA p - legA (k - p) by ring]
  · have hdvd : ((4 * legA k).natAbs : ℤ) ∣ (legA p - legA (k - p) + legA k) ^ 2 - normD p k := by
      rw [Int.natAbs_dvd, sq_sub_normD]
      exact ⟨legA p, by ring⟩
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdvd
    push_cast at this ⊢
    exact sub_eq_zero.1 this

/-! ### Step 2: square roots modulo `n` for general `d` -/

/-- val of product. -/
private theorem pv_mul {p : ℕ} [Fact p.Prime] {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    padicValInt p (a * b) = padicValInt p a + padicValInt p b := padicValInt.mul ha hb

/-- `p^e ∣ x y`, `x ≠ 0`, `¬ p^b ∣ x` gives `p^(e+1-b) ∣ y`. -/
private theorem dvd_of_dvd_mul_not {p : ℕ} [Fact p.Prime] {e b : ℕ} {x y : ℤ}
    (h : (p : ℤ) ^ e ∣ x * y) (hx : ¬ (p : ℤ) ^ b ∣ x) : (p : ℤ) ^ (e + 1 - b) ∣ y := by
  by_cases hy : y = 0
  · simp [hy]
  have hx0 : x ≠ 0 := by rintro rfl; exact hx (dvd_zero _)
  rw [padicValInt_dvd_iff] at h hx ⊢
  rw [pv_mul hx0 hy] at h
  have := mul_ne_zero hx0 hy
  right; omega

/-- The coset count. -/
private theorem card_coset_le {p e m : ℕ} (hp : p.Prime) (hm : m ≤ e) (c : ZMod (p ^ e)) :
    {t : ZMod (p ^ e) | ∃ z : ℤ, t = c + (p : ZMod (p ^ e)) ^ m * z}.ncard ≤ p ^ (e - m) := by
  rw [← Nat.card_coe_set_eq]
  let f : Fin (p ^ (e - m)) → {t : ZMod (p ^ e) | ∃ z : ℤ, t = c + (p : ZMod (p ^ e)) ^ m * z} :=
    fun y => ⟨c + (p : ZMod (p ^ e)) ^ m * ((y : ℕ) : ℤ), ⟨_, rfl⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨t, z, rfl⟩
    have hq : (0 : ℤ) < (p ^ (e - m) : ℕ) := by
      exact_mod_cast pow_pos hp.pos _
    refine ⟨⟨(z % (p ^ (e - m) : ℕ)).toNat, ?_⟩, ?_⟩
    · rw [← Int.ofNat_lt, Int.toNat_of_nonneg (Int.emod_nonneg _ hq.ne')]
      exact Int.emod_lt_of_pos _ hq
    · apply Subtype.ext
      simp only [f]
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hq.ne')]
      congr 1
      have h2 : z % (p ^ (e - m) : ℕ) = z - (p ^ (e - m) : ℕ) * (z / (p ^ (e - m) : ℕ)) := by
        rw [Int.emod_def]
      rw [h2]
      push_cast
      have h3 : (p : ZMod (p ^ e)) ^ m * (p : ZMod (p ^ e)) ^ (e - m) = 0 := by
        rw [← pow_add, Nat.add_sub_cancel' hm]
        exact_mod_cast ZMod.natCast_self (p ^ e)
      linear_combination (-(z / (p ^ (e - m) : ℤ) : ZMod (p ^ e))) * h3
  calc _ ≤ Nat.card (Fin (p ^ (e - m))) := Nat.card_le_card_of_surjective f hf
    _ = _ := Nat.card_fin _

/-- `p ^ e ∣ T²` forces `p ^ ⌈e/2⌉ ∣ T`. -/
private theorem dvd_of_dvd_sq {p : ℕ} [Fact p.Prime] {e : ℕ} {T : ℤ}
    (h : (p : ℤ) ^ e ∣ T ^ 2) : (p : ℤ) ^ (e - e / 2) ∣ T := by
  by_cases hT : T = 0
  · simp [hT]
  rw [padicValInt_dvd_iff] at h ⊢
  rw [sq, pv_mul hT hT] at h
  have := mul_ne_zero hT hT
  right; omega

/-- A root `T` of `T² ≡ D (mod p^e)` with `p^e ∤ D` has `2 v(T) = v(D) < e`. -/
private theorem val_root {p : ℕ} [Fact p.Prime] {e : ℕ} {T D : ℤ}
    (hD : ¬ (p : ℤ) ^ e ∣ D) (hT : (p : ℤ) ^ e ∣ T ^ 2 - D) :
    D ≠ 0 ∧ 2 * padicValInt p T = padicValInt p D ∧ padicValInt p D < e := by
  have hD0 : D ≠ 0 := by rintro rfl; exact hD (dvd_zero _)
  have hT0 : T ≠ 0 := by
    rintro rfl
    exact hD (by simpa using hT.neg_right)
  have hT2 : T ^ 2 ≠ 0 := pow_ne_zero _ hT0
  have hlt : padicValInt p D < e := by
    by_contra hc
    exact hD ((padicValInt_dvd_iff _ _).2 (Or.inr (by omega)))
  have hv2 : padicValInt p (T ^ 2) = 2 * padicValInt p T := by
    rw [sq, pv_mul hT0 hT0]; ring
  refine ⟨hD0, ?_, hlt⟩
  have hsub : ∀ n, n ≤ e → (p : ℤ) ^ n ∣ T ^ 2 - D :=
    fun n hn => (pow_dvd_pow _ hn).trans hT
  rcases lt_trichotomy (2 * padicValInt p T) (padicValInt p D) with h | h | h
  · exfalso
    have h1 : (p : ℤ) ^ (2 * padicValInt p T + 1) ∣ D :=
      (padicValInt_dvd_iff _ _).2 (Or.inr (by omega))
    have h2 := dvd_add (hsub _ (by omega)) h1
    rw [sub_add_cancel, padicValInt_dvd_iff] at h2
    omega
  · exact h
  · exfalso
    have h1 : (p : ℤ) ^ (padicValInt p D + 1) ∣ T ^ 2 :=
      (padicValInt_dvd_iff _ _).2 (Or.inr (by omega))
    have h2 := dvd_sub h1 (hsub _ (by omega))
    rw [sub_sub_cancel, padicValInt_dvd_iff] at h2
    omega

/-- Two roots of `T² ≡ D (mod p^e)` with `p^e ∤ D` agree up to sign modulo
`p ^ (e − (v(T₁) + δ))`, `δ = [p = 2]`. -/
private theorem pair_root {p : ℕ} [hp : Fact p.Prime] {e : ℕ} {T T₁ D : ℤ}
    (hD : ¬ (p : ℤ) ^ e ∣ D) (hT₁ : (p : ℤ) ^ e ∣ T₁ ^ 2 - D) (hT : (p : ℤ) ^ e ∣ T ^ 2 - D) :
    (p : ℤ) ^ (e - (padicValInt p T₁ + if p = 2 then 1 else 0)) ∣ T₁ - T ∨
      (p : ℤ) ^ (e - (padicValInt p T₁ + if p = 2 then 1 else 0)) ∣ T₁ + T := by
  set δ : ℕ := if p = 2 then 1 else 0 with hδ
  set a := padicValInt p T₁ with ha
  have hT0 : T₁ ≠ 0 := by
    rintro rfl
    exact hD (by simpa using hT₁.neg_right)
  have h2 : padicValInt p 2 ≤ δ := by
    by_cases hp2 : p = 2
    · subst hp2
      have h22 := padicValInt_self (p := 2)
      simp only [Nat.cast_ofNat] at h22
      simp [hδ, h22]
    · rw [padicValInt.eq_zero_of_not_dvd]
      · exact Nat.zero_le _
      intro h
      have : p ∣ 2 := by exact_mod_cast h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this)
  have hnot : ¬ ((p : ℤ) ^ (a + 1 + δ) ∣ T₁ - T ∧ (p : ℤ) ^ (a + 1 + δ) ∣ T₁ + T) := by
    rintro ⟨h1, h3⟩
    have h4 := dvd_add h1 h3
    rw [show T₁ - T + (T₁ + T) = 2 * T₁ by ring, padicValInt_dvd_iff,
      pv_mul two_ne_zero hT0] at h4
    omega
  have hprod : (p : ℤ) ^ e ∣ (T₁ - T) * (T₁ + T) := by
    have := dvd_sub hT₁ hT
    rwa [show T₁ ^ 2 - D - (T ^ 2 - D) = (T₁ - T) * (T₁ + T) by ring] at this
  have he : e + 1 - (a + 1 + δ) = e - (a + δ) := by omega
  by_cases hx : (p : ℤ) ^ (a + 1 + δ) ∣ T₁ - T
  · left
    have hy : ¬ (p : ℤ) ^ (a + 1 + δ) ∣ T₁ + T := fun hy => hnot ⟨hx, hy⟩
    rw [mul_comm] at hprod
    simpa [he] using dvd_of_dvd_mul_not hprod hy
  · right
    simpa [he] using dvd_of_dvd_mul_not hprod hx

/-- Integer lift of a root. -/
private theorem dvd_of_root {p e : ℕ} [NeZero (p ^ e)] {d : ℤ} {t : ZMod (p ^ e)}
    (ht : t ^ 2 = d) : (p : ℤ) ^ e ∣ ((t.val : ℕ) : ℤ) ^ 2 - d := by
  have h : ((((t.val : ℕ) : ℤ) ^ 2 - d : ℤ) : ZMod (p ^ e)) = 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val, ht, sub_self]
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h
  exact_mod_cast this

/-- From an integer congruence to a coset in `ZMod (p ^ e)`. -/
private theorem coset_of_dvd {p e m : ℕ} [NeZero (p ^ e)] {t₁ t : ZMod (p ^ e)} {s : ℤ}
    (hs : s = 1 ∨ s = -1)
    (h : (p : ℤ) ^ m ∣ ((t₁.val : ℕ) : ℤ) - s * ((t.val : ℕ) : ℤ)) :
    ∃ z : ℤ, t = s * t₁ + (p : ZMod (p ^ e)) ^ m * z := by
  obtain ⟨k, hk⟩ := h
  refine ⟨-(s * k), ?_⟩
  have := congrArg (fun x : ℤ => (x : ZMod (p ^ e))) hk
  push_cast at this
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at this
  have hs2 : (s : ZMod (p ^ e)) * s = 1 := by
    rcases hs with rfl | rfl <;> simp
  push_cast
  linear_combination (-(s : ZMod (p ^ e))) * this - t * hs2

/-- **Roots modulo a prime power, general `d`**: `#{t mod p^e : t² ≡ d} ≤ 4 √gcd(d, p^e)`
(route report §2.1 step 2: "#roots of `y² ≡ d mod p^e` `≤ 2p^{⌊ν_p(d)/2⌋}`", with the factor `4`
absorbing `p = 2`).  Proof sketch: with `p^ν ∥ d`, `ν < e`, roots need `ν` even and are
`p^{ν/2} t'` with `t'² ≡ d/p^ν (mod p^{e−ν})` a unit root (`≤ 4` by `int_sqrt_mod_prime_pow`
with `d' = d/p^ν`, or directly), lifted in `p^{ν/2}` ways; for `p^e ∣ d` the roots are the
multiples of `p^{⌈e/2⌉}`, `p^{⌊e/2⌋} ≤ √(p^e)` of them. -/
theorem card_sqrt_mod_prime_pow_le_sqrt_gcd (d : ℤ) {p e : ℕ} (hp : p.Prime) (he : 0 < e) :
    (Nat.card {t : ZMod (p ^ e) // t ^ 2 = d} : ℝ) ≤
      4 * Real.sqrt (Nat.gcd d.natAbs (p ^ e)) := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  set G := Nat.gcd d.natAbs (p ^ e) with hG
  have hGpos : 0 < G := Nat.gcd_pos_of_pos_right _ (pow_pos hp.pos _)
  have hsqrt : ∀ j : ℕ, p ^ (2 * j) ∣ d.natAbs → 2 * j ≤ e → (p : ℝ) ^ j ≤ Real.sqrt G := by
    intro j hj hje
    apply Real.le_sqrt_of_sq_le
    have : p ^ (2 * j) ≤ G :=
      Nat.le_of_dvd hGpos (Nat.dvd_gcd hj (pow_dvd_pow _ hje))
    rw [← pow_mul, mul_comm]
    exact_mod_cast this
  change ((Nat.card ↥{t : ZMod (p ^ e) | t ^ 2 = (d : ZMod (p ^ e))}) : ℝ) ≤ _
  rw [Nat.card_coe_set_eq]
  by_cases hD : (p : ℤ) ^ e ∣ d
  · have hsub : {t : ZMod (p ^ e) | t ^ 2 = (d : ZMod (p ^ e))} ⊆
        {t | ∃ z : ℤ, t = 0 + (p : ZMod (p ^ e)) ^ (e - e / 2) * z} := by
      intro t ht
      have h1 := dvd_add (dvd_of_root ht) hD
      rw [sub_add_cancel] at h1
      have h2 := dvd_of_dvd_sq h1
      simpa using coset_of_dvd (t₁ := 0) (t := t) (s := -1) (Or.inr rfl) (by simpa using h2)
    have hc := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
      (card_coset_le hp (by omega) 0)
    rw [show e - (e - e / 2) = e / 2 by omega] at hc
    have hDn : p ^ e ∣ d.natAbs := Int.natCast_dvd.1 (by exact_mod_cast hD)
    have h3 := hsqrt (e / 2) ((pow_dvd_pow p (show 2 * (e / 2) ≤ e by omega)).trans hDn)
      (by omega)
    have h4 : (({t : ZMod (p ^ e) | t ^ 2 = (d : ZMod (p ^ e))}.ncard : ℕ) : ℝ) ≤ p ^ (e / 2) := by
      exact_mod_cast hc
    nlinarith [Real.sqrt_nonneg (G : ℝ)]
  · by_cases hex : ∃ t₁ : ZMod (p ^ e), t₁ ^ 2 = d
    · obtain ⟨t₁, ht₁⟩ := hex
      set a := padicValInt p ((t₁.val : ℕ) : ℤ) with ha
      set δ : ℕ := if p = 2 then 1 else 0 with hδ
      obtain ⟨-, hv, hve⟩ := val_root hD (dvd_of_root ht₁)
      have hsub : {t : ZMod (p ^ e) | t ^ 2 = (d : ZMod (p ^ e))} ⊆
          {t | ∃ z : ℤ, t = ((1 : ℤ) : ZMod (p ^ e)) * t₁ + (p : ZMod (p ^ e)) ^ (e - (a + δ)) * z}
            ∪ {t | ∃ z : ℤ,
              t = ((-1 : ℤ) : ZMod (p ^ e)) * t₁ + (p : ZMod (p ^ e)) ^ (e - (a + δ)) * z} := by
        intro t ht
        rcases pair_root hD (dvd_of_root ht₁) (dvd_of_root ht) with h | h
        · left; exact coset_of_dvd (Or.inl rfl) (by rw [one_mul]; exact h)
        · right; exact coset_of_dvd (Or.inr rfl) (by rw [neg_one_mul, sub_neg_eq_add]; exact h)
      have hc := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
        ((Set.ncard_union_le _ _).trans
          (add_le_add (card_coset_le hp (Nat.sub_le _ _) _) (card_coset_le hp (Nat.sub_le _ _) _)))
      have h5 : p ^ (e - (e - (a + δ))) ≤ p ^ (a + δ) := Nat.pow_le_pow_right hp.pos (by omega)
      have h6 : 2 * p ^ (a + δ) ≤ 4 * p ^ a := by
        by_cases hp2 : p = 2
        · simp only [hδ, hp2, ite_true, pow_succ]; omega
        · simp only [hδ, hp2, ite_false, add_zero]; omega
      have h7 : p ^ (2 * a) ∣ d.natAbs := by
        have : (p : ℤ) ^ (2 * a) ∣ d := (padicValInt_dvd_iff _ _).2 (Or.inr hv.le)
        exact Int.natCast_dvd.1 (by exact_mod_cast this)
      have h3 := hsqrt a h7 (by omega)
      have h4 : (({t : ZMod (p ^ e) | t ^ 2 = (d : ZMod (p ^ e))}.ncard : ℕ) : ℝ) ≤ 4 * p ^ a := by
        exact_mod_cast hc.trans (by omega)
      nlinarith [Real.sqrt_nonneg (G : ℝ)]
    · have hS : {t : ZMod (p ^ e) | t ^ 2 = (d : ZMod (p ^ e))} = ∅ :=
        Set.eq_empty_iff_forall_notMem.2 fun t ht => hex ⟨t, ht⟩
      rw [hS, Set.ncard_empty, Nat.cast_zero]
      positivity

/-- `2^{ω(n)} ≤ τ(n)`: every prime factor contributes a factor `≥ 2` to `∏ (e_p + 1)`. -/
theorem two_pow_omega_le_card_divisors {n : ℕ} (hn : 0 < n) :
    2 ^ n.primeFactors.card ≤ n.divisors.card := by
  rw [Nat.card_divisors hn.ne', ← Finset.prod_const]
  refine Finset.prod_le_prod fun p hp => ?_
  have := Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp) hn.ne'
    (Nat.dvd_of_mem_primeFactors hp)
  omega

/-- **Roots modulo `n`, general `d`**: `#{t mod n : t² ≡ d} ≤ 4^{ω(n)} √gcd(d, n)` (CRT over
the prime powers of `n`: `card_sqrt_mul` of `NormCount.lean`, `Nat.Coprime.gcd_mul`). -/
theorem card_sqrt_mod_le_sqrt_gcd (d : ℤ) {n : ℕ} (hn : 0 < n) :
    (Nat.card {t : ZMod n // t ^ 2 = d} : ℝ) ≤
      4 ^ n.primeFactors.card * Real.sqrt (Nat.gcd d.natAbs n) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    rw [Nat.primeFactors_prime_pow hk.ne' hp, Finset.card_singleton, pow_one]
    exact card_sqrt_mod_prime_pow_le_sqrt_gcd d hp hk
  | zero => exact absurd hn (lt_irrefl 0)
  | one =>
    simp only [Nat.primeFactors_one, Finset.card_empty, pow_zero, Nat.gcd_one_right,
      Nat.cast_one, Real.sqrt_one, mul_one]
    exact_mod_cast Finite.card_le_one_iff_subsingleton.2 inferInstance
  | coprime a b ha hb hab iha ihb =>
    rw [card_sqrt_mul d hab, Nat.cast_mul, Nat.primeFactors_mul (by omega) (by omega),
      Finset.card_union_of_disjoint (Nat.Coprime.disjoint_primeFactors hab), pow_add,
      Nat.Coprime.gcd_mul _ hab, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
    calc (Nat.card {t : ZMod a // t ^ 2 = d} : ℝ) * Nat.card {t : ZMod b // t ^ 2 = d}
        ≤ (4 ^ a.primeFactors.card * Real.sqrt (Nat.gcd d.natAbs a)) *
          (4 ^ b.primeFactors.card * Real.sqrt (Nat.gcd d.natAbs b)) :=
          mul_le_mul (iha (by omega)) (ihb (by omega)) (by positivity) (by positivity)
      _ = _ := by ring

/-- The number of nonzero multiples of `g ≥ 1` in `[−T, T]` is at most `2T/g`. -/
theorem card_multiples_le (g T : ℕ) (hg : 0 < g) :
    ((((Finset.Icc (-(T : ℤ)) T).erase 0).filter fun d => (g : ℤ) ∣ d).card : ℝ) ≤
      2 * T / g := by
  set S := ((Finset.Icc (-(T : ℤ)) T).erase 0).filter fun d => (g : ℤ) ∣ d with hS
  set R : ℤ := ((T / g : ℕ) : ℤ) with hR
  have hg' : (0 : ℤ) < g := by exact_mod_cast hg
  have hsub : S ⊆ ((Finset.Icc (-R) R).erase 0).image fun m => (g : ℤ) * m := by
    intro d hd
    rw [hS, Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc] at hd
    obtain ⟨⟨hd0, hdT⟩, m, rfl⟩ := hd
    rw [Finset.mem_image]
    refine ⟨m, ?_, rfl⟩
    rw [Finset.mem_erase, Finset.mem_Icc]
    have hm0 : m ≠ 0 := by
      rintro rfl
      simp at hd0
    have h1 : |(g : ℤ) * m| ≤ T := abs_le.2 hdT
    rw [abs_mul, abs_of_pos hg'] at h1
    have h3 : |m| ≤ (T : ℤ) / g := by
      rw [Int.le_ediv_iff_mul_le hg']
      linarith
    rw [hR, Int.natCast_ediv]
    exact ⟨hm0, abs_le.1 h3⟩
  have hinj : Set.InjOn (fun m : ℤ => (g : ℤ) * m) ((Finset.Icc (-R) R).erase 0) :=
    fun m _ m' _ h => mul_left_cancel₀ hg'.ne' h
  have hR0 : 0 ≤ R := by rw [hR]; exact Int.natCast_nonneg _
  have hIcc : (Finset.Icc (-R) R).card = 2 * (T / g) + 1 := by
    rw [Int.card_Icc]
    have : R + 1 - -R = ((2 * (T / g) + 1 : ℕ) : ℤ) := by
      rw [hR]
      push_cast
      ring
    rw [this, Int.toNat_natCast]
  have hcard : S.card ≤ 2 * (T / g) := by
    calc S.card ≤ _ := Finset.card_le_card hsub
      _ = ((Finset.Icc (-R) R).erase 0).card := Finset.card_image_of_injOn hinj
      _ = (Finset.Icc (-R) R).card - 1 :=
          Finset.card_erase_of_mem (by rw [Finset.mem_Icc]; constructor <;> linarith)
      _ = 2 * (T / g) := by rw [hIcc]; rfl
  calc (S.card : ℝ) ≤ ((2 * (T / g) : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = 2 * ((T / g : ℕ) : ℝ) := by push_cast; ring
    _ ≤ 2 * ((T : ℝ) / g) := by gcongr; exact Nat.cast_div_le
    _ = 2 * T / g := by ring

/-- **The residue sum**: `Σ_{1 ≤ |d| ≤ T} #{t mod n : t² ≡ d} ≤ 2 T τ(n)³` (route report §2.1
step 2: "the total number of residues `y mod 4C` is `≤ 4·2^ω Σ_∞ T`", here with the elementary
`4^ω ≤ τ²` and `Σ_{g ∣ n} g^{−1/2} ≤ τ(n)`). -/
theorem sum_card_sqrt_le (n T : ℕ) (hn : 0 < n) :
    (∑ d ∈ (Finset.Icc (-(T : ℤ)) T).erase 0, (Nat.card {t : ZMod n // t ^ 2 = d} : ℝ)) ≤
      2 * T * (n.divisors.card : ℝ) ^ 3 := by
  set S := (Finset.Icc (-(T : ℤ)) T).erase 0 with hS
  have h4 : (4 : ℝ) ^ n.primeFactors.card ≤ (n.divisors.card : ℝ) ^ 2 := by
    have h' : ((2 ^ n.primeFactors.card : ℕ) : ℝ) ≤ n.divisors.card := by
      exact_mod_cast two_pow_omega_le_card_divisors hn
    push_cast at h'
    calc (4 : ℝ) ^ n.primeFactors.card = ((2 : ℝ) ^ n.primeFactors.card) ^ 2 := by
          rw [← pow_mul, mul_comm, pow_mul]
          norm_num
      _ ≤ (n.divisors.card : ℝ) ^ 2 := by gcongr
  have hmaps : ∀ d ∈ S, Nat.gcd d.natAbs n ∈ n.divisors := fun d _ =>
    Nat.mem_divisors.2 ⟨Nat.gcd_dvd_right _ _, hn.ne'⟩
  calc ∑ d ∈ S, (Nat.card {t : ZMod n // t ^ 2 = d} : ℝ)
      ≤ ∑ d ∈ S, 4 ^ n.primeFactors.card * Real.sqrt (Nat.gcd d.natAbs n) :=
        Finset.sum_le_sum fun d _ => card_sqrt_mod_le_sqrt_gcd d hn
    _ = ∑ g ∈ n.divisors, ∑ d ∈ S.filter (fun d => Nat.gcd d.natAbs n = g),
          4 ^ n.primeFactors.card * Real.sqrt (Nat.gcd d.natAbs n) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ _g ∈ n.divisors, (4 : ℝ) ^ n.primeFactors.card * (2 * (T : ℝ)) := by
        refine Finset.sum_le_sum fun g hg => ?_
        have hg1 : 1 ≤ g := Nat.pos_of_mem_divisors hg
        have hgR : (1 : ℝ) ≤ g := by exact_mod_cast hg1
        have hcard : ((S.filter fun d => Nat.gcd d.natAbs n = g).card : ℝ) ≤ 2 * T / g := by
          refine le_trans ?_ (card_multiples_le g T hg1)
          exact_mod_cast Finset.card_le_card fun d hd => by
            rw [Finset.mem_filter] at hd ⊢
            exact ⟨hd.1, Int.natCast_dvd.2 (hd.2 ▸ Nat.gcd_dvd_left _ _)⟩
        have hsg : Real.sqrt g / g ≤ 1 := by
          rw [div_le_one (by positivity)]
          exact Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
        calc ∑ d ∈ S.filter (fun d => Nat.gcd d.natAbs n = g),
              4 ^ n.primeFactors.card * Real.sqrt (Nat.gcd d.natAbs n)
            = ∑ _d ∈ S.filter (fun d => Nat.gcd d.natAbs n = g),
                4 ^ n.primeFactors.card * Real.sqrt g :=
              Finset.sum_congr rfl fun d hd => by rw [(Finset.mem_filter.1 hd).2]
          _ = ((S.filter fun d => Nat.gcd d.natAbs n = g).card : ℝ) *
                (4 ^ n.primeFactors.card * Real.sqrt g) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (2 * T / g) * (4 ^ n.primeFactors.card * Real.sqrt g) := by gcongr
          _ = (4 : ℝ) ^ n.primeFactors.card * (2 * (T : ℝ)) * (Real.sqrt g / g) := by ring
          _ ≤ (4 : ℝ) ^ n.primeFactors.card * (2 * (T : ℝ)) * 1 := by gcongr
          _ = (4 : ℝ) ^ n.primeFactors.card * (2 * (T : ℝ)) := mul_one _
    _ = (n.divisors.card : ℝ) * ((4 : ℝ) ^ n.primeFactors.card * (2 * (T : ℝ))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (n.divisors.card : ℝ) * ((n.divisors.card : ℝ) ^ 2 * (2 * (T : ℝ))) := by gcongr
    _ = 2 * T * (n.divisors.card : ℝ) ^ 3 := by ring

/-! ### Step 3: lifts of a residue into a window -/

/-- **Lifts**: a window `[c₀ − W, c₀ + W]` contains at most `2W/n + 1` integers of a given residue
class modulo `n` (route report §2.1 step 2: "each residue has `≤ (9/4)K/|w|` lifts"). -/
theorem card_residue_window_le {n : ℕ} (hn : 0 < n) (c₀ : ℤ) {W : ℤ} (hW : 0 ≤ W) (r : ZMod n) :
    (((Finset.Icc (c₀ - W) (c₀ + W)).filter fun y : ℤ => ((y : ℤ) : ZMod n) = r).card : ℝ) ≤
      2 * W / n + 1 := by
  set S := (Finset.Icc (c₀ - W) (c₀ + W)).filter fun y : ℤ => ((y : ℤ) : ZMod n) = r with hS
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hmaps : ∀ y ∈ S, (y - (c₀ - W)) / n ∈ Finset.Icc (0 : ℤ) (2 * W / n) := by
    intro y hy
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hy
    rw [Finset.mem_Icc]
    exact ⟨Int.ediv_nonneg (by linarith) hn'.le, Int.ediv_le_ediv hn' (by linarith)⟩
  have hinj : Set.InjOn (fun y : ℤ => (y - (c₀ - W)) / n) S := by
    intro y hy y' hy' h
    simp only at h
    rw [Finset.mem_coe, hS, Finset.mem_filter] at hy hy'
    have hmod : (y - (c₀ - W)) % n = (y' - (c₀ - W)) % n := by
      have : ((y - (c₀ - W) : ℤ) : ZMod n) = ((y' - (c₀ - W) : ℤ) : ZMod n) := by
        push_cast
        rw [hy.2, hy'.2]
      exact (ZMod.intCast_eq_intCast_iff' _ _ _).1 this
    have e1 := Int.mul_ediv_add_emod (y - (c₀ - W)) n
    have e2 := Int.mul_ediv_add_emod (y' - (c₀ - W)) n
    rw [h, hmod] at e1
    linarith
  have hcard : S.card ≤ (2 * W / n + 1).toNat := by
    calc S.card ≤ (Finset.Icc (0 : ℤ) (2 * W / n)).card :=
          Finset.card_le_card_of_injOn _ hmaps hinj
      _ = (2 * W / n + 1).toNat := by rw [Int.card_Icc, sub_zero]
  have hq : ((2 * W / n : ℤ) : ℝ) ≤ 2 * W / n := by
    rw [le_div_iff₀ (by exact_mod_cast hn)]
    exact_mod_cast Int.ediv_mul_le (2 * W) hn'.ne'
  have h0 : (0 : ℤ) ≤ 2 * W / n + 1 := by
    have := Int.ediv_nonneg (by linarith : (0 : ℤ) ≤ 2 * W) hn'.le
    linarith
  calc (S.card : ℝ) ≤ (((2 * W / n + 1).toNat : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = ((2 * W / n : ℤ) : ℝ) + 1 := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
        push_cast
        ring
    _ ≤ 2 * W / n + 1 := by linarith

/-! ### Step 4: the fibres of `(A, B)` -/

open Polynomial in
/-- The line–circle quadratic `4(a² + b²)Y² − 4bLY + (L² − 4a²r)`. -/
private def circPoly (a b L r : ℤ) : Polynomial ℤ :=
  C (4 * (a ^ 2 + b ^ 2)) * X ^ 2 + C (-4 * b * L) * X + C (L ^ 2 - 4 * a ^ 2 * r)

private lemma natDegree_circPoly {a : ℤ} (ha : a ≠ 0) (b L r : ℤ) :
    (circPoly a b L r).natDegree = 2 := by
  have h : a ^ 2 + b ^ 2 ≠ 0 := by positivity
  unfold circPoly
  compute_degree!

private lemma eval_circPoly (a b L r y : ℤ) :
    (circPoly a b L r).eval y = 4 * (a ^ 2 + b ^ 2) * y ^ 2 - 4 * b * L * y +
      (L ^ 2 - 4 * a ^ 2 * r) := by
  simp only [circPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  ring

/-- Two circles with centres `0` and `c`, `c₁ ≠ 0`: the second coordinate determines the point
and is a root of `circPoly`. -/
private theorem card_two_circles_le_aux {c : ℤ × ℤ} (hc : c.1 ≠ 0) (r₁ r₂ : ℤ)
    (S : Finset (ℤ × ℤ))
    (hS : ∀ x ∈ S, x.1 ^ 2 + x.2 ^ 2 = r₁ ∧ (c.1 - x.1) ^ 2 + (c.2 - x.2) ^ 2 = r₂) :
    S.card ≤ 2 := by
  classical
  set L := c.1 ^ 2 + c.2 ^ 2 + r₁ - r₂ with hL
  have hlin : ∀ x ∈ S, 2 * c.1 * x.1 + 2 * c.2 * x.2 = L := by
    intro x hx
    obtain ⟨h1, h2⟩ := hS x hx
    rw [hL]
    linear_combination h1 - h2
  set P := circPoly c.1 c.2 L r₁ with hP
  have hdeg : P.natDegree = 2 := natDegree_circPoly hc c.2 L r₁
  have hP0 : P ≠ 0 := by
    intro h0
    simp [h0] at hdeg
  have hmaps : ∀ x ∈ S, x.2 ∈ P.roots.toFinset := by
    intro x hx
    obtain ⟨h1, -⟩ := hS x hx
    have h3 := hlin x hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0, Polynomial.IsRoot.def, hP, eval_circPoly,
      ← h3, ← h1]
    ring
  have hinj : Set.InjOn (fun x : ℤ × ℤ => x.2) S := by
    intro x hx x' hx' h
    simp only at h
    have h3 := hlin x hx
    have h3' := hlin x' hx'
    rw [h] at h3
    have h4 : 2 * c.1 * x.1 = 2 * c.1 * x'.1 := by linarith
    exact Prod.ext (mul_left_cancel₀ (mul_ne_zero two_ne_zero hc) h4) h
  calc S.card ≤ P.roots.toFinset.card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
    _ ≤ 2 := hdeg ▸ Polynomial.card_roots' P

/-- **Two circles** in `ℤ²` with distinct centres `0` and `c ≠ 0` meet in at most two points
(subtract the equations: a line; a line meets a circle in `≤ 2` points, `Polynomial.card_roots'`
on a quadratic with leading coefficient `c₁² + c₂² ≠ 0`). -/
theorem card_two_circles_le {c : ℤ × ℤ} (hc : c ≠ 0) (r₁ r₂ : ℤ) (S : Finset (ℤ × ℤ))
    (hS : ∀ x ∈ S, x.1 ^ 2 + x.2 ^ 2 = r₁ ∧ (c.1 - x.1) ^ 2 + (c.2 - x.2) ^ 2 = r₂) :
    S.card ≤ 2 := by
  classical
  by_cases h1 : c.1 ≠ 0
  · exact card_two_circles_le_aux h1 r₁ r₂ S hS
  · push Not at h1
    have h2 : c.2 ≠ 0 := fun h2 => hc (Prod.ext h1 h2)
    have key := card_two_circles_le_aux (c := c.swap) (by simpa using h2) r₁ r₂
      (S.image Prod.swap) (by
        intro x hx
        rw [Finset.mem_image] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        obtain ⟨hy1, hy2⟩ := hS y hy
        simp only [Prod.fst_swap, Prod.snd_swap]
        constructor <;> linarith)
    rwa [Finset.card_image_of_injective _ Prod.swap_injective] at key

open Polynomial in
/-- The axis quintic `A(w−u)² − u⁴(w−u)² − Bu² + u²(w−u)⁴`, expanded in `u`:
`−2w u⁵ + 5w² u⁴ − 4w³ u³ + (A − B + w⁴) u² − 2Aw u + Aw²`. -/
private def axisPoly (w A B : ℤ) : Polynomial ℤ :=
  C (-2 * w) * X ^ 5 + C (5 * w ^ 2) * X ^ 4 + C (-4 * w ^ 3) * X ^ 3 + C (A - B + w ^ 4) * X ^ 2
    + C (-2 * A * w) * X + C (A * w ^ 2)

private lemma natDegree_axisPoly {w : ℤ} (hw : w ≠ 0) (A B : ℤ) :
    (axisPoly w A B).natDegree = 5 := by
  have h : -2 * w ≠ 0 := by positivity
  unfold axisPoly
  compute_degree!

private lemma eval_axisPoly (w A B u : ℤ) :
    (axisPoly w A B).eval u = -2 * w * u ^ 5 + 5 * w ^ 2 * u ^ 4 - 4 * w ^ 3 * u ^ 3 +
      (A - B + w ^ 4) * u ^ 2 - 2 * A * w * u + A * w ^ 2 := by
  simp only [axisPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  ring

/-- **On-axis vertical components**: for `k = (0, 0, w)`, `w ≠ 0`, the vertical component
`u = p₃` of a leg with `A(p) = A`, `A(k − p) = B` and `|p_h|² = n` satisfies
`A(w − u)² − u⁴(w − u)² = Bu² − u²(w − u)⁴`, a polynomial of degree exactly `5` in `u` (leading
coefficient `−2w`), so at most five values of `u` occur (`Polynomial.card_roots'`, as in
`Counting.lean`'s `card_resonant_vertical`). -/
theorem card_axis_vertical_le {w : ℤ} (hw : w ≠ 0) (A B : ℤ) (S : Finset ℤ)
    (hS : ∀ u ∈ S, u ≠ 0 ∧ w - u ≠ 0 ∧
      ∃ n : ℤ, A = u ^ 2 * (n + u ^ 2) ∧ B = (w - u) ^ 2 * (n + (w - u) ^ 2)) :
    S.card ≤ 5 := by
  classical
  set P := axisPoly w A B with hP
  have hdeg : P.natDegree = 5 := natDegree_axisPoly hw A B
  have hP0 : P ≠ 0 := by
    intro h0
    simp [h0] at hdeg
  have hsub : S ⊆ P.roots.toFinset := by
    intro u hu
    obtain ⟨-, -, n, hA, hB⟩ := hS u hu
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0, Polynomial.IsRoot.def, hP, eval_axisPoly,
      hA, hB]
    ring
  calc S.card ≤ P.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
    _ ≤ 5 := hdeg ▸ Polynomial.card_roots' P

/-- **Lattice points on a circle**: `r₂(n) = #{(x, y) : x² + y² = n} ≤ C_δ n^δ`, from
`sol_card_bound` at `a = −1` (`NormCount.lean`: `≤ (4 log₂(2n²) + 4) τ(n)³`) and
`divisor_bound`. -/
theorem card_circle_le {δ : ℝ} (hδ : 0 < δ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
    ((solSet (-1) n n).card : ℝ) ≤ C * (n : ℝ) ^ δ := by
  obtain ⟨K₁, hK₁, h₁⟩ := log_count_bound 1 hδ
  obtain ⟨K₂, hK₂, h₂⟩ := tau_cube_bound 1 hδ
  refine ⟨max 9 (K₁ * K₂), by positivity, fun n hn => ?_⟩
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hnδ : 1 ≤ (n : ℝ) ^ δ := Real.one_le_rpow (by exact_mod_cast hn) hδ.le
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · obtain rfl : n = 1 := by omega
    have h9 : (solSet (-1) 1 1).card ≤ 9 := by
      calc (solSet (-1) 1 1).card ≤ (Finset.Icc (-(1 : ℤ)) 1 ×ˢ Finset.Icc (-(1 : ℤ)) 1).card :=
            Finset.card_filter_le _ _
        _ = 9 := by simp [Finset.card_product, Int.card_Icc]
    calc ((solSet (-1) 1 1).card : ℝ) ≤ 9 := by exact_mod_cast h9
      _ ≤ max 9 (K₁ * K₂) := le_max_left _ _
      _ = max 9 (K₁ * K₂) * ((1 : ℕ) : ℝ) ^ δ := by simp [Real.one_rpow]
  · obtain ⟨d, hd, hcount⟩ :=
      sol_card_bound (a := -1) (M := (n : ℤ)) (N := n) (by norm_num) hn0
    have hB : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hX : (((1 + d.natAbs) * (n * (-1 : ℤ).natAbs) ^ 2 : ℕ) : ℝ) ≤ (n : ℝ) ^ (5 * 1 + 1) := by
      have hd1 : ((d.natAbs : ℕ) : ℝ) ≤ 1 := by
        have : d.natAbs ≤ (-1 : ℤ).natAbs := hd
        exact_mod_cast this
      simp only [Int.natAbs_neg, Int.natAbs_one, mul_one]
      push_cast
      have h2 : (2 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      have h4 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := one_le_pow₀ (by linarith)
      calc (1 + ((d.natAbs : ℕ) : ℝ)) * (n : ℝ) ^ 2 ≤ 2 * (n : ℝ) ^ 2 := by gcongr; linarith
        _ ≤ (n : ℝ) ^ 2 * (n : ℝ) ^ 4 := by nlinarith
        _ = (n : ℝ) ^ (5 * 1 + 1) := by ring
    have hlog := h₁ n hB _ hX
    have htau := h₂ n hB (n : ℤ) hn0 (by simp)
    calc ((solSet (-1) n n).card : ℝ)
        ≤ (((4 * Nat.log 2 ((1 + d.natAbs) * (n * (-1 : ℤ).natAbs) ^ 2) + 4) *
            (n : ℤ).natAbs.divisors.card ^ 3 : ℕ) : ℝ) := by exact_mod_cast hcount
      _ = (4 * Nat.log 2 ((1 + d.natAbs) * (n * (-1 : ℤ).natAbs) ^ 2) + 4 : ℝ) *
            (((n : ℤ).natAbs.divisors.card ^ 3 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (K₁ * (n : ℝ) ^ (δ / 2)) * (K₂ * (n : ℝ) ^ (δ / 2)) :=
          mul_le_mul hlog htau (by positivity) (by positivity)
      _ = K₁ * K₂ * (n : ℝ) ^ δ := by
          rw [mul_mul_mul_comm, ← Real.rpow_add (by positivity), add_halves]
      _ ≤ max 9 (K₁ * K₂) * (n : ℝ) ^ δ := by
          gcongr
          exact le_max_right _ _

theorem nsqZ_eq (p : Mode) : nsqZ p = p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 := by
  simp [nsqZ, Fin.sum_univ_three]

/-- Off-axis outputs: over a fixed vertical component `u`, the fibre legs are lattice points of
two circles with centres `0` and `k_h ≠ 0`, hence at most two. -/
private theorem card_fibre_filter_le_two {k : Mode} (hk : (k 0, k 1) ≠ (0, 0)) (A B u : ℤ) :
    ((fibre k A B).filter fun p => p 2 = u).card ≤ 2 := by
  classical
  set S := (fibre k A B).filter fun p => p 2 = u with hS
  have hinj : Set.InjOn (fun p : Mode => (p 0, p 1)) S := by
    intro p hp p' hp' h
    simp only [Prod.mk.injEq] at h
    rw [Finset.mem_coe, hS, Finset.mem_filter] at hp hp'
    have h2 : p 2 = p' 2 := hp.2.trans hp'.2.symm
    funext i
    fin_cases i
    · exact h.1
    · exact h.2
    · exact h2
  rw [← Finset.card_image_of_injOn hinj]
  by_cases hu : u = 0
  · have hempty : S = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro p hp
      rw [hS, Finset.mem_filter, fibre, Finset.mem_filter] at hp
      exact (mem_nearBox.1 hp.1.1).2.1 (hp.2.trans hu)
    simp [hempty]
  apply card_two_circles_le (c := (k 0, k 1)) hk (A / u ^ 2 - u ^ 2)
    (B / (k 2 - u) ^ 2 - (k 2 - u) ^ 2)
  intro x hx
  rw [Finset.mem_image] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  rw [hS, Finset.mem_filter, fibre, Finset.mem_filter] at hp
  obtain ⟨⟨hbox, hA, hB⟩, hpu⟩ := hp
  obtain ⟨-, -, hj3, -, -⟩ := mem_nearBox.1 hbox
  have hju : (k - p) 2 = k 2 - u := by simp [hpu]
  have e1 : A / u ^ 2 = p 0 ^ 2 + p 1 ^ 2 + u ^ 2 := by
    rw [← hA, legA, nsqZ_eq, hpu]
    exact Int.mul_ediv_cancel_left _ (pow_ne_zero 2 hu)
  have e2 : B / (k 2 - u) ^ 2 = (k 0 - p 0) ^ 2 + (k 1 - p 1) ^ 2 + (k 2 - u) ^ 2 := by
    rw [← hB, legA, nsqZ_eq]
    simp only [Pi.sub_apply]
    rw [hpu]
    exact Int.mul_ediv_cancel_left _ (pow_ne_zero 2 (by rwa [hju] at hj3))
  constructor
  · simp only
    rw [e1]
    ring
  · simp only
    rw [e2]
    ring

/-- Over a fixed vertical component `u`, the fibre legs inject into the lattice points of the
circle `x² + y² = A/u² − u²`. -/
private theorem card_fibre_filter_le_circle {k : Mode} (A B u : ℤ) (hu : u ≠ 0) :
    ((fibre k A B).filter fun p => p 2 = u).card ≤
      (solSet (-1) (((A / u ^ 2 - u ^ 2).toNat : ℕ) : ℤ) (A / u ^ 2 - u ^ 2).toNat).card := by
  classical
  set n : ℤ := A / u ^ 2 - u ^ 2 with hn
  apply Finset.card_le_card_of_injOn (fun p : Mode => (p 0, p 1))
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_filter, fibre, Finset.mem_filter] at hp
    obtain ⟨⟨-, hA, -⟩, hpu⟩ := hp
    have hn' : n = p 0 ^ 2 + p 1 ^ 2 := by
      rw [hn, ← hA, legA, nsqZ_eq, hpu, Int.mul_ediv_cancel_left _ (pow_ne_zero 2 hu)]
      ring
    have hn0 : 0 ≤ n := by
      rw [hn']
      positivity
    rw [Finset.mem_coe, mem_solSet, Int.toNat_of_nonneg hn0]
    refine ⟨?_, ?_, ?_⟩
    · rw [hn', Int.abs_eq_natAbs]
      nlinarith [Int.natAbs_le_self_sq (p 0), sq_nonneg (p 1)]
    · rw [hn', Int.abs_eq_natAbs]
      nlinarith [Int.natAbs_le_self_sq (p 1), sq_nonneg (p 0)]
    · simp only
      rw [hn']
      ring
  · intro p hp p' hp' h
    simp only [Prod.mk.injEq] at h
    rw [Finset.mem_coe, Finset.mem_filter] at hp hp'
    funext i
    fin_cases i
    · exact h.1
    · exact h.2
    · exact hp.2.trans hp'.2.symm

/-- Off-axis: the vertical components occurring in the fibre divide `A`, so there are at most
`2τ(|A|)` of them. -/
private theorem card_image_vertical_le {k : Mode} (A B : ℤ) (hA : A ≠ 0) :
    ((fibre k A B).image fun p => p 2).card ≤ 2 * A.natAbs.divisors.card := by
  classical
  have hsub : (fibre k A B).image (fun p => p 2) ⊆
      A.natAbs.divisors.image (fun d : ℕ => (d : ℤ)) ∪
        A.natAbs.divisors.image (fun d : ℕ => -(d : ℤ)) := by
    intro u hu
    rw [Finset.mem_image] at hu
    obtain ⟨p, hp, rfl⟩ := hu
    rw [fibre, Finset.mem_filter] at hp
    obtain ⟨-, hA', -⟩ := hp
    have hdvd : (p 2).natAbs ∣ A.natAbs := by
      rw [Int.natAbs_dvd_natAbs, ← hA', legA]
      exact Dvd.intro (p 2 * nsqZ p) (by ring)
    have hmem : (p 2).natAbs ∈ A.natAbs.divisors :=
      Nat.mem_divisors.2 ⟨hdvd, Int.natAbs_ne_zero.2 hA⟩
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
    rcases Int.natAbs_eq (p 2) with h | h
    · exact Or.inl ⟨_, hmem, h.symm⟩
    · exact Or.inr ⟨_, hmem, h.symm⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ A.natAbs.divisors.card + A.natAbs.divisors.card :=
        Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = 2 * A.natAbs.divisors.card := by ring

/-- On-axis: at most five vertical components occur in the fibre (`card_axis_vertical_le`). -/
private theorem card_image_vertical_le_five {k : Mode} (hk : k 2 ≠ 0) (h0 : k 0 = 0)
    (h1 : k 1 = 0) (A B : ℤ) : ((fibre k A B).image fun p => p 2).card ≤ 5 := by
  classical
  apply card_axis_vertical_le hk A B
  intro u hu
  rw [Finset.mem_image] at hu
  obtain ⟨p, hp, rfl⟩ := hu
  rw [fibre, Finset.mem_filter] at hp
  obtain ⟨hbox, hA, hB⟩ := hp
  obtain ⟨-, hp3, hj3, -, -⟩ := mem_nearBox.1 hbox
  refine ⟨hp3, by simpa using hj3, p 0 ^ 2 + p 1 ^ 2, ?_, ?_⟩
  · rw [← hA, legA, nsqZ_eq]
  · rw [← hB, legA, nsqZ_eq]
    simp only [Pi.sub_apply, h0, h1]
    ring

/-- **The fibre bound**: `#{p ∈ box : A(p) = A, A(k − p) = B} ≤ C_δ K^δ` for fast outputs
(route report §2.1 step 2, "fibre off-axis `≤ 4τ(d_A)`", "fibre on-axis: quintic in `u`, then
`r₂(n) ≤ 4τ(n)`"; here `r₂` through `card_circle_le`). -/
theorem card_fibre_le {δ : ℝ} (hδ : 0 < δ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (k : Mode) (A B : ℤ), k 2 ≠ 0 → ((fibre k A B).card : ℝ) ≤ C * absk k ^ δ := by
  classical
  obtain ⟨C₁, hC₁, hτ⟩ := divisor_bound (by positivity : 0 < δ / 4)
  obtain ⟨C₂, hC₂, hr⟩ := card_circle_le (by positivity : 0 < δ / 2)
  refine ⟨4 * C₁ + 5 * (1 + C₂), by positivity, fun k A B hk => ?_⟩
  have hK1 : 1 ≤ absk k := one_le_absk (by rintro rfl; simp at hk)
  have hKδ : 1 ≤ absk k ^ δ := Real.one_le_rpow hK1 hδ.le
  have hK0 : 0 ≤ absk k ^ δ := by linarith
  rcases (fibre k A B).eq_empty_or_nonempty with he | ⟨p₀, hp₀⟩
  · rw [he, Finset.card_empty, Nat.cast_zero]
    positivity
  have hp₀' := hp₀
  rw [fibre, Finset.mem_filter] at hp₀'
  obtain ⟨hbox₀, hA₀, -⟩ := hp₀'
  have hApos : 0 < A := hA₀ ▸ legA_pos (mem_nearBox.1 hbox₀).2.1
  have hAle : (A : ℝ) ≤ absk k ^ 4 := by
    rw [← hA₀]
    exact (legA_le p₀).trans
      (pow_le_pow_left₀ (absk_nonneg _) (mem_nearBox.1 hbox₀).2.2.2.1 4)
  have hfw : ∀ x ∈ fibre k A B, (fun p : Mode => p 2) x ∈ (fibre k A B).image fun p => p 2 :=
    fun x hx => Finset.mem_image_of_mem _ hx
  by_cases hax : (k 0, k 1) = (0, 0)
  · -- on-axis output: at most five vertical components, each fibre on one circle
    simp only [Prod.mk.injEq] at hax
    obtain ⟨h0, h1⟩ := hax
    have himg := card_image_vertical_le_five hk h0 h1 A B
    have hfib : ∀ u ∈ (fibre k A B).image (fun p => p 2),
        (((fibre k A B).filter fun p => p 2 = u).card : ℝ) ≤ 1 + C₂ * absk k ^ δ := by
      intro u hu
      rw [Finset.mem_image] at hu
      obtain ⟨p, hp, rfl⟩ := hu
      rw [fibre, Finset.mem_filter] at hp
      obtain ⟨hbox, hA, -⟩ := hp
      obtain ⟨-, hp3, -, hpk, -⟩ := mem_nearBox.1 hbox
      set n : ℤ := A / p 2 ^ 2 - p 2 ^ 2 with hn
      have hn' : n = p 0 ^ 2 + p 1 ^ 2 := by
        rw [hn, ← hA, legA, nsqZ_eq, Int.mul_ediv_cancel_left _ (pow_ne_zero 2 hp3)]
        ring
      have hn0 : 0 ≤ n := by
        rw [hn']
        positivity
      have hnK : (n : ℝ) ≤ absk k ^ 2 := by
        rw [absk_sq_eq_nsqZ]
        have h2 := (absk_le_absk_iff p k).1 hpk
        rw [nsqZ_eq] at h2
        have : n ≤ nsqZ k := by
          rw [hn']
          nlinarith [sq_nonneg (p 2)]
        exact_mod_cast this
      have hcard := card_fibre_filter_le_circle (k := k) A B (p 2) hp3
      rcases Nat.eq_zero_or_pos n.toNat with hz | hpos
      · have h1' : (solSet (-1) ((0 : ℕ) : ℤ) 0).card ≤ 1 := by
          calc (solSet (-1) ((0 : ℕ) : ℤ) 0).card
              ≤ (Finset.Icc (-((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ) ×ˢ
                  Finset.Icc (-((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ)).card := Finset.card_filter_le _ _
            _ = 1 := by simp
        rw [hz] at hcard
        have : (((fibre k A B).filter fun p' => p' 2 = p 2).card : ℝ) ≤ 1 := by
          exact_mod_cast hcard.trans h1'
        linarith [mul_nonneg hC₂ hK0]
      · have h := hr n.toNat hpos
        have hnR : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
          rw [← Int.cast_natCast, Int.toNat_of_nonneg hn0]
        calc (((fibre k A B).filter fun p' => p' 2 = p 2).card : ℝ)
            ≤ (solSet (-1) (n.toNat : ℤ) n.toNat).card := by exact_mod_cast hcard
          _ ≤ C₂ * ((n.toNat : ℕ) : ℝ) ^ (δ / 2) := h
          _ ≤ C₂ * (absk k ^ 2) ^ (δ / 2) := by
              gcongr
              rw [hnR]
              exact hnK
          _ = C₂ * absk k ^ δ := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul (absk_nonneg k)]
              congr 2
              push_cast
              ring
          _ ≤ 1 + C₂ * absk k ^ δ := by linarith
    calc ((fibre k A B).card : ℝ)
        = ∑ u ∈ (fibre k A B).image (fun p => p 2),
            (((fibre k A B).filter fun p => p 2 = u).card : ℝ) := by
          rw [Finset.card_eq_sum_card_fiberwise hfw]
          push_cast
          rfl
      _ ≤ ∑ _u ∈ (fibre k A B).image (fun p => p 2), (1 + C₂ * absk k ^ δ) :=
          Finset.sum_le_sum hfib
      _ = (((fibre k A B).image fun p => p 2).card : ℝ) * (1 + C₂ * absk k ^ δ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 5 * (1 + C₂ * absk k ^ δ) := by
          gcongr
          exact_mod_cast himg
      _ ≤ (4 * C₁ + 5 * (1 + C₂)) * absk k ^ δ := by nlinarith
  · -- off-axis output: `u² ∣ A`, then two circles with distinct centres
    have h2 : ∀ u ∈ (fibre k A B).image (fun p => p 2),
        ((fibre k A B).filter fun p => p 2 = u).card ≤ 2 :=
      fun u _ => card_fibre_filter_le_two hax A B u
    have hmul := Finset.card_le_mul_card_image (fibre k A B) 2 h2
    have himg := card_image_vertical_le (k := k) A B hApos.ne'
    have hτA : (A.natAbs.divisors.card : ℝ) ≤ C₁ * (A.natAbs : ℝ) ^ (δ / 4) :=
      hτ A.natAbs (Int.natAbs_pos.2 hApos.ne')
    have hAn : ((A.natAbs : ℕ) : ℝ) ≤ absk k ^ 4 := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hApos)]
      exact hAle
    calc ((fibre k A B).card : ℝ) ≤ ((2 * (2 * A.natAbs.divisors.card) : ℕ) : ℝ) := by
          exact_mod_cast hmul.trans (Nat.mul_le_mul_left 2 himg)
      _ = 4 * (A.natAbs.divisors.card : ℝ) := by push_cast; ring
      _ ≤ 4 * (C₁ * (A.natAbs : ℝ) ^ (δ / 4)) := by gcongr
      _ ≤ 4 * (C₁ * (absk k ^ 4) ^ (δ / 4)) := by gcongr
      _ = 4 * C₁ * absk k ^ δ := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (absk_nonneg k)]
          push_cast
          rw [show (4 : ℝ) * (δ / 4) = δ by ring]
          ring
      _ ≤ (4 * C₁ + 5 * (1 + C₂)) * absk k ^ δ := by nlinarith

/-! ### The centred count -/

/-- **The centred count** (route report §2.1 step 2 and §2.2): for every `δ > 0` there is `C_δ`
such that for every fast output `k`, every pattern `(s₁, s₂)` and every `T ≥ 0`,
`#{p near : |D(p)| ≤ T} ≤ C_δ (K/|k₃|) K^δ T`.  Assembly of steps 1–4 above:
`#countSet ≤ Σ_{(d, y) ∈ dyMap(countSet)} #fibre ≤ (Σ_{1≤|d|≤T} #{y mod 4C : y² ≡ d}) ·
(3K/|k₃|) · C_δ K^δ ≤ 2Tτ(4C)³ · 3K/|k₃| · C_δK^δ`, with `τ(4C)³ ≤ C_δ' K^δ` (`divisor_bound`,
`4C ≤ 4K⁴`).  For `T < 1` the set is empty (`countSet_eq_empty_of_lt_one`). -/
theorem near_count {δ : ℝ} (hδ : 0 < δ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (s₁ s₂ : Sgn) (k : Mode) (T : ℝ), k 2 ≠ 0 → 0 ≤ T →
      ((countSet s₁ s₂ k T).card : ℝ) ≤ C * (absk k / |(k 2 : ℝ)|) * absk k ^ δ * T := by
  classical
  obtain ⟨Cf, hCf, hfib⟩ := card_fibre_le (by positivity : 0 < δ / 2)
  obtain ⟨Cτ, hCτ, hτ⟩ := divisor_bound (by positivity : 0 < δ / 24)
  refine ⟨7 * Cτ ^ 3 * (4 : ℝ) ^ (δ / 8) * Cf, by positivity, fun s₁ s₂ k T hk hT => ?_⟩
  have hK1 : 1 ≤ absk k := one_le_absk (by rintro rfl; simp at hk)
  have hK0 : 0 < absk k := by linarith
  have hw : 0 < |(k 2 : ℝ)| := abs_pos.2 (by exact_mod_cast hk)
  have hwK : |(k 2 : ℝ)| ≤ absk k := abs_coord_le_absk k 2
  have hw1 : 1 ≤ |(k 2 : ℝ)| := by exact_mod_cast Int.one_le_abs hk
  have hKw : 1 ≤ absk k / |(k 2 : ℝ)| := by
    rw [le_div_iff₀ hw]
    linarith
  -- the modulus `n = 4C`
  set n : ℕ := (4 * legA k).natAbs with hn
  have hC : 0 < legA k := legA_pos hk
  have hn0 : 0 < n := by
    rw [hn]
    exact Int.natAbs_pos.2 (by omega)
  have : NeZero n := ⟨hn0.ne'⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnR : (n : ℝ) = 4 * |(k 2 : ℝ)| ^ 2 * absk k ^ 2 := by
    have h1 : ((n : ℤ) : ℝ) = (n : ℝ) := Int.cast_natCast n
    have h2 : (n : ℤ) = 4 * legA k := by
      rw [hn]
      exact Int.natAbs_of_nonneg (by omega)
    rw [← h1, h2, sq_abs, absk_sq_eq_nsqZ, legA]
    push_cast
    ring
  have hnK : (n : ℝ) ≤ 4 * absk k ^ 4 := by
    rw [hnR]
    have h1 : |(k 2 : ℝ)| ^ 2 ≤ absk k ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hwK 2
    have h2 : 0 ≤ absk k ^ 2 := by positivity
    nlinarith
  -- the window half-width `W`
  set W : ℤ := ⌈4 * |(k 2 : ℝ)| * absk k ^ 3⌉ with hW
  have hW0 : 0 ≤ W := by
    rw [hW]
    exact Int.ceil_nonneg (by positivity)
  have hWR : (0 : ℝ) ≤ W := by exact_mod_cast hW0
  have hWle : (W : ℝ) ≤ 5 * |(k 2 : ℝ)| * absk k ^ 3 := by
    have h1 := Int.ceil_lt_add_one (4 * |(k 2 : ℝ)| * absk k ^ 3)
    have h2 : 1 ≤ |(k 2 : ℝ)| * absk k ^ 3 := by
      have := one_le_pow₀ hK1 (n := 3)
      nlinarith
    rw [hW]
    linarith
  -- the `d`-range and the window
  set Tn : ℕ := ⌊T⌋₊ with hTn
  have hTnT : (Tn : ℝ) ≤ T := Nat.floor_le hT
  set D : Finset ℤ := (Finset.Icc (-(Tn : ℤ)) Tn).erase 0 with hD
  set win : Finset ℤ := Finset.Icc (legA k - W) (legA k + W) with hwin
  set S := countSet s₁ s₂ k T with hS
  set f : Mode → ℤ × ℤ := fun p => dyMap p k with hf
  -- Step A: the fibres of `(d, y)` are fibres of `(A, B)`.
  have hfw : ∀ p ∈ S, f p ∈ S.image f := fun p hp => Finset.mem_image_of_mem f hp
  have hA : (S.card : ℝ) ≤ (S.image f).card * (Cf * absk k ^ (δ / 2)) := by
    rw [Finset.card_eq_sum_card_fiberwise hfw]
    push_cast
    calc ∑ dy ∈ S.image f, ((S.filter fun p => f p = dy).card : ℝ)
        ≤ ∑ _dy ∈ S.image f, Cf * absk k ^ (δ / 2) := by
          refine Finset.sum_le_sum ?_
          rintro ⟨d, y⟩ _
          calc ((S.filter fun p => f p = (d, y)).card : ℝ)
              ≤ ((fibre k ((y ^ 2 - d) / (4 * legA k))
                  ((y ^ 2 - d) / (4 * legA k) + legA k - y)).card : ℝ) := by
                exact_mod_cast Finset.card_le_card (fibre_dyMap_subset s₁ s₂ hk T d y)
            _ ≤ Cf * absk k ^ (δ / 2) := hfib k _ _ hk
      _ = (S.image f).card * (Cf * absk k ^ (δ / 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- Step B: the image lies in the pairs `(d, y)`, `d ∈ D`, `y ∈ win`, `y² ≡ d (mod n)`.
  have hB : S.image f ⊆ D.biUnion fun d =>
      (win.filter fun y : ℤ => ((y : ℤ) : ZMod n) ^ 2 = (d : ZMod n)).image fun y => (d, y) := by
    intro dy hdy
    rw [Finset.mem_image] at hdy
    obtain ⟨p, hp, rfl⟩ := hdy
    obtain ⟨⟨hd0, hdT⟩, hwin', hcong⟩ := dyMap_mem hp
    rw [Finset.mem_biUnion]
    refine ⟨normD p k, ?_, ?_⟩
    · rw [hD, Finset.mem_erase, Finset.mem_Icc]
      have h1 : (normD p k).natAbs ≤ Tn := by
        rw [hTn]
        apply Nat.le_floor
        rw [Nat.cast_natAbs, Int.cast_abs]
        exact hdT
      refine ⟨hd0, ?_, ?_⟩ <;> omega
    · rw [Finset.mem_image]
      refine ⟨legA p - legA (k - p) + legA k, ?_, rfl⟩
      rw [Finset.mem_filter, hwin, Finset.mem_Icc]
      refine ⟨?_, hcong⟩
      have h1 : |((legA p - legA (k - p) + legA k - legA k : ℤ) : ℝ)| ≤ (W : ℝ) :=
        hwin'.trans (by rw [hW]; exact Int.le_ceil _)
      have h2 : |legA p - legA (k - p) + legA k - legA k| ≤ W := by exact_mod_cast h1
      rw [abs_le] at h2
      constructor <;> linarith [h2.1, h2.2]
  -- Step C: for each `d`, the window carries at most `#roots · (2W/n + 1)` values of `y`.
  have hroots : ∀ d : ℤ,
      ((win.filter fun y : ℤ => ((y : ℤ) : ZMod n) ^ 2 = (d : ZMod n)).card : ℝ) ≤
        (Nat.card {t : ZMod n // t ^ 2 = d} : ℝ) * (2 * W / n + 1) := by
    intro d
    set R : Finset (ZMod n) := Finset.univ.filter fun r => r ^ 2 = (d : ZMod n) with hR
    have hsub : (win.filter fun y : ℤ => ((y : ℤ) : ZMod n) ^ 2 = (d : ZMod n)) ⊆
        R.biUnion fun r => win.filter fun y : ℤ => ((y : ℤ) : ZMod n) = r := by
      intro y hy
      rw [Finset.mem_filter] at hy
      rw [Finset.mem_biUnion]
      refine ⟨(y : ZMod n), ?_, ?_⟩
      · rw [hR, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hy.2⟩
      · rw [Finset.mem_filter]
        exact ⟨hy.1, rfl⟩
    have hcardR : (R.card : ℝ) = Nat.card {t : ZMod n // t ^ 2 = d} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    calc ((win.filter fun y : ℤ => ((y : ℤ) : ZMod n) ^ 2 = (d : ZMod n)).card : ℝ)
        ≤ ((R.biUnion fun r => win.filter fun y : ℤ => ((y : ℤ) : ZMod n) = r).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ∑ r ∈ R, ((win.filter fun y : ℤ => ((y : ℤ) : ZMod n) = r).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _r ∈ R, (2 * (W : ℝ) / n + 1) :=
          Finset.sum_le_sum fun r _ => card_residue_window_le hn0 (legA k) hW0 r
      _ = (R.card : ℝ) * (2 * W / n + 1) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = _ := by rw [hcardR]
  have hsumroots : ∑ d ∈ D, (Nat.card {t : ZMod n // t ^ 2 = d} : ℝ) ≤
      2 * T * (n.divisors.card : ℝ) ^ 3 := by
    refine (sum_card_sqrt_le n Tn hn0).trans ?_
    gcongr
  have hlift0 : (0 : ℝ) ≤ 2 * W / n + 1 := by positivity
  have himg : ((S.image f).card : ℝ) ≤
      2 * T * (n.divisors.card : ℝ) ^ 3 * (2 * W / n + 1) := by
    calc ((S.image f).card : ℝ)
        ≤ ((D.biUnion fun d => (win.filter fun y : ℤ =>
            ((y : ℤ) : ZMod n) ^ 2 = (d : ZMod n)).image fun y => (d, y)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hB
      _ ≤ ∑ d ∈ D, (((win.filter fun y : ℤ => ((y : ℤ) : ZMod n) ^ 2 = (d : ZMod n)).image
            fun y => (d, y)).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ d ∈ D, ((win.filter fun y : ℤ => ((y : ℤ) : ZMod n) ^ 2 = (d : ZMod n)).card : ℝ) :=
          Finset.sum_le_sum fun d _ => by exact_mod_cast Finset.card_image_le
      _ ≤ ∑ d ∈ D, (Nat.card {t : ZMod n // t ^ 2 = d} : ℝ) * (2 * W / n + 1) :=
          Finset.sum_le_sum fun d _ => hroots d
      _ = (∑ d ∈ D, (Nat.card {t : ZMod n // t ^ 2 = d} : ℝ)) * (2 * W / n + 1) := by
          rw [Finset.sum_mul]
      _ ≤ 2 * T * (n.divisors.card : ℝ) ^ 3 * (2 * W / n + 1) := by gcongr
  -- Step D: numerics of the lifts and of `τ(n)³`.
  have hlift : 2 * (W : ℝ) / n + 1 ≤ 7 / 2 * (absk k / |(k 2 : ℝ)|) := by
    have h1 : 2 * (W : ℝ) / n ≤ 5 / 2 * (absk k / |(k 2 : ℝ)|) := by
      rw [div_le_iff₀ hnpos, hnR]
      calc 2 * (W : ℝ) ≤ 2 * (5 * |(k 2 : ℝ)| * absk k ^ 3) := by gcongr
        _ = 5 / 2 * (absk k / |(k 2 : ℝ)|) * (4 * |(k 2 : ℝ)| ^ 2 * absk k ^ 2) := by
            field_simp
            ring
    linarith
  have hτ3 : (n.divisors.card : ℝ) ^ 3 ≤ Cτ ^ 3 * (4 : ℝ) ^ (δ / 8) * absk k ^ (δ / 2) := by
    have h1 := hτ n hn0
    have h2 : (n : ℝ) ^ (δ / 24) ≤ (4 * absk k ^ 4) ^ (δ / 24) :=
      Real.rpow_le_rpow (by positivity) hnK (by positivity)
    have h3 : ((4 : ℝ) * absk k ^ 4) ^ (δ / 24) = 4 ^ (δ / 24) * absk k ^ (δ / 6) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast,
        ← Real.rpow_mul hK0.le]
      congr 2
      push_cast
      ring
    have e4 : ((4 : ℝ) ^ (δ / 24)) ^ 3 = 4 ^ (δ / 8) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1
      push_cast
      ring
    have eK : (absk k ^ (δ / 6)) ^ 3 = absk k ^ (δ / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le]
      congr 1
      push_cast
      ring
    calc (n.divisors.card : ℝ) ^ 3 ≤ (Cτ * (n : ℝ) ^ (δ / 24)) ^ 3 :=
          pow_le_pow_left₀ (by positivity) h1 3
      _ ≤ (Cτ * (4 ^ (δ / 24) * absk k ^ (δ / 6))) ^ 3 := by
          gcongr
          rw [← h3]
          exact h2
      _ = Cτ ^ 3 * (4 : ℝ) ^ (δ / 8) * absk k ^ (δ / 2) := by
          rw [mul_pow, mul_pow, e4, eK]
          ring
  have hKδ : absk k ^ (δ / 2) * absk k ^ (δ / 2) = absk k ^ δ := by
    rw [← Real.rpow_add hK0, add_halves]
  have hτ0 : (0 : ℝ) ≤ (n.divisors.card : ℝ) ^ 3 := by positivity
  calc (S.card : ℝ) ≤ (S.image f).card * (Cf * absk k ^ (δ / 2)) := hA
    _ ≤ (2 * T * (n.divisors.card : ℝ) ^ 3 * (2 * W / n + 1)) * (Cf * absk k ^ (δ / 2)) := by
        gcongr
    _ ≤ (2 * T * (Cτ ^ 3 * (4 : ℝ) ^ (δ / 8) * absk k ^ (δ / 2)) *
          (7 / 2 * (absk k / |(k 2 : ℝ)|))) * (Cf * absk k ^ (δ / 2)) := by
        gcongr
    _ = 7 * Cτ ^ 3 * (4 : ℝ) ^ (δ / 8) * Cf * (absk k / |(k 2 : ℝ)|) *
          (absk k ^ (δ / 2) * absk k ^ (δ / 2)) * T := by ring
    _ = 7 * Cτ ^ 3 * (4 : ℝ) ^ (δ / 8) * Cf * (absk k / |(k 2 : ℝ)|) * absk k ^ δ * T := by
        rw [hKδ]

/-- The count in the form used by the layer-cake summation: at integer thresholds `t ≥ 1`,
`#{p near : |D(p)| ≤ t} ≤ L t` with `L = C_δ (K/|k₃|) K^δ`. -/
theorem near_count_nat {δ : ℝ} (hδ : 0 < δ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (s₁ s₂ : Sgn) (k : Mode), k 2 ≠ 0 → ∀ t : ℕ, 1 ≤ t →
      ((((nearBox k).filter fun p => IsNear s₁ s₂ p k).filter
        fun p => (normD p k).natAbs ≤ t).card : ℝ) ≤
          C * (absk k / |(k 2 : ℝ)|) * absk k ^ δ * t := by
  obtain ⟨C, hC, h⟩ := near_count hδ
  refine ⟨C, hC, fun s₁ s₂ k hk t _ => ?_⟩
  refine le_trans ?_ (h s₁ s₂ k t hk (by positivity))
  gcongr
  intro p hp
  simp only [Finset.mem_filter] at hp
  refine mem_countSet.2 ⟨hp.1.1, hp.1.2, ?_⟩
  have h1 : ((normD p k).natAbs : ℝ) ≤ t := by exact_mod_cast hp.2
  rwa [Nat.cast_natAbs, Int.cast_abs] at h1

end OVNS.Quant

end
