import OddViscousNS.Quant.Arith.Weighted.Defs
import OddViscousNS.Quant.Arith.Divisor

/-!
# The uniform quadratic norm count (Lemma quant-norm), proved

`quadraticNormCount : QuadraticNormCount`: for every `C` and `η > 0` there is `K` such that for
`B ≥ 2` and nonzero integers `a, M` with `|a|, |M| ≤ B^C`, the equation `X² − aY² = M` has at most
`K B^η` integer solutions with `|X|, |Y| ≤ B^C`.

Elementary route (`OddViscousNS_data/reports/t12_normcount_route.md`): (A) squarefree reduction
`a = s² d`; (B) strip `g = gcd(X, Y)` (`g² ∣ M`, at most `τ(|M|)` values); (C) primitive solutions
with the same class `t = X Y⁻¹ ∈ ZMod |m|` (`t² = d`) differ by an integer Pell solution of
`u² − d v² = 1` in a polynomial box, injectively; (D) `ρ_d(n) = #{t mod n : t² ≡ d} ≤ τ(n)²` for
squarefree `d` (at most four roots modulo each prime power, CRT); (E) the Pell points in a box of
side `N` number at most `4 log₂ N + 4` (Mathlib's `Pell.Solution₁`, `IsFundamental`, growth
`x(a₁ⁿ) ≥ 2ⁿ`; finitely many for `d < 0`, two for square `d`).  Assembly:
`#Sol ≤ τ(|M|)³ (4L + 4)` with `L = log₂((1 + |d|)(N|a|)²)`, then `divisor_bound` and
`Real.log_le_rpow_div`.
-/

namespace OVNS.Quant

open Finset Pell

/-! ### Step D: square roots modulo `n` -/

/-- If a prime `p` does not divide `B` and `p ^ k ∣ A * B`, then `p ^ k ∣ A`. -/
private theorem prime_pow_dvd_of_dvd_mul {p : ℤ} (hp : Prime p) (k : ℕ) {A B : ℤ} (hB : ¬p ∣ B)
    (h : p ^ k ∣ A * B) : p ^ k ∣ A :=
  ((Irreducible.coprime_iff_not_dvd hp.irreducible).2 hB).pow_left.dvd_of_dvd_mul_right h

/-- The `2`-adic step: if `B = 2 w` with `w` odd and `2 ^ k ∣ A * B` (`k ≥ 1`), then
`A ≡ 0` or `A ≡ 2 ^ (k - 1)` modulo `2 ^ k`. -/
private theorem two_pow_dvd_aux {k : ℕ} (hk : 0 < k) {A w : ℤ} (hw : Odd w)
    (h : (2 : ℤ) ^ k ∣ A * (2 * w)) : (2 : ℤ) ^ k ∣ A ∨ (2 : ℤ) ^ k ∣ A - 2 ^ (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h2 : (2 : ℤ) * 2 ^ j ∣ 2 * (A * w) := by
    have : A * (2 * w) = 2 * (A * w) := by ring
    rw [← this, mul_comm]; simpa [pow_succ] using h
  have h3 : (2 : ℤ) ^ j ∣ A * w := (mul_dvd_mul_iff_left (by norm_num)).1 h2
  have hw2 : ¬(2 : ℤ) ∣ w := by
    rw [← even_iff_two_dvd, Int.not_even_iff_odd]; exact hw
  obtain ⟨c, hc⟩ := prime_pow_dvd_of_dvd_mul Int.prime_two j hw2 h3
  rcases Int.even_or_odd' c with ⟨e, rfl | rfl⟩
  · left; exact ⟨e, by rw [hc, pow_succ]; ring⟩
  · right; exact ⟨e, by rw [hc, pow_succ]; ring⟩

/-- Integer form of the prime-power root count: two square roots of a squarefree `d` modulo
`p ^ k` agree up to sign and up to adding `p ^ (k - 1)`. -/
theorem int_sqrt_mod_prime_pow {d : ℤ} (hd : Squarefree d) {p k : ℕ} (hp : p.Prime)
    (hk : 0 < k) {T T₁ : ℤ} (h : (p : ℤ) ^ k ∣ T ^ 2 - d) (h₁ : (p : ℤ) ^ k ∣ T₁ ^ 2 - d) :
    (p : ℤ) ^ k ∣ T - T₁ ∨ (p : ℤ) ^ k ∣ T + T₁ ∨ (p : ℤ) ^ k ∣ T - T₁ - p ^ (k - 1) ∨
      (p : ℤ) ^ k ∣ T + T₁ - p ^ (k - 1) := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp1 : (p : ℤ) ∣ (p : ℤ) ^ k := dvd_pow_self _ hk.ne'
  by_cases hpd : (p : ℤ) ∣ d
  · have hT : (p : ℤ) ∣ T := by
      apply hpz.dvd_of_dvd_pow (n := 2)
      have := dvd_add (hp1.trans h) hpd; simpa using this
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have hT₁ : (p : ℤ) ∣ T₁ := by
        apply hpz.dvd_of_dvd_pow (n := 2)
        have := dvd_add (hp1.trans h₁) hpd; simpa using this
      left
      obtain rfl : k = 1 := by omega
      simpa using dvd_sub hT hT₁
    · exfalso
      have hp2 : (p : ℤ) * p ∣ (p : ℤ) ^ k := by
        rw [← sq]; exact pow_dvd_pow _ hk2
      have hTT : (p : ℤ) * p ∣ T ^ 2 := by rw [sq]; exact mul_dvd_mul hT hT
      have : (p : ℤ) * p ∣ d := by
        have := dvd_sub hTT (hp2.trans h); simpa using this
      exact hpz.not_isUnit (hd _ this)
  · have hnT : ∀ {S : ℤ}, (p : ℤ) ^ k ∣ S ^ 2 - d → ¬(p : ℤ) ∣ S := by
      intro S hS hpS
      apply hpd
      have := dvd_sub (dvd_pow hpS two_ne_zero) (hp1.trans hS); simpa using this
    have hprod : (p : ℤ) ^ k ∣ (T - T₁) * (T + T₁) := by
      have := dvd_sub h h₁
      have e : T ^ 2 - d - (T₁ ^ 2 - d) = (T - T₁) * (T + T₁) := by ring
      rwa [e] at this
    by_cases hp2 : p = 2
    · subst hp2
      push_cast at *
      have hTo : ¬(2 : ℤ) ∣ T := hnT h
      have hT₁o : ¬(2 : ℤ) ∣ T₁ := hnT h₁
      by_cases h4 : (4 : ℤ) ∣ T - T₁
      · -- then `T + T₁ = 2 w` with `w` odd
        obtain ⟨w, hw⟩ : (2 : ℤ) ∣ T + T₁ := by omega
        have hwo : Odd w := by
          rw [← Int.not_even_iff_odd, even_iff_two_dvd]; rintro ⟨e, rfl⟩; omega
        rw [hw] at hprod
        rcases two_pow_dvd_aux hk hwo hprod with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inr (Or.inl h'))
      · obtain ⟨w, hw⟩ : (2 : ℤ) ∣ T - T₁ := by omega
        have hwo : Odd w := by
          rw [← Int.not_even_iff_odd, even_iff_two_dvd]; rintro ⟨e, rfl⟩; omega
        rw [hw, mul_comm] at hprod
        rcases two_pow_dvd_aux hk hwo hprod with h' | h'
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr (Or.inr h'))
    · by_cases hm : (p : ℤ) ∣ T + T₁
      · have hm' : ¬(p : ℤ) ∣ T - T₁ := by
          intro hm'
          have h2T : (p : ℤ) ∣ 2 * T := by
            have := dvd_add hm hm'; rwa [show T + T₁ + (T - T₁) = 2 * T by ring] at this
          rcases hpz.dvd_or_dvd h2T with h2 | h2
          · have : p ∣ 2 := by exact_mod_cast h2
            exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
          · exact hnT h h2
        rw [mul_comm] at hprod
        exact Or.inr (Or.inl (prime_pow_dvd_of_dvd_mul hpz k hm' hprod))
      · exact Or.inl (prime_pow_dvd_of_dvd_mul hpz k hm hprod)

/-- An integer divisible by `n` vanishes in `ZMod n` (cast form used below). -/
private theorem zmod_eq_zero_of_dvd {n : ℕ} {A : ℤ} (h : (n : ℤ) ∣ A) : (A : ZMod n) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd A n).2 h

/-- **Roots modulo a prime power.** Two square roots of a squarefree `d` modulo `p ^ k` agree up
to sign and up to adding `p ^ (k - 1)`. -/
theorem sqrt_mod_prime_pow_cases {d : ℤ} (hd : Squarefree d) {p k : ℕ} (hp : p.Prime)
    (hk : 0 < k) {t₁ t : ZMod (p ^ k)} (h₁ : t₁ ^ 2 = d) (h : t ^ 2 = d) :
    t = t₁ ∨ t = -t₁ ∨ t = t₁ + (p : ZMod (p ^ k)) ^ (k - 1) ∨
      t = -t₁ + (p : ZMod (p ^ k)) ^ (k - 1) := by
  set T : ℤ := (t.cast : ℤ) with hT
  set T₁ : ℤ := (t₁.cast : ℤ) with hT₁
  have eT : (T : ZMod (p ^ k)) = t := ZMod.intCast_zmod_cast t
  have eT₁ : (T₁ : ZMod (p ^ k)) = t₁ := ZMod.intCast_zmod_cast t₁
  have dv : ∀ {S : ℤ}, (S : ZMod (p ^ k)) ^ 2 = d → (p : ℤ) ^ k ∣ S ^ 2 - d := by
    intro S hS
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (S ^ 2 - d) (p ^ k)).1 (by push_cast; rw [hS]; ring)
    exact_mod_cast this
  have hc : ((p ^ k : ℕ) : ℤ) = (p : ℤ) ^ k := by push_cast; ring
  rcases int_sqrt_mod_prime_pow hd hp hk (dv (eT ▸ h)) (dv (eT₁ ▸ h₁)) with h' | h' | h' | h' <;>
    rw [← hc] at h' <;> have h'' := zmod_eq_zero_of_dvd h' <;> push_cast at h'' <;>
    rw [eT, eT₁] at h''
  · left; linear_combination h''
  · right; left; linear_combination h''
  · right; right; left; linear_combination h''
  · right; right; right; linear_combination h''

/-- At most four square roots of a squarefree `d` modulo a prime power. -/
theorem card_sqrt_mod_prime_pow_le {d : ℤ} (hd : Squarefree d) {p k : ℕ} (hp : p.Prime)
    (hk : 0 < k) : Nat.card {t : ZMod (p ^ k) // t ^ 2 = d} ≤ 4 := by
  by_cases hex : ∃ t₁ : ZMod (p ^ k), t₁ ^ 2 = d
  · obtain ⟨t₁, h₁⟩ := hex
    set q : ZMod (p ^ k) := (p : ZMod (p ^ k)) ^ (k - 1)
    let S : Finset (ZMod (p ^ k)) := {t₁, -t₁, t₁ + q, -t₁ + q}
    have hsub : {t : ZMod (p ^ k) | t ^ 2 = d} ⊆ (S : Set (ZMod (p ^ k))) := by
      intro t ht
      have := sqrt_mod_prime_pow_cases hd hp hk h₁ ht
      simp only [S, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      tauto
    calc Nat.card {t : ZMod (p ^ k) // t ^ 2 = d}
        = Nat.card {t : ZMod (p ^ k) | t ^ 2 = d} := rfl
      _ ≤ Nat.card (S : Set (ZMod (p ^ k))) := Nat.card_mono S.finite_toSet hsub
      _ = S.card := by rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
      _ ≤ 4 := Finset.card_le_four
  · simp only [not_exists] at hex
    have : IsEmpty {t : ZMod (p ^ k) // t ^ 2 = d} := ⟨fun t ↦ hex t.1 t.2⟩
    simp

/-- The number of square roots of `d` modulo `n` is multiplicative over coprime moduli (CRT). -/
theorem card_sqrt_mul (d : ℤ) {m n : ℕ} (h : m.Coprime n) :
    Nat.card {t : ZMod (m * n) // t ^ 2 = d} =
      Nat.card {t : ZMod m // t ^ 2 = d} * Nat.card {t : ZMod n // t ^ 2 = d} := by
  rw [← Nat.card_prod]
  refine Nat.card_congr ?_
  refine ((ZMod.chineseRemainder h).toEquiv.subtypeEquiv
      (p := fun t ↦ t ^ 2 = (d : ZMod (m * n)))
      (q := fun c : ZMod m × ZMod n ↦ c.1 ^ 2 = (d : ZMod m) ∧ c.2 ^ 2 = (d : ZMod n)) ?_).trans
    (Equiv.subtypeProdEquivProd (p := fun t : ZMod m ↦ t ^ 2 = (d : ZMod m))
      (q := fun t : ZMod n ↦ t ^ 2 = (d : ZMod n)))
  intro t
  have hd : (ZMod.chineseRemainder h) (d : ZMod (m * n)) = ((d : ZMod m), (d : ZMod n)) := by
    rw [map_intCast]; ext <;> simp
  constructor
  · intro ht
    have := congrArg (ZMod.chineseRemainder h) ht
    rw [map_pow, hd] at this
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  · rintro ⟨h1, h2⟩
    apply (ZMod.chineseRemainder h).injective
    rw [map_pow, hd]
    exact Prod.ext h1 h2

/-- **Root count.** For squarefree `d` and `n ≥ 1`, `#{t mod n : t² ≡ d} ≤ τ(n)²`. -/
theorem card_sqrt_mod_le {d : ℤ} (hd : Squarefree d) (n : ℕ) (hn : 0 < n) :
    Nat.card {t : ZMod n // t ^ 2 = d} ≤ n.divisors.card ^ 2 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    rw [Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]
    calc _ ≤ 4 := card_sqrt_mod_prime_pow_le hd hp hk
      _ ≤ (k + 1) ^ 2 := by nlinarith
  | zero => exact absurd hn (lt_irrefl 0)
  | one =>
    simp only [Nat.divisors_one, Finset.card_singleton, one_pow]
    exact Finite.card_le_one_iff_subsingleton.2 inferInstance
  | coprime a b ha hb hab iha ihb =>
    rw [card_sqrt_mul d hab, hab.card_divisors_mul, mul_pow]
    exact Nat.mul_le_mul (iha (by omega)) (ihb (by omega))

/-! ### Step E: Pell points in a box -/

/-- Integer solutions of `x² − d y² = m` in the box `[−N, N]²`. -/
def solSet (d m : ℤ) (N : ℕ) : Finset (ℤ × ℤ) :=
  (Icc (-(N : ℤ)) N ×ˢ Icc (-(N : ℤ)) N).filter fun q ↦ q.1 ^ 2 - d * q.2 ^ 2 = m

/-- Membership in `solSet`. -/
theorem mem_solSet {d m : ℤ} {N : ℕ} {q : ℤ × ℤ} :
    q ∈ solSet d m N ↔ |q.1| ≤ N ∧ |q.2| ≤ N ∧ q.1 ^ 2 - d * q.2 ^ 2 = m := by
  simp only [solSet, mem_filter, mem_product, mem_Icc, abs_le]
  tauto

/-- Growth of powers of a fundamental Pell solution: `x(a₁ⁿ) ≥ 2ⁿ`. -/
theorem x_pow_ge_two_pow {d : ℤ} {a : Solution₁ d} (h : IsFundamental a) (n : ℕ) :
    (2 : ℤ) ^ n ≤ (a ^ n).x := by
  obtain ⟨hx, hy, -⟩ := h
  have hd : 0 < d := Solution₁.d_pos_of_one_lt_x hx
  induction n with
  | zero => simp
  | succ n ih =>
    have hyn : 0 ≤ (a ^ n).y := by
      rcases n with _ | n
      · simp
      · exact (Solution₁.y_pow_succ_pos (by omega) hy n).le
    rw [pow_succ (2 : ℤ), pow_succ a, Solution₁.x_mul]
    have : 0 ≤ d * ((a ^ n).y * a.y) := by positivity
    have h2 : (2 : ℤ) ≤ a.x := by omega
    have hp : (0 : ℤ) ≤ (a ^ n).x := le_trans (by positivity) ih
    nlinarith [mul_le_mul ih h2 (by norm_num) hp]

/-- `x(aⁿ) = x(a^|n|)` for integer `n`. -/
private theorem x_zpow_eq_natAbs {d : ℤ} (a : Solution₁ d) (n : ℤ) :
    (a ^ n).x = (a ^ n.natAbs).x := by
  rcases Int.natAbs_eq n with h | h
  · conv_lhs => rw [h]
    rw [zpow_natCast]
  · conv_lhs => rw [h]
    rw [zpow_neg, Solution₁.x_inv, zpow_natCast]

/-- `u² = 1 → u = ±1`. -/
private theorem sq_eq_one' {u : ℤ} (h : u ^ 2 = 1) : u = 1 ∨ u = -1 :=
  mul_self_eq_one_iff.1 (by rw [← sq]; exact h)

/-- Pell box, `d < 0`: at most four points. -/
theorem pell_card_neg {d : ℤ} (hd : d < 0) (N : ℕ) : (solSet d 1 N).card ≤ 4 := by
  have hsub : solSet d 1 N ⊆ {(1, 0), (-1, 0), (0, 1), (0, -1)} := by
    intro q hq
    obtain ⟨-, -, h⟩ := mem_solSet.1 hq
    obtain ⟨u, v⟩ := q
    simp only at h
    simp only [mem_insert, mem_singleton, Prod.mk.injEq]
    rcases eq_or_ne v 0 with rfl | hv
    · have : u ^ 2 = 1 := by simpa using h
      rcases sq_eq_one' this with rfl | rfl <;> simp
    · have hv2 : 1 ≤ v ^ 2 := by have := pow_pos (abs_pos.2 hv) 2; rw [sq_abs] at this; omega
      have hu : u = 0 := by nlinarith [sq_nonneg u]
      subst hu
      have : v ^ 2 = 1 := by nlinarith
      rcases sq_eq_one' this with rfl | rfl <;> simp
  exact (card_le_card hsub).trans (card_le_four)

/-- Pell box, `d` a nonzero square: at most two points. -/
theorem pell_card_sq {d : ℤ} (hd : d ≠ 0) (hsq : IsSquare d) (N : ℕ) :
    (solSet d 1 N).card ≤ 2 := by
  obtain ⟨r, rfl⟩ := hsq
  have hr : r ≠ 0 := by rintro rfl; simp at hd
  have hsub : solSet (r * r) 1 N ⊆ {(1, 0), (-1, 0)} := by
    intro q hq
    obtain ⟨-, -, h⟩ := mem_solSet.1 hq
    obtain ⟨u, v⟩ := q
    simp only at h
    have hf : (u - r * v) * (u + r * v) = 1 := by linear_combination h
    have h1 := Int.eq_one_or_neg_one_of_mul_eq_one hf
    have h2 := Int.eq_one_or_neg_one_of_mul_eq_one ((mul_comm _ _).trans hf)
    have hv : r * v = 0 := by
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] at hf <;>
        norm_num at hf <;> linarith
    have hv' : v = 0 := by rcases mul_eq_zero.1 hv with h | h; exact absurd h hr; exact h
    subst hv'
    simp only [mem_insert, mem_singleton, Prod.mk.injEq, and_true]
    have : u ^ 2 = 1 := by simpa using h
    exact sq_eq_one' this
  exact (card_le_card hsub).trans (card_le_two)

/-- Pell box, `d > 0` not a square: at most `4 log₂ N + 2` points. -/
theorem pell_card_nonsq {d : ℤ} (hd : 0 < d) (hsq : ¬IsSquare d) (N : ℕ) :
    (solSet d 1 N).card ≤ 4 * Nat.log 2 N + 4 := by
  obtain ⟨a₁, ha₁⟩ := IsFundamental.exists_of_not_isSquare hd hsq
  set L := Nat.log 2 N
  let g : ℤ × Bool → ℤ × ℤ := fun nb ↦
    if nb.2 then ((a₁ ^ nb.1).x, (a₁ ^ nb.1).y) else ((-a₁ ^ nb.1).x, (-a₁ ^ nb.1).y)
  have hsub : solSet d 1 N ⊆ (Icc (-(L : ℤ)) L ×ˢ (univ : Finset Bool)).image g := by
    intro q hq
    obtain ⟨hu, -, h⟩ := mem_solSet.1 hq
    obtain ⟨n, hn⟩ := ha₁.eq_zpow_or_neg_zpow (Solution₁.mk q.1 q.2 h)
    have hx : |q.1| = (a₁ ^ n.natAbs).x := by
      have hpos : 0 < (a₁ ^ n.natAbs).x := Solution₁.x_pow_pos (by linarith [ha₁.1]) _
      rcases hn with hn | hn
      · have := congrArg Solution₁.x hn
        rw [Solution₁.x_mk, x_zpow_eq_natAbs] at this
        rw [this, abs_of_pos hpos]
      · have := congrArg Solution₁.x hn
        rw [Solution₁.x_mk, Solution₁.x_neg, x_zpow_eq_natAbs] at this
        rw [this, abs_neg, abs_of_pos hpos]
    have hpow : 2 ^ n.natAbs ≤ N := by
      have := (x_pow_ge_two_pow ha₁ n.natAbs).trans (hx.symm.le.trans hu)
      exact_mod_cast this
    have hnL : n.natAbs ≤ L := Nat.le_log_of_pow_le (by norm_num) hpow
    have hmem : ∀ b : Bool, (n, b) ∈ Icc (-(L : ℤ)) L ×ˢ (univ : Finset Bool) := by
      intro b; simp only [mem_product, mem_Icc, mem_univ, and_true]; omega
    rcases hn with hn | hn
    · refine mem_image.2 ⟨(n, true), hmem true, ?_⟩
      show ((a₁ ^ n).x, (a₁ ^ n).y) = q
      rw [← hn, Solution₁.x_mk, Solution₁.y_mk]
    · refine mem_image.2 ⟨(n, false), hmem false, ?_⟩
      show ((-a₁ ^ n).x, (-a₁ ^ n).y) = q
      rw [← hn, Solution₁.x_mk, Solution₁.y_mk]
  calc (solSet d 1 N).card ≤ _ := card_le_card hsub
    _ ≤ (Icc (-(L : ℤ)) L ×ˢ (univ : Finset Bool)).card := card_image_le
    _ = (2 * L + 1) * 2 := by
      rw [card_product, Int.card_Icc, card_univ, Fintype.card_bool]
      congr 1; omega
    _ ≤ 4 * L + 4 := by omega

/-- **Pell box.** For `d ≠ 0`, `#{(u, v) ∈ [−N, N]² : u² − d v² = 1} ≤ 4 log₂ N + 4`. -/
theorem pell_card_le {d : ℤ} (hd : d ≠ 0) (N : ℕ) :
    (solSet d 1 N).card ≤ 4 * Nat.log 2 N + 4 := by
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · exact (pell_card_neg hneg N).trans (by omega)
  · by_cases hsq : IsSquare d
    · exact (pell_card_sq hd hsq N).trans (by omega)
    · exact pell_card_nonsq hpos hsq N

/-! ### Step C: primitive solutions and classes modulo `m` -/

/-- Primitive solutions (`gcd(x, y) = 1`) of `x² − d y² = m` in the box `[−N, N]²`. -/
def primSet (d m : ℤ) (N : ℕ) : Finset (ℤ × ℤ) :=
  (solSet d m N).filter fun q ↦ Int.gcd q.1 q.2 = 1

/-- For a primitive solution of `x² − d y² = m`, `y` is coprime to `m`. -/
theorem isCoprime_snd_of_prim {d m x y : ℤ} (h : x ^ 2 - d * y ^ 2 = m)
    (hg : Int.gcd x y = 1) : IsCoprime y m := by
  have hxy : IsCoprime y (x ^ 2) := (Int.isCoprime_iff_gcd_eq_one.2 hg).symm.pow_right
  obtain ⟨a, b, hab⟩ := hxy
  exact ⟨a + b * d * y, b, by rw [← h]; linear_combination hab⟩

/-- The composition identity: two solutions of `x² − d y² = m` with `m ∣ x x₀ − d y y₀` and
`m ∣ x₀ y − x y₀` differ by the Pell solution `(u, v)`, and `(x, y)` is recovered from it. -/
theorem pell_quotient {d m x y x₀ y₀ : ℤ} (hm : m ≠ 0) (h : x ^ 2 - d * y ^ 2 = m)
    (h₀ : x₀ ^ 2 - d * y₀ ^ 2 = m) (hA : m ∣ x * x₀ - d * y * y₀) (hB : m ∣ x₀ * y - x * y₀) :
    ((x * x₀ - d * y * y₀) / m) ^ 2 - d * ((x₀ * y - x * y₀) / m) ^ 2 = 1 ∧
      x = (x * x₀ - d * y * y₀) / m * x₀ + d * ((x₀ * y - x * y₀) / m) * y₀ ∧
      y = (x₀ * y - x * y₀) / m * x₀ + (x * x₀ - d * y * y₀) / m * y₀ := by
  set u := (x * x₀ - d * y * y₀) / m
  set v := (x₀ * y - x * y₀) / m
  have hu : x * x₀ - d * y * y₀ = m * u := (Int.mul_ediv_cancel' hA).symm
  have hv : x₀ * y - x * y₀ = m * v := (Int.mul_ediv_cancel' hB).symm
  refine ⟨?_, ?_, ?_⟩
  · have : (m * m) * (u ^ 2 - d * v ^ 2) = (m * m) * 1 := by
      linear_combination (-(m * u) - (x * x₀ - d * y * y₀)) * hu +
        (d * (m * v) + d * (x₀ * y - x * y₀)) * hv + (x₀ ^ 2 - d * y₀ ^ 2) * h + m * h₀
    exact mul_left_cancel₀ (mul_ne_zero hm hm) this
  · apply mul_left_cancel₀ hm
    linear_combination x₀ * hu + d * y₀ * hv - x * h₀
  · apply mul_left_cancel₀ hm
    linear_combination y₀ * hu + x₀ * hv - y * h₀

/-- `y` is a unit modulo `|m|` when `y` is coprime to `m`. -/
private theorem isUnit_of_isCoprime {y m : ℤ} (h : IsCoprime y m) : IsUnit (y : ZMod m.natAbs) := by
  obtain ⟨a, b, hab⟩ := h
  have hm : (m : ZMod m.natAbs) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd m m.natAbs).2 (Int.natAbs_dvd.2 dvd_rfl)
  refine IsUnit.of_mul_eq_one (a : ZMod m.natAbs) ?_
  have := congrArg (fun z : ℤ ↦ (z : ZMod m.natAbs)) hab
  push_cast at this
  rw [hm, mul_zero, add_zero] at this
  rw [mul_comm]; exact this

/-- `|x x₀ − d y y₀| ≤ (1 + |d|) N²` in the box. -/
private theorem abs_bilin_le {d x y x₀ y₀ : ℤ} {N : ℕ} (hx : |x| ≤ N) (hy : |y| ≤ N)
    (hx₀ : |x₀| ≤ N) (hy₀ : |y₀| ≤ N) (s : ℤ) (hs : |s| ≤ |d|) :
    |x * x₀ - s * y * y₀| ≤ ((1 + d.natAbs) * N ^ 2 : ℕ) := by
  push_cast
  have h1 : |x * x₀| ≤ (N : ℤ) * N := by
    rw [abs_mul]; exact mul_le_mul hx hx₀ (abs_nonneg _) (by positivity)
  have h2 : |s * y * y₀| ≤ |d| * (N * N) := by
    rw [abs_mul, abs_mul, mul_assoc]
    exact mul_le_mul hs (mul_le_mul hy hy₀ (abs_nonneg _) (by positivity)) (by positivity)
      (abs_nonneg _)
  calc |x * x₀ - s * y * y₀| ≤ |x * x₀| + |s * y * y₀| := abs_sub _ _
    _ ≤ _ := by nlinarith

/-- `|u| ≤ |m u|` for `m ≠ 0`. -/
private theorem abs_le_abs_mul {m u : ℤ} (hm : m ≠ 0) : |u| ≤ |m * u| := by
  rw [abs_mul]; have := Int.one_le_abs hm; nlinarith [abs_nonneg u]

/-- Class map of a primitive solution: `t = x y⁻¹ mod |m|` satisfies `x = t y` and `t² = d`. -/
theorem prim_class {d m : ℤ} {N : ℕ} {q : ℤ × ℤ} (hq : q ∈ primSet d m N) :
    (q.1 : ZMod m.natAbs) = (q.1 : ZMod m.natAbs) * (q.2 : ZMod m.natAbs)⁻¹ * q.2 ∧
      ((q.1 : ZMod m.natAbs) * (q.2 : ZMod m.natAbs)⁻¹) ^ 2 = d := by
  obtain ⟨hs, hg⟩ := mem_filter.1 hq
  obtain ⟨-, -, h⟩ := mem_solSet.1 hs
  have hu := isUnit_of_isCoprime (isCoprime_snd_of_prim h hg)
  have hinv := ZMod.mul_inv_of_unit _ hu
  have hx : (q.1 : ZMod m.natAbs) = (q.1 : ZMod m.natAbs) * (q.2 : ZMod m.natAbs)⁻¹ * q.2 := by
    rw [mul_assoc, mul_comm _ (q.2 : ZMod m.natAbs), hinv, mul_one]
  refine ⟨hx, ?_⟩
  have hm0 : (m : ZMod m.natAbs) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd m m.natAbs).2 (Int.natAbs_dvd.2 dvd_rfl)
  have e := congrArg (fun z : ℤ ↦ (z : ZMod m.natAbs)) h
  push_cast at e
  rw [hm0] at e
  set t := (q.1 : ZMod m.natAbs) * (q.2 : ZMod m.natAbs)⁻¹
  have e2 : (t ^ 2 - d) * (q.2 : ZMod m.natAbs) ^ 2 = 0 := by
    rw [hx] at e; linear_combination e
  exact sub_eq_zero.1 ((hu.pow 2).mul_left_eq_zero.1 e2)

/-- **Class bound.** `#Prim(d, m, N) ≤ U(d, (1 + |d|) N²) · ρ_d(|m|)`. -/
theorem prim_card_le {d m : ℤ} (hd : d ≠ 0) (hm : m ≠ 0) (N : ℕ) :
    (primSet d m N).card ≤
      (solSet d 1 ((1 + d.natAbs) * N ^ 2)).card * Nat.card {t : ZMod m.natAbs // t ^ 2 = d} := by
  classical
  set n := m.natAbs
  have : NeZero n := ⟨Int.natAbs_ne_zero.2 hm⟩
  let cls : ℤ × ℤ → ZMod n := fun q ↦ (q.1 : ZMod n) * (q.2 : ZMod n)⁻¹
  refine (card_le_mul_card_image (f := cls) (primSet d m N) _ ?_).trans (Nat.mul_le_mul_left _ ?_)
  · intro t ht
    obtain ⟨q₀, hq₀, rfl⟩ := mem_image.1 ht
    obtain ⟨hx₀', ht₀⟩ := prim_class hq₀
    obtain ⟨hx₀, hy₀, h₀⟩ := mem_solSet.1 (mem_filter.1 hq₀).1
    have hdiv : ∀ q ∈ (primSet d m N).filter (fun q ↦ cls q = cls q₀), q ∈ solSet d m N ∧
        m ∣ q.1 * q₀.1 - d * q.2 * q₀.2 ∧ m ∣ q₀.1 * q.2 - q.1 * q₀.2 := by
      intro q hq
      obtain ⟨hqp, hc⟩ := mem_filter.1 hq
      obtain ⟨hx', -⟩ := prim_class hqp
      refine ⟨(mem_filter.1 hqp).1, ?_, ?_⟩ <;> apply Int.natAbs_dvd.1 <;>
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).1 <;> push_cast <;>
        rw [hx', hx₀'] <;> simp only [cls] at hc <;> rw [hc]
      · linear_combination ((q.2 : ZMod n) * q₀.2) * ht₀
      · ring
    let φ : ℤ × ℤ → ℤ × ℤ := fun q ↦
      ((q.1 * q₀.1 - d * q.2 * q₀.2) / m, (q₀.1 * q.2 - q.1 * q₀.2) / m)
    apply card_le_card_of_injOn φ
    · intro q hq
      obtain ⟨hs, hA, hB⟩ := hdiv q hq
      obtain ⟨hx, hy, h⟩ := mem_solSet.1 hs
      obtain ⟨hp, -, -⟩ := pell_quotient hm h h₀ hA hB
      refine mem_solSet.2 ⟨?_, ?_, hp⟩
      · calc _ ≤ |q.1 * q₀.1 - d * q.2 * q₀.2| := by
              conv_rhs => rw [← Int.mul_ediv_cancel' hA]
              exact abs_le_abs_mul hm
          _ ≤ _ := abs_bilin_le hx hy hx₀ hy₀ d le_rfl
      · calc _ ≤ |q₀.1 * q.2 - 1 * q.1 * q₀.2| := by
              rw [one_mul]
              conv_rhs => rw [← Int.mul_ediv_cancel' hB]
              exact abs_le_abs_mul hm
          _ ≤ _ := abs_bilin_le hx₀ hx hy hy₀ 1 (by rw [abs_one]; exact Int.one_le_abs hd)
    · intro q hq q' hq' he
      obtain ⟨hs, hA, hB⟩ := hdiv q hq
      obtain ⟨hs', hA', hB'⟩ := hdiv q' hq'
      obtain ⟨-, -, h⟩ := mem_solSet.1 hs
      obtain ⟨-, -, h'⟩ := mem_solSet.1 hs'
      obtain ⟨-, e1, e2⟩ := pell_quotient hm h h₀ hA hB
      obtain ⟨-, e1', e2'⟩ := pell_quotient hm h' h₀ hA' hB'
      simp only [φ, Prod.mk.injEq] at he
      rw [he.1, he.2] at e1 e2
      exact Prod.ext (e1.trans e1'.symm) (e2.trans e2'.symm)
  · have hsub : (((primSet d m N).image cls : Finset (ZMod n)) : Set (ZMod n)) ⊆
        {t | t ^ 2 = d} := by
      intro t ht
      obtain ⟨q, hq, rfl⟩ := mem_image.1 ht
      exact (prim_class hq).2
    calc _ = Nat.card (((primSet d m N).image cls : Finset (ZMod n)) : Set (ZMod n)) := by
          rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
      _ ≤ Nat.card {t : ZMod n | t ^ 2 = d} := Nat.card_mono (Set.toFinite _) hsub
      _ = _ := rfl

/-! ### Steps A, B: squarefree reduction and gcd stripping -/

/-- **Gcd stripping.** Solutions with `gcd(x, y) = g` inject into primitive solutions of
`x² − d y² = M / g²`, and `g ∣ |M|`. -/
theorem sol_card_le_prim {d M : ℤ} (hM : M ≠ 0) (N : ℕ) (P : ℕ)
    (hP : ∀ m : ℤ, m ≠ 0 → m.natAbs ∣ M.natAbs → (primSet d m N).card ≤ P) :
    (solSet d M N).card ≤ P * M.natAbs.divisors.card := by
  classical
  let f : ℤ × ℤ → ℕ := fun q ↦ Int.gcd q.1 q.2
  have hfac : ∀ q ∈ solSet d M N, ∃ m : ℤ, M = (Int.gcd q.1 q.2 : ℤ) ^ 2 * m := by
    intro q hq
    obtain ⟨-, -, h⟩ := mem_solSet.1 hq
    obtain ⟨x', hx'⟩ := Int.gcd_dvd_left q.1 q.2
    obtain ⟨y', hy'⟩ := Int.gcd_dvd_right q.1 q.2
    exact ⟨x' ^ 2 - d * y' ^ 2, by
      linear_combination (-h) + (q.1 + (Int.gcd q.1 q.2 : ℤ) * x') * hx' -
        d * (q.2 + (Int.gcd q.1 q.2 : ℤ) * y') * hy'⟩
  refine (card_le_mul_card_image (f := f) _ _ ?_).trans (Nat.mul_le_mul_left _ ?_)
  · intro g hg
    obtain ⟨q₀, hq₀, rfl⟩ := mem_image.1 hg
    obtain ⟨m, hMm⟩ := hfac q₀ hq₀
    have hm : m ≠ 0 := by rintro rfl; simp at hMm; exact hM hMm
    have hg0 : (f q₀ : ℤ) ≠ 0 := by rintro h; rw [h] at hMm; simp at hMm; exact hM hMm
    refine le_trans ?_ (hP m hm (Int.natAbs_dvd_natAbs.2 ⟨_, hMm.trans (mul_comm _ _)⟩))
    have hdv : ∀ q ∈ (solSet d M N).filter (fun q ↦ f q = f q₀),
        q.1 = (f q₀ : ℤ) * (q.1 / f q₀) ∧ q.2 = (f q₀ : ℤ) * (q.2 / f q₀) ∧
          Int.gcd q.1 q.2 = f q₀ := by
      intro q hq
      have hfq : Int.gcd q.1 q.2 = f q₀ := (mem_filter.1 hq).2
      refine ⟨(Int.mul_ediv_cancel' ?_).symm, (Int.mul_ediv_cancel' ?_).symm, hfq⟩
      · rw [← hfq]; exact Int.gcd_dvd_left _ _
      · rw [← hfq]; exact Int.gcd_dvd_right _ _
    refine card_le_card_of_injOn (fun q ↦ (q.1 / f q₀, q.2 / f q₀)) ?_ ?_
    · intro q hq
      obtain ⟨hx2, hy2, hfq⟩ := hdv q hq
      obtain ⟨hx, hy, h⟩ := mem_solSet.1 (mem_filter.1 hq).1
      simp only [coe_filter, primSet, solSet, mem_filter] at hq ⊢
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp only [mem_product, mem_Icc, ← abs_le]
        refine ⟨le_trans ?_ hx, le_trans ?_ hy⟩
        · conv_rhs => rw [hx2]
          exact abs_le_abs_mul hg0
        · conv_rhs => rw [hy2]
          exact abs_le_abs_mul hg0
      · apply mul_left_cancel₀ (pow_ne_zero 2 hg0)
        rw [← hMm, ← h]
        conv_rhs => rw [hx2, hy2]
        ring
      · have := Int.gcd_div_gcd_div_gcd (i := q.1) (j := q.2) (by rw [hfq]; omega)
        rwa [hfq] at this
    · intro q hq q' hq' he
      obtain ⟨hx2, hy2, -⟩ := hdv q hq
      obtain ⟨hx2', hy2', -⟩ := hdv q' hq'
      simp only [Prod.mk.injEq] at he
      exact Prod.ext (by rw [hx2, hx2', he.1]) (by rw [hy2, hy2', he.2])
  · refine card_le_card fun g hg ↦ ?_
    obtain ⟨q, hq, rfl⟩ := mem_image.1 hg
    obtain ⟨m, hMm⟩ := hfac q hq
    rw [Nat.mem_divisors]
    refine ⟨Int.natCast_dvd.1 ⟨(f q : ℤ) * m, by rw [hMm]; ring⟩, Int.natAbs_ne_zero.2 hM⟩

/-- **Squarefree reduction.** `a = s² d` with `d` squarefree; `(X, Y) ↦ (X, s Y)` injects the
solutions of `X² − a Y² = M` into those of `X² − d Z² = M` in the box `N |a|`. -/
theorem sol_card_le_sqfree {a M : ℤ} (ha : a ≠ 0) (N : ℕ) :
    ∃ d : ℤ, Squarefree d ∧ d ≠ 0 ∧ d.natAbs ≤ a.natAbs ∧
      (solSet a M N).card ≤ (solSet d M (N * a.natAbs)).card := by
  obtain ⟨d₀, s, hd₀, hs, hsd, hsq⟩ := Nat.sq_mul_squarefree_of_pos (Int.natAbs_pos.2 ha)
  have hdabs : (a.sign * d₀).natAbs = d₀ := by
    rw [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero ha, one_mul, Int.natAbs_natCast]
  have hd0 : a.sign * d₀ ≠ 0 := by
    intro h; rw [h] at hdabs; simp at hdabs; omega
  have has : a = (s : ℤ) ^ 2 * (a.sign * d₀) := by
    conv_lhs => rw [← Int.sign_mul_natAbs a, ← hsd]
    push_cast; ring
  have hsa : s ≤ a.natAbs := by rw [← hsd]; nlinarith
  have ha1 : (1 : ℤ) ≤ |a| := Int.one_le_abs ha
  have hsa' : (s : ℤ) ≤ |a| := by rw [← Int.natCast_natAbs]; exact_mod_cast hsa
  refine ⟨a.sign * d₀, Int.squarefree_natAbs.1 (by rw [hdabs]; exact hsq), hd0, ?_, ?_⟩
  · rw [hdabs, ← hsd]; exact Nat.le_mul_of_pos_left _ (by positivity)
  refine card_le_card_of_injOn (fun q ↦ (q.1, (s : ℤ) * q.2)) ?_ ?_
  · intro q hq
    obtain ⟨hx, hy, h⟩ := mem_solSet.1 hq
    refine mem_solSet.2 ⟨?_, ?_, ?_⟩
    · push_cast
      exact hx.trans (le_mul_of_one_le_right (by positivity) ha1)
    · push_cast
      rw [abs_mul, Nat.abs_cast, mul_comm (N : ℤ)]
      exact mul_le_mul hsa' hy (abs_nonneg _) (by positivity)
    · simp only
      linear_combination h + q.2 ^ 2 * has
  · intro q _ q' _ he
    simp only [Prod.mk.injEq] at he
    exact Prod.ext he.1 (mul_left_cancel₀ (by exact_mod_cast hs.ne') he.2)

/-! ### Combined count -/

/-- **Combined count.** `#Sol(a, M, N) ≤ (4 log₂((1 + |d|)(N|a|)²) + 4) · τ(|M|)³` for some
`d` with `|d| ≤ |a|` (the squarefree part of `a`, with sign). -/
theorem sol_card_bound {a M : ℤ} (ha : a ≠ 0) (hM : M ≠ 0) (N : ℕ) :
    ∃ d : ℤ, d.natAbs ≤ a.natAbs ∧ (solSet a M N).card ≤
      (4 * Nat.log 2 ((1 + d.natAbs) * (N * a.natAbs) ^ 2) + 4) *
        M.natAbs.divisors.card ^ 3 := by
  obtain ⟨d, hsq, hd0, hda, hA⟩ := sol_card_le_sqfree (M := M) ha N
  refine ⟨d, hda, hA.trans ?_⟩
  set N₁ := N * a.natAbs
  have hP : ∀ m : ℤ, m ≠ 0 → m.natAbs ∣ M.natAbs → (primSet d m N₁).card ≤
      (4 * Nat.log 2 ((1 + d.natAbs) * N₁ ^ 2) + 4) * M.natAbs.divisors.card ^ 2 := by
    intro m hm hdvd
    calc _ ≤ _ := prim_card_le hd0 hm N₁
      _ ≤ (4 * Nat.log 2 ((1 + d.natAbs) * N₁ ^ 2) + 4) * m.natAbs.divisors.card ^ 2 :=
          Nat.mul_le_mul (pell_card_le hd0 _) (card_sqrt_mod_le hsq _ (Int.natAbs_pos.2 hm))
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (card_le_card
          (Nat.divisors_subset_of_dvd (Int.natAbs_ne_zero.2 hM) hdvd)) 2)
  calc _ ≤ _ := sol_card_le_prim hM N₁ _ hP
    _ = _ := by ring

/-! ### Step F: real estimates and assembly -/

/-- `4 log₂ X + 4 ≤ K₁ B^{η/2}` whenever `X ≤ B^{5C+1}`. -/
theorem log_count_bound (C : ℕ) {η : ℝ} (hη : 0 < η) : ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ B : ℝ, 2 ≤ B →
    ∀ X : ℕ, (X : ℝ) ≤ B ^ (5 * C + 1) → (4 * Nat.log 2 X + 4 : ℝ) ≤ K₁ * B ^ (η / 2) := by
  set ε : ℝ := η / (2 * (5 * C + 1)) with hε
  have hε0 : 0 < ε := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨4 / (ε * Real.log 2) + 4, by positivity, fun B hB X hX ↦ ?_⟩
  set L := Nat.log 2 X
  have hB0 : 0 < B := by linarith
  have hB1 : 1 ≤ B ^ (η / 2) := Real.one_le_rpow (by linarith) (by positivity)
  have h2L : (2 : ℝ) ^ L ≤ B ^ (5 * C + 1) := by
    rcases Nat.eq_zero_or_pos X with h0 | hpos
    · simp only [L, h0, Nat.log_zero_right, pow_zero]
      exact one_le_pow₀ (by linarith)
    · refine le_trans ?_ hX
      exact_mod_cast Nat.pow_log_le_self 2 hpos.ne'
  have hlog : (L : ℝ) * Real.log 2 ≤ B ^ (η / 2) / ε := by
    have h1 : (L : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ L) := by
      rw [Real.log_pow]
    have h2 := Real.log_le_rpow_div (x := (2 : ℝ) ^ L) (by positivity) hε0
    have h3 : ((2 : ℝ) ^ L) ^ ε ≤ B ^ (η / 2) := by
      calc ((2 : ℝ) ^ L) ^ ε ≤ (B ^ (5 * C + 1)) ^ ε :=
            Real.rpow_le_rpow (by positivity) h2L hε0.le
        _ = B ^ (η / 2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hB0.le]
          congr 1
          rw [hε]; push_cast; field_simp
    rw [h1]
    exact h2.trans (div_le_div_of_nonneg_right h3 hε0.le)
  have hL : (L : ℝ) ≤ B ^ (η / 2) / (ε * Real.log 2) := by
    rw [le_div_iff₀ (by positivity)]
    calc (L : ℝ) * (ε * Real.log 2) = (L * Real.log 2) * ε := by ring
      _ ≤ B ^ (η / 2) / ε * ε := mul_le_mul_of_nonneg_right hlog hε0.le
      _ = B ^ (η / 2) := div_mul_cancel₀ _ hε0.ne'
  calc (4 * L + 4 : ℝ) ≤ 4 * (B ^ (η / 2) / (ε * Real.log 2)) + 4 * B ^ (η / 2) := by
        nlinarith
    _ = (4 / (ε * Real.log 2) + 4) * B ^ (η / 2) := by ring

/-- `τ(|M|)³ ≤ K₂ B^{η/2}` whenever `0 < |M| ≤ B^C`. -/
theorem tau_cube_bound (C : ℕ) {η : ℝ} (hη : 0 < η) : ∃ K₂ : ℝ, 0 ≤ K₂ ∧ ∀ B : ℝ, 2 ≤ B →
    ∀ M : ℤ, M ≠ 0 → (|M| : ℝ) ≤ B ^ C →
      ((M.natAbs.divisors.card ^ 3 : ℕ) : ℝ) ≤ K₂ * B ^ (η / 2) := by
  set δ : ℝ := η / (6 * C + 6) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨K, hK0, hK⟩ := divisor_bound hδ0
  refine ⟨K ^ 3, by positivity, fun B hB M hM hMB ↦ ?_⟩
  have hB0 : 0 < B := by linarith
  have hM1 : (1 : ℝ) ≤ |M| := by exact_mod_cast Int.one_le_abs hM
  have hcast : ((M.natAbs : ℕ) : ℝ) = |(M : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have h1 := hK M.natAbs (Int.natAbs_pos.2 hM)
  rw [hcast] at h1
  have h2 : |(M : ℝ)| ^ δ ≤ B ^ (C * δ) := by
    rw [Real.rpow_mul hB0.le, Real.rpow_natCast]
    exact Real.rpow_le_rpow (abs_nonneg _) hMB hδ0.le
  have hδη : δ * (6 * C + 6) = η := by rw [hδ]; field_simp
  have h3 : (B ^ ((C : ℝ) * δ)) ^ 3 ≤ B ^ (η / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hB0.le]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    push_cast
    nlinarith
  have h4 : (M.natAbs.divisors.card : ℝ) ≤ K * B ^ ((C : ℝ) * δ) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 hK0)
  push_cast
  calc (M.natAbs.divisors.card : ℝ) ^ 3 ≤ (K * B ^ ((C : ℝ) * δ)) ^ 3 :=
        pow_le_pow_left₀ (by positivity) h4 3
    _ = K ^ 3 * (B ^ ((C : ℝ) * δ)) ^ 3 := by ring
    _ ≤ K ^ 3 * B ^ (η / 2) := mul_le_mul_of_nonneg_left h3 (by positivity)

/-- The box points of `boxPts 2 (fun _ ↦ B^C)` solving `X² − aY² = M` inject into
`solSet a M ⌊B^C⌋`. -/
theorem boxPts_card_le_solSet (B : ℝ) (C : ℕ) (hB : 0 ≤ B) (a M : ℤ) :
    ((boxPts 2 fun _ ↦ B ^ C).filter fun p ↦ p 0 ^ 2 - a * p 1 ^ 2 = M).card ≤
      (solSet a M ⌊B ^ C⌋.toNat).card := by
  have hN : ((⌊B ^ C⌋.toNat : ℕ) : ℤ) = ⌊B ^ C⌋ :=
    Int.toNat_of_nonneg (Int.floor_nonneg.2 (by positivity))
  refine card_le_card_of_injOn (fun p ↦ (p 0, p 1)) ?_ ?_
  · intro p hp
    simp only [coe_filter, boxPts, Fintype.mem_piFinset, mem_Icc] at hp
    obtain ⟨hb, h⟩ := hp
    refine mem_solSet.2 ⟨?_, ?_, h⟩ <;> rw [abs_le, hN]
    · exact hb 0
    · exact hb 1
  · intro p _ q _ he
    simp only [Prod.mk.injEq] at he
    funext i
    fin_cases i
    · exact he.1
    · exact he.2

/-- **Lemma quant-norm.** -/
theorem quadraticNormCount : QuadraticNormCount := by
  intro C η hη
  obtain ⟨K₁, hK₁, h₁⟩ := log_count_bound C hη
  obtain ⟨K₂, hK₂, h₂⟩ := tau_cube_bound C hη
  refine ⟨K₁ * K₂, fun B hB a M ha hM haB hMB ↦ ?_⟩
  have hB0 : 0 < B := by linarith
  set N : ℕ := ⌊B ^ C⌋.toNat with hNdef
  have hN : ((N : ℤ) : ℝ) = (⌊B ^ C⌋ : ℝ) := by
    rw [hNdef, Int.toNat_of_nonneg (Int.floor_nonneg.2 (by positivity))]
  have hNB : (N : ℝ) ≤ B ^ C := by
    have : ((N : ℤ) : ℝ) ≤ B ^ C := by rw [hN]; exact Int.floor_le _
    exact_mod_cast this
  obtain ⟨d, hda, hcount⟩ := sol_card_bound ha hM N
  set X := (1 + d.natAbs) * (N * a.natAbs) ^ 2
  have hX : (X : ℝ) ≤ B ^ (5 * C + 1) := by
    have haR : (a.natAbs : ℝ) ≤ B ^ C := by rw [Nat.cast_natAbs]; exact_mod_cast haB
    have hdR : (d.natAbs : ℝ) ≤ B ^ C := le_trans (by exact_mod_cast hda) haR
    have hBC1 : 1 ≤ B ^ C := one_le_pow₀ (by linarith)
    simp only [X]
    push_cast
    calc (1 + (d.natAbs : ℝ)) * ((N : ℝ) * a.natAbs) ^ 2
        ≤ (B ^ C + B ^ C) * (B ^ C * B ^ C) ^ 2 := by gcongr
      _ = 2 * B ^ (5 * C) := by ring
      _ ≤ B * B ^ (5 * C) := by gcongr
      _ = B ^ (5 * C + 1) := by ring
  calc (((boxPts 2 fun _ ↦ B ^ C).filter fun p ↦ p 0 ^ 2 - a * p 1 ^ 2 = M).card : ℝ)
      ≤ (solSet a M N).card := by exact_mod_cast boxPts_card_le_solSet B C hB0.le a M
    _ ≤ ((4 * Nat.log 2 X + 4) * M.natAbs.divisors.card ^ 3 : ℕ) := by exact_mod_cast hcount
    _ = (4 * Nat.log 2 X + 4 : ℝ) * ((M.natAbs.divisors.card ^ 3 : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (K₁ * B ^ (η / 2)) * (K₂ * B ^ (η / 2)) :=
        mul_le_mul (h₁ B hB X hX) (h₂ B hB M hM hMB) (by positivity) (by positivity)
    _ = K₁ * K₂ * B ^ η := by
        rw [mul_mul_mul_comm, ← Real.rpow_add hB0, add_halves]

end OVNS.Quant
