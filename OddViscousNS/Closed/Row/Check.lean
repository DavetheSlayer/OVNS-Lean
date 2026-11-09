import OddViscousNS.Closed.Row.HHsum

/-!
# From the digit tables to quadratic forms

`KerOK` says that two tables hold the convolutions of a kernel; `kerForm_real` identifies the integer
form read from them with the real form `MR` at an integer vector, using the coordinate symmetry of
the box to read the other weights at permuted outputs.
-/

open Finset

noncomputable section

namespace OVNS
namespace Row

set_option maxRecDepth 20000
set_option linter.constructorNameAsVariable false

/-- The tables `T0`, `T1` hold the convolutions of the kernel `(F,G)`. -/
structure KerOK (F G : ℕ → ℕ) (T0 T1 : ℕ) : Prop where
  r0 : ∀ {x y z : ℕ}, x < 44 → y < 44 → z < 44 → rdC T0 x y z = DN wx F G (kN x y z)
  r1 : ∀ {x y z : ℕ}, x < 44 → y < 44 → z < 44 → rdC T1 x y z = DN wxy F G (kN x y z)

lemma wx_le (p : Mode) : wx p ≤ 2 * nsq p := by
  have := coord_sq_le p 0
  unfold wx
  omega

lemma wxy_le (p : Mode) : wxy p ≤ 2 * nsq p := by
  have h : ((wxy p : ℕ) : ℤ) ≤ ((2 * nsq p : ℕ) : ℤ) := by
    have e1 : ((wxy p : ℕ) : ℤ) = (p 0 + p 1) ^ 2 := by simp [wxy, sq_abs]
    have e2 : ((nsq p : ℕ) : ℤ) = p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 := by
      simp [nsq, Fin.sum_univ_three, sq_abs]
    rw [e1]
    push_cast
    rw [e2]
    nlinarith [sq_nonneg (p 0 - p 1), sq_nonneg (p 2)]
  exact_mod_cast h

lemma rad_phiL {F : ℕ → ℕ} (hF : Ball 6084 F) :
    rad78 (phiL F) = ∑ p ∈ boxM 78, (2 * nsq p * F (nsq p)) ^ 2 := by
  have e : (2 : ℕ) ^ 13 = 8192 := by norm_num
  rw [rad78_eq (phiL F) (fun s hs => by
    have h1 : 6084 < s := by omega
    simp [phiL, hF s h1])]
  exact sum_congr rfl fun p _ => by simp [phiL, lit_eq, pow_two]

lemma rad_phiR78 {G : ℕ → ℕ} (hG : Ball 6084 G) :
    rad78 (phiR G) = ∑ p ∈ boxM 78, G (nsq p) ^ 2 := by
  have e : (2 : ℕ) ^ 13 = 8192 := by norm_num
  rw [rad78_eq (phiR G) (fun s hs => by
    have h1 : 6084 < s := by omega
    simp [phiR, hG s h1])]
  exact sum_congr rfl fun p _ => by simp [phiR, lit_eq, pow_two]

/-- The norm hypothesis of `hh_read_gen`, from `normChk`. -/
lemma norm_bound {F G : ℕ → ℕ} {w : Mode → ℕ} (hF : Ball 6084 F) (hG : Ball 6084 G)
    (hw : ∀ p, w p ≤ 2 * nsq p) (h : normChk F G = true) :
    (∑ p ∈ boxM 78, (F (nsq p) * w p) ^ 2) * (∑ p ∈ boxM 78, G (nsq p) ^ 2) < (2 ^ 80) ^ 2 := by
  have h1 : Nat.add (Nat.mul (rad78 (phiL F)) (rad78 (phiR G))) 1 ≤
      1461501637330902918203684832716283019655932542976 := Nat.le_of_ble_eq_true h
  have e2 : ((2 : ℕ) ^ 80) ^ 2 = 1461501637330902918203684832716283019655932542976 := by norm_num
  rw [e2]
  rw [rad_phiL hF, rad_phiR78 hG] at h1
  have h2 : ∑ p ∈ boxM 78, (F (nsq p) * w p) ^ 2 ≤ ∑ p ∈ boxM 78, (2 * nsq p * F (nsq p)) ^ 2 := by
    refine sum_le_sum fun p _ => Nat.pow_le_pow_left ?_ 2
    calc F (nsq p) * w p ≤ F (nsq p) * (2 * nsq p) := Nat.mul_le_mul_left _ (hw p)
      _ = _ := by ring
  have h3 := Nat.mul_le_mul_right (∑ p ∈ boxM 78, G (nsq p) ^ 2) h2
  simp only [Nat.add_eq, Nat.mul_eq] at h1
  generalize (∑ p ∈ boxM 78, (2 * nsq p * F (nsq p)) ^ 2) * ∑ p ∈ boxM 78, G (nsq p) ^ 2 = Z at h1 h3
  generalize (∑ p ∈ boxM 78, (F (nsq p) * w p) ^ 2) * ∑ p ∈ boxM 78, G (nsq p) ^ 2 = Y at h3 ⊢
  clear h h2 e2
  omega

/-- A kernel whose tables were checked. -/
theorem kerOK_of {F G : ℕ → ℕ} {T0 T1 : ℕ} (h0 : hhChk T0 (arrLx F) (arrR78 G) = true)
    (h1 : hhChk T1 (arrLxy F) (arrR78 G) = true) (hn : normChk F G = true) (hF : Ball 6084 F)
    (hG : Ball 6084 G) (hFb : ∀ A, F A < 2 ^ 64) (hGb : ∀ A, G A < 2 ^ 64) : KerOK F G T0 T1 where
  r0 := fun hx hy hz => by
    rw [hh_read_gen (U := fun p => F (nsq p) * wx p) (arrLx_spec hF hFb) (arrR78_spec hG hGb) h0 hG
      (norm_bound hF hG wx_le hn) hx hy hz]
    rfl
  r1 := fun hx hy hz => by
    rw [hh_read_gen (U := fun p => F (nsq p) * wxy p) (arrLxy_spec hF hFb) (arrR78_spec hG hGb) h1
      hG (norm_bound hF hG wxy_le hn) hx hy hz]
    rfl

/-- A real-weighted convolution. -/
def DR (F G : ℕ → ℕ) (k : Mode) (ψ : Mode → ℝ) : ℝ :=
  ∑ p ∈ boxM 78, (F (nsq p) : ℝ) * (G (nsq (k - p)) : ℝ) * ψ p

lemma act_one_mem {σ : Equiv.Perm (Fin 3)} {R : ℕ} {p : Mode} (hp : p ∈ boxM R) :
    act σ (fun _ => 1) p ∈ boxM R := by
  rw [mem_boxM] at hp ⊢
  intro i
  simpa [act] using hp (σ i)

lemma one_mul_one : ∀ i : Fin 3, (fun _ => (1 : ℤ)) i * (fun _ => (1 : ℤ)) i = 1 := by
  intro i; norm_num

/-- Reindexing a box sum by a permutation of the coordinates. -/
lemma box_perm (σ : Equiv.Perm (Fin 3)) (R : ℕ) (f : Mode → ℝ) :
    ∑ p ∈ boxM R, f (act σ (fun _ => 1) p) = ∑ p ∈ boxM R, f p := by
  refine sum_nbij' (act σ (fun _ => 1)) (actInv σ (fun _ => 1)) ?_ ?_ ?_ ?_ ?_
  · intro p hp; exact act_one_mem hp
  · intro p hp
    rw [mem_boxM] at hp ⊢
    intro i
    simpa [actInv] using hp (σ⁻¹ i)
  · intro p _; exact actInv_act one_mul_one p
  · intro p _; exact act_actInv one_mul_one p
  · intro p _; rfl

/-- Convolutions at a permuted output. -/
lemma DR_perm (σ : Equiv.Perm (Fin 3)) (F G : ℕ → ℕ) (k : Mode) (ψ : Mode → ℝ) :
    DR F G (act σ (fun _ => 1) k) ψ = DR F G k (fun p => ψ (act σ (fun _ => 1) p)) := by
  unfold DR
  rw [← box_perm σ 78]
  refine sum_congr rfl fun p _ => ?_
  rw [nsq_act one_mul_one, ← act_sub, nsq_act one_mul_one]

lemma DN_DR (w : Mode → ℕ) (F G : ℕ → ℕ) (k : Mode) :
    (DN w F G k : ℝ) = DR F G k (fun p => (w p : ℝ)) := by
  unfold DN DR
  push_cast
  exact sum_congr rfl fun _ _ => by ring

lemma wx_real (p : Mode) : (wx p : ℝ) = (p 0 : ℝ) ^ 2 := by
  have e : ((wx p : ℕ) : ℤ) = p 0 ^ 2 := by simp [wx, sq_abs]
  have h2 : (((wx p : ℕ) : ℤ) : ℝ) = ((p 0 ^ 2 : ℤ) : ℝ) := by rw [e]
  push_cast at h2
  exact h2

lemma wxy_real (p : Mode) : (wxy p : ℝ) = ((p 0 : ℝ) + p 1) ^ 2 := by
  have e : ((wxy p : ℕ) : ℤ) = (p 0 + p 1) ^ 2 := by simp [wxy, sq_abs]
  have h2 : (((wxy p : ℕ) : ℤ) : ℝ) = (((p 0 + p 1) ^ 2 : ℤ) : ℝ) := by rw [e]
  push_cast at h2
  exact h2

lemma kN_swap01 (a b c : ℕ) : kN b a c = act (Equiv.swap 0 1) (fun _ => 1) (kN a b c) := by
  funext i
  fin_cases i <;> simp [kN, act, Equiv.swap_apply_def]

lemma kN_swap02 (a b c : ℕ) : kN c b a = act (Equiv.swap 0 2) (fun _ => 1) (kN a b c) := by
  funext i
  fin_cases i <;> simp [kN, act, Equiv.swap_apply_def]

lemma kN_swap12 (a b c : ℕ) : kN a c b = act (Equiv.swap 1 2) (fun _ => 1) (kN a b c) := by
  funext i
  fin_cases i <;> simp [kN, act, Equiv.swap_apply_def]

/-- The real vector of an integer triple. -/
def kv3 (u0 u1 u2 : ℤ) : R3 := kv ![u0, u1, u2]

lemma dR_kv3 (p : Mode) (u0 u1 u2 : ℤ) :
    dR p (kv3 u0 u1 u2) = (p 0 : ℝ) * u0 + (p 1 : ℝ) * u1 + (p 2 : ℝ) * u2 := by
  simp [dR, kv3, kv, Fin.sum_univ_three]

/-- **The integer form read from the tables is the real form at an integer vector.** -/
theorem kerForm_real {F G : ℕ → ℕ} {T0 T1 : ℕ} (hK : KerOK F G T0 T1) {a b c : ℕ} (ha : a < 44)
    (hb : b < 44) (hc : c < 44) (u0 u1 u2 : ℤ) :
    ((kerForm T0 T1 a b c u0 u1 u2 : ℤ) : ℝ) = MR F G (kN a b c) (kv3 u0 u1 u2) := by
  set k := kN a b c with hk
  have d0 : (rdC T0 a b c : ℝ) = DR F G k (fun p => (p 0 : ℝ) ^ 2) := by
    rw [hK.r0 ha hb hc, DN_DR]
    exact congrArg _ (funext wx_real)
  have d1 : (rdC T0 b a c : ℝ) = DR F G k (fun p => (p 1 : ℝ) ^ 2) := by
    rw [hK.r0 hb ha hc, DN_DR, kN_swap01, DR_perm]
    refine congrArg _ (funext fun p => ?_)
    rw [wx_real]
    simp [act, Equiv.swap_apply_def]
  have d2 : (rdC T0 c b a : ℝ) = DR F G k (fun p => (p 2 : ℝ) ^ 2) := by
    rw [hK.r0 hc hb ha, DN_DR, kN_swap02, DR_perm]
    refine congrArg _ (funext fun p => ?_)
    rw [wx_real]
    simp [act, Equiv.swap_apply_def]
  have t01 : (rdC T1 a b c : ℝ) = DR F G k (fun p => ((p 0 : ℝ) + p 1) ^ 2) := by
    rw [hK.r1 ha hb hc, DN_DR]
    exact congrArg _ (funext wxy_real)
  have t02 : (rdC T1 a c b : ℝ) = DR F G k (fun p => ((p 0 : ℝ) + p 2) ^ 2) := by
    rw [hK.r1 ha hc hb, DN_DR, kN_swap12, DR_perm]
    refine congrArg _ (funext fun p => ?_)
    rw [wxy_real]
    simp [act, Equiv.swap_apply_def]
  have t12 : (rdC T1 c b a : ℝ) = DR F G k (fun p => ((p 2 : ℝ) + p 1) ^ 2) := by
    rw [hK.r1 hc hb ha, DN_DR, kN_swap02, DR_perm]
    refine congrArg _ (funext fun p => ?_)
    rw [wxy_real]
    simp [act, Equiv.swap_apply_def]
  unfold kerForm formZ
  push_cast
  rw [d0, d1, d2, t01, t02, t12]
  unfold DR MR
  simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib, dR_kv3]
  refine sum_congr rfl fun p _ => ?_
  ring

/-- Quadratic behaviour on the plane spanned by `r`, `s`. -/
def Polar (Q : R3 → ℝ) (r s t : R3) : Prop :=
  ∀ x y : ℝ, Q (x • r + y • s) = x ^ 2 * Q r + y ^ 2 * Q s + x * y * (Q t - Q r - Q s)

lemma dR_add_smul (p : Mode) (x y : ℝ) (r s : R3) :
    dR p (x • r + y • s) = x * dR p r + y * dR p s := by
  simp only [dR, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma polar_sum {ι : Type*} (S : Finset ι) (c : ι → ℝ) (d : ι → R3 → ℝ) (r s t : R3)
    (hd : ∀ i x y, d i (x • r + y • s) = x * d i r + y * d i s)
    (ht : ∀ i, d i t = d i r + d i s) :
    Polar (fun v => ∑ i ∈ S, c i * d i v ^ 2) r s t := by
  intro x y
  simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [hd, ht]
  ring

lemma Polar.add {Q Q' : R3 → ℝ} {r s t : R3} (h : Polar Q r s t) (h' : Polar Q' r s t) :
    Polar (fun v => Q v + Q' v) r s t := fun x y => by
  simp only [h x y, h' x y]; ring

lemma Polar.sub {Q Q' : R3 → ℝ} {r s t : R3} (h : Polar Q r s t) (h' : Polar Q' r s t) :
    Polar (fun v => Q v - Q' v) r s t := fun x y => by
  simp only [h x y, h' x y]; ring

lemma Polar.smul {Q : R3 → ℝ} {r s t : R3} (a : ℝ) (h : Polar Q r s t) :
    Polar (fun v => a * Q v) r s t := fun x y => by
  simp only [h x y]; ring

/-- `MR` is quadratic. -/
lemma polar_MR (F G : ℕ → ℕ) (k : Mode) (r s : R3) :
    Polar (MR F G k) r s (r + s) := by
  have := polar_sum (boxM 78) (fun p => (F (nsq p) : ℝ) * (G (nsq (k - p)) : ℝ)) (fun p v => dR p v)
    r s (r + s) (fun p x y => dR_add_smul p x y r s)
    (fun p => by simp only [dR, Fin.sum_univ_three, Pi.add_apply]; ring)
  exact this

end Row
end OVNS
