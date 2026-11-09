import OddViscousNS.Closed.Row.RowFinal

/-!
# The matrix band: a passing `rowTest` gives the row bound
-/

open Finset
open scoped ENNReal

noncomputable section

namespace OVNS
namespace Row

set_option maxRecDepth 20000
set_option linter.constructorNameAsVariable false

lemma quad_nonneg (P Q g x y : ℝ) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (h : g ^ 2 ≤ 4 * P * Q) :
    0 ≤ P * x ^ 2 + Q * y ^ 2 - g * (x * y) := by
  rcases hP.eq_or_lt with h0 | h0
  · subst h0
    have hg : g = 0 := by
      have : g ^ 2 ≤ 0 := by simpa using h
      exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm this (sq_nonneg _))
    subst hg
    simp
    positivity
  · have h1 : 0 ≤ 4 * P * (P * x ^ 2 + Q * y ^ 2 - g * (x * y)) := by
      have e : 4 * P * (P * x ^ 2 + Q * y ^ 2 - g * (x * y)) =
          (2 * P * x - g * y) ^ 2 + (4 * P * Q - g ^ 2) * y ^ 2 := by ring
      rw [e]
      have := sq_nonneg (2 * P * x - g * y)
      have h2 : 0 ≤ (4 * P * Q - g ^ 2) * y ^ 2 :=
        mul_nonneg (by linarith) (sq_nonneg _)
      linarith
    exact nonneg_of_mul_nonneg_right h1 (by positivity)

/-- The real content of the `2×2` test. -/
lemma test2_real {Gam al be ga r2 s2 : ℚ} (h : test2 Gam al be ga r2 s2 = true) (x y : ℝ) :
    (al : ℝ) * x ^ 2 + (be : ℝ) * y ^ 2 + (ga : ℝ) * (x * y) ≤
      (Gam : ℝ) * (x ^ 2 * r2 + y ^ 2 * s2) := by
  unfold test2 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have h1' : (0 : ℝ) ≤ (Gam : ℝ) * r2 - al := by exact_mod_cast h1
  have h2' : (0 : ℝ) ≤ (Gam : ℝ) * s2 - be := by exact_mod_cast h2
  have h3' : (ga : ℝ) * ga ≤ 4 * ((Gam : ℝ) * r2 - al) * ((Gam : ℝ) * s2 - be) := by
    exact_mod_cast h3
  have := quad_nonneg ((Gam : ℝ) * r2 - al) ((Gam : ℝ) * s2 - be) (ga : ℝ) x y h1' h2'
    (by nlinarith)
  nlinarith

lemma cast_hQ (HC : ℕ) : ((hQ HC : ℚ) : ℝ) = (HC : ℝ) / 1000 := by
  simp only [hQ]; push_cast; rfl

lemma cast_a2 : ((a2Q : ℚ) : ℝ) = (29 / 100) ^ 2 := by
  simp only [a2Q]; push_cast; ring

section row
variable {k : Mode}

lemma hm_cast (hk : k ≠ 0) : hm k = ((hQ (metric (nsq k)) : ℚ) : ℝ) := by
  rw [cast_hQ, hm, metric_spec (nsq_pos_of_ne hk)]

lemma e_cast (hk : k ≠ 0) : ((eQ (metric (nsq k)) : ℚ) : ℝ) = hm k - 117 / 500 := by
  rw [hm_cast hk]
  simp only [eQ]
  push_cast
  rfl

lemma d_cast (hk : k ≠ 0) :
    ((dQ (nsq k) (metric (nsq k)) : ℚ) : ℝ) = hm k - 29 / 100 * absSq k - 117 / 500 := by
  rw [hm_cast hk, ← nsq_cast]
  simp only [dQ]
  push_cast
  rfl

lemma om_cast (C : ℕ) : ((omQ (root C) : ℚ) : ℝ) = om C := by
  have hr : (0 : ℝ) < root C := by exact_mod_cast root_pos C
  simp only [omQ, om, root_spec]
  push_cast
  field_simp
  ring

end row

/-- The real value of `formX`. -/
lemma formX_real {T : Tabs} (hT : TabsOK T) {a b c : ℕ} (ha : a < 44) (hb : b < 44) (hc : c < 44)
    (e om2 dX : ℚ) (u0 u1 u2 : ℤ) :
    ((formX T a b c e om2 dX u0 u1 u2 : ℚ) : ℝ) =
      (om2 : ℝ) * (2 * (e : ℝ) ^ 2 * m10 (kN a b c) (kv3 u0 u1 u2)
        - 4 * (29 / 100) * (e : ℝ) * m20 (kN a b c) (kv3 u0 u1 u2)
        + 2 * (29 / 100) ^ 2 * m30 (kN a b c) (kv3 u0 u1 u2)) + (dX : ℝ) := by
  unfold formX m10 m20 m30
  rw [← kerForm_real hT.k10 ha hb hc, ← kerForm_real hT.k20 ha hb hc, ← kerForm_real hT.k30 ha hb hc]
  push_cast [cast_a2]
  ring

/-- The real value of `formY`. -/
lemma formY_real {T : Tabs} (hT : TabsOK T) {a b c : ℕ} (ha : a < 44) (hb : b < 44) (hc : c < 44)
    (dl om2 dY : ℚ) (u0 u1 u2 : ℤ) :
    ((formY T a b c dl om2 dY u0 u1 u2 : ℚ) : ℝ) =
      (om2 : ℝ) * (2 * (dl : ℝ) ^ 2 * (m20 (kN a b c) (kv3 u0 u1 u2) - m11 (kN a b c) (kv3 u0 u1 u2))
        + 2 * (29 / 100) ^ 2 * (m31 (kN a b c) (kv3 u0 u1 u2) - m22 (kN a b c) (kv3 u0 u1 u2)))
        + (dY : ℝ) := by
  unfold formY m20 m11 m31 m22
  rw [← kerForm_real hT.k20 ha hb hc, ← kerForm_real hT.k11 ha hb hc,
    ← kerForm_real hT.k31 ha hb hc, ← kerForm_real hT.k22 ha hb hc]
  push_cast [cast_a2]
  ring

/-- The constant of the low zone. -/
def lfR (rC : ℕ) : ℝ := 9 * (rC : ℝ) * rC / lowS

/-- The total form on `(p·c'')²`. -/
def q1 (k : Mode) (v : R3) : ℝ :=
  om (nsq k) ^ 2 * (2 * (hm k - 117 / 500) ^ 2 * m10 k v
      - 4 * (29 / 100) * (hm k - 117 / 500) * m20 k v + 2 * (29 / 100) ^ 2 * m30 k v)
    + lfR (root (nsq k)) * LX k (metric (nsq k)) (root (nsq k)) v

/-- The total form on `(p·c)²`. -/
def q2 (k : Mode) (v : R3) : ℝ :=
  om (nsq k) ^ 2 * (2 * (hm k - 29 / 100 * absSq k - 117 / 500) ^ 2 * (m20 k v - m11 k v)
      + 2 * (29 / 100) ^ 2 * (m31 k v - m22 k v))
    + lfR (root (nsq k)) * LY k (nsq k) (metric (nsq k)) (root (nsq k)) v

lemma polar_div {Q : R3 → ℝ} {r s t : R3} (h : Polar Q r s t) (d : ℝ) :
    Polar (fun v => Q v / d) r s t := fun x y => by
  simp only [h x y]; ring

lemma polar_LX (k : Mode) (HC rC : ℕ) (r s : R3) : Polar (LX k HC rC) r s (r + s) :=
  polar_sum (boxM 10) (fun p => (fa1 k HC rC p : ℝ)) (fun p v => dR p v) r s (r + s)
    (fun p x y => dR_add_smul p x y r s)
    (fun p => by simp only [dR, Fin.sum_univ_three, Pi.add_apply]; ring)

lemma polar_LY (k : Mode) (C HC rC : ℕ) (r s : R3) : Polar (LY k C HC rC) r s (r + s) :=
  polar_sum (boxM 10) (fun p => (fa2 k C HC rC p : ℝ)) (fun p v => dR p v) r s (r + s)
    (fun p x y => dR_add_smul p x y r s)
    (fun p => by simp only [dR, Fin.sum_univ_three, Pi.add_apply]; ring)

lemma polar_q1 (k : Mode) (r s : R3) : Polar (q1 k) r s (r + s) := by
  intro x y
  have a1 := polar_div (polar_MR L10 R10 k r s) 618970019642690137449562112 x y
  have a2 := polar_div (polar_MR L20 R20 k r s) 604462909807314587353088 x y
  have a3 := polar_div (polar_MR L30 R30 k r s) 147573952589676412928 x y
  have a4 := polar_LX k (metric (nsq k)) (root (nsq k)) r s x y
  simp only [] at a1 a2 a3
  unfold q1 m10 m20 m30
  rw [a1, a2, a3, a4]
  ring

lemma polar_q2 (k : Mode) (r s : R3) : Polar (q2 k) r s (r + s) := by
  intro x y
  have a1 := polar_div (polar_MR L20 R20 k r s) 604462909807314587353088 x y
  have a2 := polar_div (polar_MR L11 R11 k r s) 1208925819614629174706176 x y
  have a3 := polar_div (polar_MR L31 R31 k r s) 1152921504606846976 x y
  have a5 := polar_div (polar_MR L22 R22 k r s) 9223372036854775808 x y
  have a4 := polar_LY k (nsq k) (metric (nsq k)) (root (nsq k)) r s x y
  simp only [] at a1 a2 a3 a5
  unfold q2 m20 m11 m31 m22
  rw [a1, a2, a3, a4, a5]
  ring

lemma wS_real (u p : Mode) : (wS u p : ℝ) = dR p (kv u) ^ 2 := by
  have h := wS_int u p
  have h2 : (((wS u p : ℕ) : ℤ) : ℝ) = ((iprod p u ^ 2 : ℤ) : ℝ) := by rw [h]
  push_cast at h2
  rw [h2]
  simp [dR, kv, iprod, Fin.sum_univ_three]

lemma lowD_cast (S rC i : ℕ) : ((lowD S rC i : ℚ) : ℝ) = lfR rC * (rd 128 i S : ℝ) := by
  unfold lowD lfR
  push_cast
  ring

/-- The bound on the lens from the forms. -/
theorem lens_le (hE : ErrOK) {k : Mode} (hk : k ≠ 0) (hk1 : nsq k < 1936) (c : R3)
    (hc : dR k c = 0) :
    ∑ p ∈ lensF k 78, pterm k c p ≤ q1 k (crR k c) + q2 k c +
      om (nsq k) ^ 2 * ((2 * (hm k - 117 / 500) ^ 2 * (E10 : ℝ)
        + 2 * (29 / 100) ^ 2 * (E30 : ℝ)) * absSq k
        + 2 * (hm k - 29 / 100 * absSq k - 117 / 500) ^ 2 * (E20 : ℝ)
        + 2 * (29 / 100) ^ 2 * (E31 : ℝ)) * nR c := by
  rw [lens_split k c hc hk1]
  have h1 := hh_le hE k c hc (hm_small hk hk1).1
  have h2 := lo_le k hk c
  simp only [] at h1
  unfold q1 q2 lfR
  linarith

set_option exponentiation.threshold 2000 in
lemma lim_eq : (528294531135665246352339784916516606518847326036121522127960709026673902556724859474417255887657187894674394993257128678882347559502685537250538978462939576908386683999005084168731517676426441053024232908211188404148028292751561738838396898767036476489538580897737998336 : ℕ) = Yb ^ 7 := by
  unfold Yb
  rw [← pow_mul]
  norm_num

/-- The real value of the tail. -/
lemma tail_cast {k : Mode} (hk : k ≠ 0) (cK : ℕ) :
    ((tailQ (nsq k) (metric (nsq k)) (root (nsq k)) cK : ℚ) : ℝ) =
      om (nsq k) ^ 2 * (1 + (hm k - 29 / 100 * absSq k - 117 / 500) ^ 2 /
        ((29 / 100) ^ 2 * ((78 - cK : ℕ) : ℝ) ^ 4)) * (absSq k * (4 * (15 * ((78 - cK : ℕ) : ℝ)⁻¹)
        + absSq k * (15 * ((78 - cK : ℕ) : ℝ)⁻¹ ^ 3))) / 3 := by
  unfold tailQ
  simp only []
  rw [← nsq_cast k]
  push_cast [d_cast hk, om_cast, cast_a2]
  rw [← nsq_cast k]
  ring

/-- The real value of the rounding error. -/
lemma err_cast {k : Mode} (hk : k ≠ 0) :
    ((errQ (nsq k) (metric (nsq k)) (root (nsq k)) : ℚ) : ℝ) =
      om (nsq k) ^ 2 * ((2 * (hm k - 117 / 500) ^ 2 * (E10 : ℝ)
        + 2 * (29 / 100) ^ 2 * (E30 : ℝ)) * absSq k
        + 2 * (hm k - 29 / 100 * absSq k - 117 / 500) ^ 2 * (E20 : ℝ)
        + 2 * (29 / 100) ^ 2 * (E31 : ℝ)) := by
  unfold errQ
  rw [← nsq_cast k]
  push_cast [d_cast hk, e_cast hk, om_cast, cast_a2]
  rw [← nsq_cast k]
  ring

/-- The real value of `Γ`. -/
lemma gam_cast {k : Mode} (hk : k ≠ 0) (G cK : ℕ) :
    ((gamQ (nsq k) (metric (nsq k)) (root (nsq k)) G cK : ℚ) : ℝ) =
      36 * ((G : ℝ) / 1000000000) * hm k
        - ((tailQ (nsq k) (metric (nsq k)) (root (nsq k)) cK : ℚ) : ℝ)
        - ((errQ (nsq k) (metric (nsq k)) (root (nsq k)) : ℚ) : ℝ) := by
  unfold gamQ
  push_cast
  rw [cast_hQ, hm, metric_spec (nsq_pos_of_ne hk)]

/-- The real value of the `X` forms. -/
lemma X_val {T : Tabs} (hT : TabsOK T) {a b c : ℕ} (ha : a < 44) (hb : b < 44) (hc : c < 44)
    (hk : kN a b c ≠ 0) (S i : ℕ) (u0 u1 u2 : ℤ)
    (hd : (rd 128 i S : ℝ) = LX (kN a b c) (metric (nsq (kN a b c))) (root (nsq (kN a b c)))
      (kv3 u0 u1 u2)) :
    ((formX T a b c (eQ (metric (nsq (kN a b c))))
        (omQ (root (nsq (kN a b c))) * omQ (root (nsq (kN a b c))))
        (lowD S (root (nsq (kN a b c))) i) u0 u1 u2 : ℚ) : ℝ) = q1 (kN a b c) (kv3 u0 u1 u2) := by
  rw [formX_real hT ha hb hc, lowD_cast, hd, e_cast hk]
  push_cast [om_cast]
  unfold q1
  ring

/-- The real value of the `Y` forms. -/
lemma Y_val {T : Tabs} (hT : TabsOK T) {a b c : ℕ} (ha : a < 44) (hb : b < 44) (hc : c < 44)
    (hk : kN a b c ≠ 0) (S i : ℕ) (u0 u1 u2 : ℤ)
    (hd : (rd 128 i S : ℝ) = LY (kN a b c) (nsq (kN a b c)) (metric (nsq (kN a b c)))
      (root (nsq (kN a b c))) (kv3 u0 u1 u2)) :
    ((formY T a b c (dQ (nsq (kN a b c)) (metric (nsq (kN a b c))))
        (omQ (root (nsq (kN a b c))) * omQ (root (nsq (kN a b c))))
        (lowD S (root (nsq (kN a b c))) i) u0 u1 u2 : ℚ) : ℝ) = q2 (kN a b c) (kv3 u0 u1 u2) := by
  rw [formY_real hT ha hb hc, lowD_cast, hd, d_cast hk]
  push_cast [om_cast]
  unfold q2
  ring

/-- The sum vector. -/
lemma rV_add_sV (a b ac bc Q : ℕ) :
    kv (rV a b + sV ac bc Q) = kv3 (-(b : ℤ) - ac) ((a : ℤ) - bc) (Q : ℤ) := by
  funext i
  fin_cases i <;> simp [kv, kv3, rV, sV] <;> ring

lemma vt_add (a b ac bc Q : ℕ) :
    kv3 (-(b : ℤ) - ac) ((a : ℤ) - bc) (Q : ℤ) =
      kv3 (-(b : ℤ)) (a : ℤ) 0 + kv3 (-(ac : ℤ)) (-(bc : ℤ)) (Q : ℤ) := by
  funext i
  fin_cases i <;> simp [kv, kv3] <;> ring

/-- Coordinates of a vector orthogonal to `k`. -/
lemma coords {a b c : ℕ} (ha0 : 0 < a) (w : R3) (hw : dR (kN a b c) w = 0) :
    let Q : ℝ := (a : ℝ) * a + (b : ℝ) * b
    let x := ((a : ℝ) * w 1 - (b : ℝ) * w 0) / Q
    let y := w 2 / Q
    w = x • kv3 (-(b : ℤ)) (a : ℤ) 0 + y • kv3 (-((a * c : ℕ) : ℤ)) (-((b * c : ℕ) : ℤ))
      ((a * a + b * b : ℕ) : ℤ) := by
  intro Q x y
  have hQ : Q ≠ 0 := by
    have : (0 : ℝ) < a := by exact_mod_cast ha0
    positivity
  have h : (a : ℝ) * w 0 + (b : ℝ) * w 1 + (c : ℝ) * w 2 = 0 := by
    simpa [dR, kN, Fin.sum_univ_three] using hw
  funext i
  fin_cases i
  · simp [kv, kv3, x, y]
    field_simp
    simp only [Q]
    linear_combination (a : ℝ) * h
  · simp [kv, kv3, x, y]
    field_simp
    simp only [Q]
    linear_combination (b : ℝ) * h
  · simp [kv, kv3, y]
    field_simp
    simp only [Q]
    ring

/-- `k × r = s`, `k × s = -C r`. -/
lemma cross_vec {a b c : ℕ} (x y : ℝ) :
    crR (kN a b c) (x • kv3 (-(b : ℤ)) (a : ℤ) 0 + y • kv3 (-((a * c : ℕ) : ℤ)) (-((b * c : ℕ) : ℤ))
      ((a * a + b * b : ℕ) : ℤ)) =
      (-y * (nsq (kN a b c) : ℝ)) • kv3 (-(b : ℤ)) (a : ℤ) 0
        + x • kv3 (-((a * c : ℕ) : ℤ)) (-((b * c : ℕ) : ℤ)) ((a * a + b * b : ℕ) : ℤ) := by
  rw [nsq_kN]
  funext i
  fin_cases i <;> simp [crR, kN, kv, kv3] <;> ring

/-- The squared length in the coordinates. -/
lemma nR_coords {a b c : ℕ} (x y : ℝ) :
    nR (x • kv3 (-(b : ℤ)) (a : ℤ) 0 + y • kv3 (-((a * c : ℕ) : ℤ)) (-((b * c : ℕ) : ℤ))
      ((a * a + b * b : ℕ) : ℤ)) =
      x ^ 2 * (((a * a + b * b : ℕ) : ℚ) : ℝ) + y ^ 2 *
        ((((nsq (kN a b c) : ℕ) : ℚ) * ((a * a + b * b : ℕ) : ℚ) : ℚ) : ℝ) := by
  rw [nsq_kN]
  simp [nR, kv, kv3, Fin.sum_univ_three]
  ring

/-- **A passing row test gives the row bound.** -/
theorem row_matrix {T : Tabs} (hT : TabsOK T) (hE : ErrOK) {a b c cK : ℕ} (hab : b ≤ a)
    (hbc : c ≤ b) (ha0 : 0 < a) (hC1 : a * a + (b * b + c * c) < 1936)
    (ht : rowTest T a b c cK = true) (w : R3) (hw : dR (kN a b c) w = 0) :
    rowR (kN a b c) w ≤
      ENNReal.ofReal (36 * gOVNS (nsq (kN a b c)) * hm (kN a b c) * nR w) := by
  have ha : a < 44 := by nlinarith
  have hb : b < 44 := by omega
  have hc : c < 44 := by omega
  have hk : kN a b c ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [kN] at this
    omega
  have hC : nsq (kN a b c) = a * a + (b * b + c * c) := nsq_kN a b c
  have hk1 : nsq (kN a b c) < 1936 := by rw [hC]; exact hC1
  unfold rowTest at ht
  simp only [litB_eq, Nat.add_eq, Nat.mul_eq] at ht
  rw [← hC] at ht
  simp only [Bool.and_eq_true] at ht
  obtain ⟨h1, h2, h3, h4⟩ := ht
  have hlim : Nat.add (lowSum a b c (nsq (kN a b c)) (metric (nsq (kN a b c)))
      (root (nsq (kN a b c))) (a * a + b * b) (a * c) (b * c)) 1 ≤ Yb ^ 7 := by
    rw [← lim_eq]
    exact Nat.le_of_ble_eq_true h1
  have hcK : nsq (kN a b c) ≤ cK * cK := Nat.le_of_ble_eq_true h2
  have hcK2 : cK + 34 ≤ 78 := Nat.le_of_ble_eq_true h3
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := lowSum_slots a b c (nsq (kN a b c)) (metric (nsq (kN a b c)))
    (root (nsq (kN a b c))) (a * a + b * b) (a * c) (b * c) hlim
  set S := lowSum a b c (nsq (kN a b c)) (metric (nsq (kN a b c)))
    (root (nsq (kN a b c))) (a * a + b * b) (a * c) (b * c) with hS
  set k := kN a b c with hkk
  set HC := metric (nsq k) with hHC
  set rC := root (nsq k) with hrC
  set Q := a * a + b * b with hQd
  set vr := kv3 (-(b : ℤ)) (a : ℤ) 0 with hvr
  set vs := kv3 (-((a * c : ℕ) : ℤ)) (-((b * c : ℕ) : ℤ)) (Q : ℤ) with hvs
  have hvr' : kv (rV a b) = vr := rfl
  have hvs' : kv (sV (a * c) (b * c) Q) = vs := rfl
  have hvt' : kv (rV a b + sV (a * c) (b * c) Q) =
      kv3 (-(b : ℤ) - ((a * c : ℕ) : ℤ)) ((a : ℤ) - ((b * c : ℕ) : ℤ)) (Q : ℤ) := rV_add_sV _ _ _ _ _
  have hvadd := vt_add a b (a * c) (b * c) Q
  set vt := kv3 (-(b : ℤ) - ((a * c : ℕ) : ℤ)) ((a : ℤ) - ((b * c : ℕ) : ℤ)) (Q : ℤ) with hvt
  have dig : ∀ (f : Mode → ℕ) (g : Mode → ℕ) (u : R3) (hg : ∀ p, (g p : ℝ) = dR p u ^ 2) (i : ℕ)
      (hi : rd 128 i S = ∑ p ∈ boxM 10, f p * g p),
      (rd 128 i S : ℝ) = ∑ p ∈ boxM 10, (f p : ℝ) * dR p u ^ 2 := by
    intro f g u hg i hi
    rw [hi]
    push_cast
    exact sum_congr rfl fun p _ => by rw [hg]
  have d0 := dig _ _ vs (fun p => by rw [wS_real, hvs']) 0 s0
  have d1 := dig _ _ vr (fun p => by rw [wS_real, hvr']) 1 s1
  have d2 := dig _ _ vt (fun p => by rw [wS_real, hvt']) 2 s2
  have d3 := dig _ _ vs (fun p => by rw [wS_real, hvs']) 3 s3
  have d4 := dig _ _ vr (fun p => by rw [wS_real, hvr']) 4 s4
  have d5 := dig _ _ vt (fun p => by rw [wS_real, hvt']) 5 s5
  have hXs : ((formX T a b c (eQ HC) (omQ rC * omQ rC) (lowD S rC 0) (-((a * c : ℕ) : ℤ))
      (-((b * c : ℕ) : ℤ)) (Q : ℤ) : ℚ) : ℝ) = q1 k vs := X_val hT ha hb hc hk S 0 _ _ _ d0
  have hXr : ((formX T a b c (eQ HC) (omQ rC * omQ rC) (lowD S rC 1) (-(b : ℤ)) (a : ℤ) 0 : ℚ) : ℝ) =
      q1 k vr := X_val hT ha hb hc hk S 1 _ _ _ d1
  have hXt : ((formX T a b c (eQ HC) (omQ rC * omQ rC) (lowD S rC 2) (-(b : ℤ) - ((a * c : ℕ) : ℤ))
      ((a : ℤ) - ((b * c : ℕ) : ℤ)) (Q : ℤ) : ℚ) : ℝ) = q1 k vt :=
    X_val hT ha hb hc hk S 2 _ _ _ d2
  have hYs : ((formY T a b c (dQ (nsq k) HC) (omQ rC * omQ rC) (lowD S rC 3) (-((a * c : ℕ) : ℤ))
      (-((b * c : ℕ) : ℤ)) (Q : ℤ) : ℚ) : ℝ) = q2 k vs := Y_val hT ha hb hc hk S 3 _ _ _ d3
  have hYr : ((formY T a b c (dQ (nsq k) HC) (omQ rC * omQ rC) (lowD S rC 4) (-(b : ℤ)) (a : ℤ) 0 :
      ℚ) : ℝ) = q2 k vr := Y_val hT ha hb hc hk S 4 _ _ _ d4
  have hYt : ((formY T a b c (dQ (nsq k) HC) (omQ rC * omQ rC) (lowD S rC 5)
      (-(b : ℤ) - ((a * c : ℕ) : ℤ)) ((a : ℤ) - ((b * c : ℕ) : ℤ)) (Q : ℤ) : ℚ) : ℝ) = q2 k vt :=
    Y_val hT ha hb hc hk S 5 _ _ _ d5
  obtain ⟨x, y, hxy⟩ : ∃ x y : ℝ, w = x • vr + y • vs := ⟨_, _, coords ha0 w hw⟩
  subst hxy
  have hcr : crR k (x • vr + y • vs) = (-y * (nsq k : ℝ)) • vr + x • vs := cross_vec x y
  have hnorm := nR_coords (a := a) (b := b) (c := c) x y
  have p1 := polar_q1 k vr vs (-y * (nsq k : ℝ)) x
  have p2 := polar_q2 k vr vs x y
  have hlens := lens_le hE hk hk1 (x • vr + y • vs) hw
  rw [hcr, p1, p2, ← hvadd, ← err_cast hk] at hlens
  unfold rowTestS testF at h4
  have h5 := test2_real h4 x y
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_sub, Rat.cast_natCast] at h5
  rw [hXs, hXr, hXt, hYs, hYr, hYt, gam_cast hk] at h5
  have htail := tail_row hk hk1 hcK hcK2 (x • vr + y • vs) hw
  simp only [] at htail
  rw [← tail_cast hk cK] at htail
  have hT0 : 0 ≤ ((tailQ (nsq k) HC rC cK : ℚ) : ℝ) := by
    rw [hHC, hrC, tail_cast hk cK]
    have := absSq_nonneg' k
    positivity
  have hn : nR (x • vr + y • vs) = x ^ 2 * (Q : ℝ) + y ^ 2 * ((nsq k : ℝ) * (Q : ℝ)) := by
    have hQc : (Q : ℝ) = (a : ℝ) * a + (b : ℝ) * b := by
      simp only [hQd]
      push_cast
      ring
    rw [hnorm]
    push_cast
    rw [hQc]
  rw [← hn] at h5
  set n := nR (x • vr + y • vs) with hndef
  have hn0 : 0 ≤ n := nR_nonneg _
  set L := ∑ p ∈ lensF k 78, pterm k (x • vr + y • vs) p with hL
  have hL0 : 0 ≤ L := sum_nonneg fun _ _ => pterm_nonneg _ _ _
  set Tl := ((tailQ (nsq k) HC rC cK : ℚ) : ℝ) with hTl
  set Er := ((errQ (nsq k) (metric (nsq k)) (root (nsq k)) : ℚ) : ℝ) with hEr
  have hmain : L + Tl * n ≤ 36 * ((gN (nsq k) : ℝ) / 1000000000) * hm k * n := by
    have e1 : L ≤ ((36 * ((gN (nsq k) : ℝ) / 1000000000) * hm k - Tl - Er) * n) + Er * n := by
      refine hlens.trans ?_
      refine add_le_add ?_ le_rfl
      refine le_trans (le_of_eq ?_) h5
      ring
    linarith
  have hg := gN_le (nsq k)
  have hfin : 36 * ((gN (nsq k) : ℝ) / 1000000000) * hm k * n ≤ 36 * gOVNS (nsq k) * hm k * n := by
    have := hm_nonneg k
    have h6 : 36 * ((gN (nsq k) : ℝ) / 1000000000) ≤ 36 * gOVNS (nsq k) := by linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h6 this) hn0
  rw [rowR_split k _ 78]
  refine (add_le_add le_rfl htail).trans ?_
  rw [← ENNReal.ofReal_add hL0 (mul_nonneg hT0 hn0)]
  exact ENNReal.ofReal_le_ofReal (hmain.trans hfin)

end Row
end OVNS
