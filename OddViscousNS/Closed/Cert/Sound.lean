import OddViscousNS.Closed.Cert.Bounds
import OddViscousNS.Closed.Moments

/-!
# Soundness of the directed cube certificate (Lemma 5.5 of the reconstruction)

If a nonzero admissible field `w` has `(X(w), Y(w))` on the edge at parameter `u`, first-shell
ratio `ρ(w) = ρ(u,p)` and moment `t(w) = v·T(z,ρ)` with `(u,p,v)` in a box `b ⊆ [0,1]³`, then
`Z − m J₁ − s |cubic w| ≥ gap(e,b) · Z`: every directed bound of `gap` dominates the actual
quantity (`√Y ≤ √↑Y₊`, `J₁/Z ≤ K₊`, `|cubic|/(√Y Z) ≤ C_cond(ρ,t,q) ≤ C₊`; the conditional cubic
bound is taken as a hypothesis here and supplied by `cubic_le_cond`).  The recursive checker
is sound: an accepted tree below `b` covers `b` by accepted leaves.
-/

open Set

namespace OVNS

namespace Cert

/-- `√v ≤ √↑v` for `v ≥ 0`. -/
private lemma nat_aux (A d N : ℕ) (hd : 0 < d) (hA : 1 ≤ A) (h : (A - 1) / d < N * N) :
    A ≤ d * (N * N) := by
  have h2 := Nat.div_add_mod (A - 1) d
  have h3 := Nat.mod_lt (A - 1) hd
  have h4 := Nat.mul_le_mul_left d (Nat.succ_le_of_lt h)
  rw [Nat.mul_succ] at h4
  generalize d * ((A - 1) / d) = P at *
  generalize d * (N * N) = Q at *
  omega

private lemma usqrt_sq_ge {v : ℚ} (hv : 0 < v) : v ≤ usqrt v ^ 2 := by
  have hn : 0 < v.num := Rat.num_pos.2 hv
  have hnn : ((v.num.toNat : ℕ) : ℤ) = v.num := Int.toNat_of_nonneg hn.le
  have hd : 0 < v.den := v.den_pos
  have hn1 : 1 ≤ v.num.toNat := by omega
  have h4 : 1 ≤ v.num.toNat * 10 ^ 24 := le_trans hn1 (Nat.le_mul_of_pos_right _ (by positivity))
  have h5 := nat_aux _ _ _ hd h4 (Nat.lt_succ_sqrt ((v.num.toNat * 10 ^ 24 - 1) / v.den))
  have hv' : v = (v.num.toNat : ℚ) / v.den := by
    conv_lhs => rw [← Rat.num_div_den v]
    rw [← hnn]; push_cast; rfl
  simp only [usqrt, not_le.2 hv, ↓reduceIte]
  conv_lhs => rw [hv']
  rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  have h6 : ((v.num.toNat * 10 ^ 24 : ℕ) : ℚ) ≤ ((v.den *
      ((Nat.sqrt ((v.num.toNat * 10 ^ 24 - 1) / v.den)).succ *
        (Nat.sqrt ((v.num.toNat * 10 ^ 24 - 1) / v.den)).succ) : ℕ) : ℚ) := by
    exact_mod_cast h5
  push_cast at h6 ⊢
  nlinarith

theorem sqrt_le_usqrt {v : ℚ} (hv : 0 ≤ v) : Real.sqrt (v : ℝ) ≤ (usqrt v : ℝ) := by
  rcases hv.lt_or_eq with hv | hv
  · have h := usqrt_sq_ge hv
    have h0 : (0 : ℝ) ≤ (usqrt v : ℝ) := by
      unfold usqrt; split_ifs <;> push_cast <;> positivity
    rw [Real.sqrt_le_left h0]
    exact_mod_cast h
  · rw [← hv]; simp [usqrt]

theorem usqrt_nonneg (v : ℚ) : 0 ≤ usqrt v := by
  unfold usqrt; split_ifs <;> positivity

/-- `√x ≤ √↑v` whenever `x ≤ v` (no sign condition). -/
theorem sqrt_le_usqrt' {x : ℝ} {v : ℚ} (h : x ≤ v) : Real.sqrt x ≤ (usqrt v : ℝ) := by
  rcases le_or_gt 0 v with hv | hv
  · exact (Real.sqrt_le_sqrt h).trans (sqrt_le_usqrt hv)
  · have hx : x ≤ 0 := h.trans (by exact_mod_cast hv.le)
    rw [Real.sqrt_eq_zero'.2 hx]
    exact_mod_cast usqrt_nonneg v

/-- The actual parameters of a field on the edge. -/
structure OnEdge (e : Edge) (w : Field) (u p v : ℝ) : Prop where
  u01 : u ∈ Icc (0 : ℝ) 1
  p01 : p ∈ Icc (0 : ℝ) 1
  v01 : v ∈ Icc (0 : ℝ) 1
  hX : Xr w = (e.xl : ℝ) + ((e.xh : ℝ) - e.xl) * u
  hY : Yr w = (e.yl : ℝ) + ((e.yh : ℝ) - e.yl) * u
  hρ : ρw w = (1 - p) * max 0 (((h2q : ℝ) * (Xr w / Yr w) - 1) / ((h2q : ℝ) - 1)) +
    p * (Xr w / Yr w)
  ht : tYZ w = v * min (Xr w / Yr w) (min (1 / (2 - ρw w))
    (1 / max 1 ((Cq : ℝ) - Dq * (Xr w / Yr w) + Lq * ρw w)))

/-- Membership of real parameters in a rational box. -/
def Box.mem (b : Box) (u p v : ℝ) : Prop :=
  u ∈ Icc (b.ul : ℝ) b.uh ∧ p ∈ Icc (b.pl : ℝ) b.ph ∧ v ∈ Icc (b.vl : ℝ) b.vh

/-- Admissible edges: those of the plan (positive slope `< 2/3`, positive intercept, left knot
above the plateau, knots in `[0,1]`). -/
structure Edge.Good (e : Edge) : Prop where
  m_pos : 0 < e.m
  m_lt : e.m < 2 / 3
  width_pos : 0 < e.width
  xh_le : e.xh ≤ 1
  xl_nonneg : 0 ≤ e.xl
  intercept_pos : 0 < e.yh - e.m * e.xh
  yl_ge : Yc ≤ e.yl
  yl_ge_xl : e.xl ≤ e.yl
  yh_ge_xh : e.xh ≤ e.yh

private theorem kX_nonneg : ∀ i ≤ 41, 0 ≤ kX i := by
  decide +kernel

private theorem kX_le_kY : ∀ i ≤ 41, kX i ≤ kY i := by
  decide +kernel

private theorem edgeOf_xl (i : ℕ) : (edgeOf i).xl = kX (i + 1) := by
  simp only [Edge.xl, edgeOf]; ring

private theorem edgeOf_yl {i : ℕ} (hi : i < 41) : (edgeOf i).yl = kY (i + 1) := by
  simp only [Edge.yl, edgeOf]; rw [knot_step i hi]

theorem edgeOf_good {i : ℕ} (hi : i < 41) : (edgeOf i).Good where
  m_pos := slope_pos i hi
  m_lt := slope_lt i hi
  width_pos := sub_pos.2 (kX_anti i hi)
  xh_le := kX_le_one i hi.le
  xl_nonneg := by rw [edgeOf_xl]; exact kX_nonneg _ hi
  intercept_pos := intercept_pos i hi
  yl_ge := by rw [edgeOf_yl hi]; exact Yc_le_kY _ hi
  yl_ge_xl := by rw [edgeOf_xl, edgeOf_yl hi]; exact kX_le_kY _ hi
  yh_ge_xh := kX_le_kY i hi.le

/-! ### Constants -/

private lemma h2q_eq : (h2q : ℝ) = 1569 / 1000 := by norm_num [h2q]
private lemma h3q_eq : (h3q : ℝ) = 1021 / 500 := by norm_num [h3q]
private lemma Dq_eq : (Dq : ℝ) = 1601949 / 236500 := by norm_num [Dq, h2q, h3q]
private lemma Cq_eq : (Cq : ℝ) = 2988 / 473 := by norm_num [Cq, Dq, h2q, h3q]
private lemma Lq_eq : (Lq : ℝ) = 344449 / 236500 := by norm_num [Lq, Cq, Dq, h2q, h3q]
private lemma βq_eq : (βq : ℝ) = 473 / 1021 := by norm_num [βq, h2q, h3q]
private lemma a0q_eq : (a0q : ℝ) = 29 / 100 := by norm_num [a0q]
private lemma aq_eq : (aq : ℝ) = 11 / 60 := by norm_num [aq]
private lemma κq_eq : (κq : ℝ) = κ₀ := by norm_num [κq, κ₀]
private lemma gramq_eq : (gramq : ℝ) = M₀ := by norm_num [gramq, M₀]

/-! ### The edge parametrization -/

private lemma good_real {e : Edge} (he : e.Good) :
    0 < (e.xh : ℝ) - e.xl ∧ 0 < (e.yh : ℝ) - e.yl ∧ 0 < (e.yl : ℝ) ∧ 0 ≤ (e.xl : ℝ) ∧
      (e.xl : ℝ) ≤ e.yl ∧ (e.xh : ℝ) ≤ e.yh ∧
      0 < (e.yl : ℝ) * (e.xh - e.xl) - e.xl * (e.yh - e.yl) := by
  have h1 : e.xh - e.xl = e.width := by simp only [Edge.xl]; ring
  have h2 : e.yh - e.yl = e.m * e.width := by simp only [Edge.yl]; ring
  have h3 : e.yl * (e.xh - e.xl) - e.xl * (e.yh - e.yl) = e.width * (e.yh - e.m * e.xh) := by
    simp only [Edge.xl, Edge.yl]; ring
  have q1 : 0 < e.xh - e.xl := by rw [h1]; exact he.width_pos
  have q2 : 0 < e.yh - e.yl := by rw [h2]; exact mul_pos he.m_pos he.width_pos
  have q3 : 0 < e.yl := lt_of_lt_of_le Yc_pos he.yl_ge
  have q4 : 0 < e.yl * (e.xh - e.xl) - e.xl * (e.yh - e.yl) := by
    rw [h3]; exact mul_pos he.width_pos he.intercept_pos
  refine ⟨by exact_mod_cast q1, by exact_mod_cast q2, by exact_mod_cast q3,
    by exact_mod_cast he.xl_nonneg, by exact_mod_cast he.yl_ge_xl, by exact_mod_cast he.yh_ge_xh,
    by exact_mod_cast q4⟩

private lemma edge_z_cast (e : Edge) (u : ℚ) : (e.z u : ℝ) =
    ((e.xl : ℝ) + ((e.xh : ℝ) - e.xl) * u) / ((e.yl : ℝ) + ((e.yh : ℝ) - e.yl) * u) := by
  simp only [Edge.z, Edge.X, Edge.Y]; push_cast; ring

private lemma edge_Y_cast (e : Edge) (u : ℚ) : (e.Y u : ℝ) =
    (e.yl : ℝ) + ((e.yh : ℝ) - e.yl) * u := by
  simp only [Edge.Y]; push_cast; ring

private lemma edge_Y_pos {e : Edge} (he : e.Good) {s : ℝ} (hs : 0 ≤ s) :
    0 < (e.yl : ℝ) + ((e.yh : ℝ) - e.yl) * s := by
  obtain ⟨-, h2, h3, -⟩ := good_real he
  positivity

private lemma edge_z_mono {e : Edge} (he : e.Good) {s s' : ℝ} (hs : 0 ≤ s) (hss : s ≤ s') :
    ((e.xl : ℝ) + ((e.xh : ℝ) - e.xl) * s) / ((e.yl : ℝ) + ((e.yh : ℝ) - e.yl) * s) ≤
      ((e.xl : ℝ) + ((e.xh : ℝ) - e.xl) * s') / ((e.yl : ℝ) + ((e.yh : ℝ) - e.yl) * s') := by
  obtain ⟨-, -, -, -, -, -, h7⟩ := good_real he
  rw [div_le_div_iff₀ (edge_Y_pos he hs) (edge_Y_pos he (hs.trans hss))]
  have key : ((e.xl : ℝ) + ((e.xh : ℝ) - e.xl) * s') * ((e.yl : ℝ) + ((e.yh : ℝ) - e.yl) * s) -
      ((e.xl : ℝ) + ((e.xh : ℝ) - e.xl) * s) * ((e.yl : ℝ) + ((e.yh : ℝ) - e.yl) * s') =
      (s' - s) * ((e.yl : ℝ) * (e.xh - e.xl) - e.xl * (e.yh - e.yl)) := by ring
  nlinarith [mul_nonneg (sub_nonneg.2 hss) h7.le]

private lemma edge_z_unit {e : Edge} (he : e.Good) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ ((e.xl : ℝ) + ((e.xh : ℝ) - e.xl) * s) / ((e.yl : ℝ) + ((e.yh : ℝ) - e.yl) * s) ∧
      ((e.xl : ℝ) + ((e.xh : ℝ) - e.xl) * s) / ((e.yl : ℝ) + ((e.yh : ℝ) - e.yl) * s) ≤ 1 := by
  obtain ⟨h1, -, -, h4, h5, h6, -⟩ := good_real he
  have hp := edge_Y_pos he hs
  refine ⟨div_nonneg (by positivity) hp.le, (div_le_one hp).2 ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left h5 (sub_nonneg.2 hs1), mul_le_mul_of_nonneg_left h6 hs]

/-- Bounds on `z = X/Y` and `Y` from the edge parametrization. -/
private lemma z_bounds {e : Edge} (he : e.Good) {w : Field} {u p v : ℝ}
    (hon : OnEdge e w u p v) {b : Box} (hul0 : (0 : ℚ) ≤ b.ul) (huh1 : b.uh ≤ 1)
    (hu1 : (b.ul : ℝ) ≤ u) (hu2 : u ≤ b.uh) :
    (e.z b.ul : ℝ) ≤ Xr w / Yr w ∧ Xr w / Yr w ≤ e.z b.uh ∧ 0 ≤ (e.z b.ul : ℝ) ∧
      (e.z b.uh : ℝ) ≤ 1 ∧ Yr w ≤ e.Y b.uh := by
  have hul0' : (0 : ℝ) ≤ b.ul := by exact_mod_cast hul0
  have huh1' : (b.uh : ℝ) ≤ 1 := by exact_mod_cast huh1
  have hu0 : 0 ≤ u := hul0'.trans hu1
  have hz : Xr w / Yr w = ((e.xl : ℝ) + ((e.xh : ℝ) - e.xl) * u) /
      ((e.yl : ℝ) + ((e.yh : ℝ) - e.yl) * u) := by rw [hon.hX, hon.hY]
  obtain ⟨-, h2, -⟩ := good_real he
  rw [hz, edge_z_cast, edge_z_cast, edge_Y_cast, hon.hY]
  refine ⟨edge_z_mono he hul0' hu1, edge_z_mono he hu0 hu2, (edge_z_unit he hul0' (hu1.trans
    (hu2.trans huh1'))).1, (edge_z_unit he (hu0.trans hu2) huh1').2, ?_⟩
  nlinarith

/-! ### The lower first-shell ratio -/

/-- `ρ_min(z) = [(h₂z − 1)/(h₂ − 1)]₊` over the reals. -/
private noncomputable def lowR (y : ℝ) : ℝ := max 0 ((1569 / 1000 * y - 1) / (1569 / 1000 - 1))

private lemma lowerQ_cast (y : ℚ) : (lowerQ y : ℝ) = lowR y := by
  simp only [lowerQ, lowR]; push_cast; rw [h2q_eq]

private lemma rho_cast (e : Edge) (u p : ℚ) :
    (e.ρ u p : ℝ) = (1 - (p : ℝ)) * lowR (e.z u) + p * e.z u := by
  simp only [Edge.ρ]; push_cast; rw [lowerQ_cast]

private lemma lowR_mono {y y' : ℝ} (h : y ≤ y') : lowR y ≤ lowR y' :=
  max_le_max le_rfl (div_le_div_of_nonneg_right (by linarith) (by norm_num))

private lemma lowR_le {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : lowR y ≤ y :=
  max_le h0 (by rw [div_le_iff₀ (by norm_num)]; linarith)

private lemma lowR_nonneg (y : ℝ) : 0 ≤ lowR y := le_max_left _ _

private lemma rho_bounds {z ρ p zl zh pl ph : ℝ} (hzl : zl ≤ z) (hzh : z ≤ zh) (hz1 : z ≤ 1)
    (hzl0 : 0 ≤ zl) (hzh1 : zh ≤ 1) (hpl : pl ≤ p) (hph : p ≤ ph) (hpl0 : 0 ≤ pl)
    (hph1 : ph ≤ 1) (hρ : ρ = (1 - p) * lowR z + p * z) :
    (1 - pl) * lowR zl + pl * zl ≤ ρ ∧ ρ ≤ (1 - ph) * lowR zh + ph * zh ∧
      0 ≤ (1 - pl) * lowR zl + pl * zl ∧ (1 - ph) * lowR zh + ph * zh ≤ 1 ∧
      lowR zl ≤ (1 - ph) * lowR zh + ph * zh ∧ ρ ≤ z := by
  have hz0 : 0 ≤ z := hzl0.trans hzl
  have a1 := lowR_mono hzl
  have a2 := lowR_mono hzh
  have a3 := lowR_le hz0 hz1
  have a4 := lowR_le (hz0.trans hzh) hzh1
  have a5 := lowR_nonneg zl
  have b1 : 0 ≤ 1 - pl := by linarith
  have b2 : 0 ≤ 1 - ph := by linarith
  have b3 : 0 ≤ ph := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left a1 b1, mul_le_mul_of_nonneg_left hzl hpl0,
      mul_nonneg (sub_nonneg.2 hpl) (sub_nonneg.2 a3)]
  · nlinarith [mul_le_mul_of_nonneg_left a2 b2, mul_le_mul_of_nonneg_left hzh b3,
      mul_nonneg (sub_nonneg.2 hph) (sub_nonneg.2 a3)]
  · positivity
  · nlinarith [mul_le_mul_of_nonneg_left a4 b2, mul_le_mul_of_nonneg_left hzh1 b3]
  · nlinarith [mul_le_mul_of_nonneg_left (a1.trans a2) b2, mul_le_mul_of_nonneg_left
      (a1.trans (a2.trans a4)) b3]
  · nlinarith [mul_le_mul_of_nonneg_left a3 (show 0 ≤ 1 - p by linarith)]

/-! ### The moment `t` -/

private lemma t_bounds {z ρ v zl zh rl rh vl vh : ℝ} (hzl : zl ≤ z) (hzh : z ≤ zh)
    (hz1 : z ≤ 1) (hzl0 : 0 ≤ zl) (hzh1 : zh ≤ 1) (hrl : rl ≤ ρ) (hrh : ρ ≤ rh)
    (hrh1 : rh ≤ 1) (hlow : lowR zl ≤ rh) (hvl : vl ≤ v) (hvh : v ≤ vh) (hvl0 : 0 ≤ vl)
    (hvh1 : vh ≤ 1) :
    0 ≤ vl * min zl (min (1 / (2 - rl)) (1 / (2988 / 473 - 1601949 / 236500 * zl +
        344449 / 236500 * rh))) ∧
      vl * min zl (min (1 / (2 - rl)) (1 / (2988 / 473 - 1601949 / 236500 * zl +
        344449 / 236500 * rh))) ≤
      v * min z (min (1 / (2 - ρ)) (1 / max 1 (2988 / 473 - 1601949 / 236500 * z +
        344449 / 236500 * ρ))) ∧
      v * min z (min (1 / (2 - ρ)) (1 / max 1 (2988 / 473 - 1601949 / 236500 * z +
        344449 / 236500 * ρ))) ≤
      vh * min zh (min (1 / (2 - rh)) (1 / max 1 (2988 / 473 - 1601949 / 236500 * zh +
        344449 / 236500 * rl))) ∧
      vh * min zh (min (1 / (2 - rh)) (1 / max 1 (2988 / 473 - 1601949 / 236500 * zh +
        344449 / 236500 * rl))) ≤ 1 := by
  have hz0 : 0 ≤ z := hzl0.trans hzl
  have hlow' : (1569 / 1000 * zl - 1) / (1569 / 1000 - 1) ≤ rh := (le_max_right _ _).trans hlow
  have hrh0 : 0 ≤ rh := (le_max_left _ _).trans hlow
  have hd : 1 ≤ 2988 / 473 - 1601949 / 236500 * zl + 344449 / 236500 * rh := by
    rcases le_total zl (1000 / 1569) with h | h
    · nlinarith
    · rw [div_le_iff₀ (by norm_num)] at hlow'
      nlinarith
  set T := min z (min (1 / (2 - ρ)) (1 / max 1 (2988 / 473 - 1601949 / 236500 * z +
    344449 / 236500 * ρ))) with hT
  set Tl := min zl (min (1 / (2 - rl)) (1 / (2988 / 473 - 1601949 / 236500 * zl +
    344449 / 236500 * rh))) with hTl
  set Th := min zh (min (1 / (2 - rh)) (1 / max 1 (2988 / 473 - 1601949 / 236500 * zh +
    344449 / 236500 * rl))) with hTh
  have hρ1 : ρ ≤ 1 := hrh.trans hrh1
  have hmax : (0 : ℝ) < max 1 (2988 / 473 - 1601949 / 236500 * z + 344449 / 236500 * ρ) :=
    lt_of_lt_of_le one_pos (le_max_left _ _)
  have hT0 : 0 ≤ T := le_min hz0 (le_min (by
    have : 0 < 2 - ρ := by linarith
    positivity) (by positivity))
  have hTl0 : 0 ≤ Tl := le_min hzl0 (le_min (by
    have : 0 < 2 - rl := by linarith
    positivity) (by
    have : (0 : ℝ) < 2988 / 473 - 1601949 / 236500 * zl + 344449 / 236500 * rh := by linarith
    positivity))
  have hTlT : Tl ≤ T := by
    refine le_min ((min_le_left _ _).trans hzl) (le_min ?_ ?_)
    · exact (min_le_right _ _).trans ((min_le_left _ _).trans
        (one_div_le_one_div_of_le (by linarith) (by linarith)))
    · rcases le_total (2988 / 473 - 1601949 / 236500 * z + 344449 / 236500 * ρ) 1 with h | h
      · rw [max_eq_left h, div_one]
        exact (min_le_left _ _).trans (hzl.trans hz1)
      · rw [max_eq_right h]
        exact (min_le_right _ _).trans ((min_le_right _ _).trans
          (one_div_le_one_div_of_le (by linarith) (by nlinarith)))
  have hTTh : T ≤ Th := by
    refine le_min ((min_le_left _ _).trans hzh) (le_min ?_ ?_)
    · exact (min_le_right _ _).trans ((min_le_left _ _).trans
        (one_div_le_one_div_of_le (by linarith) (by linarith)))
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans
        (one_div_le_one_div_of_le (lt_of_lt_of_le one_pos (le_max_left _ _))
          (max_le_max le_rfl (by nlinarith))))
  refine ⟨mul_nonneg hvl0 hTl0, mul_le_mul hvl hTlT hTl0 (hvl0.trans hvl),
    mul_le_mul hvh hTTh hT0 (hvl0.trans (hvl.trans hvh)), ?_⟩
  have : Th ≤ 1 := (min_le_left _ _).trans hzh1
  nlinarith [mul_le_mul_of_nonneg_left this (hvl0.trans (hvl.trans hvh))]

/-! ### The Lieb–Hölder deficit -/

/-- The certificate's lower bound for `D_LH`. -/
private def defiQ (rl tl th : ℚ) : ℚ :=
  if max (1 + (1 - 2 * rl) * tl) (1 + (1 - 2 * rl) * th) ≠ 0 then
    rl * (1 - th) ^ 2 / max (1 + (1 - 2 * rl) * tl) (1 + (1 - 2 * rl) * th) else 0

private lemma defiQ_le {rl tl th : ℚ} {ρ t : ℝ} (hrl0 : 0 ≤ (rl : ℝ)) (hrl : (rl : ℝ) ≤ ρ)
    (hρ1 : ρ ≤ 1) (htl : (tl : ℝ) ≤ t) (hth : t ≤ th) (hth1 : (th : ℝ) ≤ 1) (ht0 : 0 ≤ t) :
    (defiQ rl tl th : ℝ) ≤ DLH ρ t := by
  have hden0 : 0 ≤ 1 + (1 - 2 * ρ) * t := by
    nlinarith [mul_le_mul_of_nonneg_right (show 2 * ρ - 1 ≤ 1 by linarith) ht0]
  have hden_le : 1 + (1 - 2 * ρ) * t ≤
      max (1 + (1 - 2 * (rl : ℝ)) * tl) (1 + (1 - 2 * (rl : ℝ)) * th) := by
    have h0 : 1 + (1 - 2 * ρ) * t ≤ 1 + (1 - 2 * (rl : ℝ)) * t := by nlinarith
    rcases le_total (1 - 2 * (rl : ℝ)) 0 with h | h
    · exact h0.trans (le_max_of_le_left (by nlinarith))
    · exact h0.trans (le_max_of_le_right (by nlinarith))
  have hnum : (rl : ℝ) * (1 - th) ^ 2 ≤ ρ * (1 - t) ^ 2 := by
    have : (1 - (th : ℝ)) ^ 2 ≤ (1 - t) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    exact mul_le_mul hrl this (sq_nonneg _) (hrl0.trans hrl)
  unfold defiQ DLH
  split_ifs with h1 h2 h2
  · have ht1 : 1 ≤ t := by
      nlinarith [mul_le_mul_of_nonneg_right (show 2 * ρ - 1 ≤ 1 by linarith) ht0]
    have : (th : ℝ) = 1 := le_antisymm hth1 (ht1.trans hth)
    push_cast
    rw [this]; simp
  · have hpos : 0 < 1 + (1 - 2 * ρ) * t := lt_of_le_of_ne hden0 (Ne.symm h2)
    push_cast
    calc (rl : ℝ) * (1 - th) ^ 2 / max (1 + (1 - 2 * (rl : ℝ)) * tl)
          (1 + (1 - 2 * (rl : ℝ)) * th)
        ≤ (rl : ℝ) * (1 - th) ^ 2 / (1 + (1 - 2 * ρ) * t) :=
          div_le_div_of_nonneg_left (by positivity) hpos hden_le
      _ ≤ ρ * (1 - t) ^ 2 / (1 + (1 - 2 * ρ) * t) :=
          div_le_div_of_nonneg_right hnum hpos.le
  · simp
  · push_cast
    exact div_nonneg (mul_nonneg (hrl0.trans hrl) (sq_nonneg _)) hden0

/-! ### The function `G` -/

/-- `G(m,w) = m/2 + m w/(2(w + 4am))` (with `x/0 = 0`). -/
private noncomputable def gR (m w : ℝ) : ℝ := m / 2 + m * w / (2 * (w + 4 * (11 / 60) * m))

private lemma Gq_cast (m w : ℚ) : (Gq m w : ℝ) = gR m w := by
  unfold Gq gR
  split_ifs with h
  · push_cast; rw [aq_eq]
  · rcases not_and_or.1 h with h | h <;> simp only [not_not] at h <;> simp [h]

private lemma Gfun_eq (m w : ℝ) : Gfun m w = gR m w := by
  unfold Gfun gR aC
  split_ifs with h
  · simp [h]
  · rw [mul_comm 2 (w + 4 * (11 / 60) * m), ← div_div]; ring

private lemma gR_mono {m w m' w' : ℝ} (hm : 0 ≤ m) (hmm : m ≤ m') (hw : 0 ≤ w)
    (hww : w ≤ w') : gR m w ≤ gR m' w' := by
  unfold gR
  have hm' : 0 ≤ m' := hm.trans hmm
  have hw' : 0 ≤ w' := hw.trans hww
  have key : m * w / (2 * (w + 4 * (11 / 60) * m)) ≤
      m' * w' / (2 * (w' + 4 * (11 / 60) * m')) := by
    rcases hm.lt_or_eq with hm0 | hm0
    · rcases hw.lt_or_eq with hw0 | hw0
      · rw [div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith [mul_le_mul_of_nonneg_right hmm (mul_nonneg hw hw'),
          mul_le_mul_of_nonneg_left hww (mul_nonneg hm hm'), mul_nonneg hm hw]
      · rw [← hw0]; simp only [mul_zero, zero_div]; positivity
    · rw [← hm0]; simp only [zero_mul, zero_div]; positivity
  linarith

/-! ### The kinetic bound -/

private lemma kin_bound {X Y Z x J z ρ t zh rl Rh th : ℝ} (hZ : 0 < Z) (hY : Y = t * Z)
    (hx : x = ρ * t * Z) (hX : X = z * t * Z) (k1 : J ≤ Y / (29 / 100))
    (k2 : J ≤ x + (Z - x) / (1569 / 1000)) (k3 : J ≤ x + (Y - x) / (29 / 100))
    (k4 : J ≤ x + (Z - x) / (1021 / 500) + 473 / 1021 * (X - x)) (ht0 : 0 ≤ t)
    (hth : t ≤ th) (hr : ρ * t ≤ Rh) (hrl : rl ≤ ρ) (hρ1 : ρ ≤ 1) (hρz : ρ ≤ z) (hzh : z ≤ zh) :
    J ≤ min (th / (29 / 100)) (min (Rh + (1 - Rh) / (1569 / 1000))
      (min (th * (rl + (1 - rl) / (29 / 100)))
        (Rh + (1 - Rh) / (1021 / 500) + 473 / 1021 * th * (zh - rl)))) * Z := by
  subst hY hx hX
  rw [min_mul_of_nonneg _ _ hZ.le, min_mul_of_nonneg _ _ hZ.le, min_mul_of_nonneg _ _ hZ.le]
  have hrZ := mul_le_mul_of_nonneg_right hr hZ.le
  have htZ := mul_le_mul_of_nonneg_right hth hZ.le
  refine le_min ?_ (le_min ?_ (le_min ?_ ?_))
  · linarith
  · linarith
  · have hf : 0 ≤ rl + (1 - rl) / (29 / 100) := by linarith
    have e1 := mul_le_mul_of_nonneg_left hrl (mul_nonneg ht0 hZ.le)
    have e2 := mul_le_mul_of_nonneg_right htZ hf
    nlinarith
  · have e1 : t * (z - ρ) ≤ th * (zh - rl) :=
      mul_le_mul hth (by linarith) (by linarith) (ht0.trans hth)
    have e2 := mul_le_mul_of_nonneg_right e1 hZ.le
    nlinarith

/-! ### The constant `c₁` -/

private lemma c1_le : c1 ≤ (c1q : ℝ) := by
  have h : c1 = (569 / 1000) * Real.sqrt ((3 * (1569 / 1000))⁻¹) := by
    rw [c1, hmet_two, Real.sqrt_inv]; ring
  rw [h, c1q]
  push_cast
  rw [h2q_eq]
  refine mul_le_mul (by norm_num) (sqrt_le_usqrt' ?_) (Real.sqrt_nonneg _) (by norm_num)
  push_cast; rw [h2q_eq]; norm_num

private lemma c1_nonneg : 0 ≤ c1 := by
  unfold c1; rw [hmet_two]; positivity

/-! ### The corner values of `gap` -/

private def zL (e : Edge) (b : Box) : ℚ := e.z b.ul
private def zH (e : Edge) (b : Box) : ℚ := e.z b.uh
private def rL (e : Edge) (b : Box) : ℚ := e.ρ b.ul b.pl
private def rH (e : Edge) (b : Box) : ℚ := e.ρ b.uh b.ph
private def tL (e : Edge) (b : Box) : ℚ :=
  b.vl * min (zL e b) (min (1 / (2 - rL e b)) (1 / (Cq - Dq * zL e b + Lq * rH e b)))
private def tH (e : Edge) (b : Box) : ℚ :=
  b.vh * min (zH e b) (min (1 / (2 - rH e b)) (1 / max 1 (Cq - Dq * zH e b + Lq * rL e b)))
private def RL (e : Edge) (b : Box) : ℚ := rL e b * tL e b
private def RH (e : Edge) (b : Box) : ℚ := rH e b * tH e b
private def resQ (e : Edge) (b : Box) : ℚ :=
  Gq (1 - RL e b ^ 2) (max 0 (1 - RL e b * rL e b - defiQ (rL e b) (tL e b) (tH e b)))
private def llhQ (e : Edge) (b : Box) : ℚ :=
  c1q * RH e b * usqrt (min (1 - rL e b) (h2q * (zH e b - rL e b)))
private def cubQ (e : Edge) (b : Box) : ℚ :=
  min κq (llhQ e b + usqrt (gramq * (1 + aq) * resQ e b))
private def kinQ (e : Edge) (b : Box) : ℚ :=
  min (tH e b / a0q) (min (RH e b + (1 - RH e b) / h2q)
    (min (tH e b * (rL e b + (1 - rL e b) / a0q))
      (RH e b + (1 - RH e b) / h3q + βq * tH e b * (zH e b - rL e b))))

private lemma gap_eq (e : Edge) (b : Box) :
    gap e b = 1 - e.m * kinQ e b - sq * usqrt (e.Y b.uh) * cubQ e b := rfl

/-! ### Assembly -/

/-- The directed corner bounds for a field in a box. -/
private structure Corner (e : Edge) (b : Box) (w : Field) : Prop where
  Ypos : 0 < Yr w
  Zpos : 0 < Zr w
  zl_le : (zL e b : ℝ) ≤ Xr w / Yr w
  le_zh : Xr w / Yr w ≤ zH e b
  zl0 : 0 ≤ (zL e b : ℝ)
  zh1 : (zH e b : ℝ) ≤ 1
  Y_le : Yr w ≤ e.Y b.uh
  rl_le : (rL e b : ℝ) ≤ ρw w
  le_rh : ρw w ≤ rH e b
  rl0 : 0 ≤ (rL e b : ℝ)
  rh1 : (rH e b : ℝ) ≤ 1
  ρz : ρw w ≤ Xr w / Yr w
  tl_le : (tL e b : ℝ) ≤ tYZ w
  le_th : tYZ w ≤ tH e b
  tl0 : 0 ≤ (tL e b : ℝ)
  th1 : (tH e b : ℝ) ≤ 1

private lemma corner {e : Edge} (he : e.Good) {w : Field} (hw : Adm 2 w) (hne : w ≠ 0)
    {u p v : ℝ} (hon : OnEdge e w u p v) {b : Box}
    (hb0 : (0 : ℚ) ≤ b.ul ∧ b.uh ≤ 1 ∧ 0 ≤ b.pl ∧ b.ph ≤ 1 ∧ 0 ≤ b.vl ∧ b.vh ≤ 1)
    (hmem : b.mem u p v) : Corner e b w := by
  obtain ⟨hul0, huh1, hpl0, hph1, hvl0, hvh1⟩ := hb0
  obtain ⟨⟨hu1, hu2⟩, ⟨hp1, hp2⟩, ⟨hv1, hv2⟩⟩ := hmem
  have hY := Yr_pos_of_ne hw hne
  obtain ⟨hzl, hzh, hzl0, hzh1, hYY⟩ := z_bounds he hon hul0 huh1 hu1 hu2
  change (zL e b : ℝ) ≤ Xr w / Yr w at hzl
  change Xr w / Yr w ≤ (zH e b : ℝ) at hzh
  change 0 ≤ (zL e b : ℝ) at hzl0
  change (zH e b : ℝ) ≤ 1 at hzh1
  have hz1 : Xr w / Yr w ≤ 1 := (div_le_one hY).2 (Xr_le_Yr hw)
  have hρ := hon.hρ
  rw [h2q_eq] at hρ
  have hpl0' : (0 : ℝ) ≤ b.pl := by exact_mod_cast hpl0
  have hph1' : (b.ph : ℝ) ≤ 1 := by exact_mod_cast hph1
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := rho_bounds hzl hzh hz1 hzl0 hzh1 hp1 hp2 hpl0' hph1' hρ
  have hrL : (rL e b : ℝ) = (1 - (b.pl : ℝ)) * lowR (zL e b) + b.pl * (zL e b : ℝ) :=
    rho_cast e b.ul b.pl
  have hrH : (rH e b : ℝ) = (1 - (b.ph : ℝ)) * lowR (zH e b) + b.ph * (zH e b : ℝ) :=
    rho_cast e b.uh b.ph
  rw [← hrL] at r1 r3
  rw [← hrH] at r2 r4 r5
  have ht := hon.ht
  rw [Cq_eq, Dq_eq, Lq_eq] at ht
  have hvl0' : (0 : ℝ) ≤ b.vl := by exact_mod_cast hvl0
  have hvh1' : (b.vh : ℝ) ≤ 1 := by exact_mod_cast hvh1
  obtain ⟨t1, t2, t3, t4⟩ := t_bounds hzl hzh hz1 hzl0 hzh1 r1 r2 r4 r5 hv1 hv2 hvl0' hvh1'
  have htL : (tL e b : ℝ) = b.vl * min (zL e b : ℝ) (min (1 / (2 - (rL e b : ℝ)))
      (1 / (2988 / 473 - 1601949 / 236500 * (zL e b : ℝ) + 344449 / 236500 * (rH e b : ℝ)))) := by
    simp only [tL]; push_cast; rw [Cq_eq, Dq_eq, Lq_eq]
  have htH : (tH e b : ℝ) = b.vh * min (zH e b : ℝ) (min (1 / (2 - (rH e b : ℝ)))
      (1 / max 1 (2988 / 473 - 1601949 / 236500 * (zH e b : ℝ) +
        344449 / 236500 * (rL e b : ℝ)))) := by
    simp only [tH]; push_cast; rw [Cq_eq, Dq_eq, Lq_eq]
  rw [← ht, ← htL] at t2
  rw [← ht, ← htH] at t3
  rw [← htL] at t1
  rw [← htH] at t4
  exact ⟨hY, Zr_pos_of_ne hw hne, hzl, hzh, hzl0, hzh1, hYY, r1, r2, r3, r4, r6, t2, t3, t1, t4⟩

private lemma ratios_nonneg {w : Field} (hw : Adm 2 w) (hne : w ≠ 0) :
    0 ≤ ρw w ∧ 0 ≤ tYZ w ∧ tYZ w ≤ 1 ∧ 0 ≤ qw w ∧ qw w ≤ 1 - ρw w ∧
      qw w ≤ 1569 / 1000 * (Xr w / Yr w - ρw w) := by
  have hY := Yr_pos_of_ne hw hne
  have hZ := Zr_pos_of_ne hw hne
  have h1 := Y2r_le_Yr_sub hw
  have h2 := Y2r_le_h2_X hw
  rw [hmet_two] at h2
  have h3 : 0 ≤ Y2r w := by
    unfold Y2r; rw [hmet_two]; exact mul_nonneg (by norm_num) (m2_nonneg hw)
  refine ⟨div_nonneg (x1_nonneg hw) hY.le, div_nonneg hY.le hZ.le,
    (div_le_one hZ).2 (Yr_le_Zr hw), div_nonneg h3 hY.le, ?_, ?_⟩
  · unfold qw ρw
    rw [div_le_iff₀ hY, sub_mul, div_mul_cancel₀ _ hY.ne', one_mul]; exact h1
  · unfold qw ρw
    rw [div_le_iff₀ hY, ← sub_div, mul_div_assoc', div_mul_cancel₀ _ hY.ne']; exact h2

private lemma cub_bound {e : Edge} {b : Box} {w : Field} (hw : Adm 2 w) (hne : w ≠ 0)
    (c : Corner e b w) :
    Ccond (ρw w) (tYZ w) (qw w) ≤ cubQ e b ∧ 0 ≤ (cubQ e b : ℝ) := by
  obtain ⟨hρ0, ht0, ht1, hq0, hq1, hq2⟩ := ratios_nonneg hw hne
  have hρ1 : ρw w ≤ 1 := c.le_rh.trans c.rh1
  have hr0 : 0 ≤ ρw w * tYZ w := mul_nonneg hρ0 ht0
  have hRL : (RL e b : ℝ) = rL e b * tL e b := by simp only [RL]; push_cast; ring
  have hRH : (RH e b : ℝ) = rH e b * tH e b := by simp only [RH]; push_cast; ring
  have hRLr : (RL e b : ℝ) ≤ ρw w * tYZ w := by
    rw [hRL]; exact mul_le_mul c.rl_le c.tl_le c.tl0 hρ0
  have hRLₒ : 0 ≤ (RL e b : ℝ) := by rw [hRL]; exact mul_nonneg c.rl0 c.tl0
  have hrRH : ρw w * tYZ w ≤ RH e b := by
    rw [hRH]; exact mul_le_mul c.le_rh c.le_th ht0 (hρ0.trans c.le_rh)
  have hr1 : ρw w * tYZ w ≤ 1 := by nlinarith
  -- the LLH term
  have hc1q : 0 ≤ (c1q : ℝ) := c1_nonneg.trans c1_le
  have hllh : c1 * (ρw w * tYZ w) * Real.sqrt (qw w) ≤ llhQ e b := by
    have hq : qw w ≤ ((min (1 - rL e b) (h2q * (zH e b - rL e b)) : ℚ) : ℝ) := by
      push_cast; rw [h2q_eq]
      refine le_min (by linarith [c.rl_le]) (hq2.trans ?_)
      have := c.le_zh; have := c.rl_le
      nlinarith
    simp only [llhQ]; push_cast
    exact mul_le_mul (mul_le_mul c1_le hrRH hr0 hc1q) (sqrt_le_usqrt' hq) (Real.sqrt_nonneg _)
      (mul_nonneg hc1q (hr0.trans hrRH))
  -- the residual term
  have hres : (resQ e b : ℝ) = gR (1 - (RL e b : ℝ) ^ 2)
      (max 0 (1 - (RL e b : ℝ) * rL e b - defiQ (rL e b) (tL e b) (tH e b))) := by
    simp only [resQ]; rw [Gq_cast]; push_cast; rfl
  have hdef := defiQ_le c.rl0 c.rl_le hρ1 c.tl_le c.le_th c.th1 ht0
  have hG : Gfun (1 - (ρw w * tYZ w) ^ 2) (max 0 (1 - ρw w * tYZ w * ρw w - DLH (ρw w) (tYZ w)))
      ≤ resQ e b := by
    rw [hres, Gfun_eq]
    refine gR_mono (by nlinarith) (by nlinarith) (le_max_left _ _) (max_le_max le_rfl ?_)
    nlinarith [mul_le_mul hRLr c.rl_le c.rl0 hr0]
  have hsq : Real.sqrt (M₀ * (1 + aC) * Gfun (1 - (ρw w * tYZ w) ^ 2)
      (max 0 (1 - ρw w * tYZ w * ρw w - DLH (ρw w) (tYZ w)))) ≤
        (usqrt (gramq * (1 + aq) * resQ e b) : ℝ) := by
    refine sqrt_le_usqrt' ?_
    push_cast; rw [gramq_eq, aq_eq]
    exact mul_le_mul_of_nonneg_left hG (by unfold M₀ aC; norm_num)
  have hcub : (cubQ e b : ℝ) = min κ₀ ((llhQ e b : ℝ) + usqrt (gramq * (1 + aq) * resQ e b)) := by
    simp only [cubQ]; push_cast; rw [κq_eq]
  rw [hcub]
  refine ⟨min_le_min le_rfl (add_le_add hllh hsq), le_min (by unfold κ₀; norm_num) ?_⟩
  have := Real.sqrt_nonneg (qw w)
  have := mul_nonneg (mul_nonneg c1_nonneg hr0) this
  have := usqrt_nonneg (gramq * (1 + aq) * resQ e b)
  have : (0 : ℝ) ≤ (usqrt (gramq * (1 + aq) * resQ e b) : ℝ) := by exact_mod_cast this
  linarith

private lemma kin_le {e : Edge} {b : Box} {w : Field} (hw : Adm 2 w) (hne : w ≠ 0)
    (c : Corner e b w) : J1r w ≤ (kinQ e b : ℝ) * Zr w := by
  obtain ⟨hρ0, ht0, ht1, -⟩ := ratios_nonneg hw hne
  have hY := c.Ypos
  have hZ := c.Zpos
  have hRH : (RH e b : ℝ) = rH e b * tH e b := by simp only [RH]; push_cast; ring
  have hrRH : ρw w * tYZ w ≤ RH e b := by
    rw [hRH]; exact mul_le_mul c.le_rh c.le_th ht0 (hρ0.trans c.le_rh)
  have hkin : (kinQ e b : ℝ) = min ((tH e b : ℝ) / (29 / 100))
      (min ((RH e b : ℝ) + (1 - RH e b) / (1569 / 1000))
        (min ((tH e b : ℝ) * (rL e b + (1 - rL e b) / (29 / 100)))
          ((RH e b : ℝ) + (1 - RH e b) / (1021 / 500) +
            473 / 1021 * tH e b * (zH e b - rL e b)))) := by
    simp only [kinQ]; push_cast; rw [a0q_eq, h2q_eq, h3q_eq, βq_eq]
  rw [hkin]
  have k2 := J1r_le_k2 hw
  have k4 := J1r_le_k4 hw
  rw [hmet_two] at k2
  rw [hmet_three] at k4
  refine kin_bound hZ ?_ ?_ ?_ (J1r_le_k1 hw) k2 (J1r_le_k3 hw) k4 ht0 c.le_th hrRH c.rl_le
    (c.le_rh.trans c.rh1) c.ρz c.le_zh
  · unfold tYZ; field_simp
  · unfold tYZ ρw; field_simp
  · unfold tYZ; field_simp

/-- **Box soundness.** -/
theorem box_sound {e : Edge} (he : e.Good) {w : Field} (hw : Adm 2 w) (hne : w ≠ 0)
    (hcond : |cubic w| ≤ Ccond (ρw w) (tYZ w) (qw w) * Real.sqrt (Yr w) * Zr w)
    {u p v : ℝ} (hon : OnEdge e w u p v) {b : Box}
    (hb0 : (0 : ℚ) ≤ b.ul ∧ b.uh ≤ 1 ∧ 0 ≤ b.pl ∧ b.ph ≤ 1 ∧ 0 ≤ b.vl ∧ b.vh ≤ 1)
    (hmem : b.mem u p v) :
    (gap e b : ℝ) * Zr w ≤ Zr w - (e.m : ℝ) * J1r w - (sq : ℝ) * |cubic w| := by
  have c := corner he hw hne hon hb0 hmem
  obtain ⟨hC, hC0⟩ := cub_bound hw hne c
  have hJ := kin_le hw hne c
  have hU : Real.sqrt (Yr w) ≤ (usqrt (e.Y b.uh) : ℝ) := sqrt_le_usqrt' c.Y_le
  have hc : |cubic w| ≤ (cubQ e b : ℝ) * usqrt (e.Y b.uh) * Zr w :=
    hcond.trans (mul_le_mul_of_nonneg_right (mul_le_mul hC hU (Real.sqrt_nonneg _) hC0)
      c.Zpos.le)
  have hm0 : (0 : ℝ) ≤ e.m := by exact_mod_cast he.m_pos.le
  have hs0 : (0 : ℝ) ≤ sq := by norm_num [sq]
  rw [gap_eq]
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hJ hm0, mul_le_mul_of_nonneg_left hc hs0]

/-- The sub-box relation. -/
private def SubBox (b' b : Box) : Prop :=
  b'.ul ≥ b.ul ∧ b'.uh ≤ b.uh ∧ b'.pl ≥ b.pl ∧ b'.ph ≤ b.ph ∧ b'.vl ≥ b.vl ∧ b'.vh ≤ b.vh

private lemma subBox_trans {b'' b' b : Box} (h1 : SubBox b'' b') (h2 : SubBox b' b) :
    SubBox b'' b := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h1
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := h2
  exact ⟨le_trans c1 a1, le_trans a2 c2, le_trans c3 a3, le_trans a4 c4, le_trans c5 a5,
    le_trans a6 c6⟩

private lemma split_cover {b : Box} {u p v : ℝ} (hmem : b.mem u p v) :
    ((split b).1.mem u p v ∧ SubBox (split b).1 b) ∨
      ((split b).2.mem u p v ∧ SubBox (split b).2 b) := by
  obtain ⟨⟨hu1, hu2⟩, ⟨hp1, hp2⟩, ⟨hv1, hv2⟩⟩ := hmem
  have hu : b.ul ≤ b.uh := by exact_mod_cast hu1.trans hu2
  have hp : b.pl ≤ b.ph := by exact_mod_cast hp1.trans hp2
  have hv : b.vl ≤ b.vh := by exact_mod_cast hv1.trans hv2
  unfold split
  dsimp only
  split_ifs
  · rcases le_total u (((b.ul + b.uh) / 2 : ℚ) : ℝ) with h | h
    · left
      refine ⟨⟨⟨hu1, h⟩, ⟨hp1, hp2⟩, ⟨hv1, hv2⟩⟩, ?_⟩
      refine ⟨le_rfl, ?_, le_rfl, le_rfl, le_rfl, le_rfl⟩
      show (b.ul + b.uh) / 2 ≤ b.uh; linarith
    · right
      refine ⟨⟨⟨h, hu2⟩, ⟨hp1, hp2⟩, ⟨hv1, hv2⟩⟩, ?_⟩
      refine ⟨?_, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
      show b.ul ≤ (b.ul + b.uh) / 2; linarith
  · rcases le_total p (((b.pl + b.ph) / 2 : ℚ) : ℝ) with h | h
    · left
      refine ⟨⟨⟨hu1, hu2⟩, ⟨hp1, h⟩, ⟨hv1, hv2⟩⟩, ?_⟩
      refine ⟨le_rfl, le_rfl, le_rfl, ?_, le_rfl, le_rfl⟩
      show (b.pl + b.ph) / 2 ≤ b.ph; linarith
    · right
      refine ⟨⟨⟨hu1, hu2⟩, ⟨h, hp2⟩, ⟨hv1, hv2⟩⟩, ?_⟩
      refine ⟨le_rfl, le_rfl, ?_, le_rfl, le_rfl, le_rfl⟩
      show b.pl ≤ (b.pl + b.ph) / 2; linarith
  · rcases le_total v (((b.vl + b.vh) / 2 : ℚ) : ℝ) with h | h
    · left
      refine ⟨⟨⟨hu1, hu2⟩, ⟨hp1, hp2⟩, ⟨hv1, h⟩⟩, ?_⟩
      refine ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, ?_⟩
      show (b.vl + b.vh) / 2 ≤ b.vh; linarith
    · right
      refine ⟨⟨⟨hu1, hu2⟩, ⟨hp1, hp2⟩, ⟨h, hv2⟩⟩, ?_⟩
      refine ⟨le_rfl, le_rfl, le_rfl, le_rfl, ?_, le_rfl⟩
      show b.vl ≤ (b.vl + b.vh) / 2; linarith

/-- **Checker soundness.** An accepted tree below `b` covers `b` by accepted boxes. -/
theorem check_sound {e : Edge} {n : ℕ} {b : Box} (h : check e n b = true) {u p v : ℝ}
    (hmem : b.mem u p v) :
    ∃ b' : Box, b'.mem u p v ∧ (b'.ul ≥ b.ul ∧ b'.uh ≤ b.uh ∧ b'.pl ≥ b.pl ∧ b'.ph ≤ b.ph ∧
      b'.vl ≥ b.vl ∧ b'.vh ≤ b.vh) ∧ εq < gap e b' := by
  induction n generalizing b with
  | zero =>
    exact ⟨b, hmem, ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩,
      by simpa [check, accept] using h⟩
  | succ n ih =>
    simp only [check, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · exact ⟨b, hmem, ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩, by simpa [accept] using h⟩
    · rcases split_cover hmem with ⟨hm, hs⟩ | ⟨hm, hs⟩
      · obtain ⟨b', hb', hsub, hg⟩ := ih h1 hm
        exact ⟨b', hb', subBox_trans hsub hs, hg⟩
      · obtain ⟨b', hb', hsub, hg⟩ := ih h2 hm
        exact ⟨b', hb', subBox_trans hsub hs, hg⟩

private theorem kX_pos : ∀ i ≤ 41, 0 < kX i := by
  decide +kernel

private lemma t_le_T {w : Field} (hw : Adm 2 w) (hne : w ≠ 0) (hXpos : 0 < Xr w) :
    0 < min (Xr w / Yr w) (min (1 / (2 - ρw w))
      (1 / max 1 ((Cq : ℝ) - Dq * (Xr w / Yr w) + Lq * ρw w))) ∧
    tYZ w ≤ min (Xr w / Yr w) (min (1 / (2 - ρw w))
      (1 / max 1 ((Cq : ℝ) - Dq * (Xr w / Yr w) + Lq * ρw w))) := by
  have hY := Yr_pos_of_ne hw hne
  have hZ := Zr_pos_of_ne hw hne
  have hz1 : Xr w / Yr w ≤ 1 := (div_le_one hY).2 (Xr_le_Yr hw)
  have hρz : ρw w ≤ Xr w / Yr w := div_le_div_of_nonneg_right (x1_le_Xr hw) hY.le
  have h2ρ : 0 < 2 - ρw w := by linarith
  have hmax : (0 : ℝ) < max 1 ((Cq : ℝ) - Dq * (Xr w / Yr w) + Lq * ρw w) :=
    lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨lt_min (div_pos hXpos hY) (lt_min (by positivity) (by positivity)), ?_⟩
  refine le_min ?_ (le_min ?_ ?_)
  · unfold tYZ
    rw [div_le_div_iff₀ hZ hY]
    nlinarith [Yr_sq_le hw]
  · rw [le_div_iff₀ h2ρ]
    have e : tYZ w * (2 - ρw w) = (2 * Yr w - x1 w) / Zr w := by
      unfold tYZ ρw; field_simp
    rw [e, div_le_one hZ]; exact Zr_ge_two_Y hw
  · rw [le_div_iff₀ hmax, mul_max_of_nonneg _ _ (show 0 ≤ tYZ w from div_nonneg hY.le hZ.le)]
    refine max_le ?_ ?_
    · rw [mul_one]; exact (div_le_one hZ).2 (Yr_le_Zr hw)
    · have e : tYZ w * ((Cq : ℝ) - Dq * (Xr w / Yr w) + Lq * ρw w) =
          (2988 / 473 * Yr w - 1601949 / 236500 * Xr w + 344449 / 236500 * x1 w) / Zr w := by
        rw [Cq_eq, Dq_eq, Lq_eq]; unfold tYZ ρw; field_simp
      rw [e, div_le_one hZ]; exact Zr_ge_line hw

/-- Every nonzero admissible field on the closed edge `i` has parameters in the root box. -/
theorem exists_params {i : ℕ} (hi : i < 41) {w : Field} (hw : Adm 2 w) (hne : w ≠ 0)
    (hX : Xr w ∈ Icc (kX (i + 1) : ℝ) (kX i)) (hY : Yr w = piece i (Xr w)) :
    ∃ u p v : ℝ, OnEdge (edgeOf i) w u p v := by
  have hY0 := Yr_pos_of_ne hw hne
  have hxl : ((edgeOf i).xl : ℝ) = kX (i + 1) := by rw [edgeOf_xl]
  have hyl : ((edgeOf i).yl : ℝ) = kY (i + 1) := by rw [edgeOf_yl hi]
  have hxh : ((edgeOf i).xh : ℝ) = kX i := rfl
  have hyh : ((edgeOf i).yh : ℝ) = kY i := rfl
  have hW : (kX (i + 1) : ℝ) < kX i := by exact_mod_cast kX_anti i hi
  have hst : (kY (i + 1) : ℝ) = kY i - slope i * (kX i - kX (i + 1)) := by
    exact_mod_cast knot_step i hi
  have hXpos : 0 < Xr w := lt_of_lt_of_le (by exact_mod_cast kX_pos (i + 1) hi) hX.1
  have hz0 : 0 < Xr w / Yr w := div_pos hXpos hY0
  have hz1 : Xr w / Yr w ≤ 1 := (div_le_one hY0).2 (Xr_le_Yr hw)
  have hρ0 : 0 ≤ ρw w := div_nonneg (x1_nonneg hw) hY0.le
  have hρz : ρw w ≤ Xr w / Yr w := div_le_div_of_nonneg_right (x1_le_Xr hw) hY0.le
  have hLρ : max 0 (((h2q : ℝ) * (Xr w / Yr w) - 1) / ((h2q : ℝ) - 1)) ≤ ρw w := by
    refine max_le hρ0 ?_
    rw [h2q_eq, div_le_iff₀ (by norm_num)]
    have h := Yr_ge_shell hw
    rw [hmet_two] at h
    have e1 : (1569 / 1000 * (Xr w / Yr w) - 1) * Yr w = 1569 / 1000 * Xr w - Yr w := by
      field_simp
    have e2 : ρw w * (1569 / 1000 - 1) * Yr w = 569 / 1000 * x1 w := by
      unfold ρw; field_simp; ring
    refine le_of_mul_le_mul_right ?_ hY0
    rw [e1, e2]; linarith
  obtain ⟨hT0, htT⟩ := t_le_T hw hne hXpos
  refine ⟨(Xr w - kX (i + 1)) / (kX i - kX (i + 1)),
    if Xr w / Yr w = max 0 (((h2q : ℝ) * (Xr w / Yr w) - 1) / ((h2q : ℝ) - 1)) then 0 else
      (ρw w - max 0 (((h2q : ℝ) * (Xr w / Yr w) - 1) / ((h2q : ℝ) - 1))) /
        (Xr w / Yr w - max 0 (((h2q : ℝ) * (Xr w / Yr w) - 1) / ((h2q : ℝ) - 1))),
    tYZ w / min (Xr w / Yr w) (min (1 / (2 - ρw w))
      (1 / max 1 ((Cq : ℝ) - Dq * (Xr w / Yr w) + Lq * ρw w))), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact ⟨div_nonneg (by linarith [hX.1]) (by linarith),
      (div_le_one (by linarith)).2 (by linarith [hX.2])⟩
  · split_ifs with h
    · exact ⟨le_rfl, zero_le_one⟩
    · have hpos : 0 < Xr w / Yr w - max 0 (((h2q : ℝ) * (Xr w / Yr w) - 1) / ((h2q : ℝ) - 1)) :=
        lt_of_le_of_ne (by linarith) (fun h' => h (by linarith))
      exact ⟨div_nonneg (by linarith) hpos.le, (div_le_one hpos).2 (by linarith)⟩
  · exact ⟨div_nonneg (div_nonneg hY0.le (Zr_pos_of_ne hw hne).le) hT0.le,
      (div_le_one hT0).2 htT⟩
  · rw [hxl, hxh]; field_simp; ring
  · rw [hyl, hyh, hY, piece, hst]; field_simp; ring
  · split_ifs with h
    · linarith
    · have hne' : Xr w / Yr w - max 0 (((h2q : ℝ) * (Xr w / Yr w) - 1) / ((h2q : ℝ) - 1)) ≠ 0 :=
        sub_ne_zero.2 h
      generalize max 0 (((h2q : ℝ) * (Xr w / Yr w) - 1) / ((h2q : ℝ) - 1)) = L at *
      generalize Xr w / Yr w = z at *
      field_simp
      ring
  · exact (div_mul_cancel₀ _ hT0.ne').symm

end Cert

end OVNS
