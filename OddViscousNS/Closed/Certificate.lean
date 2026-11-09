import OddViscousNS.Closed.Plan
import OddViscousNS.Closed.Moments
import OddViscousNS.Closed.Cert.Sound
import OddViscousNS.Closed.Cert.Check
import OddViscousNS.Closed.Cond.CondCubic

/-!
# The edge certificate (U785)

For every edge `i` of the plan and every nonzero admissible normalized field `w` with
`(X(w), Y(w))` on the closed edge `i`,
`Z − m_i J₁ − s |⟨B(w,w),h(A)w⟩| ≥ 10⁻⁵ Z` (`s = 97/40`).
Proof: the field has parameters `(u,p,v)` in the root box (`exists_params`); the kernel-checked
tree (`check_all`) covers the root by accepted cells (`check_sound`); on an accepted cell the
directed bounds dominate the actual quantities (`box_sound`, with the conditional cubic bound
`cubic_le_cond`), so the heat is at least the cell's gap `> 10⁻⁵`.
-/

open Set

namespace OVNS

open Cert

theorem edge_heat (hRB : RowBound fun _ => M₀) {i : ℕ} (hi : i < 41) {w : Field} (hw : Adm 2 w)
    (hne : w ≠ 0) (hX : Xr w ∈ Icc (kX (i + 1) : ℝ) (kX i)) (hY : Yr w = piece i (Xr w)) :
    1 / 100000 * Zr w ≤ Zr w - (slope i : ℝ) * J1r w - 97 / 40 * |cubic w| := by
  obtain ⟨u, p, v, hon⟩ := exists_params hi hw hne hX hY
  have hmem : Box.root.mem u p v := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [Box.root] using hon.u01
    · simpa [Box.root] using hon.p01
    · simpa [Box.root] using hon.v01
  obtain ⟨b', hb'mem, hsub, hgap⟩ := check_sound (check_all i hi) hmem
  have hb0 : (0 : ℚ) ≤ b'.ul ∧ b'.uh ≤ 1 ∧ 0 ≤ b'.pl ∧ b'.ph ≤ 1 ∧ 0 ≤ b'.vl ∧ b'.vh ≤ 1 := by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hsub
    simp only [Box.root] at h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  have h := box_sound (edgeOf_good hi) hw hne (cubic_le_cond hRB hw) hon hb0 hb'mem
  have hZ : 0 ≤ Zr w := le_trans (Xr_nonneg hw) ((Xr_le_Yr hw).trans (Yr_le_Zr hw))
  have hε : (εq : ℝ) < (gap (edgeOf i) b' : ℝ) := by exact_mod_cast hgap
  have hε' : ((εq : ℚ) : ℝ) = 1 / 100000 := by norm_num [εq]
  have hs : ((Cert.sq : ℚ) : ℝ) = 97 / 40 := by norm_num [Cert.sq]
  have hm : ((edgeOf i).m : ℝ) = (slope i : ℝ) := rfl
  rw [hs, hm] at h
  calc 1 / 100000 * Zr w = (εq : ℝ) * Zr w := by rw [hε']
    _ ≤ (gap (edgeOf i) b' : ℝ) * Zr w := mul_le_mul_of_nonneg_right hε.le hZ
    _ ≤ _ := h

end OVNS
