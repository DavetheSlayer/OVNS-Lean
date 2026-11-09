import OddViscousNS.Closed.Forced.RowConclusion
import OddViscousNS.Closed.Forced.Check.Rows
import OddViscousNS.Closed.Forced.Common.Final

/-!
# Theorem 1.3, forced branch: assembly of the seven rows

The six off-axis rows are the kernel-checked F662 certificates (`Forced/Check/Rows.lean`) through
`row_conclusion`.  The common row `(419650, 419650, 850)` (`k = .8393`, `f₀ = 1`,
`s = 419650/208013`) is `common_row_conclusion`, supplied by the moment-regime branch.  The anchor
`closed_regions_forced` takes the maximum of the seven bounds (`GlobalConclusion'.mono`).
-/

open scoped ENNReal
open MeasureTheory Set

namespace OVNS

namespace Forced

open Chk

theorem rowOK_F851 : RowOK kF851 f0F851 JF851 cellsF851 termF851 :=
  ⟨chainF851_ok, cellsF851_ok, termF851_ok, windowF851_ok⟩
theorem rowOK_F868 : RowOK kF868 f0F868 JF868 cellsF868 termF868 :=
  ⟨chainF868_ok, cellsF868_ok, termF868_ok, windowF868_ok⟩
theorem rowOK_F884 : RowOK kF884 f0F884 JF884 cellsF884 termF884 :=
  ⟨chainF884_ok, cellsF884_ok, termF884_ok, windowF884_ok⟩
theorem rowOK_F917 : RowOK kF917 f0F917 JF917 cellsF917 termF917 :=
  ⟨chainF917_ok, cellsF917_ok, termF917_ok, windowF917_ok⟩
theorem rowOK_F957 : RowOK kF957 f0F957 JF957 cellsF957 termF957 :=
  ⟨chainF957_ok, cellsF957_ok, termF957_ok, windowF957_ok⟩
theorem rowOK_F979 : RowOK kF979 f0F979 JF979 cellsF979 termF979 :=
  ⟨chainF979_ok, cellsF979_ok, termF979_ok, windowF979_ok⟩

/-- An F662 row from its certificate: `r = (500000 k, 500000 k f₀, J)`, `s = r.1/208013`. -/
theorem f662_row_conclusion {k f0 : ℚ} {J : ℕ} {cells : List Cell} {t : Term} {r : ℕ × ℕ × ℕ}
    (hr1 : ((r.1 : ℚ)) = 500000 * k) (hr2 : ((r.2.1 : ℚ)) = 500000 * k * f0) (hrJ : r.2.2 = J)
    (hk : 0 < k) (hf0 : f0 ≤ 1) (hR : RowOK k f0 J cells t) (hRB : RowBound fun _ => M₀) :
    ∃ Bd : ℝ, 0 ≤ Bd ∧ RowConcl r Bd := by
  set s : ℚ := (r.1 : ℚ) / 208013 with hs_def
  have hsR : (s : ℝ) = (r.1 : ℝ) / 208013 := by rw [hs_def]; push_cast; rfl
  have hs : 0 < s := by rw [hs_def, hr1]; positivity
  have hkR : (k : ℝ) = ((r.1 : ℚ) : ℝ) / 500000 := by rw [hr1]; push_cast; ring
  have hk' : (k : ℝ) = s * κ₀ := by
    rw [hsR, hkR, κ₀]; push_cast; ring
  have h2R : (r.2.1 : ℝ) = (r.1 : ℝ) * f0 := by
    have h : ((r.2.1 : ℕ) : ℚ) = (r.1 : ℚ) * f0 := by rw [hr2, hr1]
    exact_mod_cast h
  obtain ⟨Bd, hBd, hrow⟩ := row_conclusion hs hk' hf0 hR hRB
  refine ⟨Bd, hBd, fun ν α M F u₀ f hν hM hF hu₀ hf hu₀M hfF hMν hFν => ?_⟩
  have hMs : M / ν ≤ s := by rw [hsR, le_div_iff₀ (by norm_num)]; linarith
  have hFs : F / ν ^ 2 ≤ f0 * s := by
    rw [hsR, ← mul_div_assoc, mul_comm (f0 : ℝ), ← h2R, le_div_iff₀ (by norm_num)]; linarith
  obtain ⟨hg, hw⟩ := hrow ν α M F u₀ f hν hM hF hu₀ hf hu₀M hfF hMs hFs
  refine ⟨hg, fun u hu a b ha hab hb => ?_⟩
  rw [← hsR, hrJ]
  exact hw u hu a b ha hab hb

theorem closed_regions_forced_of_rows (hRB : RowBound gOVNS) : ∃ Bd : ℝ, 0 ≤ Bd ∧
    ∀ r ∈ forcedRows, ∀ (ν α M F : ℝ) (u₀ f : Field), 0 < ν → 0 ≤ M → 0 ≤ F →
      Adm 2 u₀ → Adm 2 f → hnorm 2 u₀ ≤ M → hnorm 2 f ≤ F →
      208013 * (M / ν) ≤ r.1 → 208013 * (F / ν ^ 2) ≤ r.2.1 →
      GlobalConclusion' ν α f u₀ Bd ∧
      ∀ u : ℝ → Field, IsStrongSolution ν α f u₀ u →
        ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ a + 1 →
          ∫⁻ τ in Icc a b, Zmet (scaled ν ((r.1 : ℝ) / 208013) u τ) ≤ r.2.2 := by
  have hRB' : RowBound fun _ => M₀ := hRB.mono gOVNS_le_M₀
  obtain ⟨B0, hB0, h0⟩ := common_row_conclusion hRB
  obtain ⟨B1, hB1, h1⟩ := f662_row_conclusion (r := (425500, 382950, 294))
    (by norm_num [kF851]) (by norm_num [kF851, f0F851]) (by rfl) (by norm_num [kF851])
    (by norm_num [f0F851]) rowOK_F851 hRB'
  obtain ⟨B2, hB2, h2⟩ := f662_row_conclusion (r := (434000, 347200, 468))
    (by norm_num [kF868]) (by norm_num [kF868, f0F868]) (by rfl) (by norm_num [kF868])
    (by norm_num [f0F868]) rowOK_F868 hRB'
  obtain ⟨B3, hB3, h3⟩ := f662_row_conclusion (r := (442000, 309400, 320))
    (by norm_num [kF884]) (by norm_num [kF884, f0F884]) (by rfl) (by norm_num [kF884])
    (by norm_num [f0F884]) rowOK_F884 hRB'
  obtain ⟨B4, hB4, h4⟩ := f662_row_conclusion (r := (458500, 229250, 808))
    (by norm_num [kF917]) (by norm_num [kF917, f0F917]) (by rfl) (by norm_num [kF917])
    (by norm_num [f0F917]) rowOK_F917 hRB'
  obtain ⟨B5, hB5, h5⟩ := f662_row_conclusion (r := (478500, 119625, 355))
    (by norm_num [kF957]) (by norm_num [kF957, f0F957]) (by rfl) (by norm_num [kF957])
    (by norm_num [f0F957]) rowOK_F957 hRB'
  obtain ⟨B6, hB6, h6⟩ := f662_row_conclusion (r := (489500, 48950, 124))
    (by norm_num [kF979]) (by norm_num [kF979, f0F979]) (by rfl) (by norm_num [kF979])
    (by norm_num [f0F979]) rowOK_F979 hRB'
  refine ⟨max B0 (max B1 (max B2 (max B3 (max B4 (max B5 B6))))), le_max_of_le_left hB0, ?_⟩
  intro r hr ν α M F u₀ f hν hM hF hu₀ hf hu₀M hfF hMν hFν
  simp only [forcedRows, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨hg, hw⟩ := h0 ν α M F u₀ f hν hM hF hu₀ hf hu₀M hfF hMν hFν
    exact ⟨GlobalConclusion'.mono hν (by simp) hg, hw⟩
  · obtain ⟨hg, hw⟩ := h1 ν α M F u₀ f hν hM hF hu₀ hf hu₀M hfF hMν hFν
    exact ⟨GlobalConclusion'.mono hν (by simp [le_max_iff]) hg, hw⟩
  · obtain ⟨hg, hw⟩ := h2 ν α M F u₀ f hν hM hF hu₀ hf hu₀M hfF hMν hFν
    exact ⟨GlobalConclusion'.mono hν (by simp [le_max_iff]) hg, hw⟩
  · obtain ⟨hg, hw⟩ := h3 ν α M F u₀ f hν hM hF hu₀ hf hu₀M hfF hMν hFν
    exact ⟨GlobalConclusion'.mono hν (by simp [le_max_iff]) hg, hw⟩
  · obtain ⟨hg, hw⟩ := h4 ν α M F u₀ f hν hM hF hu₀ hf hu₀M hfF hMν hFν
    exact ⟨GlobalConclusion'.mono hν (by simp [le_max_iff]) hg, hw⟩
  · obtain ⟨hg, hw⟩ := h5 ν α M F u₀ f hν hM hF hu₀ hf hu₀M hfF hMν hFν
    exact ⟨GlobalConclusion'.mono hν (by simp [le_max_iff]) hg, hw⟩
  · obtain ⟨hg, hw⟩ := h6 ν α M F u₀ f hν hM hF hu₀ hf hu₀M hfF hMν hFν
    exact ⟨GlobalConclusion'.mono hν (by simp [le_max_iff]) hg, hw⟩

end Forced

end OVNS
