import OddViscousNS.Quant.Joint.Metric.Bracket

/-!
# The third correction: its derivative off the source (nodes N8, N10)

`TIMED_METRIC_PROOF_V2.md` (8.7), (8.8), (9.6), (9.8).  `Fam3.rhs` is the source and five insertions:
two exterior fast slots and three slow slots.  Here is the size of these five, and of the value.

* `Q3_ext_half`: the exterior slots, one derivative on the direction: (9.6).
* `Q3_slots_le`: the three slow slots, in `‖v‖₁`, with `Q3_leaf`: (9.8).
* `Q3_val_le`: the value.
-/

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace OVNS.Quant.Metric

variable {r τ D : ℝ} {s : ℕ} {S F N z : Field}

/-- The operator norm of `O`. -/
def K3 (q W b : ℝ) : ℝ := 2 ^ 37 / q ^ 2 * clsS W W W b b b

lemma K3_nonneg {q W b : ℝ} (hW : 0 ≤ W) (hb : 0 ≤ b) : 0 ≤ K3 q W b := by
  have := c4_pos
  unfold K3 clsS
  positivity

/-- The low part of a field in `ℓ¹`. -/
lemma l1B_lo' {f : Field} {W : ℝ} (h : L1B (nrm f) W) (D : ℝ) : L1B (nrm (loP D f)) W := by
  have hle : ∀ k, nrm (loP D f) k ≤ nrm f k := fun k => by
    simp only [nrm, loP]
    split_ifs <;> simp
  have hs : Summable (nrm (loP D f)) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hle h.s
  exact ⟨fun k => norm_nonneg _, hs, (hs.tsum_le_tsum hle h.s).trans h.le⟩

/-- The value of `O`. -/
theorem Q3_val_le (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ D : ℝ) (hS : MZ 2 S) (hS' : PiS S = S)
    (hz : Summable fun k => ‖z k‖ ^ 2) (hz' : PiF z = z) :
    ‖(famQ s r D).form r τ S S S z z‖ ≤ K3 |r| (wiener S) (hnorm 2 S) * l2n z ^ 2 := by
  refine (Q3_static hs hr τ D hS hS' hS hS' hS hS' hz hz hz').trans (le_of_eq ?_)
  unfold K3
  ring

/-- **The exterior slots**: (9.6), one derivative on the direction; at weight one `N` is the
direction in `L²`, and at weight two it is `zOf 1` of the direction. -/
theorem Q3_ext_half (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ D : ℝ) (hS : MZ 2 S) (hS' : PiS S = S)
    (hN : Summable fun k => ‖N k‖ ^ 2) (hN' : PiF N = N)
    (hz : Summable fun k => ‖z k‖ ^ 2) (hz' : PiF z = z) :
    ‖(famQ s r D).form r τ S S S (zOf 1 N) z‖ + ‖(famQ s r D).form r τ S S S z (zOf 1 N)‖ ≤
      2 * (K3 |r| (wiener S) (hnorm 2 S) * (l2n N * l2n z)) := by
  have h1 := Q3_half_left hs hr τ D hS hS' hS hS' hS hS' hN hz hz'
  have h2 := Q3_half_right hs hr τ D hS hS' hS hS' hS hS' hz hN hN'
  refine (add_le_add h1 h2).trans (le_of_eq ?_)
  unfold K3
  ring

/-- The coefficient of the slow slots. -/
def T3 (D a W : ℝ) : ℝ :=
  6 * (Real.sqrt (9 + 8 * Real.log D) * W ^ 2) +
    4 * c4 * (Real.sqrt (9 + 8 * Real.log D) * (a * W)) + 2 * c4 * W ^ 2 +
    Real.sqrt 17 * Real.sqrt (9 + 8 * Real.log (4 * D)) *
      (2 * (a * W) + Real.sqrt (9 + 8 * Real.log D) * a ^ 2)

/-- **The three slow slots** (9.8), for a slow `H¹` direction `v`. -/
theorem Q3_slots_le (hs : s = 1 ∨ s = 2) (hr : r ≠ 0) (τ : ℝ) (hD : 1 ≤ D) {v : Field}
    (hv : MZ 1 v) (hv' : PiS v = v) (hS : MZ 2 S) (hS' : PiS S = S)
    (hz : Summable fun k => ‖z k‖ ^ 2) (hz' : PiF z = z) :
    ‖(famQ s r D).form r τ v S S z z‖ + ‖(famQ s r D).form r τ S v S z z‖ +
        ‖(famQ s r D).form r τ S S v z z‖ ≤
      2 ^ 36 / |r| ^ 2 * (l2n z ^ 2 * (hnorm 1 v * T3 D (hnorm 1 S) (wiener S))) := by
  have hS1 : MZ 1 S := hS.mono' (by norm_num)
  have wv := l1B_lo hD hv hv'
  have wS := l1B_lo' (l1B_nrm hS.inH) D
  have h1 := Q3_leaf hs hr τ hD hv hv' hS1 hS' hS1 hS' hz hz hz' wv wS wS
  have h2 := Q3_leaf hs hr τ hD hS1 hS' hv hv' hS1 hS' hz hz hz' wS wv wS
  have h3 := Q3_leaf hs hr τ hD hS1 hS' hS1 hS' hv hv' hz hz hz' wS wS wv
  refine (add_le_add (add_le_add h1 h2) h3).trans (le_of_eq ?_)
  unfold T3
  ring

end OVNS.Quant.Metric

end
