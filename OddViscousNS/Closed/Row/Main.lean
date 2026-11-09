import OddViscousNS.Closed.Row.Assemble
import OddViscousNS.Closed.Row.Data.LowAll

/-!
# `RowBound gOVNS` and `RowBound (fun _ => M₀)`

The finite-computation hypotheses of `closed_regions_forced` and `closed_regions_unforced`, proved
without `native_decide`, axioms or external oracles: every table is re-derived by the kernel.
-/

namespace OVNS

namespace Row

/-- The sorted triples of the matrix band are enumerated. -/
lemma mem_enum {a b c : ℕ} (hcb : c ≤ b) (hba : b ≤ a) (ha0 : 0 < a)
    (hC : a * a + (b * b + c * c) < 1936) : (a, b, c) ∈ enumTriples := by
  have ha : a < 44 := by nlinarith
  simp only [enumTriples, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range]
  refine ⟨a, ha, b, by omega, c, ⟨by omega, ?_⟩, rfl⟩
  rw [Bool.and_eq_true]
  have h1 : 1 ≤ a * a + (b * b + c * c) := by nlinarith
  exact ⟨Nat.ble_eq_true_of_le h1, Nat.ble_eq_true_of_le (by omega)⟩

/-- Every row of the matrix band passes. -/
theorem rows_pass (a b c : ℕ) (hcb : c ≤ b) (hba : b ≤ a) (ha0 : 0 < a)
    (hC : a * a + (b * b + c * c) < 1936) : ∃ cK, rowTest TT a b c cK = true := by
  have hmem := mem_enum hcb hba ha0 hC
  rw [← rowsAll_tri] at hmem
  obtain ⟨r, hr, e⟩ := List.mem_map.1 hmem
  have hok := List.all_eq_true.1 rowsAll_ok r hr
  obtain ⟨a', b', c', cK⟩ := r
  simp only [tri, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl, rfl⟩ := e
  exact ⟨cK, hok⟩

end Row

/-- **The finite-computation hypothesis of the forced branch of Theorem 1.3.** -/
theorem rowBound_gOVNS : RowBound gOVNS :=
  Row.rowBound_of_real gOVNS_nonneg (Row.realRow_of_rows Row.rows_pass)

/-- **The finite-computation hypothesis of the unforced branch of Theorem 1.3.** -/
theorem rowBound_M₀ : RowBound fun _ => M₀ :=
  rowBound_mono rowBound_gOVNS gOVNS_le_M₀

end OVNS

#print axioms OVNS.rowBound_gOVNS
#print axioms OVNS.rowBound_M₀
