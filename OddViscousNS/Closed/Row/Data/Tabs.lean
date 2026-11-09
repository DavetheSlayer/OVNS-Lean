import OddViscousNS.Closed.Row.RowK
import OddViscousNS.Closed.Row.Data.HH10a
import OddViscousNS.Closed.Row.Data.HH10b
import OddViscousNS.Closed.Row.Data.HH20a
import OddViscousNS.Closed.Row.Data.HH20b
import OddViscousNS.Closed.Row.Data.HH30a
import OddViscousNS.Closed.Row.Data.HH30b
import OddViscousNS.Closed.Row.Data.HH11a
import OddViscousNS.Closed.Row.Data.HH11b
import OddViscousNS.Closed.Row.Data.HH31a
import OddViscousNS.Closed.Row.Data.HH31b
import OddViscousNS.Closed.Row.Data.HH22a
import OddViscousNS.Closed.Row.Data.HH22b

/-! The twelve digit tables, as one record. -/

namespace OVNS.Row

noncomputable def TT : Tabs :=
  ⟨HH10a, HH10b, HH20a, HH20b, HH30a, HH30b, HH11a, HH11b, HH31a, HH31b, HH22a, HH22b⟩

/-- The test at a row `(a, b, c, cK)`. -/
noncomputable def rowOK (r : Nat × Nat × Nat × Nat) : Bool :=
  rowTest TT r.1 r.2.1 r.2.2.1 r.2.2.2

/-- The sorted triples with `0 < C < 1936`, in lexicographic order. -/
def enumTriples : List (Nat × Nat × Nat) :=
  (List.range 44).flatMap fun a => (List.range (a + 1)).flatMap fun b =>
    ((List.range (b + 1)).filter fun c =>
      Nat.ble 1 (a * a + (b * b + c * c)) && Nat.ble (a * a + (b * b + c * c) + 1) 1936).map
        fun c => (a, b, c)

/-- The triple of a row. -/
def tri (r : Nat × Nat × Nat × Nat) : Nat × Nat × Nat := (r.1, r.2.1, r.2.2.1)

end OVNS.Row
