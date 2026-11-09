import OddViscousNS.Closed.Row.Data.HH11a

/-! The kernel check of the table `HH11a`: its digits are those of the product. Kept apart from the
table so that the row modules, which import the tables, do not depend on this check. -/

namespace OVNS.Row

theorem HH11a_ok : hhChk HH11a (arrLx (F1 1099511627776000 6084)) (arrR78 (F1 1099511627776000 6084)) = true := by
  decide +kernel

end OVNS.Row
