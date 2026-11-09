import OddViscousNS.Closed.Row.Data.HH22a

/-! The kernel check of the table `HH22a`: its digits are those of the product. Kept apart from the
table so that the row modules, which import the tables, do not depend on this check. -/

namespace OVNS.Row

theorem HH22a_ok : hhChk HH22a (arrLx (F2 1073741824000 6084)) (arrR78 (F2 8589934592000 6084)) = true := by
  decide +kernel

end OVNS.Row
