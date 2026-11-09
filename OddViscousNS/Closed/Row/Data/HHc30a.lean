import OddViscousNS.Closed.Row.Data.HH30a

/-! The kernel check of the table `HH30a`: its digits are those of the product. Kept apart from the
table so that the row modules, which import the tables, do not depend on this check. -/

namespace OVNS.Row

theorem HH30a_ok : hhChk HH30a (arrLx (F3 131072000 6084)) (arrR78 (F0 1125899906842624000 6084)) = true := by
  decide +kernel

end OVNS.Row
