import OddViscousNS.Closed.Row.Data.HH10b

/-! The kernel check of the table `HH10b`: its digits are those of the product. Kept apart from the
table so that the row modules, which import the tables, do not depend on this check. -/

namespace OVNS.Row

theorem HH10b_ok : hhChk HH10b (arrLxy (F1 17592186044416000 6084)) (arrR78 (F0 35184372088832000 6084)) = true := by
  decide +kernel

end OVNS.Row
