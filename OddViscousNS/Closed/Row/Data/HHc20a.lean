import OddViscousNS.Closed.Row.Data.HH20a

/-! The kernel check of the table `HH20a`: its digits are those of the product. Kept apart from the
table so that the row modules, which import the tables, do not depend on this check. -/

namespace OVNS.Row

theorem HH20a_ok : hhChk HH20a (arrLx (F2 4294967296000 6084)) (arrR78 (F0 140737488355328000 6084)) = true := by
  decide +kernel

end OVNS.Row
