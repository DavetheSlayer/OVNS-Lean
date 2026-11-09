import OddViscousNS.Closed.Row.RadK

/-! The ball counts `N(t)`, `128 ≤ t ≤ 258`, checked by the kernel. -/

namespace OVNS.Row

theorem seed_ok : seedChk = true := by decide +kernel

end OVNS.Row
