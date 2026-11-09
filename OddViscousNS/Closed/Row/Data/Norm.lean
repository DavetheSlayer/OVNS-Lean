import OddViscousNS.Closed.Row.NormK

/-! Generated: norm bounds of the products and the rounding constants. -/

namespace OVNS.Row

theorem norm10 : normChk (F1 17592186044416000 6084) (F0 35184372088832000 6084) = true := by decide +kernel

theorem err10 : errChk (F1 17592186044416000 6084) (F0 35184372088832000 6084) 89 8627525101 = true := by decide +kernel

theorem norm20 : normChk (F2 4294967296000 6084) (F0 140737488355328000 6084) = true := by decide +kernel

theorem err20 : errChk (F2 4294967296000 6084) (F0 140737488355328000 6084) 79 6402549530670 = true := by decide +kernel

theorem norm30 : normChk (F3 131072000 6084) (F0 1125899906842624000 6084) = true := by decide +kernel

theorem err30 : errChk (F3 131072000 6084) (F0 1125899906842624000 6084) 67 52950986516337952 = true := by decide +kernel

theorem norm11 : normChk (F1 1099511627776000 6084) (F1 1099511627776000 6084) = true := by decide +kernel

theorem err11 : errChk (F1 1099511627776000 6084) (F1 1099511627776000 6084) 80 2141621816643 = true := by decide +kernel

theorem norm31 : normChk (F3 1048576000 6084) (F1 1099511627776000 6084) = true := by decide +kernel

theorem err31 : errChk (F3 1048576000 6084) (F1 1099511627776000 6084) 60 4243239449817840128 = true := by decide +kernel

theorem norm22 : normChk (F2 1073741824000 6084) (F2 8589934592000 6084) = true := by decide +kernel

theorem err22 : errChk (F2 1073741824000 6084) (F2 8589934592000 6084) 63 1724170456527612672 = true := by decide +kernel

theorem normS_ok : normS = true := by decide +kernel


end OVNS.Row
