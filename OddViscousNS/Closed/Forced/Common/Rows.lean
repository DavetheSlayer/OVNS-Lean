import OddViscousNS.Closed.Forced.Common.Defs
import OddViscousNS.Closed.Forced.Common.Data.C_0
import OddViscousNS.Closed.Forced.Common.Data.C_1
import OddViscousNS.Closed.Forced.Common.Data.C_2
import OddViscousNS.Closed.Forced.Common.Data.C_3
import OddViscousNS.Closed.Forced.Common.Data.C_4
import OddViscousNS.Closed.Forced.Common.Data.C_5
import OddViscousNS.Closed.Forced.Common.Data.C_6
import OddViscousNS.Closed.Forced.Common.Data.C_7
import OddViscousNS.Closed.Forced.Common.Data.C_8
import OddViscousNS.Closed.Forced.Common.Data.C_9
import OddViscousNS.Closed.Forced.Common.Data.C_10
import OddViscousNS.Closed.Forced.Common.Data.C_11
import OddViscousNS.Closed.Forced.Common.Data.C_12
import OddViscousNS.Closed.Forced.Common.Data.C_13
import OddViscousNS.Closed.Forced.Common.Data.C_14
import OddViscousNS.Closed.Forced.Common.Data.C_15
import OddViscousNS.Closed.Forced.Common.Data.C_16
import OddViscousNS.Closed.Forced.Common.Data.C_17
import OddViscousNS.Closed.Forced.Common.Data.C_18
import OddViscousNS.Closed.Forced.Common.Data.C_19
import OddViscousNS.Closed.Forced.Common.Data.C_20
import OddViscousNS.Closed.Forced.Common.Data.C_21

set_option maxRecDepth 100000

namespace OVNS.Forced.Com

/-- The common row: `k = 8393/10000`, `f₀ = 1/1`, `s = 419650/208013`, `J = 850`, 436 cells. -/
def kC : ℚ := (8393 / 10000 : ℚ)
def f0C : ℚ := (1 : ℚ)
def sC : ℚ := (419650 / 208013 : ℚ)
def JC : ℕ := 850
def cellsC : List CCell := cellsC_0 ++ (cellsC_1 ++ (cellsC_2 ++ (cellsC_3 ++ (cellsC_4 ++ (cellsC_5 ++ (cellsC_6 ++ (cellsC_7 ++ (cellsC_8 ++ (cellsC_9 ++ (cellsC_10 ++ (cellsC_11 ++ (cellsC_12 ++ (cellsC_13 ++ (cellsC_14 ++ (cellsC_15 ++ (cellsC_16 ++ (cellsC_17 ++ (cellsC_18 ++ (cellsC_19 ++ (cellsC_20 ++ (cellsC_21)))))))))))))))))))))
def termC : MTerm := ⟨(359 / 250 : ℚ), (143603 / 819200 : ℚ), (59916608715781 / 50000000000000 : ℚ), (21 / 500 : ℚ), [⟨(0 : ℚ), (13 / 2000 : ℚ), .small, (83059050845050024639 / 10400650000000000000000 : ℚ), .scalar (41868440484377 / 100000000000000 : ℚ)⟩,
    ⟨(13 / 2000 : ℚ), (1 / 50 : ℚ), .small, (83059050845050024639 / 10400650000000000000000 : ℚ), .supp ⟨(0 : ℚ), (1 : ℚ), (83059050845050024639 / 10400650000000000000000 : ℚ), (12500000000000 / 6746485278047 : ℚ), (34525927108767022321371427969915339509 / 63852727217478772800500000000000000000 : ℚ), (188894257063194270934410838002269562714177 / 63852727217478772800500000000000000000000 : ℚ), 34⟩⟩,
    ⟨(1 / 50 : ℚ), (21 / 500 : ℚ), .cf (205380972793181889 / 500000000000000000 : ℚ), (724496489761052613391606665236563 / 104006500000000000000000000000000000 : ℚ), .supp ⟨(0 : ℚ), (1 : ℚ), (724496489761052613391606665236563 / 104006500000000000000000000000000000 : ℚ), (12500000000000 / 6746485278047 : ℚ), (303191806626100546003777451854343075280172876630353 / 638527272174787728005000000000000000000000000000000 : ℚ), (1680015750588048307514557550668697392823670053169512109 / 638527272174787728005000000000000000000000000000000000 : ℚ), 34⟩⟩]⟩
def winC : Win := ⟨(83059050845050024639 / 10400650000000000000000 : ℚ), (-284961088562072821 / 2080130000000000000000 : ℚ), (-2880096951549933 / 500000000000000000 : ℚ), (1429688115633256459519 / 3120195000000000000000 : ℚ)⟩

theorem cellsC_ok : (cellsC).all (CCell.ok kC f0C sC) = true := by
  simp only [cellsC, List.all_append, Bool.and_eq_true, kC, f0C, sC]
  exact ⟨cellsC_0_ok, cellsC_1_ok, cellsC_2_ok, cellsC_3_ok, cellsC_4_ok, cellsC_5_ok, cellsC_6_ok, cellsC_7_ok, cellsC_8_ok, cellsC_9_ok, cellsC_10_ok, cellsC_11_ok, cellsC_12_ok, cellsC_13_ok, cellsC_14_ok, cellsC_15_ok, cellsC_16_ok, cellsC_17_ok, cellsC_18_ok, cellsC_19_ok, cellsC_20_ok, cellsC_21_ok⟩

theorem termC_ok : (termC).ok sC f0C = true := by
  decide +kernel

theorem chainC_ok : cchainOk 1 1 cellsC termC = true := by
  decide +kernel

theorem winC_ok : (winC).ok sC f0C JC termC = true := by
  decide +kernel

end OVNS.Forced.Com
