import OddViscousNS.Closed.Forced.Check.Defs
import OddViscousNS.Closed.Forced.Check.Data.F851_0
import OddViscousNS.Closed.Forced.Check.Data.F851_1
import OddViscousNS.Closed.Forced.Check.Data.F851_2
import OddViscousNS.Closed.Forced.Check.Data.F851_3
import OddViscousNS.Closed.Forced.Check.Data.F851_4
import OddViscousNS.Closed.Forced.Check.Data.F851_5
import OddViscousNS.Closed.Forced.Check.Data.F851_6
import OddViscousNS.Closed.Forced.Check.Data.F851_7
import OddViscousNS.Closed.Forced.Check.Data.F851_8
import OddViscousNS.Closed.Forced.Check.Data.F851_9
import OddViscousNS.Closed.Forced.Check.Data.F851_10
import OddViscousNS.Closed.Forced.Check.Data.F851_11
import OddViscousNS.Closed.Forced.Check.Data.F851_12
import OddViscousNS.Closed.Forced.Check.Data.F851_13
import OddViscousNS.Closed.Forced.Check.Data.F851_14
import OddViscousNS.Closed.Forced.Check.Data.F868_0
import OddViscousNS.Closed.Forced.Check.Data.F868_1
import OddViscousNS.Closed.Forced.Check.Data.F868_2
import OddViscousNS.Closed.Forced.Check.Data.F868_3
import OddViscousNS.Closed.Forced.Check.Data.F868_4
import OddViscousNS.Closed.Forced.Check.Data.F868_5
import OddViscousNS.Closed.Forced.Check.Data.F868_6
import OddViscousNS.Closed.Forced.Check.Data.F868_7
import OddViscousNS.Closed.Forced.Check.Data.F868_8
import OddViscousNS.Closed.Forced.Check.Data.F868_9
import OddViscousNS.Closed.Forced.Check.Data.F868_10
import OddViscousNS.Closed.Forced.Check.Data.F868_11
import OddViscousNS.Closed.Forced.Check.Data.F868_12
import OddViscousNS.Closed.Forced.Check.Data.F884_0
import OddViscousNS.Closed.Forced.Check.Data.F884_1
import OddViscousNS.Closed.Forced.Check.Data.F884_2
import OddViscousNS.Closed.Forced.Check.Data.F884_3
import OddViscousNS.Closed.Forced.Check.Data.F884_4
import OddViscousNS.Closed.Forced.Check.Data.F884_5
import OddViscousNS.Closed.Forced.Check.Data.F884_6
import OddViscousNS.Closed.Forced.Check.Data.F884_7
import OddViscousNS.Closed.Forced.Check.Data.F884_8
import OddViscousNS.Closed.Forced.Check.Data.F884_9
import OddViscousNS.Closed.Forced.Check.Data.F884_10
import OddViscousNS.Closed.Forced.Check.Data.F917_0
import OddViscousNS.Closed.Forced.Check.Data.F917_1
import OddViscousNS.Closed.Forced.Check.Data.F917_2
import OddViscousNS.Closed.Forced.Check.Data.F917_3
import OddViscousNS.Closed.Forced.Check.Data.F917_4
import OddViscousNS.Closed.Forced.Check.Data.F917_5
import OddViscousNS.Closed.Forced.Check.Data.F917_6
import OddViscousNS.Closed.Forced.Check.Data.F917_7
import OddViscousNS.Closed.Forced.Check.Data.F957_0
import OddViscousNS.Closed.Forced.Check.Data.F957_1
import OddViscousNS.Closed.Forced.Check.Data.F957_2
import OddViscousNS.Closed.Forced.Check.Data.F957_3
import OddViscousNS.Closed.Forced.Check.Data.F979_0
import OddViscousNS.Closed.Forced.Check.Data.F979_1

set_option maxRecDepth 100000

namespace OVNS.Forced.Chk

/-- Row `k = 851/1000`, `f₀ = 9/10`, `J = 294`: 365 cells. -/
def kF851 : ℚ := (851 / 1000 : ℚ)
def f0F851 : ℚ := (9 / 10 : ℚ)
def JF851 : ℕ := 294
def cellsF851 : List Cell := cellsF851_0 ++ (cellsF851_1 ++ (cellsF851_2 ++ (cellsF851_3 ++ (cellsF851_4 ++ (cellsF851_5 ++ (cellsF851_6 ++ (cellsF851_7 ++ (cellsF851_8 ++ (cellsF851_9 ++ (cellsF851_10 ++ (cellsF851_11 ++ (cellsF851_12 ++ (cellsF851_13 ++ (cellsF851_14))))))))))))))
def termF851 : Term := ⟨(273 / 200 : ℚ), (2081 / 12800 : ℚ), (14609500333687 / 12500000000000 : ℚ), (67315216032363 / 12500000000000000 : ℚ), ⟨(0 : ℚ), (1 : ℚ), (67315216032363 / 12500000000000000 : ℚ), (36000000000000 / 12823726386881 : ℚ), (50989129645969920675453165029868783 / 105321505260323407018750000000000000 : ℚ), (4405151294947286547637644090086874037437 / 1274390213649913224926875000000000000000 : ℚ), 45⟩⟩

theorem cellsF851_ok : (cellsF851).all (Cell.ok kF851 f0F851) = true := by
  simp only [cellsF851, List.all_append, Bool.and_eq_true, kF851, f0F851]
  exact ⟨cellsF851_0_ok, cellsF851_1_ok, cellsF851_2_ok, cellsF851_3_ok, cellsF851_4_ok, cellsF851_5_ok, cellsF851_6_ok, cellsF851_7_ok, cellsF851_8_ok, cellsF851_9_ok, cellsF851_10_ok, cellsF851_11_ok, cellsF851_12_ok, cellsF851_13_ok, cellsF851_14_ok⟩

theorem termF851_ok : (termF851).ok kF851 f0F851 = true := by
  decide +kernel

theorem chainF851_ok : chainOk 1 1 cellsF851 termF851 = true := by
  decide +kernel

theorem windowF851_ok : windowOk f0F851 JF851 termF851 = true := by
  decide +kernel

/-- Row `k = 217/250`, `f₀ = 4/5`, `J = 468`: 318 cells. -/
def kF868 : ℚ := (217 / 250 : ℚ)
def f0F868 : ℚ := (4 / 5 : ℚ)
def JF868 : ℕ := 468
def cellsF868 : List Cell := cellsF868_0 ++ (cellsF868_1 ++ (cellsF868_2 ++ (cellsF868_3 ++ (cellsF868_4 ++ (cellsF868_5 ++ (cellsF868_6 ++ (cellsF868_7 ++ (cellsF868_8 ++ (cellsF868_9 ++ (cellsF868_10 ++ (cellsF868_11 ++ (cellsF868_12))))))))))))
def termF868 : Term := ⟨(659 / 500 : ℚ), (653 / 5120 : ℚ), (22969545054267 / 20000000000000 : ℚ), (15608723224061 / 5000000000000000 : ℚ), ⟨(0 : ℚ), (1 : ℚ), (15608723224061 / 5000000000000000 : ℚ), (24000000000000 / 10596630625153 : ℚ), (771617622830448667311726235763 / 2288209925618975937500000000000 : ℚ), (78986618544154135967331629974671643 / 27458519107427711250000000000000000 : ℚ), 54⟩⟩

theorem cellsF868_ok : (cellsF868).all (Cell.ok kF868 f0F868) = true := by
  simp only [cellsF868, List.all_append, Bool.and_eq_true, kF868, f0F868]
  exact ⟨cellsF868_0_ok, cellsF868_1_ok, cellsF868_2_ok, cellsF868_3_ok, cellsF868_4_ok, cellsF868_5_ok, cellsF868_6_ok, cellsF868_7_ok, cellsF868_8_ok, cellsF868_9_ok, cellsF868_10_ok, cellsF868_11_ok, cellsF868_12_ok⟩

theorem termF868_ok : (termF868).ok kF868 f0F868 = true := by
  decide +kernel

theorem chainF868_ok : chainOk 1 1 cellsF868 termF868 = true := by
  decide +kernel

theorem windowF868_ok : windowOk f0F868 JF868 termF868 = true := by
  decide +kernel

/-- Row `k = 221/250`, `f₀ = 7/10`, `J = 320`: 268 cells. -/
def kF884 : ℚ := (221 / 250 : ℚ)
def f0F884 : ℚ := (7 / 10 : ℚ)
def JF884 : ℕ := 320
def cellsF884 : List Cell := cellsF884_0 ++ (cellsF884_1 ++ (cellsF884_2 ++ (cellsF884_3 ++ (cellsF884_4 ++ (cellsF884_5 ++ (cellsF884_6 ++ (cellsF884_7 ++ (cellsF884_8 ++ (cellsF884_9 ++ (cellsF884_10))))))))))
def termF884 : Term := ⟨(317 / 250 : ℚ), (3841 / 25600 : ℚ), (14081237516639 / 12500000000000 : ℚ), (13046508822781 / 3125000000000000 : ℚ), ⟨(0 : ℚ), (1 : ℚ), (13046508822781 / 3125000000000000 : ℚ), (14000000000000 / 6137782138099 : ℚ), (4862122638957240392487674098860859 / 12602429945905544089062500000000000 : ℚ), (1178655827330732112050990327338249829353 / 416667840086502051444628906250000000000 : ℚ), 46⟩⟩

theorem cellsF884_ok : (cellsF884).all (Cell.ok kF884 f0F884) = true := by
  simp only [cellsF884, List.all_append, Bool.and_eq_true, kF884, f0F884]
  exact ⟨cellsF884_0_ok, cellsF884_1_ok, cellsF884_2_ok, cellsF884_3_ok, cellsF884_4_ok, cellsF884_5_ok, cellsF884_6_ok, cellsF884_7_ok, cellsF884_8_ok, cellsF884_9_ok, cellsF884_10_ok⟩

theorem termF884_ok : (termF884).ok kF884 f0F884 = true := by
  decide +kernel

theorem chainF884_ok : chainOk 1 1 cellsF884 termF884 = true := by
  decide +kernel

theorem windowF884_ok : windowOk f0F884 JF884 termF884 = true := by
  decide +kernel

/-- Row `k = 917/1000`, `f₀ = 1/2`, `J = 808`: 185 cells. -/
def kF917 : ℚ := (917 / 1000 : ℚ)
def f0F917 : ℚ := (1 / 2 : ℚ)
def JF917 : ℕ := 808
def cellsF917 : List Cell := cellsF917_0 ++ (cellsF917_1 ++ (cellsF917_2 ++ (cellsF917_3 ++ (cellsF917_4 ++ (cellsF917_5 ++ (cellsF917_6 ++ (cellsF917_7)))))))
def termF917 : Term := ⟨(237 / 200 : ℚ), (4151 / 51200 : ℚ), (6806476695031 / 6250000000000 : ℚ), (8460870656573 / 6250000000000000 : ℚ), ⟨(0 : ℚ), (1 : ℚ), (8460870656573 / 6250000000000000 : ℚ), (312500000000 / 174826785349 : ℚ), (105323799915857328350357073627509 / 553563884457214581250000000000000 : ℚ), (28682608276105735270604439167255719957 / 13562315169201757240625000000000000000 : ℚ), 70⟩⟩

theorem cellsF917_ok : (cellsF917).all (Cell.ok kF917 f0F917) = true := by
  simp only [cellsF917, List.all_append, Bool.and_eq_true, kF917, f0F917]
  exact ⟨cellsF917_0_ok, cellsF917_1_ok, cellsF917_2_ok, cellsF917_3_ok, cellsF917_4_ok, cellsF917_5_ok, cellsF917_6_ok, cellsF917_7_ok⟩

theorem termF917_ok : (termF917).ok kF917 f0F917 = true := by
  decide +kernel

theorem chainF917_ok : chainOk 1 1 cellsF917 termF917 = true := by
  decide +kernel

theorem windowF917_ok : windowOk f0F917 JF917 termF917 = true := by
  decide +kernel

/-- Row `k = 957/1000`, `f₀ = 1/4`, `J = 355`: 86 cells. -/
def kF957 : ℚ := (957 / 1000 : ℚ)
def f0F957 : ℚ := (1 / 4 : ℚ)
def JF957 : ℕ := 355
def cellsF957 : List Cell := cellsF957_0 ++ (cellsF957_1 ++ (cellsF957_2 ++ (cellsF957_3)))
def termF957 : Term := ⟨(543 / 500 : ℚ), (7991 / 51200 : ℚ), (104259292151827 / 100000000000000 : ℚ), (223857410701561 / 100000000000000000 : ℚ), ⟨(0 : ℚ), (1 : ℚ), (223857410701561 / 100000000000000000 : ℚ), (6250000000000 / 6950316158797 : ℚ), (79643261553175979465642997906570337 / 456664615445021907550000000000000000 : ℚ), (1314316590019014703891320177738346524387 / 1212175927762153739893750000000000000000 : ℚ), 39⟩⟩

theorem cellsF957_ok : (cellsF957).all (Cell.ok kF957 f0F957) = true := by
  simp only [cellsF957, List.all_append, Bool.and_eq_true, kF957, f0F957]
  exact ⟨cellsF957_0_ok, cellsF957_1_ok, cellsF957_2_ok, cellsF957_3_ok⟩

theorem termF957_ok : (termF957).ok kF957 f0F957 = true := by
  decide +kernel

theorem chainF957_ok : chainOk 1 1 cellsF957 termF957 = true := by
  decide +kernel

theorem windowF957_ok : windowOk f0F957 JF957 termF957 = true := by
  decide +kernel

/-- Row `k = 979/1000`, `f₀ = 1/10`, `J = 124`: 32 cells. -/
def kF979 : ℚ := (979 / 1000 : ℚ)
def f0F979 : ℚ := (1 / 10 : ℚ)
def JF979 : ℕ := 124
def cellsF979 : List Cell := cellsF979_0 ++ (cellsF979_1)
def termF979 : Term := ⟨(129 / 125 : ℚ), (1631 / 5120 : ℚ), (1588071993409 / 1562500000000 : ℚ), (7777518452589 / 1562500000000000 : ℚ), ⟨(0 : ℚ), (1 : ℚ), (7777518452589 / 1562500000000000 : ℚ), (1000000000000 / 5998097430419 : ℚ), (134699542679502944638934247481501 / 1396975635599055159375000000000000 : ℚ), (24296629763964811955395915089336451 / 93131709039937010625000000000000000 : ℚ), 34⟩⟩

theorem cellsF979_ok : (cellsF979).all (Cell.ok kF979 f0F979) = true := by
  simp only [cellsF979, List.all_append, Bool.and_eq_true, kF979, f0F979]
  exact ⟨cellsF979_0_ok, cellsF979_1_ok⟩

theorem termF979_ok : (termF979).ok kF979 f0F979 = true := by
  decide +kernel

theorem chainF979_ok : chainOk 1 1 cellsF979 termF979 = true := by
  decide +kernel

theorem windowF979_ok : windowOk f0F979 JF979 termF979 = true := by
  decide +kernel

end OVNS.Forced.Chk
