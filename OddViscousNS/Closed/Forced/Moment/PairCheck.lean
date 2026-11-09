import OddViscousNS.Closed.GTable
import OddViscousNS.Closed.Forced.Check.Defs

/-!
# Exact rational checker for the central part of the moment-regime pointwise bounds

For a parameter row `P = (a, bL, λ, K, w_lo, w_hi, t_lo, t_hi, Jmax, fuel)` and a pair of output
radii `(C_l, C_h)` with prices `(g_l, g_h)`, the pair value as a function of `W` is
`raw(W) = ½[g_l W/(u_l W + z_l) + g_h W/(u_h W + z_h)]`, `u = 1 + bL/h(C)`, `z = 4aC/J`,
`J = C_l + C_h`; it is non-decreasing in `W`.  On the `W`-interval of the pair,
`I = [max(w_lo, 4/(t_hi J)), min(w_hi, 4/(t_lo J))]` (no upper cap when `t_lo = 0`), the
adaptive subdivision `subdivOk` certifies `raw(W) − λ(W − 1) < K` on every piece `[lo, hi]` by the
monotone bound `raw(hi) − λ(lo − 1) < K`.  `rangeOk P lo hi` runs this over all table pairs with
`lo ≤ C_l < hi`, `1 ≤ C_l ≤ C_h`, `C_l + C_h < Jmax`, `C_h ≡ C_l (mod 4)`.
-/

namespace OVNS

namespace Forced

namespace Mom

/-- `g` as a rational: the table for `C < 1024` (`M₀` if absent), `M_mid`, `M_high`. -/
def gq (C : ℕ) : ℚ :=
  if C < 1024 then
    match gTableN.find? (fun e => e.1 == C) with
    | some e => (e.2 : ℚ) / 1000000000
    | none => 185955292 / 1000000000
  else if C < 3600 then 172754764 / 1000000000 else 163043 / 1000000

/-- A parameter row of the pointwise check. -/
structure Params where
  (a bL lam K wlo whi tlo thi : ℚ)
  (Jmax fuel : ℕ)

/-- `raw(W)` for the pair `(C_l, C_h)` with prices `(g_l, g_h)`. -/
def rawq (P : Params) (Cl Ch : ℕ) (gl gh W : ℚ) : ℚ :=
  (gl * W / ((1 + P.bL / Chk.hq Cl) * W + 4 * P.a * Cl / ((Cl : ℚ) + Ch)) +
    gh * W / ((1 + P.bL / Chk.hq Ch) * W + 4 * P.a * Ch / ((Cl : ℚ) + Ch))) / 2

/-- The monotone piece bound on `[lo, hi]`. -/
def pieceOk (P : Params) (Cl Ch : ℕ) (gl gh lo hi : ℚ) : Bool :=
  decide (rawq P Cl Ch gl gh hi - P.lam * (lo - 1) < P.K)

/-- Adaptive subdivision with fuel. -/
def subdivOk (P : Params) (Cl Ch : ℕ) (gl gh : ℚ) : ℕ → ℚ → ℚ → Bool
  | 0, lo, hi => pieceOk P Cl Ch gl gh lo hi
  | n + 1, lo, hi =>
    pieceOk P Cl Ch gl gh lo hi ||
      (subdivOk P Cl Ch gl gh n lo ((lo + hi) / 2) && subdivOk P Cl Ch gl gh n ((lo + hi) / 2) hi)

/-- The lower end of the pair's `W`-interval. -/
def wLo (P : Params) (Cl Ch : ℕ) : ℚ := max P.wlo (4 / (P.thi * ((Cl : ℚ) + Ch)))

/-- The upper end of the pair's `W`-interval (`w_hi` when `t_lo = 0`). -/
def wHi (P : Params) (Cl Ch : ℕ) : ℚ :=
  if P.tlo = 0 then P.whi else min P.whi (4 / (P.tlo * ((Cl : ℚ) + Ch)))

/-- The check of one pair. -/
def pairOk (P : Params) (Cl Ch : ℕ) (gl gh : ℚ) : Bool :=
  decide (wHi P Cl Ch < wLo P Cl Ch) || subdivOk P Cl Ch gl gh P.fuel (wLo P Cl Ch) (wHi P Cl Ch)

/-- All table pairs with `lo ≤ C_l < hi`. -/
def rangeOk (P : Params) (lo hi : ℕ) : Bool :=
  gTableN.all fun el => decide (el.1 < lo) || decide (hi ≤ el.1) || decide (el.1 = 0) ||
    gTableN.all fun eh => decide (eh.1 < el.1) || decide (P.Jmax ≤ el.1 + eh.1) ||
      decide ((eh.1 - el.1) % 4 ≠ 0) ||
      pairOk P el.1 eh.1 ((el.2 : ℚ) / 1000000000) ((eh.2 : ℚ) / 1000000000)

/-- Representability by three squares, decided by a bounded search. -/
def rep3 (C : ℕ) : Bool :=
  (List.range 32).any fun x => (List.range 32).any fun y =>
    decide (x ^ 2 + y ^ 2 ≤ C) && decide (Nat.sqrt (C - x ^ 2 - y ^ 2) ^ 2 = C - x ^ 2 - y ^ 2)

/-- The one-dimensional check used for the large-`J` row-price cases: on `W ∈ [lo, hi]` at the
two endpoints `r ∈ {rlo, rhi}` of the `r = C_l/J` range, with prices `L, H`:
`½[L W/(W + 4ar) + H W/(W + 4a(1−r))] − λ(W − 1) < K`. -/
def rawr (a L H r W : ℚ) : ℚ := (L * W / (W + 4 * a * r) + H * W / (W + 4 * a * (1 - r))) / 2

def pieceOkR (a L H r lam K lo hi : ℚ) : Bool := decide (rawr a L H r hi - lam * (lo - 1) < K)

def subdivOkR (a L H r lam K : ℚ) : ℕ → ℚ → ℚ → Bool
  | 0, lo, hi => pieceOkR a L H r lam K lo hi
  | n + 1, lo, hi =>
    pieceOkR a L H r lam K lo hi ||
      (subdivOkR a L H r lam K n lo ((lo + hi) / 2) && subdivOkR a L H r lam K n ((lo + hi) / 2) hi)

end Mom

end Forced

end OVNS
