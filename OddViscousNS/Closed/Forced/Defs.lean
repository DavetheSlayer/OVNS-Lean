import OddViscousNS.Closed.Cond.Defs
import OddViscousNS.Closed.Moments
import OddViscousNS.Closed.GTable
import OddViscousNS.Closed.WeightedEnergy

/-!
# Forced branch of Theorem 1.3 — definitions

Rows are parametrized by the effective convection `k = s κ₀` and the force cap `f₀ = φ_max/s`
(`208013·s = 500000·k`), so that `forcedRows = (500000 k, 500000 k f₀, J)`.  The normalized field
`w = v/s` solves `w_τ + sB(w,w) = −Aw + rLw + g₀` with `‖Ag₀‖₀ ≤ f₀`.  The support quantity is
`N² = ∑_j ((r + m h(j))/j)² m_j` (`Nsq`), and the constants of the face estimates are listed.
-/

open scoped ENNReal

noncomputable section

namespace OVNS

namespace Forced

/-- A row of the forced table: effective convection `k`, force cap `f₀`, window bound `J`. -/
structure Row where
  (k f0 : ℚ)
  (J : ℕ)

/-- The seven rows (common row first, then the six F662 rows). -/
def rows : List Row :=
  [⟨8393 / 10000, 1, 850⟩, ⟨851 / 1000, 9 / 10, 294⟩, ⟨868 / 1000, 4 / 5, 468⟩,
   ⟨884 / 1000, 7 / 10, 320⟩, ⟨917 / 1000, 1 / 2, 808⟩, ⟨957 / 1000, 1 / 4, 355⟩,
   ⟨979 / 1000, 1 / 10, 124⟩]

/-- `(208013 μ_max, 208013 φ_max, J) = (500000 k, 500000 k f₀, J)` row by row. -/
theorem rows_consistent :
    forcedRows = rows.map fun ρ => ((500000 * ρ.k).num.toNat, (500000 * ρ.k * ρ.f0).num.toNat, ρ.J) := by
  decide +kernel

/-- `s = k/κ₀` as a real number. -/
def sOf (ρ : Row) : ℝ := (ρ.k : ℝ) / κ₀

/-- The support quantity `N² = ∑_{k≠0} ((r + m h_k)/|k|²)² ‖w_k‖²`. -/
def Nsq (r m : ℝ) (w : Field) : ℝ :=
  ∑' k : Mode, if k = 0 then 0 else ((r + m * hm k) / absSq k) ^ 2 * ‖w k‖ ^ 2

/-- The weight `((r + m h_k)/|k|²)²`. -/
def ωN (r m : ℝ) : Mode → ℝ := fun k => if k = 0 then 0 else ((r + m * hm k) / absSq k) ^ 2

/-- The shell function of the support test, `F(j) = ε((r + m h(j))/j)² − r j − mH j h(j)`. -/
def Fsh (r m H ε : ℝ) (j : ℕ) : ℝ :=
  ε * ((r + m * hmet j) / j) ^ 2 - r * j - m * H * j * hmet j

/-- Constants of the face estimates. -/
def Ha : ℝ := (1 + 2 * aC) / (1 + 4 * aC)
def Jp : ℝ := 2 * aC / (1 + 4 * aC) ^ 2
def ηa : ℝ := Jp / Ha
def κr : ℝ := 69 / 160
def κw : ℝ := 416532 / 1000000
def σr : ℝ := 608151 / 1000000
def σw : ℝ := 629640 / 1000000
/-- The moment coefficients. -/
def cSmall : ℝ := 41034 / 100000
def cSmall' : ℝ := 410 / 1000
def cAl : ℝ := 41325 / 100000
def cAl4 : ℝ := 4124 / 10000
def cAl8 : ℝ := 411 / 1000
def cAl35 : ℝ := 41175 / 100000
/-- `c_f(E/B) = .41085 √((1.18 + .176 E/B)/1.202)`. -/
def cf (ratio : ℝ) : ℝ := 41085 / 100000 * Real.sqrt ((118 / 100 + 176 / 1000 * ratio) / (1202 / 1000))
/-- The supporting line constants. -/
def ℓs : ℝ := 13191 / 212
def cℓ : ℝ := 63940773 / 212000

theorem M₀_lt_κr_sq : M₀ < κr ^ 2 := by
  norm_num [M₀, κr]

theorem M₀_Ha_lt_κw_sq : M₀ * (1 + aC) * Ha < κw ^ 2 := by
  norm_num [M₀, Ha, aC, κw]

theorem σr_ok : (hmet 2 - 1) ^ 2 < 3 * hmet 2 * (σr * κr) ^ 2 := by
  norm_num [hmet_two, σr, κr]

theorem σw_ok : (hmet 2 - 1) ^ 2 < 3 * hmet 2 * (σw * κw) ^ 2 := by
  norm_num [hmet_two, σw, κw]

end Forced

end OVNS
