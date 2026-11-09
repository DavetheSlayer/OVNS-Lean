import OddViscousNS.Closed.Gram
import OddViscousNS.Closed.WeightedEnergy
import OddViscousNS.Trilinear

/-!
# Energy conservation and the cubic of the filtered nonlinearity

`∑_k Re⟨w_k, B(w,w)_k⟩ = 0` for real solenoidal `H²` fields (the kinetic law `X' = −2J₁`), and
the transfer of the `X`- and `Y`-pairings of the filtered nonlinearity
`Q_τ(y,y) = R(−τ) B(R(τ)y, R(τ)y)` (`Qphase_eq`) to the physical cubic of `R(τ)y`:
`wPair ωX y (Q_τ(y,y)) = 0`, `wPair ωY y (Q_τ(y,y)) = cubic (R(τ) y)`.
-/

open scoped ENNReal

namespace OVNS

/-- The unit weight `ωX` is the `H⁰` Sobolev weight. -/
private lemma ωX_eq_sobWeight (k : Mode) : ωX k = sobWeight 0 k := by
  simp [ωX, sobWeight]

/-- The `X`-pairing is the `H⁰` pairing. -/
private lemma wPair_X_eq_pair (c F : Field) : wPair ωX c F = pair 0 c F := by
  simp only [wPair, pair, ωX_eq_sobWeight]

/-- The phased form conserves the `H⁰` energy. -/
private lemma pair_Qphase_self (τ : ℝ) {u : Field} (hu : Adm 2 u) :
    pair 0 u (Qphase τ u u) = 0 := by
  refine pair_zero_of_cyc (tripT (phaseM τ) u u u) (inner_Qm (phaseM_bdd τ) hu.real hu.mz hu.mz)
    (summable_tripT (phaseM_bdd τ) (by norm_num) hu.mz hu.mz hu.mz) ?_
    (tripT_cyc (fun a b c p q => by simp only [phaseM, Phi_cyc a b c p q]) u)
  intro p q h
  simp [tripT, h, hel_zero_mode, tau_zero_right]

/-- The constant multiplier one conserves the `H⁰` energy. -/
private lemma pair_Qone_self {u : Field} (hu : Adm 2 u) :
    pair 0 u (Qm (fun _ _ _ _ _ => 1) u u) = 0 := by
  have hb : Mult.Bdd (fun _ _ _ _ _ => 1) := fun _ _ _ _ _ => by simp
  refine pair_zero_of_cyc (tripT (fun _ _ _ _ _ => 1) u u u) (inner_Qm hb hu.real hu.mz hu.mz)
    (summable_tripT hb (by norm_num) hu.mz hu.mz hu.mz) ?_
    (tripT_cyc (fun _ _ _ _ _ => rfl) u)
  intro p q h
  simp [tripT, h, hel_zero_mode, tau_zero_right]

/-- The filter `R(-τ)` is the adjoint of `R(τ)` at each mode. -/
private lemma inner_rot_neg (τ : ℝ) (k : Mode) (v w : V3) :
    inner ℂ v (rot (-τ) k w) = inner ℂ (rot τ k v) w := by
  simp only [rot, inner_sum, sum_inner, inner_smul_right, inner_smul_left, inner_hel_right]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- Energy conservation of the convection term. -/
theorem energy_conservation {u : Field} (hu : Adm 2 u) :
    ∑' k, (inner ℂ (u k) (convec u k)).re = 0 := by
  have h := pair_Qone_self hu
  rw [Qm_one hu hu, Bsym_self hu.mz] at h
  rw [← h, pair]
  refine tsum_congr fun k => ?_
  by_cases hk : k = 0
  · subst hk
    simp [hu.mean, sobWeight]
  · simp [sobWeight, hk]

theorem wPair_X_Qphase (τ : ℝ) {u : Field} (hu : Adm 2 u) : wPair ωX u (Qphase τ u u) = 0 := by
  rw [wPair_X_eq_pair, pair_Qphase_self τ hu]

theorem wPair_Y_Qphase (τ : ℝ) {u : Field} (hu : Adm 2 u) :
    wPair ωY u (Qphase τ u u) = cubic (rotF τ u) := by
  rw [Qphase_eq τ hu hu, Bsym_self (hu.rotF τ).mz, wPair, cubic]
  refine tsum_congr fun k => ?_
  change ωY k * (inner ℂ (u k) (rot (-τ) k _)).re = _
  rw [inner_rot_neg]
  rfl

end OVNS
