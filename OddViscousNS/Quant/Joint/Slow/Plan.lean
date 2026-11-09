import OddViscousNS.Quant.Joint.Interfaces

/-!
# E7-P (block J2): the design of the proof of `SlowCapsJoint`

"Body n" is the proof volume; `[own]` flags a step of this design that is in no source (proposed
here, tested only by the Lean proof below it); `[survey]` a step of `t12_joint_route.md` §3.4 that
is in no source either; `[src]` a step of the sources.  Notation: `y_S = (h, v)` the corrected slow
field (`corrSlow`), `ω = curl h`, `f = corrRes`, `Φ² ≥ ∫_unit ‖f‖₁²`, `Φ ≲ R`; `P_N` the sharp box
truncation; `a, b, c` the `H¹, H², H³` norms.  All constants are absolute.

## The result of the design
The exponents `(3/2, 2, 3, 3/2)` and `M_∞ ≲ R` are reached, up to `Ex`: every step below is proved
(`Joint/Slow/Main.lean`, no `sorry`).  One input is outside J2: the source budget, see 0.  Moving
`p` is **needed**: at fixed even `p` the chain gives `∫ b² ≲ R^{3+1/(p−1)}`, a polynomial loss.
But `p = 2q`, `q = 2ⁿ`, `n = ⌈log log R⌉` suffices (`[own]`; the sources take `p ≍ log R`, for
polylogs): the loss `R^{1/q}` is then a subpower `Ex`, and constants `exp(O(n²))` are free.  So no
sharp constant in `p` is needed anywhere.

## The chain from `SlowHistory` to the conclusions
Write `a₀ = max 0 (s − 1)`, and `b₀ = s` if `s ≥ 1` (generic), `b₀ = 0` if `s < 1` (true zero).

0. **Source** (J4, not J2).  `∫_I ‖f‖₁² ≤ 4φ² + 4` on `|I| ≤ 2` where the caps hold:
   `corrRes_budget` at `budgetPoly`, which is above `Q` at the joint caps (`T R^{7/2}`), see
   `t12_joint_scaffold.md` 8.7.  J2 takes this as the *role* of `qS` (`SlowBudget`), and needs
   nothing else of the fast side: only `L²_t H¹`, no pointwise `H⁰`, no split `g_S + r_S`.
   `‖R_S‖₂ ≤ δ₀`: `slowCorr_le`, from the floor of `qSFull`.
1. **`L²`, no `L^p`** `[src]`.  `corr_l2_law`, `corr_horiz_law` with `Φ² → ‖f‖₁²` (`l2_stage`,
   `L2Out`): `‖y_S‖₀, a_h ≲ R`, `∫_unit a², ∫_unit b_h² ≲ R²` on `[a₀, t]`, levels `L₀, L₁` regained
   in a unit.
2. **Even powers on polynomial paths** `[own]`.  No propagator, no adjoint, no Nash, no
   regularization of the drift: for `w = P_N c`, with `c = ω` or `v`, a trigonometric polynomial
   with `C¹` coefficients, `∂_t w = Δw − U·∇w + F`, `U = P_N h`, where `F = P_N f + Z_N`,
   `‖Z_N‖₂ ≲ ‖y_S‖₂ ‖c‖₂/N` (the commutator of the truncation, `nn2_errP_le`; `nn2_errP_le'` for
   `c = v`).  All calculus is the derivation of the group algebra `ℂ[ℤ³]`: with `m_q = ∫ w^{2q}`,
   `d_q = ‖∇ w^q‖₂²`, `m_q' + (2(2q−1)/q) d_q = 2q ∫ w^{2q−1} F` (`div U = 0` kills the transport).
3. **Absorbing an `L²_t L²_x` source** `[own]`, the point of the Alikakos objection.  Ladyzhenskaya
   for `w^q` gives `m_{2q} ≤ 200 m_q (m_q + d_q)`; then `w^{4q−2} ≤ Λ⁻² w^{4q} + Λ^{4q−2}` with
   `Λ^{2q} = m_q` gives `∫ w^{4q−2} ≤ 201 m_q^{1−1/q} (m_q + d_q)`, so
   `m_q' + d_q ≤ m_q + 201 q² ‖F‖₂² m_q^{1−1/q}`, whence for `y = m_q^{1/q} = ‖w‖_{2q}²`:
   `y' ≤ y/q + 201 q ‖F‖₂²`.  Additive, no Gronwall on `‖F‖₂`, kernel `q` (the sources' `p/2`).
4. **Moser in time** `[own]`, replacing `L² → L^p` smoothing with propagator (Body 55).  From the
   law of 3 at level `q` and Ladyzhenskaya, `∫_{window} m_{2q} ≲ q² Y^{2q}`, where
   `Y ≥ sup m_q^{1/q}, Φ²`: a good time in a window of length `2^{−n−1}` gives `m_{2q}`, and 3
   propagates it.  So for `u ≥ a₀ + 1`, `‖P_N c(u)‖²_{2q} ≤ Π_n max(sup_{unit} ‖c‖₀², Φ²)`,
   `q = 2ⁿ`, `Π_n = e^{nT} 2^{18n} 8^{n(n−1)/2}` (`piM`, `moser`), `T` the length of the interval.
   `p = 4` is the case `n = 1` (`PolyPath.smoothing_four`), which needs no iteration.
   True zero `[own]`: `‖P_N ω(0)‖_{2q} ≲ ‖ω(0)‖₁` is Sobolev, got from 4 itself (`sobolev_poly`):
   on a fictitious past `t ∈ [−1, 0]`, `ŵ_k(t) = e^{t|k|²} ŵ_k(0)` solves the heat equation with
   source `2|k|² ŵ_k`, of `L²_t L²_x` norm `≤ √2 ‖w(0)‖₁`, zero drift.  Hence no Hausdorff–Young,
   no Young `ℓ^r`.
5. **Riesz** `[survey]`, with no Mathlib CZ theory, no circle, no rational directions, no density:
   for a real mean-zero polynomial `f`, and `θ` with `k·θ ≠ 0` on its finite spectrum, `f + i H_θ f`
   has spectrum in the open half plane `k·θ > 0`, so `∫ (f + i H_θ f)^{2n} = 0`:
   `2 ‖g‖^{2n}_{2n} ≤ ∫ (|f| + |g|)^{2n}`, so by convexity
   `‖H_θ f‖^{2n}_{2n} ≤ 3 (4n+1)^{2n−1} ‖f‖^{2n}_{2n}` (`mP_hilbert_le`).  Rotation `[src]`
   (Body 24, on rational directions): `∫_{S¹} θ_j sgn(k·θ) dθ = 4 k_j/|k|`, Jensen, Fubini, for
   `‖R_j f‖_{2n} ≲ n ‖f‖_{2n}` (`mP_riesz_le`).  `∂_i h_j = ± R_i R_{j'} ω` on polynomials:
   `‖P_N Dh‖_{2q} ≲ q² ‖P_N ω‖_{2q}` (`mP_strain_le`).  Density is avoided because 4 is proved on
   `P_N c` itself.  So `D := ‖P_N Dh‖_{4q} ≲ K_q R` on `[b₀, t]`, for all large `N`
   (`strain_generic`, `strain_zero`, `StrainOn`).
6. **Level split** `[own]`, replacing `‖∇v‖_{2p/(p−2)}` interpolation.  Pointwise, for `q ≥ 1`,
   `|A| ≤ Λ + |A|^q Λ^{1−q}`, `A² ≤ Λ² + A^{2q} Λ^{2−2q}`.  With `Λ = λ D`, `λ^q ≥ R^K`, `λ = Ex`:
   `∫ |A| g² ≤ λ D ‖g‖₂² + λ^{1−q} D ‖g‖₄²`, `‖g‖₄² ≤ 5 ‖g‖₂ ‖∇g‖₂`.  No Hölder at `p ≠ 2`, no rpow.
7. **Passive `H¹`** `[src]` (Bodies 24, 26; form `∫ ∂_i h_j ∂_j g ∂_i g`).  For `g` passive,
   `(‖∇g‖²)' + ‖Δg‖² ≲ λ D ‖∇g‖² + (source)`.  `g = v`: `a_v² ≲ λ K R³` after a window of length
   `1/2` (`∫_window a_v² ≲ R²`), `∫_unit b_v² ≲ λ K R³`.  `g = ω`: the same for `b_h`, `c_h`.
   Here `‖∇v‖₄² ≲ a_v b_v` (Ladyzhenskaya), not `M_∞ b_v` (`[survey]`): no sup bound needed.
   (`vert_h1_law`, `horiz_h2_law`.)
8. **Passive `H²`, barrier** `[src]`.  `g_l = ∂_l v` is passive with source `∂_l f − ∂_l h·∇v`, so
   7 applies, with `‖∂_l h·∇v‖₂² ≤ λ² D² a² + 5 λ^{2−2q} D² a b` (6 at exponent `4q`).  Barrier
   (`barrier_sup`) with `c ≥ z/a`: `z ≲ λ D A²`, so `b_v ≲ e R²`; the first unit starts from the
   levels of `SlowHistory`; regain on `[s + 1, t]` from a good time.  Integrating: `clip`, with
   `P_S ≲ R⁴ + ℓ R⁵` up to `Ex`.  (`vert_h2_law`, `vert_h2_barrier`, `chain_core`, `chain_clip`.)
9. **Wiener** `[src]` F5b.  `𝒜(u) ≲ √(1 + log N) ‖u‖₁ + ‖u‖₂/N` on slow fields (`wiener_log_le`)
   gives `W_S ≲ R^{3/2}`, `∫_unit W_S² ≲ R²` up to `Ex` (`kin`), `‖h‖_∞ ≲ R` up to `Ex`.
10. **Sup of `v`** `[own]`, replacing Body 55's Duhamel.  Step 4 for `c = v`, `P_N` at the explicit
   `N ≍ Ex R³` (`box_choice`), where `‖Z_N‖₂² ≲ ‖y_S‖₂⁴/N² ≲ R²` with no `H³` norm (`nn2_errP_le'`,
   `vert_box`); Nikolskii at even exponent: `‖w^q‖_∞ ≤ ‖coeff‖_{ℓ¹} ≤ (4qN+1) ‖w‖_{2q}^q`
   (Cauchy–Schwarz on the spectrum of `w^q`, box of half-width `2N`), the tail by `‖v‖₂/N`.
   So `‖v‖_∞ ≲ R` up to `Ex` (`norm_physS_le_of_poly`, `sup_le`).  `slowSup_le_corrected` passes
   to `Π_S x`.
   TeX has `M_∞ ≲ R` flat; `SlowCapsJoint` allows `C Ex R`, and that is what this gives.
11. **Levels** (triangular, as `SlowCapsJoint`): `slowL = (10, 10, 200, 200, 4300)`, `Tp = 4`,
   `e₀ = Ex 6 R`, `Ex (c/3) R = e₀²`, `Ex c R = e₀⁶`, `c = 36`, `Λ = Ex 4 R · K_q R`.

## Which `p`
`p ≠ 2` occurs in 4, 5, 6, 10 only.  `p = 4`: first Moser step, no Riesz.  Moving `p` is needed in
7, 8 only, for `R^{1/q}`.  Step 10 needs `q ≍ log log R` as well.  Consumers of the outputs use no
`L^p`.

## Amendments
`SlowCapsJoint` needs no change.  `SlowBudget` is the role of `qS`: `slowCapsJoint_budgetPoly` is
the theorem at `budgetPoly`, with no hypothesis, and J4 owes `SlowBudget` at `qSFull`
(`JointData.slowCaps_of_budget`).  `Sl := True`.
-/
