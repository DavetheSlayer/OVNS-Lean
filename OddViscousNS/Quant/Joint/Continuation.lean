import OddViscousNS.Quant.Regimes.Continuation

/-!
# Theorem 1.2, joint large force: causal continuation with a start predicate (R3-J)

`Regimes/Continuation.lean` runs the bootstrap from `StrictImprovement`, which quantifies over all
solutions and regains the start levels on `[s + 1, t]`, with a kinetic functional valid on every
prefix.  None of this fits the joint regime: the start of E7-P is a solution-dependent predicate
`Lev` (the backward-unit history `SlowHistory`, which is not a function of the state at the start
and is only regained on the last unit of a piece), and the kinetic law needs the bound `Bd` on
`M_∞`, which E7-P produces on pieces only.  Here the same bootstrap runs along one solution, from
`StrictOn` and `KinFunOn` (all proved, nothing is assumed beyond `Regimes/Continuation.lean`):
* `onPrefix_closed_on`, `piece_first_exit_on`: the first exit from a good point, by the library's
  `first_exit` and cap deficit;
* `piece_step_on`: one lookahead piece, with the next good point in the last unit;
* `global_of_strictOn`: the maximal solution of `exists_maximal` is global, with a uniform `H²`
  bound (`pieces_induction`).
The cap deficit `deficit` of `Regimes/Continuation.lean` is reused.
-/

open scoped ENNReal Topology
open MeasureTheory Set Filter

noncomputable section

namespace OVNS.Quant

/-- **The bootstrap input along one solution**: on every piece `[s, t]` of length `≤ Tp` inside the
lifespan, starting at a good point where `Lev` holds, on which the caps hold and the threshold
is paid, the caps improve to `ci` and the bound `Bd` holds; and on the last unit of a full piece,
the start levels `c0` and `Lev` hold again.  This is what E6, E10 and E7-P deliver. -/
def StrictOn (Mf Tp : ℝ) (q : Caps → ℝ) (caps ci c0 : Caps) (Lev Bd : ℝ → Prop) (r : ℝ)
    (g : Field) (y : ℝ → Field) (Ty : ℝ≥0∞) : Prop :=
  ∀ s t : ℝ, GoodPoint Mf c0 ci r g y s → Lev s → PieceHyp Tp q r g y Ty caps s t →
    OnPrefix ci r g y s t ∧ (∀ u ∈ Icc s t, Bd u) ∧
      ∀ v ∈ Icc (s + Tp - 1) t, PointCaps c0 r g y v ∧ Lev v

/-- The kinetic clauses of `KineticInterface` for one solution with functional `W0`, on the
prefixes where `Bd` holds (compare `KinFun`, which has no `Bd`). -/
def KinFunOn (μ : ℝ) (q₀ : Caps → ℝ) (Bd : ℝ → Prop) (r : ℝ) (g : Field) (y : ℝ → Field)
    (Ty : ℝ≥0∞) (W0 : ℝ → ℝ) : Prop :=
  ∀ (caps : Caps) (s t : ℝ), PrefixHyp q₀ r g y Ty caps s t → (∀ u ∈ Icc s t, Bd u) →
    (∀ u ∈ Icc s t, 3 / 4 * fastNorm 0 r g y u ^ 2 ≤ W0 u ∧
      W0 u ≤ 5 / 4 * fastNorm 0 r g y u ^ 2) ∧
    (s = 0 → W0 0 ≤ 5 / 4 * (μ + 1 / 4) ^ 2) ∧
    W0 t - W0 s + (∫ u in s..t, fastNorm 1 r g y u ^ 2) ≤ (t - s) / 8 ∧
    W0 t ≤ max (W0 s) (5 / 32)

section Step

variable {Mf Tp μ φ : ℝ} {q : Caps → ℝ} {caps ci c0 : Caps} {Lev Bd : ℝ → Prop} {r : ℝ}
  {g : Field} {y : ℝ → Field} {Ty : ℝ≥0∞}

/-- **Closed first exit**: the caps hold on the whole piece `[s, s + T']` when it lies strictly
inside the lifespan (as `onPrefix_closed`). -/
theorem onPrefix_closed_on (hlt : ci.Below caps)
    (himp : StrictOn Mf Tp q caps ci c0 Lev Bd r g y Ty) (hsol : ActualSol μ φ r g y Ty)
    (hthr : q caps ≤ |r|) {s T' : ℝ}
    (hgood : GoodPoint Mf c0 ci r g y s) (hLev : Lev s) (hT'0 : 0 ≤ T') (hT' : T' ≤ Tp)
    (hlife : ENNReal.ofReal (s + T') < Ty) : OnPrefix caps r g y s (s + T') := by
  have hs := hgood.nonneg
  have hcont := deficit_cont hsol caps hs hT'0 hlife
  have himp' : ∀ τ₀ ∈ Ico 0 T', (∀ τ ∈ Icc 0 τ₀, deficit caps r g y s τ ≤ 0) →
      deficit caps r g y s τ₀ < 0 := by
    intro τ₀ hτ₀ hle
    have hpre := onPrefix_of_deficit hτ₀.1 hle
    have hpiece : PieceHyp Tp q r g y Ty caps s (s + τ₀) :=
      ⟨⟨hs, by linarith [hτ₀.1],
        lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by linarith [hτ₀.2])) hlife, hthr, hpre⟩,
        by linarith [hτ₀.2]⟩
    exact deficit_neg_of_below hlt hτ₀.1 (himp s (s + τ₀) hgood hLev hpiece).1
  have hneg := first_exit (hcont.mono Ico_subset_Icc_self) (deficit_zero hlt hgood) himp'
  refine onPrefix_of_deficit hT'0 fun τ hτ ↦ ?_
  rcases lt_or_eq_of_le hτ.2 with h | h
  · exact (hneg τ ⟨hτ.1, h⟩).le
  · rw [h]
    rcases lt_or_eq_of_le hT'0 with h0 | h0
    · have hmem : Icc 0 T' ∈ 𝓝[<] T' :=
        mem_of_superset (Ico_mem_nhdsLT h0) Ico_subset_Icc_self
      have ht := (hcont T' ⟨hT'0, le_rfl⟩).mono_of_mem_nhdsWithin hmem
      exact le_of_tendsto ht
        (by filter_upwards [Ico_mem_nhdsLT h0] with u hu using (hneg u hu).le)
    · rw [← h0]
      exact (deficit_zero hlt hgood).le

/-- **First exit on a piece** (as `piece_first_exit`). -/
theorem piece_first_exit_on (hlt : ci.Below caps)
    (himp : StrictOn Mf Tp q caps ci c0 Lev Bd r g y Ty) (hsol : ActualSol μ φ r g y Ty)
    (hthr : q caps ≤ |r|) {s T' : ℝ} (hgood : GoodPoint Mf c0 ci r g y s) (hLev : Lev s)
    (hT' : T' ≤ Tp) (hlife : ENNReal.ofReal (s + T') ≤ Ty) :
    ∀ t : ℝ, s ≤ t → t < s + T' → OnPrefix caps r g y s t := by
  intro t hst htT
  have hs := hgood.nonneg
  have h := onPrefix_closed_on hlt himp hsol hthr hgood hLev (T' := t - s) (by linarith)
    (by linarith) ?_
  · rwa [add_sub_cancel] at h
  · rw [add_sub_cancel]
    exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 htT) hlife

/-- **Blow-up alternative on a piece** (as the private `lifespan_gt`). -/
theorem lifespan_gt_on (hlt : ci.Below caps)
    (himp : StrictOn Mf Tp q caps ci c0 Lev Bd r g y Ty) (hsol : ActualSol μ φ r g y Ty)
    (hbl : Ty ≠ ⊤ → ∀ C : ℝ, ¬ ∀ t, 0 ≤ t → ENNReal.ofReal t < Ty → hnorm 2 (y t) ≤ C)
    (hthr : q caps ≤ |r|) {s T' : ℝ} (hgood : GoodPoint Mf c0 ci r g y s) (hLev : Lev s)
    (hT'0 : 0 < T') (hT' : T' ≤ Tp) (hs : ENNReal.ofReal s < Ty) :
    ENNReal.ofReal (s + T') < Ty := by
  have hs0 := hgood.nonneg
  by_contra hcon
  push Not at hcon
  have hTop : Ty ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hcon
  have hse : s < Ty.toReal := (ENNReal.ofReal_lt_iff_lt_toReal hs0 hTop).1 hs
  have hle : Ty.toReal ≤ s + T' := ENNReal.toReal_le_of_le_ofReal (by linarith) hcon
  have hcaps := piece_first_exit_on hlt himp hsol hthr hgood hLev (T' := Ty.toReal - s)
    (by linarith) (by rw [add_sub_cancel, ENNReal.ofReal_toReal hTop])
  obtain ⟨M, hM⟩ := bdd_initial hsol hs
  refine hbl hTop (max M (caps.yF + caps.BS + 4 * hnorm 2 g)) fun t ht htT ↦ ?_
  rcases le_or_gt t s with h | h
  · exact (hM t ⟨ht, h⟩).trans (le_max_left _ _)
  · have htT' : t < Ty.toReal := (ENNReal.ofReal_lt_iff_lt_toReal ht hTop).1 htT
    have hc := ((hcaps t h.le (by linarith)).1 t ⟨h.le, le_rfl⟩)
    have hy := hnorm_y_le hsol ht htT
    exact hy.trans (le_trans (by linarith [hc.2.1, hc.2.2.2.1]) (le_max_right _ _))

/-- **One piece of the lookahead bootstrap** (as `piece_step`, with `Lev`, the restart on the last
unit only, and the kinetic law on the prefixes where `Bd` holds, which `StrictOn` supplies).  From a
good point `s` with `Lev s` and kinetic level `W₀(s) ≤ W_max`, the lifespan exceeds `s + Tp`, the
caps hold there, and a time `s'` of the last unit with `a_F(s') ≤ M_f` is again a good point with
`Lev s'`, `W₀(s') ≤ W_max`. -/
theorem piece_step_on {Wmax : ℝ} {q₀ : Caps → ℝ} (hlt : ci.Below caps) (hTp : 2 ≤ Tp)
    (himp : StrictOn Mf Tp q caps ci c0 Lev Bd r g y Ty) (hsol : ActualSol μ φ r g y Ty)
    (hbl : Ty ≠ ⊤ → ∀ C : ℝ, ¬ ∀ t, 0 ≤ t → ENNReal.ofReal t < Ty → hnorm 2 (y t) ≤ C)
    (hthr : q caps ≤ |r|) (hthr₀ : q₀ caps ≤ |r|) {W0 : ℝ → ℝ}
    (hW0 : KinFunOn μ q₀ Bd r g y Ty W0) (hMf : 0 ≤ Mf) (hWmax : 5 / 32 ≤ Wmax)
    (hMfW : 1 / 8 + Wmax < Mf ^ 2) {s : ℝ} (hgood : GoodPoint Mf c0 ci r g y s) (hLev : Lev s)
    (hW0s : W0 s ≤ Wmax) (hs : ENNReal.ofReal s < Ty) :
    ∃ s' : ℝ, s + (Tp - 1) ≤ s' ∧ s' ≤ s + Tp ∧ ENNReal.ofReal s' < Ty ∧
      GoodPoint Mf c0 ci r g y s' ∧ Lev s' ∧ W0 s' ≤ Wmax ∧ OnPrefix caps r g y s s' := by
  have hs0 := hgood.nonneg
  set t := s + Tp with ht
  have hlife : ENNReal.ofReal t < Ty :=
    lifespan_gt_on hlt himp hsol hbl hthr hgood hLev (by linarith) le_rfl hs
  have hlifeu : ∀ u, u ≤ t → ENNReal.ofReal u < Ty := fun u hu ↦
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hu) hlife
  have hon : ∀ u ∈ Icc s t, OnPrefix caps r g y s u := fun u hu ↦ by
    have h := onPrefix_closed_on hlt himp hsol hthr hgood hLev (T' := u - s)
      (by linarith [hu.1]) (by linarith [hu.2]) (by rw [add_sub_cancel]; exact hlifeu u hu.2)
    rwa [add_sub_cancel] at h
  have himpt := himp s t hgood hLev
    ⟨⟨hs0, by linarith, hlife, hthr, hon t ⟨by linarith, le_rfl⟩⟩, by linarith⟩
  have hBd := himpt.2.1
  have hW0u : ∀ u ∈ Icc s t, W0 u ≤ Wmax := fun u hu ↦
    ((hW0 caps s u ⟨hs0, hu.1, hlifeu u hu.2, hthr₀, hon u hu⟩
      fun v hv ↦ hBd v ⟨hv.1, hv.2.trans hu.2⟩).2.2.2).trans (max_le hW0s hWmax)
  obtain ⟨hc1, hc2, -, hc4, -⟩ := norms_continuous hsol (b := t) (by linarith) hlife
  have hsub : Icc s t ⊆ Icc 0 t := Icc_subset_Icc hs0 le_rfl
  have hrest : OnPrefix caps r g y (t - 1) t := onPrefix_sub (hon t ⟨by linarith, le_rfl⟩)
    (by linarith) (by linarith) (hc2.mono hsub) (hc4.mono hsub)
  obtain ⟨hk1, -, hk3, -⟩ := hW0 caps (t - 1) t ⟨by linarith, by linarith, hlife, hthr₀, hrest⟩
    fun v hv ↦ hBd v ⟨by linarith [hv.1], hv.2⟩
  have hWt : 0 ≤ W0 t := le_trans (by positivity) (hk1 t ⟨by linarith, le_rfl⟩).1
  have hWt1 := hW0u (t - 1) ⟨by linarith, by linarith⟩
  have hint : (∫ u in (t - 1)..t, fastNorm 1 r g y u ^ 2) < Mf ^ 2 := by
    have e : (t - (t - 1)) / 8 = 1 / 8 := by ring
    rw [e] at hk3
    linarith
  have hex : ∃ u ∈ Icc (t - 1) t, fastNorm 1 r g y u < Mf := by
    by_contra hno
    push Not at hno
    have hmono : (∫ _u in (t - 1)..t, Mf ^ 2) ≤ ∫ u in (t - 1)..t, fastNorm 1 r g y u ^ 2 :=
      intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
        (((hc1.mono (Icc_subset_Icc (by linarith) le_rfl)).pow 2).intervalIntegrable_of_Icc
          (by linarith))
        fun u hu ↦ pow_le_pow_left₀ hMf (hno u hu) 2
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    linarith
  obtain ⟨u, hu, hau⟩ := hex
  have hus : u ∈ Icc s t := ⟨by linarith [hu.1], hu.2⟩
  have hres := himpt.2.2 u ⟨by linarith [hu.1], hu.2⟩
  exact ⟨u, by linarith [hu.1], hu.2, hlifeu u hu.2, ⟨by linarith [hu.1], hau.le, hres.1,
    pointCaps_of_onPrefix himpt.1 hus⟩, hres.2, hW0u u hus, hon u hus⟩

end Step

/-- **Global from strict improvement** (as the private `global_of_strict`): on the maximal
solution of `exists_maximal` at radii `(X, φ)`, the good points (`GoodPoint`, `Lev` and the kinetic
level `W₀ ≤ 2X²`) propagate by `piece_step_on`, so `pieces_induction` gives a global solution with
`‖y‖₂ ≤ y + B_S + 4φ`.  `Lev`, `Bd`, `W₀` depend on the solution, so `himp` is asked for every
solution.  The true-zero kinetic bound uses `Bd 0`, from `StrictOn` on the degenerate piece
`[0, 0]`. -/
theorem global_of_strictOn {X φ Tp Thr : ℝ} {q₀ : Caps → ℝ} {caps ci c0 : Caps}
    (hX : 1 ≤ X) (hTp : 2 ≤ Tp) (hlt : ci.Below caps)
    (himp : ∀ (r : ℝ) (g : Field) (y : ℝ → Field) (Ty : ℝ≥0∞), ActualSol X φ r g y Ty →
      ∃ (Lev Bd : ℝ → Prop) (W0 : ℝ → ℝ), Lev 0 ∧
        StrictOn (2 * X) Tp (fun _ ↦ Thr) caps ci c0 Lev Bd r g y Ty ∧
        KinFunOn X q₀ Bd r g y Ty W0)
    {r : ℝ} {g v₀ : Field} (hg : Adm 2 g) (hgφ : hnorm 2 g ≤ φ)
    (hv : Adm 2 v₀) (hvX : hnorm 2 v₀ ≤ X) (hthr : Thr ≤ |r|) (hthr₀ : q₀ caps ≤ |r|)
    (hbase : ∀ y : ℝ → Field, y 0 = v₀ → GoodPoint (2 * X) c0 ci r g y 0) :
    ∃ y : ℝ → Field, IsHeatSol (filtN r 0) (filtG r 0 g) ⊤ y ∧ y 0 = v₀ ∧
      ∀ t, 0 ≤ t → hnorm 2 (y t) ≤ caps.yF + caps.BS + 4 * φ := by
  obtain ⟨Ty, y, hTy0, hy, hy0, hbl⟩ :=
    exists_maximal (majorized_filtN r 0) (goodForce_filtG r 0 hg) hv
  have hsol : ActualSol X φ r g y Ty := ⟨hg, hgφ, hTy0, hy, hy0 ▸ hvX⟩
  obtain ⟨Lev, Bd, W0, hLev0, hst, hW0'⟩ := himp r g y Ty hsol
  have hb := hbase y hy0
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩ := hlt
  have hJ : 0 ≤ caps.JF ∧ 0 ≤ caps.JS := ⟨p8.trans p6.le, p9.trans p7.le⟩
  have hpc : PointCaps caps r g y 0 := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hb.pointCaps
    exact ⟨a1.trans p1.le, a2.trans p2.le, a3.trans p3.le, a4.trans p4.le, a5.trans p5.le,
      a6.trans p10.le, a7.trans p11.le, a8.trans p12.le⟩
  have hlt : ci.Below caps := ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩
  have hon0 : OnPrefix caps r g y 0 0 := onPrefix_point hpc hJ.1 hJ.2
  have hlife0 : ENNReal.ofReal 0 < Ty := by simpa using hTy0
  have hBd0 := (hst 0 0 hb hLev0 ⟨⟨le_rfl, le_rfl, hlife0, hthr, hon0⟩, by linarith⟩).2.1
  have hW00 : W0 0 ≤ 2 * X ^ 2 := by
    have h := (hW0' caps 0 0 ⟨le_rfl, le_rfl, hlife0, hthr₀, hon0⟩ hBd0).2.1 rfl
    nlinarith
  have hstep : ∀ τ : ℝ, 0 ≤ τ → ENNReal.ofReal τ < Ty →
      (GoodPoint (2 * X) c0 ci r g y τ ∧ Lev τ ∧ W0 τ ≤ 2 * X ^ 2) →
      ∃ τ' : ℝ, τ + 1 ≤ τ' ∧ ENNReal.ofReal τ' < Ty ∧
        (GoodPoint (2 * X) c0 ci r g y τ' ∧ Lev τ' ∧ W0 τ' ≤ 2 * X ^ 2) ∧
        ∀ u ∈ Icc τ τ', hnorm 2 (y u) ≤ caps.yF + caps.BS + 4 * φ := by
    rintro τ hτ0 hτT ⟨hgood, hlτ, hWτ⟩
    obtain ⟨s', h1, -, h3, h4, h5, h5', h6⟩ := piece_step_on hlt hTp hst hsol hbl hthr hthr₀ hW0'
      (by linarith) (by nlinarith) (by nlinarith) hgood hlτ hWτ hτT
    refine ⟨s', by linarith, h3, ⟨h4, h5, h5'⟩, fun u hu ↦ ?_⟩
    have hu0 : 0 ≤ u := hτ0.trans hu.1
    have huT : ENNReal.ofReal u < Ty := lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hu.2) h3
    have hc := h6.1 u hu
    have := hnorm_y_le hsol hu0 huT
    linarith [hc.2.1, hc.2.2.2.1]
  obtain ⟨hTop, hB⟩ := pieces_induction le_rfl hstep hTy0 ⟨hb, hLev0, hW00⟩
  subst hTop
  exact ⟨y, hy, hy0, hB⟩

end OVNS.Quant

end
