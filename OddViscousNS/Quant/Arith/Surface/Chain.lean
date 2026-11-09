import OddViscousNS.Quant.Arith.Algebra.FewPoints

/-!
# The chain cover (route L12)

The abstract chain/Bézout cover: Salberger's Main Lemma 3.2, in the plane.  A tree of nonzero plane
polynomials vanishing along the path of each point: the irreducible factors of the root that divide
some leaf are the low curves, and every other point lies on a Bézout intersection of a parent and a
child (`plane_bezout`).
-/

open MvPolynomial Finset

namespace OVNS.Quant.Surf

abbrev A2 := MvPolynomial (Fin 2) ℚ

noncomputable local instance : StrongNormalizationMonoid A2 :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

open UniqueFactorizationMonoid in
theorem chain_cover {Ξ : Type} [DecidableEq Ξ] (S₀ : Finset Ξ) (π : Ξ → Fin 2 → ℚ) (L : ℕ)
    {ι : Type} [DecidableEq ι]
    (cl : ℕ → Ξ → ι) (par : ℕ → ι → ι) (Cl : ℕ → Finset ι) (c₀ : ι)
    (R : ℕ → ι → A2)
    (hpar : ∀ a x, par a (cl (a + 1) x) = cl a x)
    (hcl : ∀ x ∈ S₀, ∀ a, cl a x ∈ Cl a)
    (hroot : ∀ x, cl 0 x = c₀)
    (hR : ∀ a c, R a c ≠ 0)
    (hvan : ∀ x ∈ S₀, ∀ a ≤ L, eval (π x) (R a (cl a x)) = 0) :
    ∃ low : Finset A2, low.card ≤ (R 0 c₀).totalDegree ∧
      (∀ H ∈ low, Irreducible H ∧ ∃ c ∈ Cl L, H ∣ R L c) ∧
      ((S₀.image π).filter fun y => ∀ H ∈ low, eval y H ≠ 0).card ≤
        ∑ a ∈ range L, ∑ c ∈ Cl (a + 1),
          (R a (par a c)).totalDegree * (R (a + 1) c).totalDegree := by
  classical
  set S : Finset (Fin 2 → ℚ) := S₀.image π with hS
  set I : Finset A2 := (normalizedFactors (R 0 c₀)).toFinset with hI
  have hIirr : ∀ H ∈ I, Irreducible H := fun H hH =>
    irreducible_of_normalized_factor H (Multiset.mem_toFinset.1 hH)
  have hIdvd : ∀ H ∈ I, H ∣ R 0 c₀ := fun H hH =>
    dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.1 hH)
  -- distinct factors are relatively prime
  have hIrel : ∀ J : Finset A2, J ⊆ I → (J : Set A2).Pairwise (Function.onFun IsRelPrime id) := by
    intro J hJ H hH H' hH' hne
    have h1 := hIirr H (hJ hH)
    have h2 := hIirr H' (hJ hH')
    refine (h1.isRelPrime_iff_not_dvd).2 fun hd => hne ?_
    have hn := fun K (hK : K ∈ I) => (normalize_normalized_factor K (Multiset.mem_toFinset.1 hK))
    have hass : Associated H H' := h1.associated_of_dvd h2 hd
    have := normalize_eq_normalize_iff_associated.2 hass
    rw [(hn H (hJ hH)), (hn H' (hJ hH'))] at this
    exact this
  -- degree of a product of distinct factors dividing `Q ≠ 0`
  have hdeg : ∀ (J : Finset A2) (Q : A2), J ⊆ I → Q ≠ 0 → (∀ H ∈ J, H ∣ Q) →
      (∏ H ∈ J, H).totalDegree ≤ Q.totalDegree ∧ (∏ H ∈ J, H) ∣ Q ∧
        J.card ≤ (∏ H ∈ J, H).totalDegree := by
    intro J Q hJ hQ hd
    have hdvd : (∏ H ∈ J, H) ∣ Q := Finset.prod_dvd_of_isRelPrime (hIrel J hJ) hd
    obtain ⟨W, hW⟩ := hdvd
    have hne : (∏ H ∈ J, H) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hW; exact hQ hW
    have hWne : W ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hW; exact hQ hW
    refine ⟨?_, ⟨W, hW⟩, ?_⟩
    · rw [hW, totalDegree_mul_of_isDomain hne hWne]; omega
    · -- each factor has degree `≥ 1`
      clear hW hWne hne W hd
      induction J using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        have hs : s ⊆ I := fun x hx => hJ (mem_insert_of_mem hx)
        have ha' : a ∈ I := hJ (mem_insert_self _ _)
        have hane : a ≠ 0 := (hIirr a ha').ne_zero
        have hsne : (∏ H ∈ s, H) ≠ 0 := Finset.prod_ne_zero_iff.2 fun x hx => (hIirr x (hs hx)).ne_zero
        rw [Finset.prod_insert ha, totalDegree_mul_of_isDomain hane hsne, card_insert_of_notMem ha]
        have h1 : 1 ≤ a.totalDegree := by
          by_contra hc
          have h0 : a.totalDegree = 0 := by omega
          have hc' := totalDegree_eq_zero_iff_eq_C.mp h0
          have hc0 : a.coeff 0 ≠ 0 := by intro h0'; exact hane (by rw [hc', h0', C_0])
          exact (hIirr a ha').not_isUnit (hc' ▸ (Ne.isUnit hc0).map C)
        have := ih hs
        omega
  have hR0 := hR 0 c₀
  set low := I.filter fun H => ∃ c ∈ Cl L, H ∣ R L c with hlow
  have hlowsub : low ⊆ I := filter_subset _ _
  refine ⟨low, ?_, ?_, ?_⟩
  · -- the number of factors
    have hIall := hdeg I (R 0 c₀) (Subset.refl _) hR0 hIdvd
    exact (card_le_card hlowsub).trans (hIall.2.2.trans hIall.1)
  · intro H hH
    rw [hlow, mem_filter] at hH
    exact ⟨hIirr H hH.1, hH.2⟩
  · -- the exceptional bound
    set Pp : ℕ → ι → Finset A2 := fun a c =>
      I.filter fun H => H ∣ R a (par a c) ∧ ¬ H ∣ R (a + 1) c with hPp
    set T : ℕ → ι → Finset (Fin 2 → ℚ) := fun a c =>
      S.filter fun y => eval y (∏ H ∈ Pp a c, H) = 0 ∧ eval y (R (a + 1) c) = 0 with hT
    have hTcard : ∀ a c, (T a c).card ≤
        (R a (par a c)).totalDegree * (R (a + 1) c).totalDegree := by
      intro a c
      have hsub : Pp a c ⊆ I := filter_subset _ _
      obtain ⟨h1, h2, -⟩ := hdeg (Pp a c) (R a (par a c)) hsub (hR _ _) fun H hH =>
        (mem_filter.1 hH).2.1
      have hrel : IsRelPrime (∏ H ∈ Pp a c, H) (R (a + 1) c) :=
        IsRelPrime.prod_left fun H hH =>
          ((hIirr H (hsub hH)).isRelPrime_iff_not_dvd).2 (mem_filter.1 hH).2.2
      have hPne : (∏ H ∈ Pp a c, H) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun x hx => (hIirr x (hsub hx)).ne_zero
      have := OVNS.Quant.plane_bezout _ _ hrel hPne (hR _ _) (T a c) fun y hy => (mem_filter.1 hy).2
      exact this.trans (Nat.mul_le_mul_right _ h1)
    have hcov : (S.filter fun y => ∀ H ∈ low, eval y H ≠ 0) ⊆
        (range L).biUnion fun a => (Cl (a + 1)).biUnion fun c => T a c := by
      intro y hy
      obtain ⟨hyS, hylow⟩ := mem_filter.1 hy
      obtain ⟨x, hxS, rfl⟩ := mem_image.1 hyS
      -- a factor of the root through `y`
      have h0 := hvan x hxS 0 (Nat.zero_le _)
      rw [hroot] at h0
      obtain ⟨H, hHI, hHy⟩ : ∃ H ∈ I, eval (π x) H = 0 := by
        have hnorm : (normalizedFactors (R 0 c₀)).prod = normalize (R 0 c₀) :=
          prod_normalizedFactors_eq hR0
        have hev : eval (π x) (normalize (R 0 c₀)) = 0 := by
          rw [normalize_apply, map_mul, h0, zero_mul]
        rw [← hnorm, map_multiset_prod, Multiset.prod_eq_zero_iff] at hev
        obtain ⟨H, hH, hH0⟩ := Multiset.mem_map.1 hev
        exact ⟨H, Multiset.mem_toFinset.2 hH, hH0⟩
      have hnotlow : ¬ ∃ c ∈ Cl L, H ∣ R L c := by
        intro hex
        exact hylow H (mem_filter.2 ⟨hHI, hex⟩) hHy
      -- first level where `H` stops dividing
      have hstep : ∃ a, a < L ∧ H ∣ R a (cl a x) ∧ ¬ H ∣ R (a + 1) (cl (a + 1) x) := by
        by_contra hno
        push Not at hno
        have hall : ∀ a, a ≤ L → H ∣ R a (cl a x) := by
          intro a
          induction a with
          | zero => intro _; rw [hroot]; exact hIdvd H hHI
          | succ a ih => intro ha; exact hno a (by omega) (ih (by omega))
        exact hnotlow ⟨cl L x, hcl x hxS L, hall L le_rfl⟩
      obtain ⟨a, haL, h1, h2⟩ := hstep
      simp only [mem_biUnion, mem_range]
      refine ⟨a, haL, cl (a + 1) x, hcl x hxS _, ?_⟩
      refine mem_filter.2 ⟨hyS, ?_, hvan x hxS _ (by omega)⟩
      rw [map_prod]
      refine Finset.prod_eq_zero (i := H) (mem_filter.2 ⟨hHI, ?_, h2⟩) hHy
      rw [hpar]; exact h1
    calc _ ≤ _ := card_le_card hcov
      _ ≤ _ := (card_biUnion_le).trans (Finset.sum_le_sum fun a _ =>
        (card_biUnion_le).trans (Finset.sum_le_sum fun c _ => hTcard a c))

end OVNS.Quant.Surf

