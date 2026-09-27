import DifferentialGeometry.Topology.Covering.DeckGroup
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

set_option autoImplicit false

noncomputable section

open Set Function
namespace DifferentialGeometry

private theorem real_isometry_translation_or_reflection (f : ℝ ≃ᵢ ℝ) :
    (∀ x, f x = x + f 0) ∨ (∀ x, f x = -x + f 0) := by
  let L := f.toRealLinearIsometryEquiv
  have hL (x : ℝ) : L x = x * L 1 := by simpa using L.map_smul x (1 : ℝ)
  have hnorm : |L 1| = 1 := by
    rw [← Real.norm_eq_abs]
    exact (L.norm_map (1 : ℝ)).trans (norm_one)
  rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.mp hnorm with hpos | hneg
  · left; intro x; have heq := hL x; rw [hpos, mul_one] at heq
    change f x - f 0 = x at heq; linarith
  · right; intro x; have heq := hL x; rw [hneg, mul_neg_one] at heq
    change f x - f 0 = -x at heq; linarith

theorem coveringDeckGroup_translation_law
    {X : Type*} [TopologicalSpace X] {p : ℝ → X} (hp : IsCoveringMap p)
    (gamma : coveringDeckGroup p)
    (hiso : Isometry (gamma.1 : ℝ → ℝ)) :
    ∀ x : ℝ, gamma • x = x + gamma • (0 : ℝ) := by
  let e : ℝ ≃ᵢ ℝ := { toEquiv := gamma.1, isometry_toFun := hiso }
  rcases real_isometry_translation_or_reflection e with hpos | hneg
  · exact hpos
  · have hfix : gamma • (e 0 / 2) = e 0 / 2 := by
      change e (e 0 / 2) = e 0 / 2; rw [hneg]; ring
    have hidentity := coveringDeckGroup_eq_one_of_apply_eq hp gamma (e 0 / 2) hfix
    subst gamma; simp

theorem coveringDeckGroup_zero_hom
    {X : Type*} [TopologicalSpace X] {p : ℝ → X} (hp : IsCoveringMap p)
    (hIso : ∀ gamma : coveringDeckGroup p, Isometry (gamma.1 : ℝ → ℝ)) :
    ∃ τ : Additive (coveringDeckGroup p) →+ ℝ,
      ∀ gamma x, gamma • x = x + τ (.ofMul gamma) := by
  let τ : Additive (coveringDeckGroup p) →+ ℝ :=
    { toFun := fun gamma => (Additive.toMul gamma) • (0 : ℝ)
      map_zero' := by simp
      map_add' := by
        intro a b
        change (Additive.toMul (a + b)) • (0 : ℝ) =
          (Additive.toMul a) • (0 : ℝ) + (Additive.toMul b) • (0 : ℝ)
        rw [show Additive.toMul (a + b) = Additive.toMul a * Additive.toMul b by rfl]
        rw [mul_smul, coveringDeckGroup_translation_law hp (Additive.toMul a) (hIso _)]
        rw [coveringDeckGroup_translation_law hp (Additive.toMul b) (hIso _)]
        ring }
  refine ⟨τ, ?_⟩
  intro gamma x
  exact coveringDeckGroup_translation_law hp gamma (hIso gamma) x



theorem coveringDeckGroup_translation_range_cyclic
    {X : Type*} [TopologicalSpace X] {p : ℝ → X} (hp : IsCoveringMap p)
    (hIso : ∀ gamma : coveringDeckGroup p, Isometry (gamma.1 : ℝ → ℝ))
    (U : Set ℝ) (hU0 : (0 : ℝ) ∈ U) (hUopen : IsOpen U)
    (hUdisc : ∀ gamma : coveringDeckGroup p,
      ((gamma • ·) '' U ∩ U).Nonempty → gamma = 1) :
    ∃ (τ : Additive (coveringDeckGroup p) →+ ℝ) (c : ℝ),
      (∀ gamma x, gamma • x = x + τ (.ofMul gamma)) ∧
      AddMonoidHom.range τ = AddSubgroup.zmultiples c := by
  obtain ⟨τ, hτ⟩ := coveringDeckGroup_zero_hom hp hIso
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hUopen 0 hU0
  have hdisj : Disjoint (τ.range : Set ℝ) (Ioo 0 δ) := by
    rw [Set.disjoint_left]
    rintro y ⟨gamma, rfl⟩ hy
    let gamma' : coveringDeckGroup p := Additive.toMul gamma
    have hzero : gamma' • (0 : ℝ) = τ gamma := by simpa [gamma'] using hτ gamma' 0
    have hmem : gamma' • (0 : ℝ) ∈ U := by
      rw [hzero]
      exact hδU (by simpa [Real.dist_eq, abs_of_pos hy.1] using hy.2)
    have hinter : ((gamma' • ·) '' U ∩ U).Nonempty :=
      ⟨gamma' • (0 : ℝ), ⟨0, hU0, rfl⟩, hmem⟩
    have hg : gamma' = 1 := hUdisc gamma' hinter
    have hg0 : gamma = 0 := by exact_mod_cast hg
    subst hg0
    simpa using hy.1
  obtain ⟨c, hclosure⟩ := AddSubgroup.cyclic_of_isolated_zero hδ hdisj
  exact ⟨τ, c, hτ, hclosure.trans (AddSubgroup.zmultiples_eq_closure c).symm⟩



theorem nonzero_translation_period_of_compact_base
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {p : ℝ → X} (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    (τ : Additive (coveringDeckGroup p) →+ ℝ)
    (hτ : ∀ gamma x, gamma • x = x + τ (.ofMul gamma))
    (hτrange : AddMonoidHom.range τ = AddSubgroup.zmultiples 0) :
    False := by
  have hgamma : ∀ gamma : coveringDeckGroup p, gamma = 1 := by
    intro gamma
    apply coveringDeckGroup_eq_one_of_apply_eq hp gamma 0
    rw [hτ, show τ (Additive.ofMul gamma) = 0 by
      have hmem : τ (Additive.ofMul gamma) ∈ AddMonoidHom.range τ := ⟨Additive.ofMul gamma, rfl⟩
      rw [hτrange] at hmem
      simpa using hmem]
    simp
  let : LocallyPathConnectedSpace ℝ := LocallyConvexSpace.toLocallyPathConnectedSpace ℝ
  let : SimplyConnectedSpace ℝ := SimplyConnectedSpace.ofContractible ℝ
  have hinj : Function.Injective p := by
    intro x y hxy
    obtain ⟨gamma, hgam⟩ := (coveringDeckGroup_apply_eq_iff (E := ℝ) (X := X) hp).mp hxy
    have hg1 : gamma = 1 := hgamma gamma
    simpa [hg1] using hgam.symm
  let e : ℝ ≃ X := Equiv.ofBijective p ⟨hinj, hsurj⟩
  let eh : ℝ ≃ₜ X := e.toHomeomorphOfContinuousOpen hp.continuous hp.isOpenMap
  have hc : CompactSpace ℝ := eh.symm.compactSpace
  exact (not_compactSpace_iff.mpr inferInstance) hc



theorem real_cover_fiber_eq_iff_translation_range
    {X : Type*} [TopologicalSpace X] {p : ℝ → X} (hp : IsCoveringMap p)
    (τ : Additive (coveringDeckGroup p) →+ ℝ)
    (hτ : ∀ gamma x, gamma • x = x + τ (.ofMul gamma)) (x y : ℝ) :
    p x = p y ↔ x - y ∈ τ.range := by
  let : LocallyPathConnectedSpace ℝ := LocallyConvexSpace.toLocallyPathConnectedSpace ℝ
  constructor
  · intro hxy
    obtain ⟨gamma, hgam⟩ := (coveringDeckGroup_apply_eq_iff hp).mp hxy
    refine ⟨Additive.ofMul gamma, ?_⟩
    change gamma • y = x at hgam
    rw [hτ] at hgam
    linarith
  · rintro ⟨a, ha⟩
    have hgam : (Additive.toMul a) • y = x := by
      rw [hτ]
      change y + τ a = x
      linarith
    rw [← hgam]
    exact coveringDeckGroup_map _ _

private theorem exists_addCircle_homeomorph_with_translation_range
    {X : Type*} [TopologicalSpace X] {p : ℝ → X} (hp : IsCoveringMap p)
    (hsurj : Function.Surjective p)
    (hIso : ∀ gamma : coveringDeckGroup p, Isometry (gamma.1 : ℝ → ℝ)) :
    ∃ (c : ℝ) (e : AddCircle c ≃ₜ X)
      (τ : Additive (coveringDeckGroup p) →+ ℝ),
      (∀ t : ℝ, e t = p t) ∧
      (∀ gamma x, gamma • x = x + τ (.ofMul gamma)) ∧
      AddMonoidHom.range τ = AddSubgroup.zmultiples c := by
  let : LocallyPathConnectedSpace ℝ := LocallyConvexSpace.toLocallyPathConnectedSpace ℝ
  obtain ⟨U, hU, hdisc⟩ := (isQuotientCoveringMap_coveringDeckGroup hp hsurj).disjoint 0
  obtain ⟨τ, c, hτ, hc⟩ := coveringDeckGroup_translation_range_cyclic hp hIso
    (interior U) (mem_interior_iff_mem_nhds.mpr hU) isOpen_interior
    (fun gamma hinter => hdisc gamma (hinter.mono (by grw [interior_subset])))
  have hker (x y : ℝ) : p x = p y ↔ (x : AddCircle c) = y := by
    rw [real_cover_fiber_eq_iff_translation_range hp τ hτ, hc]
    exact QuotientAddGroup.eq_iff_sub_mem.symm
  have hper : Function.Periodic p c := by
    intro t
    apply (hker _ _).mpr
    simp
  let q : AddCircle c → X := hper.lift
  have hq (t : ℝ) : q t = p t := rfl
  have hqcont : Continuous q := by
    apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    exact hp.continuous
  have hqinj : Function.Injective q := by
    intro x y
    induction x using QuotientAddGroup.induction_on with | H x =>
      induction y using QuotientAddGroup.induction_on with | H y =>
        exact (hker x y).mp
  have hqsurj : Function.Surjective q := by
    intro x
    obtain ⟨t, ht⟩ := hsurj x
    exact ⟨t, ht⟩
  have hqopen : IsOpenMap q := by
    intro S hS
    have heq : q '' S = p '' (((↑) : ℝ → AddCircle c) ⁻¹' S) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        induction y using QuotientAddGroup.induction_on with | H y =>
          exact ⟨y, hy, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
    rw [heq]
    exact hp.isOpenMap _ (hS.preimage (AddCircle.continuous_mk' c))
  let e : AddCircle c ≃ₜ X :=
    (Equiv.ofBijective q ⟨hqinj, hqsurj⟩).toHomeomorphOfContinuousOpen hqcont hqopen
  exact ⟨c, e, τ, hq, hτ, hc⟩

theorem exists_addCircle_homeomorph_of_real_cover_isometric_decks
    {X : Type*} [TopologicalSpace X] {p : ℝ → X} (hp : IsCoveringMap p)
    (hsurj : Function.Surjective p)
    (hIso : ∀ gamma : coveringDeckGroup p, Isometry (gamma.1 : ℝ → ℝ)) :
    ∃ (c : ℝ) (e : AddCircle c ≃ₜ X), ∀ t : ℝ, e t = p t := by
  obtain ⟨c, e, τ, he, hτ, hc⟩ :=
    exists_addCircle_homeomorph_with_translation_range hp hsurj hIso
  exact ⟨c, e, he⟩



theorem exists_circle_homeomorph_of_compact_real_cover_isometric_decks
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {p : ℝ → X} (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    (hIso : ∀ gamma : coveringDeckGroup p, Isometry (gamma.1 : ℝ → ℝ)) :
    ∃ (c : ℝ) (e : Circle ≃ₜ X) (hc : c ≠ 0),
      ∀ t : ℝ, e (AddCircle.homeomorphCircle hc (t : AddCircle c)) = p t := by
  obtain ⟨c, e, τ, he, hτ, hcrange⟩ :=
    exists_addCircle_homeomorph_with_translation_range hp hsurj hIso
  have hne : c ≠ 0 := by
    intro hc
    subst hc
    exact nonzero_translation_period_of_compact_base hp hsurj τ hτ hcrange
  let E : Circle ≃ₜ X := (AddCircle.homeomorphCircle hne).symm.trans e
  refine ⟨c, E, hne, ?_⟩
  intro t
  simpa [E] using he t

end DifferentialGeometry
