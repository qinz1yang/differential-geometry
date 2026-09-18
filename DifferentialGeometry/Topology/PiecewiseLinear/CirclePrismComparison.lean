/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleAnnulusOrientation

/-! PL annulus maps and arc strips with prescribed end maps. -/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem IsPLCirclePositive.of_leftInverse {S : Set E} {u v : E → E}
    (hpos : IsPLCirclePositive S u) (hu : BijOn u S S) (hv : MapsTo v S S)
    (hvu : ∀ x ∈ S, v (u x) = x) : IsPLCirclePositive S v := by
  obtain ⟨g, hgc, hgb, hgu⟩ := hpos
  refine ⟨g, hgc, hgb, hgu.inv (bijective_circleConj hgb hu).2 ?_⟩
  intro θ
  apply hgb.injOn (mem_univ _) (mem_univ _)
  rw [circleConj_spec hgb hv, circleConj_spec hgb hu.mapsTo,
    hvu (g θ) (hgb.mapsTo (mem_univ θ))]

theorem isPLCirclePositive_comp_of_not_isPLCirclePositive [FiniteDimensional ℝ E]
    {S : Set E} (hS : IsPLSphere 1 S) {u v : E → E}
    (hu : IsPLHomeomorphOn u S S) (hv : IsPLHomeomorphOn v S S)
    (hnu : ¬ IsPLCirclePositive S u) (hnv : ¬ IsPLCirclePositive S v) :
    IsPLCirclePositive S (u ∘ v) := by
  obtain ⟨g, hgc, hgb⟩ := exists_loopCircle_param_of_isPLSphere_one hS
  let ψ : loopCircle ≃ₜ loopCircle := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (circleConj g u) (bijective_circleConj hgb hu.bijOn))
    (continuous_circleConj hgc hgb hu.isPiecewiseAffineOn.continuousOn hu.bijOn.mapsTo)
  let χ : loopCircle ≃ₜ loopCircle := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (circleConj g v) (bijective_circleConj hgb hv.bijOn))
    (continuous_circleConj hgc hgb hv.isPiecewiseAffineOn.continuousOn hv.bijOn.mapsTo)
  have hψ : ¬ HasIncreasingCircleLift ψ := fun h => hnu ⟨g, hgc, hgb, h⟩
  have hχ : ¬ HasIncreasingCircleLift χ := fun h => hnv ⟨g, hgc, hgb, h⟩
  refine ⟨g, hgc, hgb,
    (hasIncreasingCircleLift_comp_of_not_hasIncreasingCircleLift ψ χ hψ hχ).congr ?_⟩
  intro θ
  exact circleConj_comp hgb hv.bijOn.mapsTo θ

theorem exists_isPLHomeomorphOn_circle_prod_of_isPLCirclePositive_iff
    [FiniteDimensional ℝ E] {S : Set E} (hS : IsPLSphere 1 S) {u v : E → E}
    (hu : IsPLHomeomorphOn u S S) (hv : IsPLHomeomorphOn v S S)
    (horient : IsPLCirclePositive S u ↔ IsPLCirclePositive S v) :
    ∃ Φ : E × ℝ → E × ℝ,
      IsPLHomeomorphOn Φ (S ×ˢ Icc 0 1) (S ×ˢ Icc 0 1) ∧
        (∀ x ∈ S, Φ (x, 0) = (u x, 0)) ∧ ∀ x ∈ S, Φ (x, 1) = (v x, 1) := by
  let w := v ∘ Function.invFunOn u S
  have hw : IsPLHomeomorphOn w S S := hu.symm.trans hv
  have hwpos : IsPLCirclePositive S w := by
    by_cases hupos : IsPLCirclePositive S u
    · exact (horient.mp hupos).comp
        (hupos.of_leftInverse hu.bijOn hu.symm.bijOn.mapsTo
          fun x hx => hu.bijOn.invOn_invFunOn.1 hx) hu.symm.bijOn.mapsTo
    · have hvneg : ¬ IsPLCirclePositive S v := fun h => hupos (horient.mpr h)
      have huneg : ¬ IsPLCirclePositive S (Function.invFunOn u S) := by
        intro hinv
        exact hupos (hinv.of_leftInverse hu.symm.bijOn hu.bijOn.mapsTo
          fun x hx => hu.bijOn.invOn_invFunOn.2 hx)
      exact isPLCirclePositive_comp_of_not_isPLCirclePositive hS hv hu.symm hvneg huneg
  obtain ⟨Ξ, hΞ, hΞ0, hΞ1⟩ := isPLPseudoIsotopicToId_of_isPLCirclePositive hS hw hwpos
  have hprod : IsPLHomeomorphOn (Prod.map u (id : ℝ → ℝ))
      (S ×ˢ Icc 0 1) (S ×ˢ Icc 0 1) :=
    hu.prodMap isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id
  refine ⟨Ξ ∘ Prod.map u id, hprod.trans hΞ, fun x hx => ?_, fun x hx => ?_⟩
  · exact hΞ0 (u x) (hu.bijOn.mapsTo hx)
  · change Ξ (u x, 1) = (v x, 1)
    rw [hΞ1 (u x) (hu.bijOn.mapsTo hx)]
    change (v (Function.invFunOn u S (u x)), (1 : ℝ)) = (v x, 1)
    rw [hu.bijOn.invOn_invFunOn.1 hx]

theorem exists_isPLHomeomorphOn_arc_prod_of_isPLCirclePositive_iff
    [FiniteDimensional ℝ E] {S A : Set E} (hS : IsPLSphere 1 S)
    {γ : ℝ → E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) A) (hAS : A ⊆ S)
    {u v : E → E} (hu : IsPLHomeomorphOn u S S) (hv : IsPLHomeomorphOn v S S)
    (horient : IsPLCirclePositive S u ↔ IsPLCirclePositive S v) :
    ∃ (T : Set (E × ℝ)) (β : ℝ × ℝ → E × ℝ),
      IsPLHomeomorphOn β (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) T ∧
        T ⊆ S ×ˢ Icc 0 1 ∧
        (∀ s ∈ Icc (0 : ℝ) 1, β (s, 0) = (u (γ s), 0)) ∧
        (∀ s ∈ Icc (0 : ℝ) 1, β (s, 1) = (v (γ s), 1)) ∧
        (∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, (β z).2 = 0 ↔ z.2 = 0) ∧
        ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, (β z).2 = 1 ↔ z.2 = 1 := by
  obtain ⟨Φ, hΦ, hΦ0, hΦ1⟩ :=
    exists_isPLHomeomorphOn_circle_prod_of_isPLCirclePositive_iff hS hu hv horient
  have hA : IsPolyhedron A := ((isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hγ).isPolyhedron
  have hprod : IsPLHomeomorphOn (Prod.map γ (id : ℝ → ℝ))
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) (A ×ˢ Icc 0 1) :=
    hγ.prodMap isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id
  have hsub : A ×ˢ Icc (0 : ℝ) 1 ⊆ S ×ˢ Icc 0 1 := fun z hz => ⟨hAS hz.1, hz.2⟩
  have hrestrict := hΦ.restrict (hA.prod isHPolytope_Icc.isPolyhedron) hsub
  refine ⟨Φ '' (A ×ˢ Icc (0 : ℝ) 1), Φ ∘ Prod.map γ id, hprod.trans hrestrict, ?_,
    fun s hs => ?_, fun s hs => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · rintro y ⟨z, hz, rfl⟩
    exact hΦ.bijOn.mapsTo (hsub hz)
  · exact hΦ0 (γ s) (hAS (hγ.bijOn.mapsTo hs))
  · exact hΦ1 (γ s) (hAS (hγ.bijOn.mapsTo hs))
  · have hmem : (γ z.1, z.2) ∈ S ×ˢ Icc (0 : ℝ) 1 :=
      ⟨hAS (hγ.bijOn.mapsTo hz.1), hz.2⟩
    constructor
    · intro hzero
      exact snd_eq_of_map_level hΦ hu (by norm_num) hΦ0 hmem hzero
    · intro hzero
      change (Φ (γ z.1, z.2)).2 = 0
      rw [hzero, hΦ0 (γ z.1) (hAS (hγ.bijOn.mapsTo hz.1))]
  · have hmem : (γ z.1, z.2) ∈ S ×ˢ Icc (0 : ℝ) 1 :=
      ⟨hAS (hγ.bijOn.mapsTo hz.1), hz.2⟩
    constructor
    · intro hone
      exact snd_eq_of_map_level hΦ hv (by norm_num) hΦ1 hmem hone
    · intro hone
      change (Φ (γ z.1, z.2)).2 = 1
      rw [hone, hΦ1 (γ z.1) (hAS (hγ.bijOn.mapsTo hz.1))]

end DifferentialGeometry.Topology.PiecewiseLinear
