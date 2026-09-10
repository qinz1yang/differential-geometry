import DifferentialGeometry.Topology.Covering.Fiber.Equivalence

noncomputable section

namespace Poincare.Topology

theorem finite_fundamentalGroup_of_finite_fiber_of_simplyConnected_cover
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E] [SimplyConnectedSpace E]
    (p : E → X) (hp : IsCoveringMap p) (x : X) (e : p ⁻¹' {x})
    [Finite (p ⁻¹' {x})] : Finite (FundamentalGroup X x) :=
  Finite.of_equiv _
    (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.fibreEquivFundamentalGroup
      hp x e)

theorem finite_fundamentalGroup_of_compact_simplyConnected_cover
    {X E : Type*} [TopologicalSpace X] [T1Space X]
    [TopologicalSpace E] [CompactSpace E] [SimplyConnectedSpace E]
    (p : E → X) (hp : IsCoveringMap p) (hsurj : Function.Surjective p) (x : X) :
    Finite (FundamentalGroup X x) := by
  let : Finite (p ⁻¹' {x}) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.isCoveringMap_fibre_finite_of_compact
      hp x
  obtain ⟨e, he⟩ := hsurj x
  exact finite_fundamentalGroup_of_finite_fiber_of_simplyConnected_cover p hp x ⟨e, he⟩

end Poincare.Topology
