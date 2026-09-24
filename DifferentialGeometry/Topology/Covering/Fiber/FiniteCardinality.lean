import DifferentialGeometry.Topology.Covering.Fiber.Equivalence
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Data.Set.Card

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Topology.Covering

theorem exists_encard_fiber_eq_natCast_of_compact
    {E X : Type*} [TopologicalSpace E] [CompactSpace E]
    [TopologicalSpace X] [T1Space X] [PathConnectedSpace X]
    {p : E → X} (hp : IsCoveringMap p) :
    ∃ k : ℕ, ∀ y : X, {x : E | p x = y}.encard = (k : ℕ∞) := by
  classical
  let y₀ : X := Classical.choice inferInstance
  refine ⟨(p ⁻¹' {y₀}).ncard, ?_⟩
  intro y
  let := Geometry.Riemannian.Topology.UniversalCover.isCoveringMap_fibre_finite_of_compact hp y
  have hcard : (p ⁻¹' {y}).ncard = (p ⁻¹' {y₀}).ncard :=
    Nat.card_congr (Equiv.ofBijective
      (hp.monodromy (.mk (PathConnectedSpace.somePath y y₀)))
      (hp.monodromy_bijective _))
  change (p ⁻¹' {y}).encard = _
  rw [← Set.coe_ncard_eq_encard, hcard]

end DifferentialGeometry.Topology.Covering
