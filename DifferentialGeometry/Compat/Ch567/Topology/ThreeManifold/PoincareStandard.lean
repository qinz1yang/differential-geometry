import DifferentialGeometry.Topology.ThreeManifold.PoincareStandard

/-!
# PORT567 compatibility names: standard connected-sum presentations

The chapters 5–7 workbench is written against the later PC layout, where the declarations of
`Topology/ThreeManifold/PoincareStandard.lean` carry the names `StandardConnectedSumPresentation`
and `isStandardConnectedSum…`. In the integration layout the same declarations (identical
fields, statements and proofs) are named `PoincareStandardPresentation` and `isPoincareStandard…`.
This module only provides the later names as reducible aliases / restated theorems of the
existing declarations.
-/

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

/-- Alias of `PoincareStandardPresentation` (later-layout name). -/
abbrev StandardConnectedSumPresentation (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] :=
  PoincareStandardPresentation M

/-- Alias of `isPoincareStandard` (later-layout name). -/
abbrev isStandardConnectedSum (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] : Prop :=
  isPoincareStandard M

theorem isStandardConnectedSum_of_diffeomorph
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    (f : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ N) (hN : isStandardConnectedSum N) :
    isStandardConnectedSum M :=
  isPoincareStandard_of_diffeomorph f hN

theorem isStandardConnectedSum_of_standard_factor (M : ConnectedClosedOrientedManifold.{u} 3)
    (h : isStandardFactor M) : isStandardConnectedSum M.Carrier :=
  isPoincareStandard_of_standard_factor M h

end DifferentialGeometry.Topology
