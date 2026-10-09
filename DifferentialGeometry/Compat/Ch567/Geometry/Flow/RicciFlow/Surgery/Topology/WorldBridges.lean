import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.WorldBridges

/-!
# PORT567 compatibility names: closed oriented 3-manifolds from smooth orientations

In the later PC layout `OrientedThreeStage` is an abbreviation of
`ClosedOrientedManifold 3`, and the stage built from a smooth orientation is called
`ClosedOrientedManifold.ofSmoothOrientation`. In the integration layout `OrientedThreeStage`
is a separate structure with the conversions `OrientedThreeStage.toClosedOrientedManifold` and
`OrientedThreeStage.ofClosedOrientedManifold`, and the constructions are
`OrientedThreeStage.ofSmoothOrientation` / `OrientedThreeStage.smoothOrientation`. This module
provides the later names for `ClosedOrientedManifold 3` by composing the existing conversions;
the round-trip theorem is the existing `OrientedThreeStage.ofSmoothOrientation_smoothOrientation`
transported along `OrientedThreeStage.ofClosedOrientedManifold_toClosedOrientedManifold`.
-/

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- The closed oriented 3-manifold of a smooth orientation: the existing stage
`OrientedThreeStage.ofSmoothOrientation M o`, viewed as a `ClosedOrientedManifold`. -/
abbrev ClosedOrientedManifold.ofSmoothOrientation (M : Type u) [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M] [CompactSpace M]
    (o : DifferentialGeometry.Topology.Manifold.SmoothOrientation ThreeModel M) :
    ClosedOrientedManifold.{u} 3 :=
  (OrientedThreeStage.ofSmoothOrientation M o).toClosedOrientedManifold

/-- The smooth orientation of a closed oriented 3-manifold: the existing
`OrientedThreeStage.smoothOrientation` of `OrientedThreeStage.ofClosedOrientedManifold P`. -/
abbrev ClosedOrientedManifold.smoothOrientation (P : ClosedOrientedManifold.{u} 3) :
    DifferentialGeometry.Topology.Manifold.SmoothOrientation ThreeModel P.Carrier :=
  (OrientedThreeStage.ofClosedOrientedManifold P).smoothOrientation

theorem ClosedOrientedManifold.ofSmoothOrientation_smoothOrientation
    (P : ClosedOrientedManifold.{u} 3) :
    ClosedOrientedManifold.ofSmoothOrientation P.Carrier P.smoothOrientation = P := by
  have h := congrArg OrientedThreeStage.toClosedOrientedManifold
    (OrientedThreeStage.ofSmoothOrientation_smoothOrientation
      (OrientedThreeStage.ofClosedOrientedManifold P))
  rwa [OrientedThreeStage.ofClosedOrientedManifold_toClosedOrientedManifold] at h

end DifferentialGeometry.Topology
