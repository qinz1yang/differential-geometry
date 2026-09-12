import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import DifferentialGeometry.Topology.Manifold.ClosedOriented

noncomputable section

open scoped Manifold ContDiff

universe u

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

def OrientedThreeStage.toClosedOrientedManifold (P : OrientedThreeStage.{u}) :
    DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3 where
  Carrier := P.Carrier
  orientation :=
    { dimension_eq := by simp
      orientation := P.orientation.orientation
      locally_constant := P.orientation.locally_constant }

@[simp] theorem OrientedThreeStage.toClosedOrientedManifold_carrier
    (P : OrientedThreeStage.{u}) :
    P.toClosedOrientedManifold.Carrier = P.Carrier := rfl

@[simp] theorem OrientedThreeStage.toClosedOrientedManifold_orientation_apply
    (P : OrientedThreeStage.{u}) (x : P.Carrier) :
    P.toClosedOrientedManifold.orientation.orientation x = P.orientation.orientation x := rfl

def TangentOrientationSection.ofManifoldOrientation {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (o : DifferentialGeometry.ManifoldOrientation ThreeModel M 3) :
    TangentOrientationSection M where
  orientation := o.orientation
  locally_constant := o.locally_constant

@[simp] theorem TangentOrientationSection.ofManifoldOrientation_apply {M : Type u}
    [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (o : DifferentialGeometry.ManifoldOrientation ThreeModel M 3) (x : M) :
    (TangentOrientationSection.ofManifoldOrientation o).orientation x = o.orientation x :=
  rfl

def OrientedThreeStage.ofClosedOrientedManifold
    (M : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3) :
    OrientedThreeStage.{u} where
  Carrier := M.Carrier
  orientation := TangentOrientationSection.ofManifoldOrientation M.orientation

@[simp] theorem OrientedThreeStage.ofClosedOrientedManifold_carrier
    (M : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3) :
    (OrientedThreeStage.ofClosedOrientedManifold M).Carrier = M.Carrier := rfl

@[simp] theorem OrientedThreeStage.ofClosedOrientedManifold_orientation_apply
    (M : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3) (x : M.Carrier) :
    (OrientedThreeStage.ofClosedOrientedManifold M).orientation.orientation x =
      M.orientation.orientation x := rfl

theorem OrientedThreeStage.ofClosedOrientedManifold_toClosedOrientedManifold
    (M : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3) :
    (OrientedThreeStage.ofClosedOrientedManifold M).toClosedOrientedManifold = M := by
  obtain ⟨Carrier, orientation⟩ := M
  rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
