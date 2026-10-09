import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.CarrierRechart
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1Standard

/-!
The genuine sphere-cylinder has a transported three-dimensional atlas and whole smooth
identification, providing a carrier rechart beyond the flat linear example.
-/

set_option autoImplicit false

noncomputable section

open Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

abbrev sphereCylinder := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ

abbrev sphereCylinderRechart :=
  CarrierRechart (Homeomorph.refl sphereCylinder) (productModelEquiv 2)

def sphereCylinderRechartDiffeomorph :
    sphereCylinder ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ sphereCylinderRechart :=
  CarrierRechart.diffeomorph (Homeomorph.refl sphereCylinder) (productModelEquiv 2)

theorem sphereCylinderRechartDiffeomorph_point (x : sphereCylinder) :
    (sphereCylinderRechartDiffeomorph x).point = x := rfl

theorem sphereCylinderRechartDiffeomorph_slice
    (z : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (t : ℝ) :
    (sphereCylinderRechartDiffeomorph (z, t)).point.1 = z ∧
      (sphereCylinderRechartDiffeomorph (z, t)).point.2 = t := ⟨rfl, rfl⟩

theorem sphereCylinderRechart_poles_ne :
    sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.northPole, 0) ≠
      sphereCylinderRechartDiffeomorph (GC.GraphManifold.Assembly.southPole, 0) := by
  intro he
  have hp := congrArg (fun q : sphereCylinder => (q.1.val : EuclideanSpace ℝ (Fin 3)) 2)
    (sphereCylinderRechartDiffeomorph.injective he)
  norm_num [GC.GraphManifold.Assembly.northPole, GC.GraphManifold.Assembly.southPole] at hp

end DifferentialGeometry.Geometry.Collapse
