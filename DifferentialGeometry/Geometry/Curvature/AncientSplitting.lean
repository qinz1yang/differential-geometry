import DifferentialGeometry.Geometry.Curvature.PositiveSectional
import DifferentialGeometry.Topology.Covering.CylindricalModel

open Manifold DifferentialGeometry
open scoped ContDiff

namespace DifferentialGeometry.Geometry

def ancientKappaSolutionSpatialSplitting
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : SmoothRiemannianMetric (𝓡 3) M) : Prop :=
  HasPositiveSectionalCurvature g ∨ Nonempty (DifferentialGeometry.Topology.smoothCylinderCover M)

end DifferentialGeometry.Geometry
