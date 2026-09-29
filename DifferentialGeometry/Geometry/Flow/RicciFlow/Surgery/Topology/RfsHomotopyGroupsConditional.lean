import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Background
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LowDegreeHurewiczCubeBridge

noncomputable section

universe u

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology (integralSingularHomology)

open scoped ContDiff

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M]

theorem rfs_homotopy_groups_of_canonical_inputs (o : TangentOrientationSection M) (q : M)
    (hH₂ : Subsingleton (integralSingularHomology 2 M))
    (hgen : DifferentialGeometry.Topology.IsSphereHomologyGenerator.{u} 2
      DifferentialGeometry.Topology.cubeSphereFundamentalClass)
    (hcanonTwo : DifferentialGeometry.Topology.SphereHurewiczTwoCanonical M)
    (hcanonThree : DifferentialGeometry.Topology.SphereHurewiczThreeCanonical M) :
    Subsingleton (HomotopyGroup (Fin 2) M q) ∧ Function.Bijective (hurewiczThree q) := by
  let _ := o
  exact DifferentialGeometry.Topology.rfs_homotopy_groups_of_sphereHurewiczCanonical
    q hH₂ hgen hcanonTwo hcanonThree

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
