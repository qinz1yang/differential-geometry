import DifferentialGeometry.Topology.Homology.SphereHurewiczPrecomposition
import DifferentialGeometry.Topology.Homology.TetrahedronSpherePairing

noncomputable section

namespace DifferentialGeometry.Topology

universe u

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

def tetrahedronSphereFundamentalClass :
    integralSingularHomology 3 (liftedHomotopySphere.{u} 2) :=
  integralSingularHomologyMap 3
    (liftedHomotopySphereMap 2 Simplex.tetrahedronSphereCollapse)
      (simplexBoundarySphereClass.{u} 2)

theorem sphereHurewicz_integralSingularTetrahedronSphereClass
    (x : X) [Subsingleton (HomotopyGroup (Fin 2) X x)] (σ : integralSingularSimplex 3 X) :
    sphereHurewicz 2 x tetrahedronSphereFundamentalClass
      (integralSingularTetrahedronSphereClass x σ) =
        integralSingularCycleClass 2 X
          (integralSingularThreeCycleProjection x (integralSimplexChain 3 σ)) := by
  rw [tetrahedronSphereFundamentalClass, sphereHurewicz_precompose,
    homotopyGroupSpherePrecompose_integralSingularTetrahedronSphereClass,
    sphereHurewicz_integralSingularConeThreeSphereClass]

end DifferentialGeometry.Topology
