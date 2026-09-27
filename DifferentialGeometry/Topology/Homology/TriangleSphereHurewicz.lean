import DifferentialGeometry.Topology.Homology.SphereHurewiczPrecomposition
import DifferentialGeometry.Topology.Homology.TriangleSpherePairing
import DifferentialGeometry.Topology.Homology.SimplexBoundarySphereGenerator

noncomputable section

namespace DifferentialGeometry.Topology

universe u

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

def triangleSphereFundamentalClass :
    integralSingularHomology 2 (liftedHomotopySphere.{u} 1) :=
  integralSingularHomologyMap 2
    (liftedHomotopySphereMap 1 Simplex.triangleSphereCollapse)
      (simplexBoundarySphereClass.{u} 1)

theorem sphereHurewicz_integralSingularTriangleSphereClass
    (x : X) (σ : integralSingularSimplex 2 X) :
    sphereHurewicz 1 x triangleSphereFundamentalClass
      (integralSingularTriangleSphereClass x σ) =
        integralSingularCycleClass 1 X
          (integralSingularTwoCycleProjection x (integralSimplexChain 2 σ)) := by
  rw [triangleSphereFundamentalClass, sphereHurewicz_precompose,
    homotopyGroupSpherePrecompose_integralSingularTriangleSphereClass,
    sphereHurewicz_integralSingularConeSphereClass]

theorem isSphereHomologyGenerator_triangleSphereFundamentalClass :
    IsSphereHomologyGenerator 1 triangleSphereFundamentalClass.{u} := by
  obtain ⟨e, he⟩ := Simplex.triangleSphereCollapse_homotopyEquiv
  have h := isSphereHomologyGenerator_liftedHomotopySphereMap 1 e
    isSphereHomologyGenerator_simplexBoundarySphereClass
  simpa only [he, triangleSphereFundamentalClass] using h

end DifferentialGeometry.Topology
