import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LowDegreeHurewiczCubeBridge
import DifferentialGeometry.Topology.Homology.LiftedSphereRelativeBridge

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module
open scoped Topology

universe u

namespace DifferentialGeometry.Topology

abbrev cubeSphereBasepointSet : Set (liftedHomotopySphere.{u} 2) :=
  {ULift.up (cubeSphereBasepoint 2)}

variable {X : Type u} [TopologicalSpace X]

theorem cubeSphereFundamentalClass_isSphereHomologyGenerator_iff_exists_relative_functional :
    IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass.{u} ↔
      ∃ ψ : integralRelativeHomology 3 (cubeSphereBasepointSet.{u}) →ₗ[ℤ] ℤ,
        ψ (integralAbsoluteToRelative 3 (cubeSphereBasepointSet.{u})
          cubeSphereFundamentalClass) = 1 :=
  isSphereHomologyGenerator_iff_exists_relative_functional 2 (by norm_num)
    (ULift.up (cubeSphereBasepoint 2)) cubeSphereFundamentalClass

theorem sphereHurewicz_mul_of_cubeSphereRelativeFunctional
    (hrel : ∃ ψ : integralRelativeHomology 3 (cubeSphereBasepointSet.{u}) →ₗ[ℤ] ℤ,
      ψ (integralAbsoluteToRelative 3 (cubeSphereBasepointSet.{u})
        cubeSphereFundamentalClass) = 1)
    (x : X) (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
    (hc : IsSphereHomologyGenerator 2 c) (a b : HomotopyGroup (Fin 3) X x) :
    sphereHurewicz 2 x c (a * b) =
      sphereHurewicz 2 x c a + sphereHurewicz 2 x c b :=
  sphereHurewicz_mul_of_cubeSphereFundamentalClass_isSphereHomologyGenerator
    ((cubeSphereFundamentalClass_isSphereHomologyGenerator_iff_exists_relative_functional).mpr hrel)
    x c hc a b

end DifferentialGeometry.Topology
