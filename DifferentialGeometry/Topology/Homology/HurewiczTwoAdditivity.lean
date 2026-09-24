import DifferentialGeometry.Topology.Homology.SquareSphereGenerator

noncomputable section

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem sphereHurewicz_two_mul (x : X)
    (c : integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (a b : HomotopyGroup (Fin 2) X x) :
    sphereHurewicz 1 x c (a * b) = sphereHurewicz 1 x c a + sphereHurewicz 1 x c b := by
  obtain ⟨k, rfl⟩ :=
    (isSphereHomologyGenerator_iff_forall_exists_zsmul 1 squareSphereFundamentalClass).mp
      isSphereHomologyGenerator_squareSphereFundamentalClass c
  rw [sphereHurewicz_zsmul, sphereHurewicz_zsmul, sphereHurewicz_zsmul,
    hurewicz_two_mul_squareSphereFundamentalClass, zsmul_add]

end DifferentialGeometry.Topology
