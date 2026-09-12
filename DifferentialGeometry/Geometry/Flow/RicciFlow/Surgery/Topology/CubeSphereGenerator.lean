import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LowDegreeHurewiczCubeBridge

noncomputable section

namespace DifferentialGeometry.Topology

universe u

theorem isSphereHomologyGenerator_cubeSphereFundamentalClass_of_functional
    (φ : integralSingularHomology 3 (liftedHomotopySphere.{u} 2) →ₗ[ℤ] ℤ)
    (hφ : Function.Surjective φ) (h1 : φ cubeSphereFundamentalClass = 1) :
    IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass :=
  (isSphereHomologyGenerator_iff_exists_surjective_functional 2
    cubeSphereFundamentalClass).mpr ⟨φ, hφ, h1⟩

theorem isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_exists_functional :
    IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass ↔
      ∃ φ : integralSingularHomology 3 (liftedHomotopySphere.{u} 2) →ₗ[ℤ] ℤ,
        Function.Surjective φ ∧ φ cubeSphereFundamentalClass = 1 :=
  isSphereHomologyGenerator_iff_exists_surjective_functional 2 cubeSphereFundamentalClass

theorem isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_forall_exists_zsmul :
    IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass ↔
      ∀ x : integralSingularHomology 3 (liftedHomotopySphere.{u} 2),
        ∃ k : ℤ, x = k • cubeSphereFundamentalClass :=
  isSphereHomologyGenerator_iff_forall_exists_zsmul 2 cubeSphereFundamentalClass

end DifferentialGeometry.Topology
