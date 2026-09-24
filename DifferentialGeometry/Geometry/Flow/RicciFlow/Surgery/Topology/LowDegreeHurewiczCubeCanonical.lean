import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LowDegreeHurewiczCubeBridge

noncomputable section

universe u

namespace DifferentialGeometry.Topology

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {X : Type u} [TopologicalSpace X]

theorem bijective_hurewiczThree_of_cubeSphereFundamentalClass (x : X)
    (h : IsSphereHurewiczIsomorphism 2 X x cubeSphereFundamentalClass) :
    Function.Bijective (hurewiczThree x) := by
  rw [← sphereHurewicz_cubeSphereFundamentalClass x]
  exact h.1

variable {M : Type u} [TopologicalSpace M] [SimplyConnectedSpace M]

theorem rfs_homotopy_groups_of_cubeSphereHurewiczCanonical (q : M)
    (hH₂ : Subsingleton (integralSingularHomology 2 M))
    (hcanonTwo : SphereHurewiczTwoCanonical M)
    (hcanonThree : ∀ x : M, Subsingleton (HomotopyGroup (Fin 2) M x) →
      IsSphereHurewiczIsomorphism 2 M x cubeSphereFundamentalClass) :
    Subsingleton (HomotopyGroup (Fin 2) M q) ∧ Function.Bijective (hurewiczThree q) :=
  ⟨homotopyTwo_subsingleton_of_sphereHurewiczTwoCanonical hcanonTwo hH₂ q,
    bijective_hurewiczThree_of_cubeSphereFundamentalClass q
      (hcanonThree q (homotopyTwo_subsingleton_of_sphereHurewiczTwoCanonical hcanonTwo hH₂ q))⟩

end DifferentialGeometry.Topology
