import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HurewiczCube
import DifferentialGeometry.Topology.Homology.HurewiczLowDegreeAssembly
import DifferentialGeometry.Topology.Homology.CubeSphereGenerator
import DifferentialGeometry.Topology.Homotopy.ManifoldVanishing

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Set
open scoped Topology unitInterval Simplicial Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [hT2 : T2Space M] [hCompact : CompactSpace M]
    [hConnected : ConnectedSpace M] [hSimplyConnected : SimplyConnectedSpace M]

include hT2 hCompact hSimplyConnected
omit hConnected

theorem rfs_homotopy_groups (q : M) :
    Subsingleton (HomotopyGroup (Fin 2) M q) ∧ Function.Bijective (hurewiczThree q) := by
  have htwo : Subsingleton (HomotopyGroup (Fin 2) M q) :=
    DifferentialGeometry.Topology.homotopyGroup_two_subsingleton_of_simplyConnected_of_finrank_eq_three
      (E := ThreeSpace) (by simp [ThreeSpace]) q
  exact ⟨htwo,
    DifferentialGeometry.Topology.hurewiczThree_bijective_of_sphereHurewiczThreeCanonical
      q htwo DifferentialGeometry.Topology.cubeSphereFundamentalClass_isSphereHomologyGenerator
      DifferentialGeometry.Topology.sphereHurewiczThreeCanonical_of_hurewicz_three_isomorphism⟩

def positiveHurewiczEquiv (q : M) :
    HomotopyGroup (Fin 3) M q ≃* Multiplicative (IntegralHomology M 3) :=
  MulEquiv.ofBijective (hurewiczThreeHom q) (rfs_homotopy_groups q).2

theorem exists_unique_positiveHomotopyClass (o : TangentOrientationSection M) (q : M) :
    ∃! alpha : HomotopyGroup (Fin 3) M q,
      hurewiczThree q alpha = fundamentalClass o := by
  exact (rfs_homotopy_groups q).2.existsUnique _

def positiveHomotopyClass (o : TangentOrientationSection M) (q : M) :
    HomotopyGroup (Fin 3) M q :=
  Classical.choose (exists_unique_positiveHomotopyClass o q)

theorem positiveHomotopyClass_hurewicz (o : TangentOrientationSection M) (q : M) :
    hurewiczThree q (positiveHomotopyClass o q) = fundamentalClass o :=
  (Classical.choose_spec (exists_unique_positiveHomotopyClass o q)).1


include hConnected

theorem positiveHomotopyClass_infiniteOrder (o : TangentOrientationSection M) (q : M) :
    Function.Injective (fun z : ℤ => positiveHomotopyClass o q ^ z) := by
  intro m n h
  apply (fundamentalClass_generator o).injective
  simpa only [hurewiczThree_zpow, positiveHomotopyClass_hurewicz] using
    congrArg (hurewiczThree q) h

variable {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    [IsManifold ThreeModel ∞ N] [T2Space N] [CompactSpace N]
    [ConnectedSpace N] [SimplyConnectedSpace N]

omit hConnected in
theorem rfs_degree_class_transport (oM : TangentOrientationSection M)
    (oN : TangentOrientationSection N) (f : C(M, N)) (p : M) :
    basedHomotopyMap f p (positiveHomotopyClass oM p) =
      positiveHomotopyClass oN (f p) ^ orientedDegree oM oN f := by
  apply (rfs_homotopy_groups (f p)).2.injective
  rw [hurewiczThree_natural, positiveHomotopyClass_hurewicz, orientedDegree_spec,
    hurewiczThree_zpow, positiveHomotopyClass_hurewicz]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
