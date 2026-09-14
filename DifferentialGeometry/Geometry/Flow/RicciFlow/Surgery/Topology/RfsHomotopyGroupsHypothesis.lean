import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RfsHomotopyGroupsConditional
import DifferentialGeometry.Topology.Homology.HurewiczLowDegreeHypothesis

noncomputable section

universe u

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology (integralSingularHomology)

open scoped ContDiff

class RfsHomotopyGroupsHypothesis (M : Type u) [TopologicalSpace M] : Prop where
  subsingleton_homology_two : Subsingleton (integralSingularHomology 2 M)
  isSphereHomologyGenerator : DifferentialGeometry.Topology.IsSphereHomologyGenerator.{u} 2
    DifferentialGeometry.Topology.cubeSphereFundamentalClass
  hurewiczLowDegree : DifferentialGeometry.Topology.HurewiczLowDegreeHypothesis M

theorem rfs_homotopy_groups_hypothesis_of_canonical {M : Type u} [TopologicalSpace M]
    [SimplyConnectedSpace M]
    (hH₂ : Subsingleton (integralSingularHomology 2 M))
    (hgen : DifferentialGeometry.Topology.IsSphereHomologyGenerator.{u} 2
      DifferentialGeometry.Topology.cubeSphereFundamentalClass)
    (hcanonTwo : DifferentialGeometry.Topology.SphereHurewiczTwoCanonical M)
    (hcanonThree : DifferentialGeometry.Topology.SphereHurewiczThreeCanonical M) :
    RfsHomotopyGroupsHypothesis M where
  subsingleton_homology_two := hH₂
  isSphereHomologyGenerator := hgen
  hurewiczLowDegree := And.intro hcanonTwo hcanonThree

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [hT2 : T2Space M] [hCompact : CompactSpace M]
    [hConnected : ConnectedSpace M] [hSimplyConnected : SimplyConnectedSpace M]

omit hT2 hCompact hConnected in
theorem rfs_homotopy_groups_of_hypothesis [h : RfsHomotopyGroupsHypothesis M]
    (o : TangentOrientationSection M) (q : M) :
    Subsingleton (HomotopyGroup (Fin 2) M q) ∧ Function.Bijective (hurewiczThree q) :=
  rfs_homotopy_groups_of_canonical_inputs o q h.subsingleton_homology_two
    h.isSphereHomologyGenerator h.hurewiczLowDegree.1 h.hurewiczLowDegree.2

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
