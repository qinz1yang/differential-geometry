import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HomotopyGroupsAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RfsHomotopyGroupsHypothesis

noncomputable section

universe u

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology (cubeSphereFundamentalClass HurewiczLowDegreeHypothesis
  hurewiczLowDegreeHypothesis_iff_frontier homotopyTwo_subsingleton_of_sphereHurewiczTwoCanonical
  integralSingularHomology IsSphereHomologyGenerator)

variable {M : Type u} [TopologicalSpace M] [SimplyConnectedSpace M]

theorem hurewiczLowDegreeHypothesis_iff_forall_homotopyGroup_two_and_hurewiczThree_bijective
    (hH₂ : Subsingleton (integralSingularHomology 2 M))
    (hgen : IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass) :
    HurewiczLowDegreeHypothesis M ↔
      ∀ q : M, Subsingleton (HomotopyGroup (Fin 2) M q) ∧
        Function.Bijective (hurewiczThree q) := by
  constructor
  · intro h
    have htwo : ∀ q : M, Subsingleton (HomotopyGroup (Fin 2) M q) := fun q =>
      homotopyTwo_subsingleton_of_sphereHurewiczTwoCanonical
        (hurewiczLowDegreeHypothesis_iff_frontier.mp h).1 hH₂ q
    refine fun q => ⟨htwo q, ?_⟩
    exact (sphereHurewiczThreeCanonical_iff_forall_bijective_hurewiczThree hgen).mp
      (hurewiczLowDegreeHypothesis_iff_frontier.mp h).2 q (htwo q)
  · intro h
    exact hurewiczLowDegreeHypothesis_iff_frontier.mpr
      ⟨(sphereHurewiczTwoCanonical_iff_forall_subsingleton_homotopyGroup hH₂).mpr
          (fun q => (h q).1),
        (sphereHurewiczThreeCanonical_iff_forall_bijective_hurewiczThree hgen).mpr
          (fun q _ => (h q).2)⟩

theorem rfs_homotopy_groups_hypothesis_iff_forall_homotopyGroup_two_and_hurewiczThree_bijective
    (hH₂ : Subsingleton (integralSingularHomology 2 M))
    (hgen : IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass) :
    RfsHomotopyGroupsHypothesis M ↔
      ∀ q : M, Subsingleton (HomotopyGroup (Fin 2) M q) ∧
        Function.Bijective (hurewiczThree q) := by
  constructor
  · intro h
    exact
      (hurewiczLowDegreeHypothesis_iff_forall_homotopyGroup_two_and_hurewiczThree_bijective
        hH₂ hgen).mp h.hurewiczLowDegree
  · intro h
    exact ⟨hH₂, hgen,
      (hurewiczLowDegreeHypothesis_iff_forall_homotopyGroup_two_and_hurewiczThree_bijective
        hH₂ hgen).mpr h⟩

theorem subsingleton_homotopyGroup_two_of_forall_hurewiczLowDegree
    (hHLD : ∀ (X : Type u) [TopologicalSpace X] [SimplyConnectedSpace X],
      HurewiczLowDegreeHypothesis X)
    (hH₂ : Subsingleton (integralSingularHomology 2 M)) (q : M) :
    Subsingleton (HomotopyGroup (Fin 2) M q) :=
  homotopyTwo_subsingleton_of_sphereHurewiczTwoCanonical
    (hurewiczLowDegreeHypothesis_iff_frontier.mp (hHLD M)).1 hH₂ q

theorem bijective_hurewiczThree_of_forall_hurewiczLowDegree
    (hHLD : ∀ (X : Type u) [TopologicalSpace X] [SimplyConnectedSpace X],
      HurewiczLowDegreeHypothesis X)
    (hH₂ : Subsingleton (integralSingularHomology 2 M))
    (hgen : IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass) (q : M) :
    Function.Bijective (hurewiczThree q) :=
  (sphereHurewiczThreeCanonical_iff_forall_bijective_hurewiczThree hgen).mp
    (hurewiczLowDegreeHypothesis_iff_frontier.mp (hHLD M)).2 q
    (subsingleton_homotopyGroup_two_of_forall_hurewiczLowDegree hHLD hH₂ q)

theorem rfs_homotopy_groups_of_forall_hurewiczLowDegree
    (hHLD : ∀ (X : Type u) [TopologicalSpace X] [SimplyConnectedSpace X],
      HurewiczLowDegreeHypothesis X)
    (hH₂ : Subsingleton (integralSingularHomology 2 M))
    (hgen : IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass) (q : M) :
    Subsingleton (HomotopyGroup (Fin 2) M q) ∧ Function.Bijective (hurewiczThree q) :=
  ⟨subsingleton_homotopyGroup_two_of_forall_hurewiczLowDegree hHLD hH₂ q,
    bijective_hurewiczThree_of_forall_hurewiczLowDegree hHLD hH₂ hgen q⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
