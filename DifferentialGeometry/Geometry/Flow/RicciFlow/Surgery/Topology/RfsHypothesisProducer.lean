import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RfsHomotopyGroupsHypothesis
import DifferentialGeometry.Topology.Homology.SecondHomologyVanishingClosedThreeManifold

noncomputable section

universe u

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology (integralSingularHomology noncompactPoincareDualityTwoOne
  noncompactPoincareDualityTwoOne_iff_subsingleton_integralSingularHomology_two_compl_singleton
  subsingleton_integralSingularHomology_two_of_noncompactPoincareDuality_punctured)

open scoped ContDiff

theorem rfsHomotopyGroupsHypothesis_iff_inputs {M : Type u} [TopologicalSpace M] :
    RfsHomotopyGroupsHypothesis M ↔
      Subsingleton (integralSingularHomology 2 M) ∧
        DifferentialGeometry.Topology.IsSphereHomologyGenerator.{u} 2
            DifferentialGeometry.Topology.cubeSphereFundamentalClass ∧
          DifferentialGeometry.Topology.HurewiczLowDegreeHypothesis M :=
  ⟨fun h => ⟨h.subsingleton_homology_two, h.isSphereHomologyGenerator,
      h.hurewiczLowDegree⟩,
    fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

theorem rfsHomotopyGroupsHypothesis_of_inputs {M : Type u} [TopologicalSpace M]
    (hH₂ : Subsingleton (integralSingularHomology 2 M))
    (hgen : DifferentialGeometry.Topology.IsSphereHomologyGenerator.{u} 2
      DifferentialGeometry.Topology.cubeSphereFundamentalClass)
    (hHLD : DifferentialGeometry.Topology.HurewiczLowDegreeHypothesis M) :
    RfsHomotopyGroupsHypothesis M :=
  ⟨hH₂, hgen, hHLD⟩

theorem rfsHomotopyGroupsHypothesis_of_subsingleton_punctured_homology_two {M : Type u}
    [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    [T2Space M] [CompactSpace M] [SimplyConnectedSpace M] (x : M)
    (hH₂ : Subsingleton (integralSingularHomology 2 ({x}ᶜ : Set M)))
    (hgen : DifferentialGeometry.Topology.IsSphereHomologyGenerator.{u} 2
      DifferentialGeometry.Topology.cubeSphereFundamentalClass)
    (hHLD : DifferentialGeometry.Topology.HurewiczLowDegreeHypothesis M) :
    RfsHomotopyGroupsHypothesis M :=
  have hpd : noncompactPoincareDualityTwoOne ({x}ᶜ : Set M) :=
    (noncompactPoincareDualityTwoOne_iff_subsingleton_integralSingularHomology_two_compl_singleton
      x).mpr hH₂
  rfsHomotopyGroupsHypothesis_of_inputs
    (subsingleton_integralSingularHomology_two_of_noncompactPoincareDuality_punctured x hpd)
    hgen hHLD

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
