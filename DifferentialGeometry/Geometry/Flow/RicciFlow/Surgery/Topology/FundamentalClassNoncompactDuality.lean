import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassRealizationCriterion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassFrontier
import DifferentialGeometry.Topology.Homology.NoncompactPoincareDualityFrontier

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set
open scoped Simplicial Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M]

omit [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
theorem subsingleton_integralHomology_compl_singleton_two_of_noncompactPoincareDuality
    [T2Space M] [CompactSpace M] (x : M)
    (h : noncompactPoincareDualityTwoOne ({x}ᶜ : Set M))
    (h₁ : Subsingleton (integralSingularCohomology 1 M)) :
    Subsingleton (IntegralHomology ({x}ᶜ : Set M) 2) :=
  @subsingleton_integralSingularHomology_two_compl_singleton_of_noncompactPoincareDuality
    M _ _ _ x h h₁

omit [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
theorem subsingleton_integralHomology_compl_singleton_two_of_noncompactPoincareDuality_of_simplyConnected
    [T2Space M] [CompactSpace M] [SimplyConnectedSpace M] (x : M)
    (h : noncompactPoincareDualityTwoOne ({x}ᶜ : Set M)) :
    Subsingleton (IntegralHomology ({x}ᶜ : Set M) 2) :=
  subsingleton_integralHomology_compl_singleton_two_of_noncompactPoincareDuality x h
    (integralSingularCohomology_one_subsingleton (X := M))

omit [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
theorem absoluteToRelative_surjective_of_noncompactPoincareDuality_punctured
    [T2Space M] [CompactSpace M] [SimplyConnectedSpace M] (x : M)
    (h : noncompactPoincareDualityTwoOne ({x}ᶜ : Set M)) :
    Function.Surjective (absoluteToRelative M ({x}ᶜ) 3) :=
  absoluteToRelative_surjective_of_subsingleton_punctured x
    (subsingleton_integralHomology_compl_singleton_two_of_noncompactPoincareDuality_of_simplyConnected
      x h)

theorem exists_unique_fundamentalClass_of_noncompactPoincareDuality_punctured
    (o : TangentOrientationSection M) [ConnectedSpace M] [T2Space M] [CompactSpace M]
    (hprop : localClassRealizationLocallyConstant o) (x₀ : M) [SimplyConnectedSpace M]
    (h : noncompactPoincareDualityTwoOne ({x₀}ᶜ : Set M))
    (h₃ : Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 3)) :
    ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x :=
  exists_unique_fundamentalClass_of_subsingleton_punctured o hprop x₀
    (subsingleton_integralHomology_compl_singleton_two_of_noncompactPoincareDuality_of_simplyConnected
      x₀ h) h₃

theorem exists_unique_fundamentalClass_of_noncompactPoincareDuality_of_noncompactTopHomologyVanishing
    (o : TangentOrientationSection M) [ConnectedSpace M] [T2Space M] [CompactSpace M]
    (hprop : localClassRealizationLocallyConstant o) (x₀ : M) [SimplyConnectedSpace M]
    (h : noncompactPoincareDualityTwoOne ({x₀}ᶜ : Set M))
    (hv : noncompactThreeManifoldTopHomologyVanishing.{u}) :
    ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x :=
  exists_unique_fundamentalClass_of_subsingleton_punctured o hprop x₀
    (subsingleton_integralHomology_compl_singleton_two_of_noncompactPoincareDuality_of_simplyConnected
      x₀ h)
    (subsingleton_integralHomology_compl_singleton_of_noncompactThreeManifoldTopHomologyVanishing
      hv x₀)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
