import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassRealizationCriterion
import DifferentialGeometry.Topology.Homology.PoincareDualityThreeFrontier

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set
open scoped Simplicial Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M]

omit [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
theorem subsingleton_integralHomology_compl_singleton_two_of_poincareDuality
    (x : M) (h : poincareDualityTwoOne ({x}ᶜ : Set M))
    [SimplyConnectedSpace ({x}ᶜ : Set M)] :
    Subsingleton (IntegralHomology ({x}ᶜ : Set M) 2) :=
  subsingleton_integralSingularHomology_two_of_poincareDualityTwoOne_of_simplyConnected h

theorem exists_unique_fundamentalClass_of_poincareDuality_punctured
    (o : TangentOrientationSection M) [ConnectedSpace M]
    (hprop : localClassRealizationLocallyConstant o) (x₀ : M)
    (h : poincareDualityTwoOne ({x₀}ᶜ : Set M))
    [SimplyConnectedSpace ({x₀}ᶜ : Set M)]
    (h₃ : Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 3)) :
    ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x :=
  exists_unique_fundamentalClass_of_subsingleton_punctured o hprop x₀
    (subsingleton_integralHomology_compl_singleton_two_of_poincareDuality x₀ h) h₃

theorem exists_unique_fundamentalClass_of_poincareDuality_of_noncompactTopHomologyVanishing
    (o : TangentOrientationSection M) [ConnectedSpace M] [T2Space M]
    (hprop : localClassRealizationLocallyConstant o) (x₀ : M)
    (h : poincareDualityTwoOne ({x₀}ᶜ : Set M))
    [SimplyConnectedSpace ({x₀}ᶜ : Set M)]
    (hv : noncompactThreeManifoldTopHomologyVanishing.{u}) :
    ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x :=
  exists_unique_fundamentalClass_of_poincareDuality_punctured o hprop x₀ h
    (subsingleton_integralHomology_compl_singleton_of_noncompactThreeManifoldTopHomologyVanishing
      hv x₀)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
