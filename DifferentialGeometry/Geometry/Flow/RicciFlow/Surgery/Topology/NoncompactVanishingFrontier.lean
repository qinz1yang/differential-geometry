import DifferentialGeometry.Topology.Homology.NoncompactTopHomologyVanishing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassInputReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassNoncompactDuality

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set
open scoped Simplicial Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M]

def noncompactPoincareDualityTopHomology : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [ChartedSpace ThreeSpace X] [IsManifold ThreeModel ∞ X]
    [ConnectedSpace X] [NoncompactSpace X], noncompactPoincareDualityThreeZero X

theorem noncompactThreeManifoldTopHomologyVanishing_of_noncompactPoincareDualityTopHomology
    (h : noncompactPoincareDualityTopHomology.{u}) :
    noncompactThreeManifoldTopHomologyVanishing.{u} := by
  intro X _ _ _ _ _
  exact subsingleton_integralSingularHomology_three_of_noncompactPoincareDualityThreeZero (h X)

theorem noncompactThreeManifoldTopHomologyVanishing_of_forall_isCompact_subset
    (h : ∀ (X : Type u) [TopologicalSpace X] [ChartedSpace ThreeSpace X]
      [IsManifold ThreeModel ∞ X] [ConnectedSpace X] [NoncompactSpace X],
      ∀ K : Set X, IsCompact K → ∃ U : Set X, K ⊆ U ∧ Subsingleton (IntegralHomology U 3)) :
    noncompactThreeManifoldTopHomologyVanishing.{u} := by
  intro X _ _ _ _ _
  exact integralSingularHomology_succ_subsingleton_of_forall_isCompact_subset 2 (h X)

omit [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
theorem integralRelativeConnecting_two_eq_zero_of_noncompactPoincareDuality_punctured
    [T2Space M] [CompactSpace M] [SimplyConnectedSpace M] (x : M)
    (h : noncompactPoincareDualityTwoOne ({x}ᶜ : Set M)) :
    integralRelativeConnecting 2 ({x}ᶜ : Set M) = 0 :=
  integralRelativeConnecting_eq_zero_of_subsingleton x
    (subsingleton_integralHomology_compl_singleton_two_of_noncompactPoincareDuality_of_simplyConnected
      x h)

theorem exists_unique_fundamentalClass_of_noncompactPoincareDuality_and_topHomologyVanishing
    (o : TangentOrientationSection M) [ConnectedSpace M] [T2Space M] [CompactSpace M]
    (x₀ : M) (hprop : localClassRealizationLocallyConstant o) [SimplyConnectedSpace M]
    (h : noncompactPoincareDualityTwoOne ({x₀}ᶜ : Set M))
    (h₃ : Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 3)) :
    ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x :=
  exists_unique_fundamentalClass_of_locallyConstant_and_connecting_eq_zero_and_subsingleton
    o x₀ hprop
    (integralRelativeConnecting_two_eq_zero_of_noncompactPoincareDuality_punctured x₀ h) h₃

theorem exists_unique_fundamentalClass_of_noncompactPoincareDuality_and_noncompactVanishing
    (o : TangentOrientationSection M) [ConnectedSpace M] [T2Space M] [CompactSpace M]
    (x₀ : M) (hprop : localClassRealizationLocallyConstant o) [SimplyConnectedSpace M]
    (h : noncompactPoincareDualityTwoOne ({x₀}ᶜ : Set M))
    (hv : noncompactThreeManifoldTopHomologyVanishing.{u}) :
    ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x :=
  exists_unique_fundamentalClass_of_noncompactPoincareDuality_and_topHomologyVanishing
    o x₀ hprop h
    (subsingleton_integralHomology_compl_singleton_of_noncompactThreeManifoldTopHomologyVanishing
      hv x₀)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
