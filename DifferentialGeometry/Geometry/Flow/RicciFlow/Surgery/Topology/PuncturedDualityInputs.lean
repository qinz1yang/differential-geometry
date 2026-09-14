import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassDuality
import DifferentialGeometry.Topology.Homology.LowDegreeHurewiczNormalization

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]

def PuncturedDualityInputs (o : TangentOrientationSection M) (x₀ : M) : Prop :=
  localClassRealizationLocallyConstant o ∧
    poincareDualityTwoOne ({x₀}ᶜ : Set M) ∧
      Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 3)

omit [T2Space M] [CompactSpace M] in
theorem existsUnique_localFundamentalClass_and_subsingleton_compl_of_puncturedDualityIns
    (o : TangentOrientationSection M) (x₀ : M)
    [SimplyConnectedSpace ↥({x₀}ᶜ : Set M)]
    (h : PuncturedDualityInputs o x₀) :
    (∃! z : IntegralHomology M 3, ∀ x : M,
        absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x) ∧
      Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 2) :=
  ⟨exists_unique_fundamentalClass_of_poincareDuality_punctured o h.1 x₀ h.2.1 h.2.2,
    subsingleton_integralHomology_compl_singleton_two_of_poincareDuality x₀ h.2.1⟩

omit [T2Space M] [CompactSpace M] [ConnectedSpace M] in
theorem subsingleton_integralSingularHomology_two_iff_relative_of_puncturedDualityIns
    {o : TangentOrientationSection M} (x₀ : M) [SimplyConnectedSpace ↥({x₀}ᶜ : Set M)]
    (h : PuncturedDualityInputs o x₀)
    (h₁ : Subsingleton (integralSingularHomology 1 ({x₀}ᶜ : Set M))) :
    Subsingleton (integralSingularHomology 2 M) ↔
      Subsingleton (integralRelativeHomology 2 ({x₀}ᶜ : Set M)) :=
  subsingleton_integralSingularHomology_two_iff_subsingleton_compl_and_relative x₀ h₁
    (subsingleton_integralHomology_compl_singleton_two_of_poincareDuality x₀ h.2.1)

omit [CompactSpace M] in
theorem puncturedDualityInputs_of_noncompactThreeManifoldTopHomologyVanishing
    (o : TangentOrientationSection M) (x₀ : M)
    [SimplyConnectedSpace ↥({x₀}ᶜ : Set M)]
    (hprop : localClassRealizationLocallyConstant o)
    (h : poincareDualityTwoOne ({x₀}ᶜ : Set M))
    (hv : noncompactThreeManifoldTopHomologyVanishing.{u}) :
    PuncturedDualityInputs o x₀ :=
  ⟨hprop, h,
    subsingleton_integralHomology_compl_singleton_of_noncompactThreeManifoldTopHomologyVanishing
      hv x₀⟩

theorem not_subsingleton_integralSingularHomology_two_punctured_threeSpace :
    ¬ Subsingleton (integralSingularHomology 2 ({0}ᶜ : Set ThreeSpace)) :=
  not_subsingleton_integralSingularHomology_two_punctured_of_finrank_eq_three ThreeSpace
    (by simp)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
