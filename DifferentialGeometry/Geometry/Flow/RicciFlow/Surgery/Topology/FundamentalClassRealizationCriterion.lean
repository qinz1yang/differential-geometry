import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Homology
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassFrontier
import DifferentialGeometry.Topology.Homology.ChainSupportCompact
import DifferentialGeometry.Topology.Homology.RadialHomotopy
import DifferentialGeometry.Topology.Homology.SphereHomologyVanishing
import DifferentialGeometry.Topology.Homology.SpherePuncture

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set
open scoped Simplicial Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

universe u

variable {X : Type u} [TopologicalSpace X]

theorem subsingleton_integralSingularHomology_succ_iff_forall_isCompact_subset (n : ℕ) :
    Subsingleton (integralSingularHomology (n + 1) X) ↔
      ∀ K : Set X, IsCompact K → ∃ U : Set X, K ⊆ U ∧
        Subsingleton (integralSingularHomology (n + 1) U) := by
  constructor
  · intro h K _
    refine ⟨univ, subset_univ K, ?_⟩
    exact ⟨fun a b => (integralSingularHomologyHomotopyEquiv (n + 1)
      (Homeomorph.Set.univ X).toHomotopyEquiv).injective (Subsingleton.elim _ _)⟩
  · exact integralSingularHomology_succ_subsingleton_of_forall_isCompact_subset n

theorem subsingleton_integralSingularHomology_succ_of_isCompact_subset_contractible
    (n : ℕ) (h : ∀ K : Set X, IsCompact K →
      ∃ U : Set X, K ⊆ U ∧ ContractibleSpace U) :
    Subsingleton (integralSingularHomology (n + 1) X) :=
  integralSingularHomology_succ_subsingleton_of_forall_isCompact_subset n fun K hK => by
    obtain ⟨U, hKU, hU⟩ := h K hK
    exact ⟨U, hKU, integralSingularHomology_subsingleton_of_contractible (n + 1)
      (by omega) U⟩

end DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology

universe u

theorem subsingleton_integralHomology_compl_singleton_of_contractible {X : Type u}
    [TopologicalSpace X] (x : X) [ContractibleSpace ({x}ᶜ : Set X)] (k : ℕ) (hk : k ≠ 0) :
    Subsingleton (IntegralHomology ({x}ᶜ : Set X) k) :=
  integralSingularHomology_subsingleton_of_contractible k hk ({x}ᶜ : Set X)

theorem subsingleton_integralSingularHomology_three_compl_origin :
    Subsingleton (integralSingularHomology 3 ({0}ᶜ : Set ThreeSpace)) :=
  letI : Subsingleton
      (integralSingularHomology 3 (Metric.sphere (0 : ThreeSpace) 1)) :=
    integralSphereHomology_subsingleton 2 3 ThreeSpace (by simp) (by norm_num) (by norm_num)
  ⟨fun a b => (integralPuncturedSpaceSphereHomologyEquiv ThreeSpace 3).injective
    (Subsingleton.elim _ _)⟩

theorem not_subsingleton_integralSingularHomology_two_compl_origin :
    ¬ Subsingleton (integralSingularHomology 2 ({0}ᶜ : Set ThreeSpace)) := by
  intro h
  let e := (integralPuncturedSpaceSphereHomologyEquiv ThreeSpace 2).trans
    (integralSphereTopHomologyEquiv 1 ThreeSpace (by simp))
  have hZ : Subsingleton ℤ :=
    ⟨fun a b => by
      rw [← e.apply_symm_apply a, ← e.apply_symm_apply b,
        Subsingleton.elim (e.symm a) (e.symm b)]⟩
  exact zero_ne_one (Subsingleton.elim (0 : ℤ) 1)

theorem subsingleton_integralSingularHomology_two_punctured_threeSphere
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    Subsingleton (integralSingularHomology 2
      ({v}ᶜ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))) :=
  integralSingularHomology_subsingleton_of_punctured_sphere 2 (by norm_num) v

theorem subsingleton_integralSingularHomology_three_punctured_threeSphere
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    Subsingleton (integralSingularHomology 3
      ({v}ᶜ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))) :=
  integralSingularHomology_subsingleton_of_punctured_sphere 3 (by norm_num) v

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M]

omit [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
theorem absoluteToRelative_surjective_iff_integralRelativeConnecting_eq_zero (x : M) :
    Function.Surjective (absoluteToRelative M ({x}ᶜ) 3) ↔
      integralRelativeConnecting 2 ({x}ᶜ : Set M) = 0 := by
  change Function.Surjective (integralAbsoluteToRelative 3 ({x}ᶜ : Set M)) ↔
    integralRelativeConnecting 2 ({x}ᶜ : Set M) = 0
  have hex := LinearMap.exact_iff.mp (integralRelative_exact_relative 2 ({x}ᶜ : Set M))
  exact ⟨fun h => LinearMap.ker_eq_top.mp (by rw [hex]; exact LinearMap.range_eq_top.mpr h),
    fun h => LinearMap.range_eq_top.mp (by rw [← hex, h, LinearMap.ker_zero])⟩

omit [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
theorem integralRelativeConnecting_eq_zero_of_subsingleton (x : M)
    (h : Subsingleton (integralSingularHomology 2 ({x}ᶜ : Set M))) :
    integralRelativeConnecting 2 ({x}ᶜ : Set M) = 0 :=
  LinearMap.ext fun _ => Subsingleton.elim _ _

omit [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
theorem absoluteToRelative_surjective_of_subsingleton_punctured (x : M)
    (h : Subsingleton (IntegralHomology ({x}ᶜ : Set M) 2)) :
    Function.Surjective (absoluteToRelative M ({x}ᶜ) 3) :=
  (absoluteToRelative_surjective_iff_integralRelativeConnecting_eq_zero x).mpr
    (integralRelativeConnecting_eq_zero_of_subsingleton x h)

omit [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
theorem absoluteToRelative_bijective_of_subsingleton_punctured (x : M)
    (h₂ : Subsingleton (IntegralHomology ({x}ᶜ : Set M) 2))
    (h₃ : Subsingleton (IntegralHomology ({x}ᶜ : Set M) 3)) :
    Function.Bijective (absoluteToRelative M ({x}ᶜ) 3) :=
  ⟨absoluteToRelative_compl_singleton_injective_of_subsingleton x h₃,
    absoluteToRelative_surjective_of_subsingleton_punctured x h₂⟩

omit [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
theorem absoluteToRelative_punctured_threeSphere_surjective
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    Function.Surjective
      (absoluteToRelative (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ({v}ᶜ) 3) :=
  absoluteToRelative_surjective_of_subsingleton_punctured v
    (subsingleton_integralSingularHomology_two_punctured_threeSphere v)

omit [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
theorem absoluteToRelative_punctured_threeSphere_bijective
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    Function.Bijective
      (absoluteToRelative (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ({v}ᶜ) 3) :=
  ⟨absoluteToRelative_compl_singleton_injective_of_subsingleton v
      (subsingleton_integralSingularHomology_three_punctured_threeSphere v),
    absoluteToRelative_punctured_threeSphere_surjective v⟩

theorem exists_unique_fundamentalClass_of_subsingleton_punctured
    (o : TangentOrientationSection M) [ConnectedSpace M]
    (hprop : localClassRealizationLocallyConstant o) (x₀ : M)
    (h₂ : Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 2))
    (h₃ : Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 3)) :
    ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x :=
  exists_unique_fundamentalClass_of_surjective_and_injective o hprop x₀
    (absoluteToRelative_surjective_of_subsingleton_punctured x₀ h₂)
    (absoluteToRelative_compl_singleton_injective_of_subsingleton x₀ h₃)

theorem exists_fundamentalClass_generator_of_subsingleton_punctured
    (o : TangentOrientationSection M) [ConnectedSpace M]
    (hprop : localClassRealizationLocallyConstant o) (x₀ : M)
    (hlocal : Function.Bijective (fun z : ℤ => z • localOrientationClass o x₀))
    (h₂ : Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 2))
    (h₃ : Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 3)) :
    ∃ z : IntegralHomology M 3,
      (∀ y : M, absoluteToRelative M ({y}ᶜ) 3 z = localOrientationClass o y) ∧
        Function.Bijective (fun k : ℤ => k • z) :=
  exists_fundamentalClass_generator_of_surjective_and_injective o hprop x₀ hlocal
    (absoluteToRelative_surjective_of_subsingleton_punctured x₀ h₂)
    (absoluteToRelative_compl_singleton_injective_of_subsingleton x₀ h₃)

theorem exists_unique_fundamentalClass_of_contractible_punctured
    (o : TangentOrientationSection M) [ConnectedSpace M]
    (hprop : localClassRealizationLocallyConstant o) (x₀ : M)
    [ContractibleSpace ({x₀}ᶜ : Set M)] :
    ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x :=
  exists_unique_fundamentalClass_of_subsingleton_punctured o hprop x₀
    (subsingleton_integralHomology_compl_singleton_of_contractible x₀ 2 (by norm_num))
    (subsingleton_integralHomology_compl_singleton_of_contractible x₀ 3 (by norm_num))

theorem exists_unique_fundamentalClass_of_noncompactTopHomologyVanishing
    (o : TangentOrientationSection M) [ConnectedSpace M] [T2Space M]
    (hprop : localClassRealizationLocallyConstant o) (x₀ : M)
    (hδ : integralRelativeConnecting 2 ({x₀}ᶜ : Set M) = 0)
    (h : noncompactThreeManifoldTopHomologyVanishing.{u}) :
    ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x :=
  exists_unique_fundamentalClass_of_noncompactThreeManifoldTopHomologyVanishing o hprop x₀
    ((absoluteToRelative_surjective_iff_integralRelativeConnecting_eq_zero x₀).mpr hδ) h

theorem not_surjective_absoluteToRelative_threeSpace_compl_origin :
    ¬ Function.Surjective (absoluteToRelative ThreeSpace ({0}ᶜ) 3) := by
  intro hsurj
  have hzero := (absoluteToRelative_surjective_iff_integralRelativeConnecting_eq_zero
    (M := ThreeSpace) (0 : ThreeSpace)).mp hsurj
  have hex := LinearMap.exact_iff.mp
    (integralRelative_exact_relative 2 ({0}ᶜ : Set ThreeSpace))
  have htop : LinearMap.range (integralAbsoluteToRelative 3 ({0}ᶜ : Set ThreeSpace)) = ⊤ := by
    rw [← hex, hzero, LinearMap.ker_zero]
  have hsub : Subsingleton (integralSingularHomology 3 ThreeSpace) :=
    integralSingularHomology_subsingleton_of_contractible 3 (by norm_num) ThreeSpace
  obtain ⟨a, ha⟩ := LinearMap.range_eq_top.mp htop
    (integralEuclideanLocalTopGenerator ThreeSpace 1 (by simp) (0 : ThreeSpace))
  refine integralEuclideanLocalTopGenerator_ne_zero ThreeSpace 1 (by simp) (0 : ThreeSpace) ?_
  rw [← ha, hsub.allEq a 0, map_zero]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
