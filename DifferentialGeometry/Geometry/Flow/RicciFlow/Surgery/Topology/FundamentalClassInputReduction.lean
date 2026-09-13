import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassRealizationCriterion
import DifferentialGeometry.Topology.Homology.EuclideanLocalVanishing
import DifferentialGeometry.Topology.FundamentalGroup.Sphere

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Set
open scoped Manifold ContDiff Topology Simplicial

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M]

omit [IsManifold ThreeModel ∞ M] in
theorem subsingleton_localIntegralHomology_four_compl_singleton (x : M) :
    Subsingleton (integralRelativeHomology 4 ({x}ᶜ : Set M)) := by
  have : T1Space M := ChartedSpace.t1Space ThreeSpace M
  let uliftChart := (Homeomorph.ulift (X := ThreeSpace)).symm.toOpenPartialHomeomorph
  let : InnerProductSpace ℝ (ULift.{u} ThreeSpace) :=
    { inner := fun x y => inner ℝ x.down y.down
      norm_sq_eq_re_inner := fun x => norm_sq_eq_re_inner x.down
      conj_inner_symm := fun x y => inner_conj_symm x.down y.down
      add_left := fun x y z => inner_add_left x.down y.down z.down
      smul_left := fun x y r => inner_smul_left x.down y.down r }
  let : ChartedSpace (ULift.{u} ThreeSpace) M :=
    { atlas := (fun e : OpenPartialHomeomorph M ThreeSpace => e.trans uliftChart) ''
        atlas ThreeSpace M
      chartAt := fun x => (chartAt ThreeSpace x).trans uliftChart
      mem_chart_source := fun x => by
        rw [OpenPartialHomeomorph.trans_source]
        exact ⟨mem_chart_source ThreeSpace x, trivial⟩
      chart_mem_atlas := fun x => ⟨chartAt ThreeSpace x, chart_mem_atlas ThreeSpace x, rfl⟩ }
  have hfin : Module.finrank ℝ (ULift.{u} ThreeSpace) = 1 + 2 :=
    (ULift.moduleEquiv (R := ℝ) (M := ThreeSpace)).finrank_eq.trans (by simp)
  exact integralManifoldLocal_subsingleton (ULift.{u} ThreeSpace) 1 4 hfin (by norm_num) M x

omit [IsManifold ThreeModel ∞ M] in
theorem injective_subsingletonInclusion_of_subsingleton_localIntegralHomology_four (x : M) :
    Function.Injective (integralSingularHomologyMap 3
      (singularSubspaceInclusion ({x}ᶜ : Set M))) := by
  have hloc := subsingleton_localIntegralHomology_four_compl_singleton (M := M) x
  intro a b hab
  have hex := LinearMap.exact_iff.mp (integralRelative_exact_subspace 3 ({x}ᶜ : Set M))
  have hmem : a - b ∈ LinearMap.ker (integralSingularHomologyMap 3
      (singularSubspaceInclusion ({x}ᶜ : Set M))) :=
    LinearMap.mem_ker.mpr (by rw [map_sub, hab, sub_self])
  rw [hex] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hc0 : c = 0 := hloc.allEq c 0
  rw [hc0, map_zero] at hc
  exact sub_eq_zero.mp hc.symm

omit [IsManifold ThreeModel ∞ M] in
theorem subsingleton_integralSingularHomology_three_compl_singleton_of_subsingleton
    (x : M) (h : Subsingleton (integralSingularHomology 3 M)) :
    Subsingleton (integralSingularHomology 3 ({x}ᶜ : Set M)) :=
  ⟨fun a b => injective_subsingletonInclusion_of_subsingleton_localIntegralHomology_four x
    (h.allEq (integralSingularHomologyMap 3 (singularSubspaceInclusion ({x}ᶜ : Set M)) a)
      (integralSingularHomologyMap 3 (singularSubspaceInclusion ({x}ᶜ : Set M)) b))⟩

omit [IsManifold ThreeModel ∞ M] in
theorem subsingleton_integralSingularHomology_three_compl_singleton_iff_injective (x : M) :
    Subsingleton (integralSingularHomology 3 ({x}ᶜ : Set M)) ↔
      Function.Injective (integralAbsoluteToRelative 3 ({x}ᶜ : Set M)) := by
  refine ⟨fun h => integralAbsoluteToRelative_injective_of_subsingleton 3 ({x}ᶜ : Set M) h,
    fun hinj => ?_⟩
  have hincl : Function.Injective (integralSingularHomologyMap 3
      (singularSubspaceInclusion ({x}ᶜ : Set M))) :=
    injective_subsingletonInclusion_of_subsingleton_localIntegralHomology_four x
  have hker : ∀ a, integralSingularHomologyMap 3 (singularSubspaceInclusion ({x}ᶜ : Set M)) a
      = 0 := by
    intro a
    apply hinj
    have hex := LinearMap.exact_iff.mp (integralRelative_exact_absolute 3 ({x}ᶜ : Set M))
    have hmem : integralSingularHomologyMap 3 (singularSubspaceInclusion ({x}ᶜ : Set M)) a ∈
        LinearMap.ker (integralAbsoluteToRelative 3 ({x}ᶜ : Set M)) := by
      rw [hex]
      exact LinearMap.mem_range_self _ a
    rw [LinearMap.mem_ker.mp hmem, map_zero]
  exact ⟨fun a b => hincl (by rw [hker a, hker b])⟩

omit [IsManifold ThreeModel ∞ M] in
theorem subsingleton_integralHomology_compl_singleton_three_of_subsingleton
    (x : M) (h : Subsingleton (IntegralHomology M 3)) :
    Subsingleton (IntegralHomology ({x}ᶜ : Set M) 3) :=
  subsingleton_integralSingularHomology_three_compl_singleton_of_subsingleton x h

omit [IsManifold ThreeModel ∞ M] in
theorem subsingleton_integralHomology_compl_singleton_three_iff_injective_absoluteToRelative
    (x : M) :
    Subsingleton (IntegralHomology ({x}ᶜ : Set M) 3) ↔
      Function.Injective (absoluteToRelative M ({x}ᶜ) 3) :=
  subsingleton_integralSingularHomology_three_compl_singleton_iff_injective x

theorem exists_unique_fundamentalClass_of_locallyConstant_and_connecting_eq_zero_and_subsingleton
    (o : TangentOrientationSection M) [ConnectedSpace M] (x₀ : M)
    (hprop : localClassRealizationLocallyConstant o)
    (hδ : integralRelativeConnecting 2 ({x₀}ᶜ : Set M) = 0)
    (h₃ : Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 3)) :
    ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x :=
  exists_unique_fundamentalClass_of_surjective_and_injective o hprop x₀
    ((absoluteToRelative_surjective_iff_integralRelativeConnecting_eq_zero x₀).mpr hδ)
    (absoluteToRelative_compl_singleton_injective_of_subsingleton x₀ h₃)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology

theorem exists_unique_fundamentalClass_sphereThree_of_localClassRealizationLocallyConstant
    (o : TangentOrientationSection SphereThree)
    (hprop : localClassRealizationLocallyConstant o) :
    ∃! z : IntegralHomology SphereThree 3, ∀ x : SphereThree,
      absoluteToRelative SphereThree ({x}ᶜ) 3 z = localOrientationClass o x :=
  exists_unique_fundamentalClass_of_subsingleton_punctured o hprop sphereThreeNorth
    (subsingleton_integralSingularHomology_two_punctured_threeSphere sphereThreeNorth)
    (subsingleton_integralSingularHomology_three_punctured_threeSphere sphereThreeNorth)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Lean in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsingleton_localIntegralHomology_four_compl_singleton,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.injective_subsingletonInclusion_of_subsingleton_localIntegralHomology_four,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsingleton_integralSingularHomology_three_compl_singleton_of_subsingleton,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsingleton_integralSingularHomology_three_compl_singleton_iff_injective,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsingleton_integralHomology_compl_singleton_three_of_subsingleton,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsingleton_integralHomology_compl_singleton_three_iff_injective_absoluteToRelative,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_unique_fundamentalClass_of_locallyConstant_and_connecting_eq_zero_and_subsingleton,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_unique_fundamentalClass_sphereThree_of_localClassRealizationLocallyConstant] do
    let axs ← Lean.collectAxioms n
    unless axs.all (fun a => allowed.contains a) do
      throwError "unexpected axioms for {n}: {axs}"
