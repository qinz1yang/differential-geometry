import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassInputReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassMinimalHypotheses
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassRealizationCriterion
import DifferentialGeometry.Topology.Algebra.Module.InfiniteCyclicCriterion
import DifferentialGeometry.Topology.Homology.NoncompactPoincareDualityFrontier
import DifferentialGeometry.Topology.Homology.NoncompactTopHomologyVanishing
import DifferentialGeometry.Topology.Homology.SecondHomologyVanishingClosedThreeManifold
import DifferentialGeometry.Topology.Homology.SphereTopHomology

noncomputable section

open CategoryTheory CategoryTheory.Limits Set
open scoped Manifold ContDiff Topology

universe u

namespace DifferentialGeometry.Topology

theorem nonempty_linearEquiv_compactSupportZeroCocycles_int (X : Type u) [TopologicalSpace X]
    [ConnectedSpace X] [CompactSpace X] :
    Nonempty (↥(integralCompactSupportZeroCocycles X) ≃ₗ[ℤ] ℤ) := by
  let x₀ : X := Classical.choice (inferInstance : Nonempty X)
  have hconst : ∀ c : ℤ,
      (Function.const X c : X → ℤ) ∈ integralCompactSupportZeroCocycles X :=
    fun c => ⟨IsLocallyConstant.const c,
      ⟨Set.univ, isCompact_univ, fun x hx => absurd (Set.mem_univ x) hx⟩⟩
  refine ⟨LinearEquiv.ofBijective
    { toFun := fun f => f.1 x₀
      map_add' := fun f g => by simp [Pi.add_apply]
      map_smul' := fun c f => by simp [Pi.smul_apply] } ⟨?_, ?_⟩⟩
  · intro f g hfg
    refine Subtype.ext (funext fun x => ?_)
    change f.1 x₀ = g.1 x₀ at hfg
    have hf : f.1 x = f.1 x₀ :=
      f.2.1.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ x) (Set.mem_univ x₀)
    have hg : g.1 x = g.1 x₀ :=
      g.2.1.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ x) (Set.mem_univ x₀)
    rw [hf, hfg, hg]
  · intro c
    exact ⟨⟨Function.const X c, hconst c⟩, rfl⟩

theorem noncompactPoincareDualityThreeZero_sphereThree :
    noncompactPoincareDualityThreeZero SphereThree :=
  ⟨(integralSphereTopHomologyEquiv 2 (EuclideanSpace ℝ (Fin 4)) (by simp)).trans
    (Classical.choice (nonempty_linearEquiv_compactSupportZeroCocycles_int ↥SphereThree)).symm⟩

theorem
    not_forall_subsingleton_topHomology_three_of_noncompactPoincareDualityThreeZero :
    ¬ (∀ (X : Type) [TopologicalSpace X] [ConnectedSpace X],
      noncompactPoincareDualityThreeZero X → Subsingleton (integralSingularHomology 3 X)) :=
  fun h => not_subsingleton_integralSingularHomology_three_sphereThree
    (h ↥SphereThree noncompactPoincareDualityThreeZero_sphereThree)

theorem not_forall_nonempty_linearEquiv_compactSupportZeroCocycles_int_of_connectedSpace :
    ¬ (∀ (X : Type) [TopologicalSpace X] [ConnectedSpace X],
      Nonempty (↥(integralCompactSupportZeroCocycles X) ≃ₗ[ℤ] ℤ)) :=
  fun h => by
    have hsub : Subsingleton
        ↥(integralCompactSupportZeroCocycles (EuclideanSpace ℝ (Fin 3))) :=
      subsingleton_integralCompactSupportZeroCocycles (EuclideanSpace ℝ (Fin 3))
    exact DifferentialGeometry.Algebra.Module.not_nonempty_linearEquiv_int_of_subsingleton
      (h (EuclideanSpace ℝ (Fin 3)))

theorem not_forall_nonempty_linearEquiv_compactSupportZeroCocycles_int_of_compactSpace :
    ¬ (∀ (X : Type) [TopologicalSpace X] [CompactSpace X],
      Nonempty (↥(integralCompactSupportZeroCocycles X) ≃ₗ[ℤ] ℤ)) :=
  fun h => by
    have hsub : Subsingleton ↥(integralCompactSupportZeroCocycles Empty) :=
      ⟨fun f g => Subtype.ext (funext fun x => isEmptyElim x)⟩
    exact DifferentialGeometry.Algebra.Module.not_nonempty_linearEquiv_int_of_subsingleton
      (h Empty)

end DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M]

omit [IsManifold ThreeModel ∞ M] in
theorem surjective_singularHomologyMap_two_compl_singleton (x : M) :
    Function.Surjective
      (integralSingularHomologyMap 2 (singularSubspaceInclusion ({x}ᶜ : Set M))) := by
  have hsub : Subsingleton (integralRelativeHomology 2 ({x}ᶜ : Set M)) :=
    subsingleton_integralRelativeHomology_two_compl_singleton x
  have hzero : integralAbsoluteToRelative 2 ({x}ᶜ : Set M) = 0 :=
    LinearMap.ext fun a => hsub.allEq (integralAbsoluteToRelative 2 ({x}ᶜ : Set M) a) 0
  rw [← LinearMap.range_eq_top]
  rw [← LinearMap.exact_iff.mp (integralRelative_exact_absolute 2 ({x}ᶜ : Set M))]
  rw [hzero, LinearMap.ker_zero]

omit [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
theorem absoluteToRelative_surjective_iff_injective_singularHomologyMap_two_compl_singleton
    (x : M) :
    Function.Surjective (absoluteToRelative M ({x}ᶜ) 3) ↔
      Function.Injective
        (integralSingularHomologyMap 2 (singularSubspaceInclusion ({x}ᶜ : Set M))) := by
  rw [absoluteToRelative_surjective_iff_integralRelativeConnecting_eq_zero x]
  have hex := LinearMap.exact_iff.mp
    (integralRelative_exact_subspace 2 ({x}ᶜ : Set M))
  constructor
  · intro h
    rw [← LinearMap.range_eq_bot, ← hex] at h
    exact LinearMap.ker_eq_bot.mp h
  · intro hinj
    rw [← LinearMap.range_eq_bot, ← hex]
    exact LinearMap.ker_eq_bot.mpr hinj

omit [IsManifold ThreeModel ∞ M] in
theorem absoluteToRelative_surjective_iff_bijective_singularHomologyMap_two_compl_singleton
    (x : M) :
    Function.Surjective (absoluteToRelative M ({x}ᶜ) 3) ↔
      Function.Bijective
        (integralSingularHomologyMap 2 (singularSubspaceInclusion ({x}ᶜ : Set M))) :=
  (absoluteToRelative_surjective_iff_injective_singularHomologyMap_two_compl_singleton x).trans
    ⟨fun h => ⟨h, surjective_singularHomologyMap_two_compl_singleton x⟩, fun h => h.1⟩

omit [IsManifold ThreeModel ∞ M] in
theorem absoluteToRelative_bijective_iff_subsingleton_punctured_and_injective_homologyMap_two
    (x : M) :
    Function.Bijective (absoluteToRelative M ({x}ᶜ) 3) ↔
      Subsingleton (IntegralHomology ({x}ᶜ : Set M) 3) ∧
        Function.Injective
          (integralSingularHomologyMap 2 (singularSubspaceInclusion ({x}ᶜ : Set M))) :=
  ⟨fun h => ⟨
      (subsingleton_integralHomology_compl_singleton_three_iff_injective_absoluteToRelative
        x).mpr h.1,
      (absoluteToRelative_surjective_iff_injective_singularHomologyMap_two_compl_singleton
        x).mp h.2⟩,
    fun h => ⟨
      (subsingleton_integralHomology_compl_singleton_three_iff_injective_absoluteToRelative
        x).mp h.1,
      (absoluteToRelative_surjective_iff_injective_singularHomologyMap_two_compl_singleton
        x).mpr h.2⟩⟩

omit [IsManifold ThreeModel ∞ M] in
theorem nonempty_linearEquiv_int_of_subsingleton_punctured_of_injective_singularHomologyMap_two
    (x₀ : M) (h₃ : Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 3))
    (hinj : Function.Injective
      (integralSingularHomologyMap 2 (singularSubspaceInclusion ({x₀}ᶜ : Set M)))) :
    Nonempty (IntegralHomology M 3 ≃ₗ[ℤ] ℤ) :=
  ⟨(LinearEquiv.ofBijective ((absoluteToRelative M ({x₀}ᶜ) 3).hom)
      ⟨absoluteToRelative_compl_singleton_injective_of_subsingleton x₀ h₃,
        (absoluteToRelative_surjective_iff_injective_singularHomologyMap_two_compl_singleton
          x₀).mpr hinj⟩).trans
    (localIntegralHomologyEquivInt (M := M) x₀)⟩

omit [IsManifold ThreeModel ∞ M] in
theorem subsingleton_integralHomology_compl_singleton_three_iff_noncompactPoincareDualityThreeZero
    [T2Space M] [CompactSpace M] [ConnectedSpace M] (x₀ : M) :
    Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 3) ↔
      noncompactPoincareDualityThreeZero ({x₀}ᶜ : Set M) := by
  have hconn : ConnectedSpace ↥({x₀}ᶜ : Set M) := connectedSpace_compl_singleton (M := M) x₀
  have hnonc : NoncompactSpace ↥({x₀}ᶜ : Set M) :=
    noncompactSpace_compl_singleton (M := M) x₀
  exact ⟨fun h₃ => @noncompactPoincareDualityThreeZero_of_subsingleton
      ↥({x₀}ᶜ : Set M) _ h₃
      (@subsingleton_integralCompactSupportZeroCocycles ↥({x₀}ᶜ : Set M) _ hconn hnonc),
    fun h => subsingleton_integralSingularHomology_three_of_noncompactPoincareDualityThreeZero h⟩

theorem noncompactPoincareDualityThreeZero_compl_singleton_sphereThree (v : SphereThree) :
    noncompactPoincareDualityThreeZero ({v}ᶜ : Set SphereThree) :=
  @noncompactPoincareDualityThreeZero_of_subsingleton ↥({v}ᶜ : Set SphereThree) _
    (subsingleton_integralHomology_three_compl_singleton_sphereThree v)
    (@subsingleton_integralCompactSupportZeroCocycles ↥({v}ᶜ : Set SphereThree) _
      (connectedSpace_compl_singleton (M := SphereThree) v)
      (noncompactSpace_compl_singleton (M := SphereThree) v))

theorem injective_singularHomologyMap_two_compl_singleton_sphereThree (v : SphereThree) :
    Function.Injective
      (integralSingularHomologyMap 2 (singularSubspaceInclusion ({v}ᶜ : Set SphereThree))) :=
  fun a b _ => (subsingleton_integralHomology_two_compl_singleton_sphereThree v).allEq a b

theorem not_injective_singularHomologyMap_two_compl_origin_threeSpace :
    ¬ Function.Injective
      (integralSingularHomologyMap 2 (singularSubspaceInclusion ({0}ᶜ : Set ThreeSpace))) :=
  fun hinj => not_surjective_absoluteToRelative_threeSpace_compl_origin
    ((absoluteToRelative_surjective_iff_injective_singularHomologyMap_two_compl_singleton
      (M := ThreeSpace) 0).mpr hinj)

theorem closedThreeManifoldPuncturedVanishing_iff_noncompactPoincareDuality
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [Subsingleton (integralSingularCohomology 1 M)] (x₀ : M) :
    ClosedThreeManifoldPuncturedVanishing M x₀ ↔
      noncompactPoincareDualityTwoOne ({x₀}ᶜ : Set M) ∧
        noncompactPoincareDualityThreeZero ({x₀}ᶜ : Set M) := by
  have h₂ : Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 2) ↔
      noncompactPoincareDualityTwoOne ({x₀}ᶜ : Set M) :=
    ⟨fun h => @noncompactPoincareDualityTwoOne_of_subsingleton ↥({x₀}ᶜ : Set M) _ h
        (subsingleton_integralCompactSupportCohomologyOne_compl_singleton x₀),
      fun h =>
        (subsingleton_integralSingularHomology_two_compl_singleton_of_noncompactPoincareDuality
          x₀ h)⟩
  have h₃ : Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 3) ↔
      noncompactPoincareDualityThreeZero ({x₀}ᶜ : Set M) :=
    subsingleton_integralHomology_compl_singleton_three_iff_noncompactPoincareDualityThreeZero x₀
  exact ⟨fun h => ⟨h₂.mp h.1, h₃.mp h.2⟩, fun h => ⟨h₂.mpr h.1, h₃.mpr h.2⟩⟩

omit [IsManifold ThreeModel ∞ M] in
theorem
    nonempty_linearEquiv_int_of_noncompactPoincareDualityThreeZero_of_injective_homologyMap
    [T2Space M] [CompactSpace M] [ConnectedSpace M] (x₀ : M)
    (h : noncompactPoincareDualityThreeZero ({x₀}ᶜ : Set M))
    (hinj : Function.Injective
      (integralSingularHomologyMap 2 (singularSubspaceInclusion ({x₀}ᶜ : Set M)))) :
    Nonempty (IntegralHomology M 3 ≃ₗ[ℤ] ℤ) :=
  nonempty_linearEquiv_int_of_subsingleton_punctured_of_injective_singularHomologyMap_two x₀
    ((subsingleton_integralHomology_compl_singleton_three_iff_noncompactPoincareDualityThreeZero
      x₀).mpr h) hinj

theorem exists_unique_fundamentalClass_of_punctured_noncompactPoincareDuality
    (o : TangentOrientationSection M) [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [SimplyConnectedSpace M] (htransport : localClassTransport o) (x₀ : M)
    (hpd₂ : noncompactPoincareDualityTwoOne ({x₀}ᶜ : Set M))
    (hpd₃ : noncompactPoincareDualityThreeZero ({x₀}ᶜ : Set M)) :
    ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x := by
  have h₁ : Subsingleton (integralSingularCohomology 1 M) :=
    integralSingularCohomology_one_subsingleton (X := M)
  exact exists_unique_fundamentalClass_of_puncturedVanishing_through_connecting
    ((closedThreeManifoldPuncturedVanishing_iff_noncompactPoincareDuality x₀).mpr
      ⟨hpd₂, hpd₃⟩) htransport

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Lean in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let topologyDecls : List String :=
    ["nonempty_linearEquiv_compactSupportZeroCocycles_int",
      "noncompactPoincareDualityThreeZero_sphereThree",
      "not_forall_subsingleton_topHomology_three_of_noncompactPoincareDualityThreeZero",
      "not_forall_nonempty_linearEquiv_compactSupportZeroCocycles_int_of_connectedSpace",
      "not_forall_nonempty_linearEquiv_compactSupportZeroCocycles_int_of_compactSpace"]
  let surgeryDecls : List String :=
    ["surjective_singularHomologyMap_two_compl_singleton",
      "absoluteToRelative_surjective_iff_injective_singularHomologyMap_two_compl_singleton",
      "absoluteToRelative_surjective_iff_bijective_singularHomologyMap_two_compl_singleton",
      "absoluteToRelative_bijective_iff_subsingleton_punctured_and_injective_homologyMap_two",
      "nonempty_linearEquiv_int_of_subsingleton_punctured_of_injective_singularHomologyMap_two",
      "subsingleton_integralHomology_compl_singleton_three_iff_noncompactPoincareDualityThreeZero",
      "noncompactPoincareDualityThreeZero_compl_singleton_sphereThree",
      "injective_singularHomologyMap_two_compl_singleton_sphereThree",
      "not_injective_singularHomologyMap_two_compl_origin_threeSpace",
      "closedThreeManifoldPuncturedVanishing_iff_noncompactPoincareDuality",
      "nonempty_linearEquiv_int_of_noncompactPoincareDualityThreeZero_of_injective_homologyMap",
      "exists_unique_fundamentalClass_of_punctured_noncompactPoincareDuality"]
  for p in [(`DifferentialGeometry.Topology, topologyDecls),
      (`DifferentialGeometry.PDE.RicciFlow.Surgery.Topology, surgeryDecls)] do
    for s in p.2 do
      let n := p.1.str s
      let axs ← Lean.collectAxioms n
      unless axs.all (fun a => allowed.contains a) do
        throwError "unexpected dependencies for {n}: {axs}"
