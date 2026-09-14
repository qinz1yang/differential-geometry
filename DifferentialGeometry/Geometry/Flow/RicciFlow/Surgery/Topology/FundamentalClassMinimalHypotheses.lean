import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassRealizationCriterion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassGeneratorFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LocalClassRealizationTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LocalOrientationClassDegreeReduction

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology

universe u

def euclideanStandardSimplexClassGenerator : Prop :=
  Function.Bijective (fun z : ℤ => z • euclideanStandardSimplexClass.{u})

theorem euclideanStandardSimplexClassGenerator_iff_exists_boundaryFunctional :
    euclideanStandardSimplexClassGenerator.{u} ↔
      ∃ ψ : integralSingularHomology 2
          ({(0 : liftedSphereSpace.{u} 1)}ᶜ : Set (liftedSphereSpace.{u} 1)) →ₗ[ℤ] ℤ,
        ψ euclideanStandardSimplexBoundaryClass.{u} = 1 :=
  euclideanStandardSimplexClass_generator_iff_exists_boundary_functional_eq_one

theorem euclideanStandardSimplexClassGenerator_iff_isSphereHomologyGenerator :
    euclideanStandardSimplexClassGenerator.{u} ↔
      DifferentialGeometry.Topology.IsSphereHomologyGenerator.{u} 1
        euclideanStandardSimplexBoundarySphereClass.{u} :=
  euclideanStandardSimplexClass_generator_iff_isSphereHomologyGenerator

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M]

theorem localOrientationClass_generator_of_euclideanStandardSimplexClassGenerator
    (h : euclideanStandardSimplexClassGenerator.{u}) (o : TangentOrientationSection M) (x : M) :
    Function.Bijective (fun z : ℤ => z • localOrientationClass o x) :=
  localOrientationClass_generator_of_euclideanStandardSimplex o x h

theorem existsFundamentalClassAt_iff_integralRelativeConnecting_eq_zero
    (o : TangentOrientationSection M) (x : M)
    (hgen : Function.Bijective (fun z : ℤ => z • localOrientationClass o x)) :
    existsFundamentalClassAt o x ↔ integralRelativeConnecting 2 ({x}ᶜ : Set M) = 0 :=
  (exists_fundamentalClassAt_iff_surjective o x hgen.2).trans
    (absoluteToRelative_surjective_iff_integralRelativeConnecting_eq_zero x)

omit [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
theorem integralRelativeConnecting_eq_zero_iff_puncturedInclusion_injective (x : M) :
    integralRelativeConnecting 2 ({x}ᶜ : Set M) = 0 ↔
      Function.Injective
        (integralSingularHomologyMap 2 (singularSubspaceInclusion ({x}ᶜ : Set M))) := by
  have hex := LinearMap.exact_iff.mp
    (integralRelative_exact_subspace (X := M) 2 ({x}ᶜ : Set M))
  constructor
  · intro h0
    rw [← LinearMap.ker_eq_bot, hex, h0, LinearMap.range_zero]
  · intro hinj
    ext y
    have hmem : integralRelativeConnecting 2 ({x}ᶜ : Set M) y ∈
        LinearMap.range (integralRelativeConnecting 2 ({x}ᶜ : Set M)) :=
      LinearMap.mem_range_self _ y
    rw [← hex, LinearMap.ker_eq_bot.mpr hinj] at hmem
    simpa using hmem

omit [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
theorem integralRelativeConnecting_eq_zero_of_subsingleton_punctured (x : M)
    (h : Subsingleton (IntegralHomology ({x}ᶜ : Set M) 2)) :
    integralRelativeConnecting 2 ({x}ᶜ : Set M) = 0 :=
  integralRelativeConnecting_eq_zero_of_subsingleton x h

theorem exists_unique_fundamentalClass_of_connecting_eq_zero_of_subsingleton_punctured
    (o : TangentOrientationSection M) [ConnectedSpace M]
    (hprop : localClassRealizationLocallyConstant o) (x₀ : M)
    (hδ : integralRelativeConnecting 2 ({x₀}ᶜ : Set M) = 0)
    (h₃ : Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 3)) :
    ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x :=
  exists_unique_fundamentalClass_of_surjective_and_injective o hprop x₀
    ((absoluteToRelative_surjective_iff_integralRelativeConnecting_eq_zero x₀).mpr hδ)
    (absoluteToRelative_compl_singleton_injective_of_subsingleton x₀ h₃)

theorem exists_unique_fundamentalClass_of_connecting_eq_zero_of_localClassTransport
    (o : TangentOrientationSection M) [ConnectedSpace M] (htransport : localClassTransport o)
    (x₀ : M)
    (hδ : integralRelativeConnecting 2 ({x₀}ᶜ : Set M) = 0)
    (h₃ : Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 3)) :
    ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x :=
  exists_unique_fundamentalClass_of_connecting_eq_zero_of_subsingleton_punctured o
    (localClassRealizationLocallyConstant_of_localClassTransport o htransport) x₀ hδ h₃

def ClosedThreeManifoldPuncturedVanishing
    (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] (x : M) : Prop :=
  Subsingleton (IntegralHomology ({x}ᶜ : Set M) 2) ∧
    Subsingleton (IntegralHomology ({x}ᶜ : Set M) 3)

theorem exists_unique_fundamentalClass_of_puncturedVanishing_through_connecting
    {x : M} {o : TangentOrientationSection M} [ConnectedSpace M]
    (h : ClosedThreeManifoldPuncturedVanishing M x) (htransport : localClassTransport o) :
    ∃! z : IntegralHomology M 3, ∀ y : M,
      absoluteToRelative M ({y}ᶜ) 3 z = localOrientationClass o y :=
  exists_unique_fundamentalClass_of_connecting_eq_zero_of_localClassTransport o htransport x
    (integralRelativeConnecting_eq_zero_of_subsingleton x h.1) h.2

theorem bijective_zsmul_choose_of_euclideanStandardSimplexClassGenerator
    (o : TangentOrientationSection M) (x : M)
    (h : ∃! z : IntegralHomology M 3, ∀ y : M,
      absoluteToRelative M ({y}ᶜ) 3 z = localOrientationClass o y)
    (hgen : euclideanStandardSimplexClassGenerator.{u})
    (hinj : Function.Injective (absoluteToRelative M ({x}ᶜ) 3)) :
    Function.Bijective (fun k : ℤ => k • Classical.choose h) :=
  bijective_zsmul_choose_of_injective_absoluteToRelative o x h
    (localOrientationClass_generator_of_euclideanStandardSimplexClassGenerator hgen o x) hinj

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology

theorem subsingleton_integralHomology_two_compl_singleton_sphereThree (v : SphereThree) :
    Subsingleton (IntegralHomology ({v}ᶜ : Set SphereThree) 2) :=
  subsingleton_integralSingularHomology_two_punctured_threeSphere v

theorem subsingleton_integralHomology_three_compl_singleton_sphereThree (v : SphereThree) :
    Subsingleton (IntegralHomology ({v}ᶜ : Set SphereThree) 3) :=
  subsingleton_integralSingularHomology_three_punctured_threeSphere v

theorem integralRelativeConnecting_two_compl_singleton_sphereThree_eq_zero (v : SphereThree) :
    integralRelativeConnecting 2 ({v}ᶜ : Set SphereThree) = 0 :=
  integralRelativeConnecting_eq_zero_of_subsingleton v
    (subsingleton_integralHomology_two_compl_singleton_sphereThree v)

theorem integralRelativeConnecting_two_compl_origin_threeSpace_ne_zero :
    integralRelativeConnecting 2 ({0}ᶜ : Set ThreeSpace) ≠ 0 := fun h0 =>
  not_surjective_absoluteToRelative_threeSpace_compl_origin
    ((absoluteToRelative_surjective_iff_integralRelativeConnecting_eq_zero
      (M := ThreeSpace) (0 : ThreeSpace)).mpr h0)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Lean in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ns : Name := `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  let decls : List Name :=
    [`euclideanStandardSimplexClassGenerator,
      `euclideanStandardSimplexClassGenerator_iff_exists_boundaryFunctional,
      `euclideanStandardSimplexClassGenerator_iff_isSphereHomologyGenerator,
      `localOrientationClass_generator_of_euclideanStandardSimplexClassGenerator,
      `existsFundamentalClassAt_iff_integralRelativeConnecting_eq_zero,
      `integralRelativeConnecting_eq_zero_iff_puncturedInclusion_injective,
      `integralRelativeConnecting_eq_zero_of_subsingleton_punctured,
      `exists_unique_fundamentalClass_of_connecting_eq_zero_of_subsingleton_punctured,
      `exists_unique_fundamentalClass_of_connecting_eq_zero_of_localClassTransport,
      `exists_unique_fundamentalClass_of_puncturedVanishing_through_connecting,
      `bijective_zsmul_choose_of_euclideanStandardSimplexClassGenerator,
      `subsingleton_integralHomology_two_compl_singleton_sphereThree,
      `subsingleton_integralHomology_three_compl_singleton_sphereThree,
      `integralRelativeConnecting_two_compl_singleton_sphereThree_eq_zero,
      `integralRelativeConnecting_two_compl_origin_threeSpace_ne_zero]
  for n in decls.map (ns.append ·) do
    let axs ← Lean.collectAxioms n
    unless axs.all (fun a => allowed.contains a) do
      throwError "unexpected axioms for {n}: {axs}"
