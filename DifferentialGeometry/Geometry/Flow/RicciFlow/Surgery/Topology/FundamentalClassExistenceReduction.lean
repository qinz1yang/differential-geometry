import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NoncompactVanishingNucleus
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ThreeManifoldHomologyFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PuncturedVanishingHypotheses

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology

universe u

def ClosedThreeManifoldFundamentalClassRealizationInput : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    [T2Space M] [CompactSpace M] (o : TangentOrientationSection M),
    ∃ z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x

def ClosedThreeManifoldFundamentalClassLocalizationInjective : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    [T2Space M] [CompactSpace M],
    Function.Injective (fun w : IntegralHomology M 3 =>
      fun x : M => absoluteToRelative M ({x}ᶜ) 3 w)

theorem exists_unique_fundamentalClass_of_realizationInput_of_localizationInjective
    (h : ClosedThreeManifoldFundamentalClassRealizationInput.{u})
    (hinj : ClosedThreeManifoldFundamentalClassLocalizationInjective.{u})
    (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    [T2Space M] [CompactSpace M] (o : TangentOrientationSection M) :
    ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x :=
  (exists_unique_fundamentalClass_iff_exists_and_injective_localization o).mpr
    ⟨h M o, hinj M⟩

theorem realizationInput_connected_of_connectingInput
    (h : ClosedThreeManifoldFundamentalClassConnectingInput.{u})
    (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] (o : TangentOrientationSection M) :
    ∃ z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x :=
  (exists_unique_fundamentalClass_of_connectingInput h M (Classical.arbitrary M) o).exists

theorem realizationInput_connected_of_connectingVanishing_of_localClassTransport
    (hδ : ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold ThreeModel ∞ M] [ConnectedSpace M] (x₀ : M),
      integralRelativeConnecting 2 ({x₀}ᶜ : Set M) = 0)
    (htransport : ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold ThreeModel ∞ M] [ConnectedSpace M] (o : TangentOrientationSection M),
      localClassTransport o)
    (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    [ConnectedSpace M] (o : TangentOrientationSection M) :
    ∃ z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x :=
  exists_fundamentalClass_of_local_realization_at o
    (localClassRealizationLocallyConstant_of_localClassTransport o (htransport M o))
    (Classical.arbitrary M)
    ((absoluteToRelative_surjective_iff_integralRelativeConnecting_eq_zero (M := M)
      (Classical.arbitrary M)).mpr (hδ M (Classical.arbitrary M))
        (localOrientationClass o (Classical.arbitrary M)))

theorem localizationInjective_of_forall_exists_injective
    (h : ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold ThreeModel ∞ M] [T2Space M] [CompactSpace M],
      ∃ x : M, Function.Injective (absoluteToRelative M ({x}ᶜ) 3)) :
    ClosedThreeManifoldFundamentalClassLocalizationInjective.{u} :=
  fun M _ _ _ _ _ w w' hww =>
    injective_localization_of_exists_injective_at (M := M) (h M) w w' fun x => congrFun hww x

theorem localizationInjective_connected_of_noncompactThreeManifoldTopHomologyVanishing
    (h : noncompactThreeManifoldTopHomologyVanishing.{u})
    (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] :
    Function.Injective (fun w : IntegralHomology M 3 =>
      fun x : M => absoluteToRelative M ({x}ᶜ) 3 w) := by
  let x₀ : M := Classical.arbitrary M
  have hsub :=
    subsingleton_integralHomology_compl_singleton_of_noncompactThreeManifoldTopHomologyVanishing
      h x₀
  exact fun w w' hww => injective_localization_of_exists_injective_at
    ⟨x₀, absoluteToRelative_compl_singleton_injective_of_subsingleton x₀ hsub⟩
    w w' fun x => congrFun hww x

theorem localizationInjective_of_subsingleton_topHomology {M : Type u} [TopologicalSpace M]
    (h : Subsingleton (IntegralHomology M 3)) :
    Function.Injective (fun w : IntegralHomology M 3 =>
      fun x : M => absoluteToRelative M ({x}ᶜ) 3 w) :=
  fun w w' _ => h.allEq w w'

theorem localizationInjective_sphereThree :
    Function.Injective (fun w : IntegralHomology SphereThree 3 =>
      fun x : SphereThree => absoluteToRelative SphereThree ({x}ᶜ) 3 w) :=
  fun w w' hww => (absoluteToRelative_punctured_threeSphere_bijective sphereThreeNorth).1
    (show absoluteToRelative SphereThree ({sphereThreeNorth}ᶜ) 3 w =
        absoluteToRelative SphereThree ({sphereThreeNorth}ᶜ) 3 w' from
      congrFun hww sphereThreeNorth)

theorem localizationInjective_threeSpace :
    Function.Injective (fun w : IntegralHomology ThreeSpace 3 =>
      fun x : ThreeSpace => absoluteToRelative ThreeSpace ({x}ᶜ) 3 w) :=
  localizationInjective_of_subsingleton_topHomology subsingleton_integralHomology_three_threeSpace

theorem existsFundamentalClassAt_sphereThree (o : TangentOrientationSection SphereThree) :
    existsFundamentalClassAt o sphereThreeNorth :=
  (absoluteToRelative_punctured_threeSphere_bijective sphereThreeNorth).2
    (localOrientationClass o sphereThreeNorth)

theorem exists_unique_fundamentalClass_sphereThree_of_localClassTransport
    (o : TangentOrientationSection SphereThree) (h : localClassTransport o) :
    ∃! z : IntegralHomology SphereThree 3, ∀ x : SphereThree,
      absoluteToRelative SphereThree ({x}ᶜ) 3 z = localOrientationClass o x :=
  exists_unique_fundamentalClass_sphereThree_of_localClassRealizationLocallyConstant o
    (localClassRealizationLocallyConstant_of_localClassTransport o h)

theorem not_exists_realizationAt_threeSpace_of_euclideanStandardSimplexClassGenerator
    (hgen : euclideanStandardSimplexClassGenerator.{0})
    (o : TangentOrientationSection ThreeSpace) :
    ¬ (∃ z : IntegralHomology ThreeSpace 3, ∀ x : ThreeSpace,
      absoluteToRelative ThreeSpace ({x}ᶜ) 3 z = localOrientationClass o x) := by
  rintro ⟨z, hz⟩
  have hz0 : z = 0 := subsingleton_integralHomology_three_threeSpace.allEq z 0
  have hne : localOrientationClass o 0 ≠ 0 := by
    intro h0
    have hbij := localOrientationClass_generator_of_euclideanStandardSimplex o 0 hgen
    have h1 : (1 : ℤ) • localOrientationClass o 0 =
        (0 : ℤ) • localOrientationClass o 0 := by
      rw [h0]
      simp
    exact one_ne_zero (hbij.1 h1)
  exact hne ((hz 0).symm.trans (by rw [hz0, map_zero]))

theorem not_forall_surjective_absoluteToRelative_of_manifold_t2 :
    ¬ (∀ (M : Type) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold ThreeModel ∞ M] [T2Space M] (x : M),
      Function.Surjective (absoluteToRelative M ({x}ᶜ) 3)) :=
  fun h => not_surjective_absoluteToRelative_threeSpace_compl_origin (h ThreeSpace 0)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Lean in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ns : Name := `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  let decls : List String :=
    ["ClosedThreeManifoldFundamentalClassRealizationInput",
      "ClosedThreeManifoldFundamentalClassLocalizationInjective",
      "exists_unique_fundamentalClass_of_realizationInput_of_localizationInjective",
      "realizationInput_connected_of_connectingInput",
      "realizationInput_connected_of_connectingVanishing_of_localClassTransport",
      "localizationInjective_of_forall_exists_injective",
      "localizationInjective_connected_of_noncompactThreeManifoldTopHomologyVanishing",
      "localizationInjective_of_subsingleton_topHomology",
      "localizationInjective_sphereThree",
      "localizationInjective_threeSpace",
      "existsFundamentalClassAt_sphereThree",
      "exists_unique_fundamentalClass_sphereThree_of_localClassTransport",
      "not_exists_realizationAt_threeSpace_of_euclideanStandardSimplexClassGenerator",
      "not_forall_surjective_absoluteToRelative_of_manifold_t2"]
  for s in decls do
    let n := ns.str s
    let axs ← Lean.collectAxioms n
    unless axs.all (fun a => allowed.contains a) do
      throwError "unexpected axioms for {n}: {axs}"
