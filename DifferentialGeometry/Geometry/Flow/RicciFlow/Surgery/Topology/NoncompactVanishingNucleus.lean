import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassRealizationCriterion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassMinimalHypotheses
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PuncturedVanishingHypotheses
import DifferentialGeometry.Topology.Homology.NoncompactTopHomologyVanishing

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set
open scoped Simplicial Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology

universe u

theorem noncompactPoincareDualityTopHomology_iff_noncompactThreeManifoldTopHomologyVanishing :
    noncompactPoincareDualityTopHomology.{u} ↔
      noncompactThreeManifoldTopHomologyVanishing.{u} :=
  ⟨noncompactThreeManifoldTopHomologyVanishing_of_noncompactPoincareDualityTopHomology,
    fun h X _ _ _ _ _ => by
      exact @noncompactPoincareDualityThreeZero_of_subsingleton X _ (h X)
        (subsingleton_integralCompactSupportZeroCocycles X)⟩

theorem noncompactThreeManifoldTopHomologyVanishing_iff_forall_isCompact_subset :
    noncompactThreeManifoldTopHomologyVanishing.{u} ↔
      ∀ (X : Type u) [TopologicalSpace X] [ChartedSpace ThreeSpace X]
        [IsManifold ThreeModel ∞ X] [ConnectedSpace X] [NoncompactSpace X],
        ∀ K : Set X, IsCompact K →
          ∃ U : Set X, K ⊆ U ∧ Subsingleton (IntegralHomology U 3) :=
  ⟨fun h X _ _ _ _ _ =>
      (subsingleton_integralSingularHomology_succ_iff_forall_isCompact_subset (X := X) 2).mp
        (h X),
    noncompactThreeManifoldTopHomologyVanishing_of_forall_isCompact_subset⟩

def ClosedThreeManifoldFundamentalClassLocalDegreeInput : Prop :=
  (∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
      [T2Space M] [CompactSpace M] [ConnectedSpace M] (x₀ : M),
      integralRelativeConnecting 2 ({x₀}ᶜ : Set M) = 0) ∧
  (∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
      [T2Space M] [CompactSpace M] [ConnectedSpace M] (x₀ : M),
      Function.Injective (absoluteToRelative M ({x₀}ᶜ) 3)) ∧
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
      [T2Space M] [CompactSpace M] [ConnectedSpace M] (o : TangentOrientationSection M),
      localClassTransport o

theorem closedThreeManifoldFundamentalClassLocalDegreeInput_of_connectingInput
    (h : ClosedThreeManifoldFundamentalClassConnectingInput.{u}) :
    ClosedThreeManifoldFundamentalClassLocalDegreeInput.{u} := by
  refine ⟨h.1, ?_, h.2.2⟩
  intro M _ _ _ _ _ _ x₀
  have h₃ :=
    subsingleton_integralHomology_compl_singleton_of_noncompactThreeManifoldTopHomologyVanishing
      h.2.1 x₀
  exact (subsingleton_integralHomology_compl_singleton_three_iff_injective_absoluteToRelative
    (M := M) x₀).mp h₃

theorem exists_unique_fundamentalClass_of_connecting_eq_zero_of_injective_absoluteToRelative
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (o : TangentOrientationSection M) [ConnectedSpace M]
    (hprop : localClassRealizationLocallyConstant o) (x₀ : M)
    (hδ : integralRelativeConnecting 2 ({x₀}ᶜ : Set M) = 0)
    (hinj : Function.Injective (absoluteToRelative M ({x₀}ᶜ) 3)) :
    ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x :=
  exists_unique_fundamentalClass_of_locallyConstant_and_connecting_eq_zero_and_subsingleton
    o x₀ hprop hδ
    ((subsingleton_integralHomology_compl_singleton_three_iff_injective_absoluteToRelative x₀).mpr
      hinj)

theorem exists_unique_fundamentalClass_of_localDegreeInput
    (h : ClosedThreeManifoldFundamentalClassLocalDegreeInput.{u})
    (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    (o : TangentOrientationSection M) (x₀ : M) :
    ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x :=
  exists_unique_fundamentalClass_of_connecting_eq_zero_of_localClassTransport o (h.2.2 M o) x₀
    (h.1 M x₀)
    ((subsingleton_integralHomology_compl_singleton_three_iff_injective_absoluteToRelative x₀).mpr
      (h.2.1 M x₀))

theorem subsingleton_integralHomology_three_threeSpace :
    Subsingleton (IntegralHomology ThreeSpace 3) :=
  subsingleton_integralSingularHomology_three_euclideanThree

theorem injective_absoluteToRelative_compl_singleton_sphereThree
    (x : DifferentialGeometry.Topology.SphereThree) :
    Function.Injective (absoluteToRelative DifferentialGeometry.Topology.SphereThree ({x}ᶜ) 3) :=
  (absoluteToRelative_bijective_sphereThree x).1

theorem not_forall_subsingleton_integralHomology_three_of_isManifold :
    ¬ (∀ (X : Type) [TopologicalSpace X] [ChartedSpace ThreeSpace X]
        [IsManifold ThreeModel ∞ X] [ConnectedSpace X], Subsingleton (IntegralHomology X 3)) :=
  fun h => not_subsingleton_integralSingularHomology_three_sphereThree
    (h DifferentialGeometry.Topology.SphereThree)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Lean in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ns : Name := `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  let decls : List String :=
    ["noncompactPoincareDualityTopHomology_iff_noncompactThreeManifoldTopHomologyVanishing",
      "noncompactThreeManifoldTopHomologyVanishing_iff_forall_isCompact_subset",
      "ClosedThreeManifoldFundamentalClassLocalDegreeInput",
      "closedThreeManifoldFundamentalClassLocalDegreeInput_of_connectingInput",
      "exists_unique_fundamentalClass_of_connecting_eq_zero_of_injective_absoluteToRelative",
      "exists_unique_fundamentalClass_of_localDegreeInput",
      "subsingleton_integralHomology_three_threeSpace",
      "injective_absoluteToRelative_compl_singleton_sphereThree",
      "not_forall_subsingleton_integralHomology_three_of_isManifold"]
  for s in decls do
    let n := ns.str s
    let axs ← Lean.collectAxioms n
    unless axs.all (fun a => allowed.contains a) do
      throwError "unexpected axioms for {n}: {axs}"
