import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassMinimalHypotheses
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassNoncompactDuality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NoncompactVanishingFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassDuality

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set
open scoped Simplicial Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology

universe u

theorem not_puncturedThreeManifoldTopHomologyVanishing_threeSpace :
    ¬ PuncturedThreeManifoldTopHomologyVanishing ThreeSpace 0 :=
  fun h => not_subsingleton_integralSingularHomology_two_compl_origin h.1.1

theorem not_closedThreeManifoldPuncturedVanishing_threeSpace :
    ¬ ClosedThreeManifoldPuncturedVanishing ThreeSpace 0 :=
  fun h => not_subsingleton_integralSingularHomology_two_compl_origin h.1

theorem not_closedThreeManifoldFundamentalClassFrontier :
    ¬ ClosedThreeManifoldFundamentalClassFrontier.{0} :=
  fun h => not_puncturedThreeManifoldTopHomologyVanishing_threeSpace (h.1 ThreeSpace 0)

theorem not_poincareDualityTwoOne_punctured_threeSpace :
    ¬ poincareDualityTwoOne ({0}ᶜ : Set ThreeSpace) :=
  not_poincareDualityTwoOne_punctured_of_finrank_eq_three ThreeSpace (by simp)

theorem subsingleton_integralSingularHomology_compl_singleton_of_homeomorph_puncture
    {M : Type u} [TopologicalSpace M] (x y : M) (n : ℕ)
    (e : ({x}ᶜ : Set M) ≃ₜ ({y}ᶜ : Set M))
    (h : Subsingleton (integralSingularHomology n ({x}ᶜ : Set M))) :
    Subsingleton (integralSingularHomology n ({y}ᶜ : Set M)) :=
  @Function.Injective.subsingleton (integralSingularHomology n ({y}ᶜ : Set M))
    (integralSingularHomology n ({x}ᶜ : Set M))
    (integralSingularHomologyHomotopyEquiv n e.toHomotopyEquiv).symm
    (integralSingularHomologyHomotopyEquiv n e.toHomotopyEquiv).symm.injective h

theorem puncturedThreeManifoldTopHomologyVanishing_of_puncturedVanishing_of_punctureHomeomorph
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] (x₀ : M)
    (h : ClosedThreeManifoldPuncturedVanishing M x₀)
    (htrans : ∀ x : M, Nonempty (({x₀}ᶜ : Set M) ≃ₜ ({x}ᶜ : Set M))) :
    PuncturedThreeManifoldTopHomologyVanishing M x₀ :=
  ⟨h, fun x => (htrans x).elim fun e =>
    subsingleton_integralSingularHomology_compl_singleton_of_homeomorph_puncture x₀ x 3 e h.2⟩

theorem puncturedThreeManifoldTopHomologyVanishing_of_noncompactPoincareDuality_of_noncompactVanishing
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (x₀ : M) (h : noncompactPoincareDualityTwoOne ({x₀}ᶜ : Set M))
    (hv : noncompactThreeManifoldTopHomologyVanishing.{u}) :
    PuncturedThreeManifoldTopHomologyVanishing M x₀ :=
  ⟨⟨subsingleton_integralHomology_compl_singleton_two_of_noncompactPoincareDuality_of_simplyConnected
      x₀ h,
    subsingleton_integralHomology_compl_singleton_of_noncompactThreeManifoldTopHomologyVanishing
      hv x₀⟩,
    fun x =>
      subsingleton_integralHomology_compl_singleton_of_noncompactThreeManifoldTopHomologyVanishing
        hv x⟩

theorem absoluteToRelative_bijective_of_noncompactPoincareDuality_of_noncompactVanishing
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (x₀ : M) (h : noncompactPoincareDualityTwoOne ({x₀}ᶜ : Set M))
    (hv : noncompactThreeManifoldTopHomologyVanishing.{u}) :
    Function.Bijective (absoluteToRelative M ({x₀}ᶜ) 3) :=
  ⟨absoluteToRelative_compl_singleton_injective_of_subsingleton x₀
      (subsingleton_integralHomology_compl_singleton_of_noncompactThreeManifoldTopHomologyVanishing
        hv x₀),
    absoluteToRelative_surjective_of_noncompactPoincareDuality_punctured x₀ h⟩

theorem closedThreeManifoldPuncturedVanishing_sphereThree (x : SphereThree) :
    ClosedThreeManifoldPuncturedVanishing SphereThree x :=
  ⟨subsingleton_integralHomology_two_compl_singleton_sphereThree x,
    subsingleton_integralHomology_three_compl_singleton_sphereThree x⟩

theorem puncturedThreeManifoldTopHomologyVanishing_sphereThree (x₀ : SphereThree) :
    PuncturedThreeManifoldTopHomologyVanishing SphereThree x₀ :=
  ⟨⟨subsingleton_integralHomology_two_compl_singleton_sphereThree x₀,
      subsingleton_integralHomology_three_compl_singleton_sphereThree x₀⟩,
    fun x => subsingleton_integralHomology_three_compl_singleton_sphereThree x⟩

theorem absoluteToRelative_bijective_sphereThree (x₀ : SphereThree) :
    Function.Bijective (absoluteToRelative SphereThree ({x₀}ᶜ) 3) :=
  ⟨absoluteToRelative_compl_singleton_injective_of_subsingleton x₀
      (subsingleton_integralHomology_three_compl_singleton_sphereThree x₀),
    absoluteToRelative_surjective_of_subsingleton_punctured x₀
      (subsingleton_integralHomology_two_compl_singleton_sphereThree x₀)⟩

def ClosedThreeManifoldFundamentalClassConnectingInput : Prop :=
  (∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
      [T2Space M] [CompactSpace M] [ConnectedSpace M] (x₀ : M),
      integralRelativeConnecting 2 ({x₀}ᶜ : Set M) = 0) ∧
  noncompactThreeManifoldTopHomologyVanishing.{u} ∧
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
      [T2Space M] [CompactSpace M] [ConnectedSpace M] (o : TangentOrientationSection M),
      localClassTransport o

theorem exists_unique_fundamentalClass_of_connectingInput
    (h : ClosedThreeManifoldFundamentalClassConnectingInput.{u})
    (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    (x₀ : M) (o : TangentOrientationSection M) :
    ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x :=
  exists_unique_fundamentalClass_of_connecting_eq_zero_of_localClassTransport o (h.2.2 M o)
    x₀ (h.1 M x₀)
    (subsingleton_integralHomology_compl_singleton_of_noncompactThreeManifoldTopHomologyVanishing
      h.2.1 x₀)

def ClosedThreeManifoldFundamentalClassStandingHypotheses : Prop :=
  (∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
      [T2Space M] [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] (x₀ : M),
      Function.Bijective (absoluteToRelative M ({x₀}ᶜ) 3)) ∧
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
      [T2Space M] [CompactSpace M] [ConnectedSpace M] (o : TangentOrientationSection M),
      localClassTransport o

theorem exists_unique_fundamentalClass_of_absoluteToRelative_bijective_of_localClassTransport
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    [ConnectedSpace M] (o : TangentOrientationSection M) (htransport : localClassTransport o)
    (x₀ : M) (hbij : Function.Bijective (absoluteToRelative M ({x₀}ᶜ) 3)) :
    ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x :=
  exists_unique_fundamentalClass_of_surjective_and_injective o
    (localClassRealizationLocallyConstant_of_localClassTransport o htransport) x₀ hbij.2 hbij.1

theorem exists_unique_fundamentalClass_of_closedThreeManifoldStandingHypotheses
    (h : ClosedThreeManifoldFundamentalClassStandingHypotheses.{u})
    (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (x₀ : M) (o : TangentOrientationSection M) :
    ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x :=
  exists_unique_fundamentalClass_of_absoluteToRelative_bijective_of_localClassTransport o
    (h.2 M o) x₀ (h.1 M x₀)

theorem closedThreeManifoldFundamentalClassStandingHypotheses_of_noncompactPoincareDuality_of_noncompactVanishing
    (hpd : ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold ThreeModel ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
      [SimplyConnectedSpace M] (x₀ : M), noncompactPoincareDualityTwoOne ({x₀}ᶜ : Set M))
    (hv : noncompactThreeManifoldTopHomologyVanishing.{u})
    (htransport : ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold ThreeModel ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
      (o : TangentOrientationSection M), localClassTransport o) :
    ClosedThreeManifoldFundamentalClassStandingHypotheses.{u} :=
  ⟨fun M _ _ _ _ _ _ _ x₀ =>
    absoluteToRelative_bijective_of_noncompactPoincareDuality_of_noncompactVanishing x₀
      (hpd M x₀) hv,
    htransport⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Lean in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ns := `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  let names := ["not_puncturedThreeManifoldTopHomologyVanishing_threeSpace",
    "not_closedThreeManifoldPuncturedVanishing_threeSpace",
    "not_closedThreeManifoldFundamentalClassFrontier",
    "not_poincareDualityTwoOne_punctured_threeSpace",
    "subsingleton_integralSingularHomology_compl_singleton_of_homeomorph_puncture",
    "puncturedThreeManifoldTopHomologyVanishing_of_puncturedVanishing_of_punctureHomeomorph",
    "puncturedThreeManifoldTopHomologyVanishing_of_noncompactPoincareDuality_of_noncompactVanishing",
    "absoluteToRelative_bijective_of_noncompactPoincareDuality_of_noncompactVanishing",
    "closedThreeManifoldPuncturedVanishing_sphereThree",
    "puncturedThreeManifoldTopHomologyVanishing_sphereThree",
    "absoluteToRelative_bijective_sphereThree",
    "ClosedThreeManifoldFundamentalClassConnectingInput",
    "exists_unique_fundamentalClass_of_connectingInput",
    "ClosedThreeManifoldFundamentalClassStandingHypotheses",
    "exists_unique_fundamentalClass_of_absoluteToRelative_bijective_of_localClassTransport",
    "exists_unique_fundamentalClass_of_closedThreeManifoldStandingHypotheses",
    "closedThreeManifoldFundamentalClassStandingHypotheses_of_noncompactPoincareDuality_of_noncompactVanishing"]
  for s in names do
    let n := ns.str s
    let axs ← Lean.collectAxioms n
    unless axs.all (fun a => allowed.contains a) do
      throwError "unexpected axioms for {n}: {axs}"
