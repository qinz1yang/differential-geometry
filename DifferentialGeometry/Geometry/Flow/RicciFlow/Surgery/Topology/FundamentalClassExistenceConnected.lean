import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassDisconnectedObstruction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PuncturedVanishingHypotheses
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ThreeManifoldHomologyFrontier
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology

universe u

def ClosedConnectedFundamentalClassLocalizationBijective : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] (x₀ : M),
    Function.Bijective (absoluteToRelative M ({x₀}ᶜ) 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M]

omit [IsManifold ThreeModel ∞ M] in
theorem localizationBijective_iff_surjective_and_subsingleton_punctured (x : M) :
    Function.Bijective (absoluteToRelative M ({x}ᶜ) 3) ↔
      Function.Surjective (absoluteToRelative M ({x}ᶜ) 3) ∧
        Subsingleton (IntegralHomology ({x}ᶜ : Set M) 3) :=
  ⟨fun h => ⟨h.2,
      (subsingleton_integralHomology_compl_singleton_three_iff_injective_absoluteToRelative
        x).mpr h.1⟩,
    fun h => ⟨
      (subsingleton_integralHomology_compl_singleton_three_iff_injective_absoluteToRelative
        x).mp h.2, h.1⟩⟩

theorem closedConnectedFundamentalClassLocalizationBijective_of_surjective_of_noncompactVanishing
    (hsurj : ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold ThreeModel ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M] (x₀ : M),
      Function.Surjective (absoluteToRelative M ({x₀}ᶜ) 3))
    (hv : noncompactThreeManifoldTopHomologyVanishing.{u}) :
    ClosedConnectedFundamentalClassLocalizationBijective.{u} :=
  fun M _ _ _ _ _ _ x₀ => by
    have hsub :=
      subsingleton_integralHomology_compl_singleton_of_noncompactThreeManifoldTopHomologyVanishing
        hv x₀
    exact ⟨absoluteToRelative_compl_singleton_injective_of_subsingleton x₀ hsub, hsurj M x₀⟩

theorem closedConnectedFundamentalClassLocalizationBijective_of_connectingInput
    (h : ClosedThreeManifoldFundamentalClassConnectingInput.{u}) :
    ClosedConnectedFundamentalClassLocalizationBijective.{u} :=
  closedConnectedFundamentalClassLocalizationBijective_of_surjective_of_noncompactVanishing
    (fun M _ _ _ _ _ _ x₀ =>
      (absoluteToRelative_surjective_iff_integralRelativeConnecting_eq_zero x₀).mpr
        (h.1 M x₀))
    h.2.1

theorem exists_unique_fundamentalClass_of_localizationBijective
    (h : ClosedConnectedFundamentalClassLocalizationBijective.{u})
    (o : TangentOrientationSection M) [T2Space M] [CompactSpace M] [ConnectedSpace M]
    (hprop : localClassRealizationLocallyConstant o) (x₀ : M) :
    ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x := by
  have hb := h M x₀
  exact exists_unique_fundamentalClass_of_local_realization o hprop x₀
    ⟨(hb.2 (localOrientationClass o x₀)).choose,
      (hb.2 (localOrientationClass o x₀)).choose_spec⟩ hb.1

theorem exists_unique_fundamentalClass_of_localizationBijective_of_localClassTransport
    (h : ClosedConnectedFundamentalClassLocalizationBijective.{u})
    (o : TangentOrientationSection M) [T2Space M] [CompactSpace M] [ConnectedSpace M]
    (htransport : localClassTransport o) (x₀ : M) :
    ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x :=
  exists_unique_fundamentalClass_of_localizationBijective h o
    (localClassRealizationLocallyConstant_of_localClassTransport o htransport) x₀

theorem realizationInput_connected_of_localizationBijective
    (h : ClosedConnectedFundamentalClassLocalizationBijective.{u})
    (o : TangentOrientationSection M) [T2Space M] [CompactSpace M] [ConnectedSpace M]
    (hprop : localClassRealizationLocallyConstant o) (x₀ : M) :
    ∃ z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x :=
  (exists_unique_fundamentalClass_of_localizationBijective h o hprop x₀).exists

theorem localizationInjective_connected_of_localizationBijective
    (h : ClosedConnectedFundamentalClassLocalizationBijective.{u})
    [T2Space M] [CompactSpace M] [ConnectedSpace M] (x₀ : M) :
    Function.Injective (fun w : IntegralHomology M 3 =>
      fun x : M => absoluteToRelative M ({x}ᶜ) 3 w) :=
  fun w w' hww =>
    injective_localization_of_exists_injective_at ⟨x₀, (h M x₀).1⟩ w w'
      fun x => congrFun hww x

private theorem not_subsingleton_integralSingularHomology_three_compl_singleton_sum_inr
    (x : SphereThree) :
    ¬ Subsingleton
      (integralSingularHomology 3 ({Sum.inr x}ᶜ : Set (SphereThree ⊕ SphereThree))) := by
  intro hsub
  obtain ⟨α, hα⟩ := exists_ne_zero_integralSingularHomology_three_sphereThree
  let i : C(SphereThree, ↥({Sum.inr x}ᶜ : Set (SphereThree ⊕ SphereThree))) :=
    ⟨fun y => ⟨Sum.inl y, Sum.inl_ne_inr⟩, continuous_inl.subtype_mk _⟩
  let r : C(↥({Sum.inr x}ᶜ : Set (SphereThree ⊕ SphereThree)), SphereThree) :=
    ⟨fun z => Sum.elim (fun y => y) (fun _ => x) z.1,
      (continuous_id.sumElim continuous_const).comp continuous_subtype_val⟩
  have hri : r.comp i = ContinuousMap.id SphereThree := by
    ext y
    rfl
  have hid : (integralSingularHomologyMap 3 r).comp (integralSingularHomologyMap 3 i)
      = LinearMap.id := by
    rw [← integralSingularHomologyMap_comp 3 i r, hri, integralSingularHomologyMap_id]
  have hinj : Function.Injective (integralSingularHomologyMap 3 i) := by
    intro a b hab
    have ha : integralSingularHomologyMap 3 r (integralSingularHomologyMap 3 i a) = a := by
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using congrArg (fun f => f a) hid
    have hb : integralSingularHomologyMap 3 r (integralSingularHomologyMap 3 i b) = b := by
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using congrArg (fun f => f b) hid
    rw [hab] at ha
    exact ha.symm.trans hb
  have hzero : integralSingularHomologyMap 3 i α = 0 := hsub.allEq _ _
  exact hα (hinj (by rw [hzero, map_zero]))

theorem not_subsingleton_integralHomology_three_compl_singleton_sum_inr
    (x : SphereThree) :
    ¬ Subsingleton
      (IntegralHomology ({Sum.inr x}ᶜ : Set (SphereThree ⊕ SphereThree)) 3) :=
  not_subsingleton_integralSingularHomology_three_compl_singleton_sum_inr x

theorem not_injective_absoluteToRelative_compl_singleton_sum_inl (x : SphereThree) :
    ¬ Function.Injective
      (absoluteToRelative (SphereThree ⊕ SphereThree) ({Sum.inl x}ᶜ) 3) :=
  fun hinj =>
    not_subsingleton_integralHomology_three_compl_singleton_disjointUnion x
      ((subsingleton_integralHomology_compl_singleton_three_iff_injective_absoluteToRelative
        (M := SphereThree ⊕ SphereThree) (Sum.inl x)).mpr hinj)

theorem not_injective_absoluteToRelative_compl_singleton_sum_inr (x : SphereThree) :
    ¬ Function.Injective
      (absoluteToRelative (SphereThree ⊕ SphereThree) ({Sum.inr x}ᶜ) 3) :=
  fun hinj =>
    not_subsingleton_integralHomology_three_compl_singleton_sum_inr x
      ((subsingleton_integralHomology_compl_singleton_three_iff_injective_absoluteToRelative
        (M := SphereThree ⊕ SphereThree) (Sum.inr x)).mpr hinj)

theorem not_exists_injective_absoluteToRelative_compl_singleton_sum_sphereThree :
    ¬ ∃ x : SphereThree ⊕ SphereThree,
      Function.Injective (absoluteToRelative (SphereThree ⊕ SphereThree) ({x}ᶜ) 3) := by
  rintro ⟨x, hx⟩
  rcases x with a | b
  · exact not_injective_absoluteToRelative_compl_singleton_sum_inl a hx
  · exact not_injective_absoluteToRelative_compl_singleton_sum_inr b hx

theorem not_forall_injective_absoluteToRelative_compl_singleton_of_compactSpace :
    ¬ (∀ (M : Type) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold ThreeModel ∞ M] [T2Space M] [CompactSpace M] (x₀ : M),
      Function.Injective (absoluteToRelative M ({x₀}ᶜ) 3)) :=
  fun h => not_injective_absoluteToRelative_compl_singleton_sum_inl sphereThreeNorth
    (h (SphereThree ⊕ SphereThree) (Sum.inl sphereThreeNorth))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Lean in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ns : Name := `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  let decls : List String :=
    ["ClosedConnectedFundamentalClassLocalizationBijective",
      "localizationBijective_iff_surjective_and_subsingleton_punctured",
      "closedConnectedFundamentalClassLocalizationBijective_of_surjective_of_noncompactVanishing",
      "closedConnectedFundamentalClassLocalizationBijective_of_connectingInput",
      "exists_unique_fundamentalClass_of_localizationBijective",
      "exists_unique_fundamentalClass_of_localizationBijective_of_localClassTransport",
      "realizationInput_connected_of_localizationBijective",
      "localizationInjective_connected_of_localizationBijective",
      "not_subsingleton_integralHomology_three_compl_singleton_sum_inr",
      "not_injective_absoluteToRelative_compl_singleton_sum_inl",
      "not_injective_absoluteToRelative_compl_singleton_sum_inr",
      "not_exists_injective_absoluteToRelative_compl_singleton_sum_sphereThree",
      "not_forall_injective_absoluteToRelative_compl_singleton_of_compactSpace"]
  for s in decls do
    let n := ns.str s
    let axs ← Lean.collectAxioms n
    unless axs.all (fun a => allowed.contains a) do
      throwError "unexpected axioms for {n}: {axs}"
