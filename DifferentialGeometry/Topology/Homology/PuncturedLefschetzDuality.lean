import DifferentialGeometry.Topology.Homology.NoncompactPoincareDualityFrontier
import DifferentialGeometry.Topology.Homology.PoincareDualityTwoOnePairing
import DifferentialGeometry.Topology.Homology.Relative.Basic
import DifferentialGeometry.Topology.Homology.SecondHomologyVanishingClosedThreeManifold
import DifferentialGeometry.Topology.ThreeManifold.SphereTwoTimesCircleCohomology
import DifferentialGeometry.Topology.ThreeManifold.SphereTwoTimesCircleLift

noncomputable section

open CategoryTheory Set

open scoped Manifold ContDiff

universe u

namespace DifferentialGeometry.Topology

def puncturedLefschetzDualityTwoOne : Prop :=
  ∀ (M : ConnectedClosedOrientedManifold.{u} 3) (x : M.Carrier),
    Nonempty (integralSingularHomology 2 ({x}ᶜ : Set M.Carrier) ≅
      integralSingularCohomology 1 M.Carrier)

theorem noncompactPoincareDualityTwoOne_iff_nonempty_iso_cohomologyOne
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] (x : X) :
    noncompactPoincareDualityTwoOne ({x}ᶜ : Set X) ↔
      Nonempty (integralSingularHomology 2 ({x}ᶜ : Set X) ≅
        integralSingularCohomology 1 X) := by
  rw [noncompactPoincareDualityTwoOne_iff_nonempty_linearEquiv_cohomologyOne X x]
  exact ⟨fun ⟨e⟩ => ⟨e.toModuleIso⟩,
    fun ⟨e⟩ => ⟨LinearEquiv.ofBijective e.hom.hom
      ((ConcreteCategory.isIso_iff_bijective e.hom).mp inferInstance)⟩⟩

theorem noncompactPoincareDualityTwoOne_compl_singleton_of_puncturedLefschetzDualityTwoOne
    (h : puncturedLefschetzDualityTwoOne.{u}) (M : ConnectedClosedOrientedManifold.{u} 3)
    (x : M.Carrier) :
    noncompactPoincareDualityTwoOne ({x}ᶜ : Set M.Carrier) :=
  (noncompactPoincareDualityTwoOne_iff_nonempty_iso_cohomologyOne M.Carrier x).mpr (h M x)

theorem puncturedLefschetzDualityTwoOne_iff_forall_noncompactPoincareDuality :
    puncturedLefschetzDualityTwoOne.{u} ↔
      ∀ (M : ConnectedClosedOrientedManifold.{u} 3) (x : M.Carrier),
        noncompactPoincareDualityTwoOne ({x}ᶜ : Set M.Carrier) :=
  ⟨fun h M x =>
      noncompactPoincareDualityTwoOne_compl_singleton_of_puncturedLefschetzDualityTwoOne h M x,
    fun h M x =>
      (noncompactPoincareDualityTwoOne_iff_nonempty_iso_cohomologyOne M.Carrier x).mp (h M x)⟩

theorem
    subsingleton_integralSingularHomology_two_compl_singleton_of_puncturedLefschetzDualityTwoOne
    (h : puncturedLefschetzDualityTwoOne.{u}) (M : ConnectedClosedOrientedManifold.{u} 3)
    [SimplyConnectedSpace M.Carrier] (x : M.Carrier) :
    Subsingleton (integralSingularHomology 2 ({x}ᶜ : Set M.Carrier)) :=
  haveI : Subsingleton (integralSingularCohomology 1 M.Carrier) :=
    integralSingularCohomology_one_subsingleton (X := M.Carrier)
  subsingleton_integralSingularHomology_two_compl_singleton_of_noncompactPoincareDuality x
    (noncompactPoincareDualityTwoOne_compl_singleton_of_puncturedLefschetzDualityTwoOne h M x)

theorem subsingleton_integralSingularHomology_two_of_puncturedLefschetzDualityTwoOne
    (h : puncturedLefschetzDualityTwoOne.{u}) (M : ConnectedClosedOrientedManifold.{u} 3)
    [SimplyConnectedSpace M.Carrier] (x : M.Carrier) :
    Subsingleton (integralSingularHomology 2 M.Carrier) :=
  subsingleton_integralSingularHomology_two_of_subsingleton_compl_singleton x
    (subsingleton_integralSingularHomology_two_compl_singleton_of_puncturedLefschetzDualityTwoOne
      h M x)

theorem subsingleton_integralSingularHomology_two_of_manifoldOrientation_and_puncturedLefschetz
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (ho : ManifoldOrientation (𝓡 3) M 3) (h : puncturedLefschetzDualityTwoOne.{u}) (x : M) :
    Subsingleton (integralSingularHomology 2 M) :=
  subsingleton_integralSingularHomology_two_of_puncturedLefschetzDualityTwoOne h
    { Carrier := M, orientation := ho } x

theorem subsingleton_integralSingularHomology_one_compl_singleton
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] (x : M)
    [Subsingleton (integralSingularHomology 1 M)] :
    Subsingleton (integralSingularHomology 1 ({x}ᶜ : Set M)) := by
  have hzero : integralRelativeConnecting 1 ({x}ᶜ : Set M) = 0 := by
    ext z
    simp [(subsingleton_integralRelativeHomology_two_compl_singleton x).allEq z 0]
  have hex := LinearMap.exact_iff.mp
    (integralRelative_exact_subspace (X := M) 1 ({x}ᶜ : Set M))
  have hinj : Function.Injective
      (integralSingularHomologyMap 1 (singularSubspaceInclusion ({x}ᶜ : Set M))) := by
    rw [← LinearMap.ker_eq_bot, hex, hzero, LinearMap.range_zero]
  exact hinj.subsingleton

theorem subsingleton_integralSingularHomology_one_compl_singleton_of_simplyConnected
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] (x : M) :
    Subsingleton (integralSingularHomology 1 ({x}ᶜ : Set M)) :=
  haveI : Subsingleton (integralSingularHomology 1 M) :=
    integralSingularHomology_one_subsingleton (X := M)
  subsingleton_integralSingularHomology_one_compl_singleton x

theorem
    subsingleton_integralSingularHomology_one_two_punctured_of_puncturedLefschetzDualityTwoOne
    (h : puncturedLefschetzDualityTwoOne.{u}) (M : ConnectedClosedOrientedManifold.{u} 3)
    [SimplyConnectedSpace M.Carrier] (x : M.Carrier) :
    Subsingleton (integralSingularHomology 1 ({x}ᶜ : Set M.Carrier)) ∧
      Subsingleton (integralSingularHomology 2 ({x}ᶜ : Set M.Carrier)) ∧
        Subsingleton (integralSingularHomology 2 M.Carrier) :=
  ⟨subsingleton_integralSingularHomology_one_compl_singleton_of_simplyConnected x,
    subsingleton_integralSingularHomology_two_compl_singleton_of_puncturedLefschetzDualityTwoOne
      h M x,
    subsingleton_integralSingularHomology_two_of_puncturedLefschetzDualityTwoOne h M x⟩

theorem nonempty_iso_homologyTwo_compl_singleton_cohomologyOne_sphereThree (v : SphereThree) :
    Nonempty (integralSingularHomology 2 ({v}ᶜ : Set SphereThree) ≅
      integralSingularCohomology 1 SphereThree) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_homologyTwo_compl_singleton_sphereThree v
  exact ⟨e.toModuleIso⟩

theorem not_subsingleton_integralSingularCohomology_one_sphereTwoTimesCircleModelCopy :
    ¬ Subsingleton (integralSingularCohomology 1 sphereTwoTimesCircleModelCopy.Q) := by
  intro h
  have hc := integralSingularCohomologyEquivOfHomeomorph
    sphereTwoTimesCircleModelCopy.equiv.toHomeomorph.symm 1
  refine not_subsingleton_integralSingularCohomology_one_sphereTwoTimesCircle ⟨fun a b => ?_⟩
  obtain ⟨u, rfl⟩ := hc.surjective a
  obtain ⟨v, rfl⟩ := hc.surjective b
  rw [h.allEq u v]

theorem
    not_forall_subsingleton_integralSingularHomology_two_compl_singleton_of_puncturedLefschetz
    (h : puncturedLefschetzDualityTwoOne.{0}) :
    ¬ (∀ (M : ConnectedClosedOrientedManifold.{0} 3) (x : M.Carrier),
        Subsingleton (integralSingularHomology 2 ({x}ᶜ : Set M.Carrier))) := by
  intro hvan
  let x : sphereTwoTimesCircleLift.Carrier :=
    Classical.choice (inferInstance : Nonempty sphereTwoTimesCircleLift.Carrier)
  obtain ⟨e⟩ := h sphereTwoTimesCircleLift x
  have hsub : Subsingleton
      (integralSingularHomology 2 ({x}ᶜ : Set sphereTwoTimesCircleLift.Carrier)) :=
    hvan sphereTwoTimesCircleLift x
  have hsurj : Function.Surjective
      (e.hom.hom : integralSingularHomology 2 ({x}ᶜ : Set sphereTwoTimesCircleLift.Carrier) →
        integralSingularCohomology 1 sphereTwoTimesCircleLift.Carrier) :=
    ((ConcreteCategory.isIso_iff_bijective e.hom).mp inferInstance).2
  refine not_subsingleton_integralSingularCohomology_one_sphereTwoTimesCircleModelCopy
    ⟨fun a b => ?_⟩
  obtain ⟨u, hu⟩ := hsurj a
  obtain ⟨v, hv⟩ := hsurj b
  rw [← hu, ← hv, hsub.allEq u v]

end DifferentialGeometry.Topology
