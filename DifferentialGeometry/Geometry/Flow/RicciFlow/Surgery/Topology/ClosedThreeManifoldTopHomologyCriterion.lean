import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassInputReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassNoncompactDuality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NoncompactVanishingFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NoncompactVanishingNucleus
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PuncturedTopHomologyCriterion
import DifferentialGeometry.Topology.Algebra.Module.InfiniteCyclicCriterion
import DifferentialGeometry.Topology.FundamentalGroup.Sphere
import DifferentialGeometry.Topology.Homology.HurewiczFrontier
import DifferentialGeometry.Topology.Homology.SphereHurewicz
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SphereTopHomology

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology

universe u

def HasTopHomologyDegreeFunctional (M : Type u) [TopologicalSpace M] : Prop :=
  ∃ φ : IntegralHomology M 3 →ₗ[ℤ] ℤ, Function.Surjective φ

namespace HasTopHomologyDegreeFunctional

variable {M : Type u} [TopologicalSpace M]

theorem of_linearEquiv (e : IntegralHomology M 3 ≃ₗ[ℤ] ℤ) :
    HasTopHomologyDegreeFunctional M :=
  ⟨e.toLinearMap, e.surjective⟩

theorem of_apply_eq_one {φ : IntegralHomology M 3 →ₗ[ℤ] ℤ} {a : IntegralHomology M 3}
    (h : φ a = 1) : HasTopHomologyDegreeFunctional M :=
  ⟨φ, fun y => ⟨y • a, by rw [map_zsmul, h, smul_eq_mul, mul_one]⟩⟩

end HasTopHomologyDegreeFunctional

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M]

omit [IsManifold ThreeModel ∞ M] in
theorem hasTopHomologyDegreeFunctional_of_punctured_subsingleton_two (x₀ : M)
    (h₂ : Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 2)) :
    HasTopHomologyDegreeFunctional M :=
  ⟨(localIntegralHomologyEquivInt (M := M) x₀).toLinearMap.comp
      (absoluteToRelative M ({x₀}ᶜ) 3).hom,
    (localIntegralHomologyEquivInt (M := M) x₀).surjective.comp
      (absoluteToRelative_surjective_of_subsingleton_punctured x₀ h₂)⟩

omit [IsManifold ThreeModel ∞ M] in
theorem hasTopHomologyDegreeFunctional_iff_nontrivial_of_punctured_subsingleton_three
    (x₀ : M) (h₃ : Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 3)) :
    HasTopHomologyDegreeFunctional M ↔ Nontrivial (IntegralHomology M 3) := by
  have hf : Function.Injective
      ((localIntegralHomologyEquivInt (M := M) x₀).toLinearMap.comp
        (absoluteToRelative M ({x₀}ᶜ) 3).hom) :=
    (localIntegralHomologyEquivInt (M := M) x₀).injective.comp
      ((subsingleton_integralHomology_compl_singleton_three_iff_injective_absoluteToRelative
        x₀).mp h₃)
  constructor
  · rintro ⟨φ, hφ⟩
    obtain ⟨a, ha⟩ := hφ 1
    refine ⟨0, a, fun h0 => ?_⟩
    have hzero : φ a = 0 := by rw [← h0, map_zero]
    rw [hzero] at ha
    exact one_ne_zero ha.symm
  · intro h
    obtain ⟨a, b, hab⟩ := h
    obtain ⟨e⟩ :=
      DifferentialGeometry.Algebra.Module.nonempty_linearEquiv_int_of_injective_of_exists_ne_zero
        ((localIntegralHomologyEquivInt (M := M) x₀).toLinearMap.comp
          (absoluteToRelative M ({x₀}ᶜ) 3).hom) hf
        ⟨a - b, fun h0 => hab (sub_eq_zero.mp h0)⟩
    exact HasTopHomologyDegreeFunctional.of_linearEquiv e

omit [IsManifold ThreeModel ∞ M] in
theorem nonempty_linearEquiv_int_iff_hasTopHomologyDegreeFunctional
    (x₀ : M) (h₃ : Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 3)) :
    Nonempty (IntegralHomology M 3 ≃ₗ[ℤ] ℤ) ↔ HasTopHomologyDegreeFunctional M := by
  obtain ⟨f₀, hf₀⟩ : ∃ f : IntegralHomology M 3 →ₗ[ℤ] ℤ, Function.Injective f :=
    ⟨(localIntegralHomologyEquivInt (M := M) x₀).toLinearMap.comp
        (absoluteToRelative M ({x₀}ᶜ) 3).hom,
      (localIntegralHomologyEquivInt (M := M) x₀).injective.comp
        ((subsingleton_integralHomology_compl_singleton_three_iff_injective_absoluteToRelative
          x₀).mp h₃)⟩
  exact ⟨fun ⟨e⟩ => HasTopHomologyDegreeFunctional.of_linearEquiv e,
    fun h => DifferentialGeometry.Algebra.Module.nonempty_linearEquiv_int_of_injective_of_surjective
      f₀ (Classical.choose h) hf₀ (Classical.choose_spec h)⟩

omit [IsManifold ThreeModel ∞ M] in
theorem nonempty_linearEquiv_int_iff_nontrivial_of_punctured_subsingleton_three
    (x₀ : M) (h₃ : Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 3)) :
    Nonempty (IntegralHomology M 3 ≃ₗ[ℤ] ℤ) ↔ Nontrivial (IntegralHomology M 3) :=
  DifferentialGeometry.Algebra.Module.nonempty_linearEquiv_int_iff_nontrivial_of_injective
    ((localIntegralHomologyEquivInt (M := M) x₀).toLinearMap.comp
      (absoluteToRelative M ({x₀}ᶜ) 3).hom)
    ((localIntegralHomologyEquivInt (M := M) x₀).injective.comp
      ((subsingleton_integralHomology_compl_singleton_three_iff_injective_absoluteToRelative
        x₀).mp h₃))

omit [IsManifold ThreeModel ∞ M] in
theorem nonempty_linearEquiv_int_of_punctured_subsingleton (x₀ : M)
    (h₂ : Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 2))
    (h₃ : Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 3)) :
    Nonempty (IntegralHomology M 3 ≃ₗ[ℤ] ℤ) :=
  (nonempty_linearEquiv_int_iff_hasTopHomologyDegreeFunctional x₀ h₃).mpr
    (hasTopHomologyDegreeFunctional_of_punctured_subsingleton_two x₀ h₂)

omit [IsManifold ThreeModel ∞ M] in
theorem hasTopHomologyDegreeFunctional_of_noncompactPoincareDuality_of_simplyConnected
    [T2Space M] [CompactSpace M] [SimplyConnectedSpace M] (x₀ : M)
    (h : noncompactPoincareDualityTwoOne ({x₀}ᶜ : Set M)) :
    HasTopHomologyDegreeFunctional M :=
  hasTopHomologyDegreeFunctional_of_punctured_subsingleton_two x₀
    (subsingleton_integralHomology_compl_singleton_two_of_noncompactPoincareDuality_of_simplyConnected
      x₀ h)

theorem nonempty_linearEquiv_int_of_noncompactPoincareDuality_of_noncompactVanishing
    [ConnectedSpace M] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
    (x₀ : M) (h : noncompactPoincareDualityTwoOne ({x₀}ᶜ : Set M))
    (hv : noncompactThreeManifoldTopHomologyVanishing.{u}) :
    Nonempty (IntegralHomology M 3 ≃ₗ[ℤ] ℤ) :=
  nonempty_linearEquiv_int_of_punctured_subsingleton x₀
    (subsingleton_integralHomology_compl_singleton_two_of_noncompactPoincareDuality_of_simplyConnected
      x₀ h)
    (subsingleton_integralHomology_compl_singleton_of_noncompactThreeManifoldTopHomologyVanishing
      hv x₀)

omit [IsManifold ThreeModel ∞ M] in
theorem hasTopHomologyDegreeFunctional_of_surjective_absoluteToRelative
    (x₀ : M) (h₃ : Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 3))
    (hsurj : Function.Surjective (absoluteToRelative M ({x₀}ᶜ) 3)) :
    HasTopHomologyDegreeFunctional M :=
  HasTopHomologyDegreeFunctional.of_linearEquiv
    ((LinearEquiv.ofBijective ((absoluteToRelative M ({x₀}ᶜ) 3).hom)
        ⟨absoluteToRelative_compl_singleton_injective_of_subsingleton x₀ h₃, hsurj⟩).trans
      (localIntegralHomologyEquivInt (M := M) x₀))

omit [IsManifold ThreeModel ∞ M] in
theorem nonempty_linearEquiv_int_iff_exists_ne_zero_generator (x₀ : M)
    (h₃ : Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 3)) :
    Nonempty (IntegralHomology M 3 ≃ₗ[ℤ] ℤ) ↔
      ∃ z : IntegralHomology M 3, z ≠ 0 ∧ Function.Bijective (fun k : ℤ => k • z) := by
  have hf : Function.Injective
      ((localIntegralHomologyEquivInt (M := M) x₀).toLinearMap.comp
        (absoluteToRelative M ({x₀}ᶜ) 3).hom) :=
    (localIntegralHomologyEquivInt (M := M) x₀).injective.comp
      ((subsingleton_integralHomology_compl_singleton_three_iff_injective_absoluteToRelative
        x₀).mp h₃)
  constructor
  · rintro ⟨e⟩
    refine ⟨e.symm 1, fun h0 => ?_, ?_⟩
    · have hone : (1 : ℤ) = 0 := by rw [← e.apply_symm_apply 1, h0, map_zero]
      exact one_ne_zero hone
    · refine (isUnit_apply_iff_bijective_zsmul e (e.symm 1)).mp ?_
      rw [e.apply_symm_apply 1]
      exact isUnit_one
  · rintro ⟨z, hz, -⟩
    exact DifferentialGeometry.Algebra.Module.nonempty_linearEquiv_int_of_injective_of_exists_ne_zero
      ((localIntegralHomologyEquivInt (M := M) x₀).toLinearMap.comp
        (absoluteToRelative M ({x₀}ᶜ) 3).hom) hf ⟨z, hz⟩

omit [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] in
theorem exists_ne_zero_topHomologyClass_of_isSphereHurewiczIsomorphism
    (x : M) (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
    (hc : IsSphereHurewiczIsomorphism 2 M x c)
    (γ : HomotopyGroup (Fin 3) M x) (hγ : γ ≠ 1) :
    ∃ z : IntegralHomology M 3, z ≠ 0 :=
  ⟨sphereHurewicz 2 x c γ, fun h0 =>
    hγ (hc.1.injective (h0.trans (sphereHurewicz_one 2 x c).symm))⟩

omit [IsManifold ThreeModel ∞ M] in
theorem nonempty_linearEquiv_int_of_isSphereHurewiczIsomorphism (x₀ : M)
    (h₃ : Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 3))
    (x : M) (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
    (hc : IsSphereHurewiczIsomorphism 2 M x c)
    (γ : HomotopyGroup (Fin 3) M x) (hγ : γ ≠ 1) :
    Nonempty (IntegralHomology M 3 ≃ₗ[ℤ] ℤ) := by
  obtain ⟨z, hz⟩ := exists_ne_zero_topHomologyClass_of_isSphereHurewiczIsomorphism x c hc γ hγ
  exact (nonempty_linearEquiv_int_iff_nontrivial_of_punctured_subsingleton_three x₀ h₃).mpr
    ⟨0, z, fun h => hz h.symm⟩

theorem hasTopHomologyDegreeFunctional_of_surjective_sphereMap
    (M : Type) [TopologicalSpace M]
    (φ : C(M, SphereThree))
    (h : Function.Surjective (integralHomologyMap 3 φ)) :
    HasTopHomologyDegreeFunctional M := by
  let e : IntegralHomology SphereThree 3 ≃ₗ[ℤ] ℤ :=
    integralSphereTopHomologyEquiv 2 (EuclideanSpace ℝ (Fin 4)) (by simp)
  exact ⟨e.toLinearMap.comp (integralHomologyMap 3 φ).hom, e.surjective.comp h⟩

theorem hasTopHomologyDegreeFunctional_sphereThree :
    HasTopHomologyDegreeFunctional SphereThree :=
  HasTopHomologyDegreeFunctional.of_linearEquiv
    (integralSphereTopHomologyEquiv 2 (EuclideanSpace ℝ (Fin 4)) (by simp))

theorem not_hasTopHomologyDegreeFunctional_threeSpace :
    ¬ HasTopHomologyDegreeFunctional ThreeSpace := by
  rintro ⟨φ, hφ⟩
  obtain ⟨a, ha⟩ := hφ 1
  have hsub : Subsingleton (IntegralHomology ThreeSpace 3) :=
    subsingleton_integralHomology_three_threeSpace
  have hzero : φ a = 0 := by rw [hsub.allEq a 0, map_zero]
  rw [hzero] at ha
  exact one_ne_zero ha.symm

theorem not_forall_hasTopHomologyDegreeFunctional_of_subsingleton :
    ¬ (∀ (X : Type) [TopologicalSpace X],
        Subsingleton (IntegralHomology X 3) → HasTopHomologyDegreeFunctional X) :=
  fun h => not_hasTopHomologyDegreeFunctional_threeSpace
    (h ThreeSpace subsingleton_integralHomology_three_threeSpace)

def ClosedThreeManifoldTopHomologyDegreeInput : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M], HasTopHomologyDegreeFunctional M

def ClosedThreeManifoldInfiniteCyclicTopHomologyFrontier : Prop :=
  noncompactThreeManifoldTopHomologyVanishing.{u} ∧
    ClosedThreeManifoldTopHomologyDegreeInput.{u}

theorem closedThreeManifoldTopHomologyDegreeInput_of_forall_nonempty_linearEquiv_int
    (h : ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold ThreeModel ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M],
      Nonempty (IntegralHomology M 3 ≃ₗ[ℤ] ℤ)) :
    ClosedThreeManifoldTopHomologyDegreeInput.{u} :=
  fun M htop hchart hman hT2 hcomp hconn =>
    HasTopHomologyDegreeFunctional.of_linearEquiv
      (Classical.choice (@h M htop hchart hman hT2 hcomp hconn))

theorem nonempty_linearEquiv_int_of_closedThreeManifoldInfiniteCyclicTopHomologyFrontier
    (h : ClosedThreeManifoldInfiniteCyclicTopHomologyFrontier.{u})
    (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] (x₀ : M) :
    Nonempty (IntegralHomology M 3 ≃ₗ[ℤ] ℤ) :=
  (nonempty_linearEquiv_int_iff_hasTopHomologyDegreeFunctional (M := M) x₀
    (subsingleton_integralHomology_compl_singleton_of_noncompactThreeManifoldTopHomologyVanishing
      h.1 x₀)).mpr (h.2 M)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Lean in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ns : Name := `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  let decls : List String :=
    ["HasTopHomologyDegreeFunctional",
      "hasTopHomologyDegreeFunctional_of_punctured_subsingleton_two",
      "hasTopHomologyDegreeFunctional_iff_nontrivial_of_punctured_subsingleton_three",
      "nonempty_linearEquiv_int_iff_hasTopHomologyDegreeFunctional",
      "nonempty_linearEquiv_int_iff_nontrivial_of_punctured_subsingleton_three",
      "nonempty_linearEquiv_int_iff_exists_ne_zero_generator",
      "exists_ne_zero_topHomologyClass_of_isSphereHurewiczIsomorphism",
      "nonempty_linearEquiv_int_of_isSphereHurewiczIsomorphism",
      "nonempty_linearEquiv_int_of_punctured_subsingleton",
      "hasTopHomologyDegreeFunctional_of_noncompactPoincareDuality_of_simplyConnected",
      "nonempty_linearEquiv_int_of_noncompactPoincareDuality_of_noncompactVanishing",
      "hasTopHomologyDegreeFunctional_of_surjective_absoluteToRelative",
      "hasTopHomologyDegreeFunctional_of_surjective_sphereMap",
      "hasTopHomologyDegreeFunctional_sphereThree",
      "not_hasTopHomologyDegreeFunctional_threeSpace",
      "not_forall_hasTopHomologyDegreeFunctional_of_subsingleton",
      "ClosedThreeManifoldTopHomologyDegreeInput",
      "ClosedThreeManifoldInfiniteCyclicTopHomologyFrontier",
      "closedThreeManifoldTopHomologyDegreeInput_of_forall_nonempty_linearEquiv_int",
      "nonempty_linearEquiv_int_of_closedThreeManifoldInfiniteCyclicTopHomologyFrontier"]
  for d in decls do
    let n := ns.str d
    let axs ← Lean.collectAxioms n
    unless axs.all (fun a => allowed.contains a) do
      throwError "unexpected axioms for {n}: {axs}"
