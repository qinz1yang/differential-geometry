import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LocalOrientationClassDegreeReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassDegreeReduction

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Module Set
open scoped Manifold ContDiff Topology

universe u

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology

section ZsmulBasisCriterion

variable {A : Type*} [AddCommGroup A] [Module ℤ A]

theorem injective_zsmul_iff_apply_ne_zero (e : A ≃ₗ[ℤ] ℤ) (c : A) :
    Function.Injective (fun z : ℤ => z • c) ↔ e c ≠ 0 := by
  constructor
  · intro h hc
    have hc0 : c = 0 := e.injective (by rw [hc, map_zero])
    have h10 : (1 : ℤ) • c = (0 : ℤ) • c := by simp [hc0]
    exact one_ne_zero (h h10)
  · intro hc a b hab
    have h := congrArg e hab
    simp only [map_zsmul, smul_eq_mul] at h
    exact mul_right_cancel₀ hc h

theorem bijective_zsmul_iff_apply_eq_one_or_eq_neg_one (e : A ≃ₗ[ℤ] ℤ) (c : A) :
    Function.Bijective (fun z : ℤ => z • c) ↔ e c = 1 ∨ e c = -1 := by
  rw [← isUnit_apply_iff_bijective_zsmul e c, Int.isUnit_iff]

theorem bijective_zsmul_iff_exists_dualBasis (c : A) :
    Function.Bijective (fun z : ℤ => z • c) ↔
      ∃ φ : A →ₗ[ℤ] ℤ, φ c = 1 ∧ ∀ a : A, a = φ a • c := by
  constructor
  · intro h
    let ψ : ℤ →+ A :=
      { toFun := fun z => z • c
        map_zero' := zero_zsmul c
        map_add' := fun a b => add_zsmul c a b }
    have hψ : Function.Bijective ψ := h
    let L : ℤ ≃ₗ[ℤ] A := (AddEquiv.ofBijective ψ hψ).toIntLinearEquiv
    let e : A ≃ₗ[ℤ] ℤ := L.symm
    have hL : L 1 = c := by
      change (AddEquiv.ofBijective ψ hψ) 1 = c
      rw [AddEquiv.ofBijective_apply]
      exact one_zsmul c
    have hec : e c = 1 := by
      change L.symm c = 1
      rw [← hL, LinearEquiv.symm_apply_apply]
    refine ⟨e.toLinearMap, hec, fun a => ?_⟩
    change a = e a • c
    have h1 : e.symm (e a) = (e a) • e.symm (1 : ℤ) := by
      have h := map_zsmul e.symm (e a) (1 : ℤ)
      simpa only [smul_eq_mul, mul_one] using h
    have h2 : e.symm (1 : ℤ) = c := by
      apply e.injective
      rw [LinearEquiv.apply_symm_apply, hec]
    rw [← h2, ← h1, LinearEquiv.symm_apply_apply]
  · rintro ⟨φ, hφc, hφa⟩
    refine ⟨fun a b hab => ?_, fun w => ⟨φ w, (hφa w).symm⟩⟩
    have h := congrArg φ hab
    simpa only [map_zsmul, smul_eq_mul, hφc, mul_one] using h

theorem exists_linearMap_apply_eq_one_iff_isUnit_apply (e : A ≃ₗ[ℤ] ℤ) (c : A) :
    (∃ φ : A →ₗ[ℤ] ℤ, φ c = 1) ↔ IsUnit (e c) := by
  constructor
  · rintro ⟨φ, hφ⟩
    have h2 : (e c) • e.symm 1 = c := by
      rw [← map_zsmul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
    have hmul : (e c) * φ (e.symm 1) = 1 := calc
      (e c) * φ (e.symm 1) = φ ((e c) • e.symm 1) := by rw [map_zsmul, smul_eq_mul]
      _ = φ c := by rw [h2]
      _ = 1 := hφ
    exact Int.isUnit_iff.mpr (Int.eq_one_or_neg_one_of_mul_eq_one hmul)
  · intro h
    rcases Int.isUnit_iff.mp h with h1 | h1
    · exact ⟨e.toLinearMap, h1⟩
    · refine ⟨-e.toLinearMap, ?_⟩
      simp only [LinearMap.neg_apply, LinearEquiv.coe_toLinearMap, h1, neg_neg]

theorem not_exists_linearMap_apply_eq_one_two_zsmul (c : A) :
    ¬ ∃ φ : A →ₗ[ℤ] ℤ, φ ((2 : ℤ) • c) = 1 := by
  rintro ⟨φ, hφ⟩
  have h2 : φ ((2 : ℤ) • c) = 2 * φ c := by rw [map_zsmul, smul_eq_mul]
  rw [h2] at hφ
  omega

end ZsmulBasisCriterion

section ZsmulZeroCountermodel

variable {A : Type*} [AddCommGroup A]

theorem not_bijective_zsmul_zero :
    ¬ Function.Bijective (fun z : ℤ => z • (0 : A)) := by
  intro h
  exact one_ne_zero (h.1 (by simp))

end ZsmulZeroCountermodel

def PuncturedBoundaryClassDetectingFunctional : Prop :=
  ∃ ψ : integralSingularHomology 2
      ({(0 : liftedSphereSpace.{u} 1)}ᶜ : Set (liftedSphereSpace.{u} 1)) →ₗ[ℤ] ℤ,
    ψ euclideanStandardSimplexBoundaryClass.{u} = 1

theorem puncturedBoundaryClassDetectingFunctional_iff_isUnit :
    PuncturedBoundaryClassDetectingFunctional.{u} ↔
      IsUnit ((integralPuncturedSpaceSphereHomologyEquiv (liftedSphereSpace.{u} 1) 2).trans
        (integralSphereTopHomologyEquiv 1 (liftedSphereSpace.{u} 1)
          (liftedSphereSpace_finrank 1)) euclideanStandardSimplexBoundaryClass.{u}) :=
  exists_linearMap_apply_eq_one_iff_isUnit_apply _ _

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M]

theorem bijective_zsmul_of_puncturedBoundaryClassDetectingFunctional_of_unique_realization
    (o : TangentOrientationSection M) (x : M) (z : IntegralHomology M 3)
    (hz : ∀ y : M, absoluteToRelative M ({y}ᶜ) 3 z = localOrientationClass o y)
    (hF : PuncturedBoundaryClassDetectingFunctional.{u})
    (hinj : Function.Injective (absoluteToRelative M ({x}ᶜ) 3)) :
    Function.Bijective (fun k : ℤ => k • z) :=
  bijective_zsmul_of_forall_absoluteToRelative_eq_and_injective o x z hz
    (localOrientationClass_generator_of_exists_functional_eq_one o x hF) hinj

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
