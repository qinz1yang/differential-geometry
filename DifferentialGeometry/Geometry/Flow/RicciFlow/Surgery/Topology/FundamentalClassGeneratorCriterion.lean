import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassExistenceReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassMinimalHypotheses
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedOrientedStage
import DifferentialGeometry.Topology.Manifold.SphereOrientation
import DifferentialGeometry.Topology.Homology.SphereTopHomology

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Module Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology

universe u

private theorem bijective_of_surjective_linearMap_int_of_nonempty_linearEquiv_int
    {A : Type*} [AddCommGroup A] [Module ℤ A] (h : Nonempty (A ≃ₗ[ℤ] ℤ))
    (ψ : A →ₗ[ℤ] ℤ) (hψ : Function.Surjective ψ) : Function.Bijective ψ := by
  classical
  obtain ⟨e⟩ := h
  obtain ⟨a, ha⟩ := hψ 1
  have hform : ∀ n : ℤ, ψ (e.symm n) = n * ψ (e.symm 1) := by
    intro n
    have hn : e.symm n = n • e.symm 1 := by
      rw [← map_zsmul]
      simp
    rw [hn, map_zsmul, smul_eq_mul]
  have hka : e a * ψ (e.symm 1) = 1 := by
    have ha' : a = (e a) • e.symm 1 := by
      have h := congrArg e.symm (show e a = (e a) • (1 : ℤ) from by simp)
      rw [map_zsmul, e.symm_apply_apply] at h
      exact h
    have h := congrArg ψ ha'
    rw [map_zsmul, smul_eq_mul, ha] at h
    exact h.symm
  have hunit : ψ (e.symm 1) = 1 ∨ ψ (e.symm 1) = -1 :=
    Int.eq_one_or_neg_one_of_mul_eq_one (by rw [mul_comm]; exact hka)
  have hk0 : ψ (e.symm 1) ≠ 0 := by
    rcases hunit with h | h <;> rw [h] <;> norm_num
  have hkk : ψ (e.symm 1) * ψ (e.symm 1) = 1 := by
    rcases hunit with h | h <;> rw [h] <;> norm_num
  refine ⟨fun x y hxy => ?_, fun b => ⟨b • e.symm (ψ (e.symm 1)), ?_⟩⟩
  · have h0 : ψ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hxy' : x - y = e.symm (e (x - y)) := (e.symm_apply_apply (x - y)).symm
    rw [hxy', hform] at h0
    have hz : e (x - y) = 0 := (mul_eq_zero.mp h0).resolve_right hk0
    rw [hz, map_zero] at hxy'
    exact sub_eq_zero.mp hxy'
  · rw [map_zsmul, hform, smul_eq_mul, hkk, mul_one]

theorem not_forall_bijective_zsmul_of_nonempty_linearEquiv_int :
    ¬ (∀ (A : Type) [AddCommGroup A] [Module ℤ A], Nonempty (A ≃ₗ[ℤ] ℤ) →
        ∀ a : A, Function.Bijective (fun z : ℤ => z • a)) := by
  intro h
  obtain ⟨k, hk⟩ := (h ℤ ⟨LinearEquiv.refl ℤ ℤ⟩ 2).2 1
  simp only [smul_eq_mul] at hk
  omega

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M]

def ClosedThreeManifoldTopHomologyInfiniteCyclic : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M], Nonempty (IntegralHomology M 3 ≃ₗ[ℤ] ℤ)

theorem exists_unique_fundamentalClass_of_exists_of_localOrientationClass_generator_of_nonempty_linearEquiv_int
    [T2Space M] [CompactSpace M] (o : TangentOrientationSection M) (x : M)
    (hexists : ∃ z : IntegralHomology M 3, ∀ y : M,
      absoluteToRelative M ({y}ᶜ) 3 z = localOrientationClass o y)
    (hlocal : Function.Bijective (fun k : ℤ => k • localOrientationClass o x))
    (hcyclic : Nonempty (IntegralHomology M 3 ≃ₗ[ℤ] ℤ)) :
    ∃! z : IntegralHomology M 3, ∀ y : M,
      absoluteToRelative M ({y}ᶜ) 3 z = localOrientationClass o y := by
  classical
  obtain ⟨z, hz⟩ := hexists
  let e := localIntegralHomologyEquivInt (M := M) x
  obtain ⟨u, hu⟩ := (isUnit_apply_iff_bijective_zsmul e (localOrientationClass o x)).mpr hlocal
  have he : e.toLinearMap (localOrientationClass o x) = (u : ℤ) := by
    simpa using hu.symm
  have hsurj : Function.Surjective
      (e.toLinearMap.comp (absoluteToRelative M ({x}ᶜ) 3).hom) := by
    intro n
    refine ⟨(n * ((u⁻¹ : ℤˣ) : ℤ)) • z, ?_⟩
    rw [LinearMap.comp_apply, map_zsmul, hz x, map_zsmul, he, smul_eq_mul, mul_assoc,
      Units.inv_mul, mul_one]
  have hinj : Function.Injective
      (absoluteToRelative M ({x}ᶜ) 3).hom := fun a b hab =>
    (bijective_of_surjective_linearMap_int_of_nonempty_linearEquiv_int hcyclic
      (e.toLinearMap.comp (absoluteToRelative M ({x}ᶜ) 3).hom) hsurj).1
      (by rw [LinearMap.comp_apply, LinearMap.comp_apply, hab])
  exact exists_unique_fundamentalClass_of_exists o ⟨z, hz⟩ ⟨x, hinj⟩

theorem exists_unique_fundamentalClass_of_realizationInput_of_topHomologyInfiniteCyclic
    (hgen : euclideanStandardSimplexClassGenerator.{u})
    (hE : ClosedThreeManifoldFundamentalClassRealizationInput.{u})
    (hH : ClosedThreeManifoldTopHomologyInfiniteCyclic.{u})
    (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] (o : TangentOrientationSection M) :
    ∃! z : IntegralHomology M 3, ∀ y : M,
      absoluteToRelative M ({y}ᶜ) 3 z = localOrientationClass o y :=
  exists_unique_fundamentalClass_of_exists_of_localOrientationClass_generator_of_nonempty_linearEquiv_int
    o (Classical.arbitrary M) (hE M o)
    (localOrientationClass_generator_of_euclideanStandardSimplexClassGenerator hgen o _)
    (hH M)

theorem nonempty_tangentOrientationSection_sphereThree :
    Nonempty (TangentOrientationSection SphereThree) :=
  ⟨TangentOrientationSection.ofManifoldOrientation (sphereOrientation 3 (by decide))⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
