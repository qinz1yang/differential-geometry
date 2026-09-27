import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Homology

noncomputable section

open ContinuousMap

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open DifferentialGeometry.Topology

theorem euclideanStandardSimplexClass_generator_iff_isUnit_of_linearEquiv
    (e : integralLocalHomology 3 (0 : liftedSphereSpace.{u} 1) ≃ₗ[ℤ] ℤ) :
    Function.Bijective (fun z : ℤ => z • euclideanStandardSimplexClass.{u}) ↔
      IsUnit (e euclideanStandardSimplexClass.{u}) := by
  rw [isUnit_apply_iff_isUnit_apply_of_linearEquiv e
    (integralEuclideanLocalTopZeroEquiv (liftedSphereSpace.{u} 1) 1
      (liftedSphereSpace_finrank 1)) euclideanStandardSimplexClass.{u}]
  exact (isUnit_apply_iff_bijective_zsmul _ _).symm

theorem euclideanStandardSimplexClass_generator_of_functional_eq_one
    (ψ : integralLocalHomology 3 (0 : liftedSphereSpace.{u} 1) →ₗ[ℤ] ℤ)
    (h : ψ euclideanStandardSimplexClass.{u} = 1) :
    Function.Bijective (fun z : ℤ => z • euclideanStandardSimplexClass.{u}) := by
  let e := integralEuclideanLocalTopZeroEquiv (liftedSphereSpace.{u} 1) 1
    (liftedSphereSpace_finrank 1)
  have hgen : (e euclideanStandardSimplexClass.{u}) • e.symm 1 =
      euclideanStandardSimplexClass.{u} := by
    apply e.injective
    rw [map_zsmul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  have hmul : (e euclideanStandardSimplexClass.{u}) * ψ (e.symm 1) = 1 :=
    calc (e euclideanStandardSimplexClass.{u}) * ψ (e.symm 1)
        = ψ ((e euclideanStandardSimplexClass.{u}) • e.symm 1) := by
          rw [map_zsmul, smul_eq_mul]
      _ = ψ euclideanStandardSimplexClass.{u} := by rw [hgen]
      _ = 1 := h
  exact (isUnit_apply_iff_bijective_zsmul e euclideanStandardSimplexClass.{u}).mp
    (Int.isUnit_iff.mpr (Int.eq_one_or_neg_one_of_mul_eq_one hmul))

theorem euclideanStandardSimplexBoundaryClass_isUnit_iff
    (f : integralSingularHomology 2
      ({(0 : liftedSphereSpace.{u} 1)}ᶜ : Set (liftedSphereSpace.{u} 1)) ≃ₗ[ℤ] ℤ) :
    IsUnit (f euclideanStandardSimplexBoundaryClass.{u}) ↔
      IsUnit (integralSphereTopHomologyEquiv 1 (liftedSphereSpace.{u} 1)
        (liftedSphereSpace_finrank 1)
        (integralPuncturedSpaceSphereHomologyEquiv (liftedSphereSpace.{u} 1) 2
          euclideanStandardSimplexBoundaryClass.{u})) :=
  isUnit_apply_iff_isUnit_apply_of_linearEquiv f
    ((integralPuncturedSpaceSphereHomologyEquiv (liftedSphereSpace.{u} 1) 2).trans
      (integralSphereTopHomologyEquiv 1 (liftedSphereSpace.{u} 1)
        (liftedSphereSpace_finrank 1)))
    euclideanStandardSimplexBoundaryClass.{u}

theorem euclideanStandardSimplexBoundaryClass_isUnit_of_functional_eq_one
    (ψ : integralSingularHomology 2
      ({(0 : liftedSphereSpace.{u} 1)}ᶜ : Set (liftedSphereSpace.{u} 1)) →ₗ[ℤ] ℤ)
    (h : ψ euclideanStandardSimplexBoundaryClass.{u} = 1) :
    IsUnit (integralSphereTopHomologyEquiv 1 (liftedSphereSpace.{u} 1)
      (liftedSphereSpace_finrank 1)
      (integralPuncturedSpaceSphereHomologyEquiv (liftedSphereSpace.{u} 1) 2
        euclideanStandardSimplexBoundaryClass.{u})) := by
  let e := (integralPuncturedSpaceSphereHomologyEquiv (liftedSphereSpace.{u} 1) 2).trans
    (integralSphereTopHomologyEquiv 1 (liftedSphereSpace.{u} 1)
      (liftedSphereSpace_finrank 1))
  have hgen : (e euclideanStandardSimplexBoundaryClass.{u}) • e.symm 1 =
      euclideanStandardSimplexBoundaryClass.{u} := by
    apply e.injective
    rw [map_zsmul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  have hmul : (e euclideanStandardSimplexBoundaryClass.{u}) *
      ψ (e.symm 1) = 1 :=
    calc (e euclideanStandardSimplexBoundaryClass.{u}) * ψ (e.symm 1)
        = ψ ((e euclideanStandardSimplexBoundaryClass.{u}) • e.symm 1) := by
          rw [map_zsmul, smul_eq_mul]
      _ = ψ euclideanStandardSimplexBoundaryClass.{u} := by rw [hgen]
      _ = 1 := h
  exact Int.isUnit_iff.mpr (Int.eq_one_or_neg_one_of_mul_eq_one hmul)

theorem euclideanStandardSimplexClass_generator_of_boundaryClass_functional_eq_one
    (ψ : integralSingularHomology 2
      ({(0 : liftedSphereSpace.{u} 1)}ᶜ : Set (liftedSphereSpace.{u} 1)) →ₗ[ℤ] ℤ)
    (h : ψ euclideanStandardSimplexBoundaryClass.{u} = 1) :
    Function.Bijective (fun z : ℤ => z • euclideanStandardSimplexClass.{u}) :=
  (euclideanStandardSimplexClass_generator_iff_isUnit_boundaryClass).mpr
    (euclideanStandardSimplexBoundaryClass_isUnit_of_functional_eq_one ψ h)

theorem isUnit_integralSingularHomologyMap_iff_of_homotopyEquiv
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (e : X ≃ₕ Y) (c : integralSingularHomology (n + 1) X)
    (f : integralSingularHomology (n + 1) X ≃ₗ[ℤ] ℤ)
    (g : integralSingularHomology (n + 1) Y ≃ₗ[ℤ] ℤ) :
    IsUnit (g (integralSingularHomologyMap (n + 1) e.toFun c)) ↔ IsUnit (f c) :=
  isUnit_apply_iff_isUnit_apply_of_linearEquiv_trans
    (integralSingularHomologyHomotopyEquiv (n + 1) e) g f c

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
