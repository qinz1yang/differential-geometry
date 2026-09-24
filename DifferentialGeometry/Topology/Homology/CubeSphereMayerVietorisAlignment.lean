import DifferentialGeometry.Topology.Homology.CubeSphereDegreeUnit
import DifferentialGeometry.Topology.Homology.LiftedSphereRelativeBridge

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Metric Module
open scoped Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.Topology

universe u

theorem integralSphereTopHomologyEquiv_succ_apply {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (n : ℕ) (hd : finrank ℝ E = n + 3)
    (c : integralSingularHomology (n + 2) (sphere (0 : E) 1)) :
    integralSphereTopHomologyEquiv (n + 1) E hd c =
      integralSphereTopHomologyEquiv n
        (ℝ ∙ ((-(unitSpherePointOfFinrankPos (E := E) (by omega)) :
          sphere (0 : E) 1) : E))ᗮ
        (unitSpherePoleHyperplane_finrank (n + 2) (by omega)
          (-(unitSpherePointOfFinrankPos (E := E) (by omega))))
        (integralSphereHomologyShiftEquiv n
          (unitSpherePointOfFinrankPos (E := E) (by omega)) c) := by
  rw [integralSphereTopHomologyEquiv, Nat.recAux_succ, LinearEquiv.trans_apply]
  rfl

abbrev CubeSphereMayerVietorisSource :=
  integralSingularHomology 3 (sphere (0 : liftedSphereSpace.{u} 2) 1)

def integralSphereHomologyShiftEquiv_cubeSphereFundamentalClass
    {B : Type u} [AddCommGroup B] [Module ℤ B]
    (f : CubeSphereMayerVietorisSource.{u} ≃ₗ[ℤ] B)
    (τ : B ≃ₗ[ℤ] integralSingularHomology 2 (liftedHomotopySphere.{u} 1)) : Prop :=
  τ (f (hurewiczCubeClass cubeSphereUnliftedLoop.{u})) = squareSphereFundamentalClass.{u} ∨
    τ (f (hurewiczCubeClass cubeSphereUnliftedLoop.{u})) = -squareSphereFundamentalClass.{u}

theorem isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_isUnit_apply_trans
    {B : Type u} [AddCommGroup B] [Module ℤ B]
    (f : CubeSphereMayerVietorisSource.{u} ≃ₗ[ℤ] B) (g : B ≃ₗ[ℤ] ℤ) :
    IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass.{u} ↔
      IsUnit (g (f (hurewiczCubeClass cubeSphereUnliftedLoop.{u}))) := by
  rw [isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_unliftedCoordinate_isUnit]
  exact (isUnit_apply_iff_isUnit_apply_of_linearEquiv_trans f g
    (integralSphereTopHomologyEquiv 2 (liftedSphereSpace.{u} 2) (liftedSphereSpace_finrank 2))
    (hurewiczCubeClass cubeSphereUnliftedLoop.{u})).symm

theorem isSphereHomologyGenerator_cubeSphereFundamentalClass_of_isUnit_apply_trans
    {B : Type u} [AddCommGroup B] [Module ℤ B]
    (f : CubeSphereMayerVietorisSource.{u} ≃ₗ[ℤ] B) (g : B ≃ₗ[ℤ] ℤ)
    (h : IsUnit (g (f (hurewiczCubeClass cubeSphereUnliftedLoop.{u})))) :
    IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass.{u} :=
  (isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_isUnit_apply_trans f g).mpr h

theorem cubeSphereFundamentalClass_ne_zero_of_isUnit_apply_trans
    {B : Type u} [AddCommGroup B] [Module ℤ B]
    (f : CubeSphereMayerVietorisSource.{u} ≃ₗ[ℤ] B) (g : B ≃ₗ[ℤ] ℤ)
    (h : IsUnit (g (f (hurewiczCubeClass cubeSphereUnliftedLoop.{u})))) :
    cubeSphereFundamentalClass.{u} ≠ 0 :=
  IsSphereHomologyGenerator.ne_zero 2
    (isSphereHomologyGenerator_cubeSphereFundamentalClass_of_isUnit_apply_trans f g h)

theorem isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_squareSphereFundamentalClass
    {B : Type u} [AddCommGroup B] [Module ℤ B]
    (f : CubeSphereMayerVietorisSource.{u} ≃ₗ[ℤ] B) (g : B ≃ₗ[ℤ] ℤ)
    (τ : B ≃ₗ[ℤ] integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (halign : integralSphereHomologyShiftEquiv_cubeSphereFundamentalClass f τ) :
    IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass.{u} ↔
      IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u} := by
  rw [isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_isUnit_apply_trans f g,
    isSphereHomologyGenerator_squareSphereFundamentalClass_iff_coordinate, ← Int.isUnit_iff]
  rcases halign with h | h
  · have himg : f (hurewiczCubeClass cubeSphereUnliftedLoop.{u}) =
        τ.symm squareSphereFundamentalClass.{u} := by
      rw [← h, LinearEquiv.symm_apply_apply]
    rw [himg]
    exact isUnit_apply_iff_isUnit_apply_of_linearEquiv_trans τ.symm g
      (integralLiftedSphereTopEquiv.{u} 1) squareSphereFundamentalClass.{u}
  · have himg : f (hurewiczCubeClass cubeSphereUnliftedLoop.{u}) =
        -(τ.symm squareSphereFundamentalClass.{u}) := by
      rw [← map_neg τ.symm squareSphereFundamentalClass.{u}, ← h,
        LinearEquiv.symm_apply_apply]
    rw [himg, map_neg, IsUnit.neg_iff]
    exact isUnit_apply_iff_isUnit_apply_of_linearEquiv_trans τ.symm g
      (integralLiftedSphereTopEquiv.{u} 1) squareSphereFundamentalClass.{u}

theorem isSphereHomologyGenerator_cubeSphereFundamentalClass_of_squareSphereFundamentalClass
    {B : Type u} [AddCommGroup B] [Module ℤ B]
    (f : CubeSphereMayerVietorisSource.{u} ≃ₗ[ℤ] B) (g : B ≃ₗ[ℤ] ℤ)
    (τ : B ≃ₗ[ℤ] integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (halign : integralSphereHomologyShiftEquiv_cubeSphereFundamentalClass f τ)
    (hsq : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u}) :
    IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass.{u} :=
  (isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_squareSphereFundamentalClass
    f g τ halign).mpr hsq

theorem isSphereHomologyGenerator_cubeSphereFundamentalClass_of_squareRelativeFunctional
    {B : Type u} [AddCommGroup B] [Module ℤ B]
    (f : CubeSphereMayerVietorisSource.{u} ≃ₗ[ℤ] B) (g : B ≃ₗ[ℤ] ℤ)
    (τ : B ≃ₗ[ℤ] integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (halign : integralSphereHomologyShiftEquiv_cubeSphereFundamentalClass f τ)
    (hrel : ∃ ψ : integralRelativeHomology 2 (liftedSphereBasepoint.{u}) →ₗ[ℤ] ℤ,
      ψ (integralAbsoluteToRelative 2 (liftedSphereBasepoint.{u})
        squareSphereFundamentalClass.{u}) = 1) :
    IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass.{u} :=
  isSphereHomologyGenerator_cubeSphereFundamentalClass_of_squareSphereFundamentalClass
    f g τ halign
    (squareSphereFundamentalClass_isSphereHomologyGenerator_iff_exists_relative_functional.mpr hrel)

end DifferentialGeometry.Topology
