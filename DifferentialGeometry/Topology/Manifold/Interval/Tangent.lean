import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open Set Function Manifold Bundle
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace Poincare.Manifold.Interval

variable {a b : ℝ} [Fact (a < b)]

def tangentCoordinateIcc (z : Icc a b) : TangentSpace (𝓡∂ 1) z ≃L[ℝ] ℝ := by
  let _ : FiniteDimensional ℝ (TangentSpace (𝓡∂ 1) z) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 1)))
  let _ : T2Space (TangentSpace (𝓡∂ 1) z) :=
    inferInstanceAs (T2Space (EuclideanSpace ℝ (Fin 1)))
  let L : TangentSpace (𝓡∂ 1) z →L[ℝ] ℝ :=
    (NormedSpace.fromTangentSpace (z : ℝ)).toContinuousLinearMap.comp
      (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : Icc a b → ℝ) z)
  have hs : Surjective L := by
    intro y
    refine ⟨y • (1 : TangentSpace (𝓡∂ 1) z), ?_⟩
    rw [map_smul]
    have hone : L 1 = 1 := by
      dsimp only [L, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
      rw [mfderiv_subtypeVal_Icc_one]
      rfl
    rw [hone]
    exact mul_one y
  have hd : Module.finrank ℝ (TangentSpace (𝓡∂ 1) z) = Module.finrank ℝ ℝ := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) = Module.finrank ℝ ℝ
    simp
  have hi : Injective L := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr hs
  exact (LinearEquiv.ofBijective L.toLinearMap ⟨hi, hs⟩).toContinuousLinearEquiv


theorem tangentCoordinateIcc_apply (z : Icc a b) (v : TangentSpace (𝓡∂ 1) z) :
    tangentCoordinateIcc z v = (NormedSpace.fromTangentSpace (z : ℝ))
      (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : Icc a b → ℝ) z v) := rfl


theorem tangentCoordinateIcc_one (z : Icc a b) : tangentCoordinateIcc z 1 = 1 := by
  rw [tangentCoordinateIcc_apply, mfderiv_subtypeVal_Icc_one]
  rfl

theorem tangentCoordinateIcc_symm_apply (z : Icc a b) (r : ℝ) :
    (tangentCoordinateIcc z).symm r = r • (1 : TangentSpace (𝓡∂ 1) z) := by
  apply (tangentCoordinateIcc z).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, map_smul, tangentCoordinateIcc_one]
  simp


theorem contMDiff_tangentCoordinateIcc :
    ContMDiff (𝓡∂ 1).tangent 𝓘(ℝ, ℝ) ∞
      (fun p : TangentBundle (𝓡∂ 1) (Icc a b) => tangentCoordinateIcc p.proj p.2) := by
  have hT := (contMDiff_subtypeVal_Icc (x := a) (y := b) (n := ∞)).contMDiff_tangentMap
    (m := ∞) (by simp)
  apply ((contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)).comp hT).congr
  intro p
  rfl

end Poincare.Manifold.Interval
