/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.LocalDegree.SphereSuspension.RadialExtension

/-! Radial extensions of sphere homeomorphisms to normed spaces and closed balls. -/

open Metric Set

namespace DifferentialGeometry.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem sphereRadialExtension_inverse
    (f : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1) (x : E) :
    LocalDegree.sphereRadialExtension (toContinuousMap f.symm)
      (LocalDegree.sphereRadialExtension (toContinuousMap f) x) = x := by
  by_cases hx : x = 0
  · simp [hx]
  have hy : LocalDegree.sphereRadialExtension (toContinuousMap f) x ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [LocalDegree.sphereRadialExtension_norm]
    exact norm_ne_zero_iff.mpr hx
  have hdir : ((homeomorphUnitSphereProd F)
      ⟨LocalDegree.sphereRadialExtension (toContinuousMap f) x, hy⟩).1 =
      f ((homeomorphUnitSphereProd E) ⟨x, hx⟩).1 := by
    apply Subtype.ext
    rw [homeomorphUnitSphereProd_apply_fst_coe]
    change ‖LocalDegree.sphereRadialExtension (toContinuousMap f) x‖⁻¹ •
      LocalDegree.sphereRadialExtension (toContinuousMap f) x = _
    rw [LocalDegree.sphereRadialExtension_norm,
      LocalDegree.sphereRadialExtension_apply_of_ne_zero _ hx]
    simp only [smul_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]
    rfl
  rw [LocalDegree.sphereRadialExtension_apply_of_ne_zero _ hy, hdir]
  change ‖LocalDegree.sphereRadialExtension (toContinuousMap f) x‖ •
    (f.symm (f ((homeomorphUnitSphereProd E) ⟨x, hx⟩).1) : E) = x
  rw [f.symm_apply_apply, LocalDegree.sphereRadialExtension_norm,
    homeomorphUnitSphereProd_apply_fst_coe]
  simp only [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

noncomputable def sphereRadialHomeomorph
    (f : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1) : E ≃ₜ F where
  toFun := LocalDegree.sphereRadialExtension (toContinuousMap f)
  invFun := LocalDegree.sphereRadialExtension (toContinuousMap f.symm)
  left_inv := sphereRadialExtension_inverse f
  right_inv := sphereRadialExtension_inverse f.symm
  continuous_toFun := (LocalDegree.sphereRadialExtension (toContinuousMap f)).continuous
  continuous_invFun := (LocalDegree.sphereRadialExtension (toContinuousMap f.symm)).continuous

@[simp]
theorem sphereRadialHomeomorph_symm (f : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1) :
    (sphereRadialHomeomorph f).symm = sphereRadialHomeomorph f.symm := rfl

@[simp]
theorem sphereRadialHomeomorph_zero (f : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1) :
    sphereRadialHomeomorph f 0 = 0 := LocalDegree.sphereRadialExtension_zero _

@[simp]
theorem norm_sphereRadialHomeomorph (f : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1) (x : E) :
    ‖sphereRadialHomeomorph f x‖ = ‖x‖ := LocalDegree.sphereRadialExtension_norm _ _

@[simp]
theorem sphereRadialHomeomorph_apply_sphere
    (f : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1) (x : sphere (0 : E) 1) :
    sphereRadialHomeomorph f x = f x := LocalDegree.sphereRadialExtension_sphere _ _

noncomputable def closedBallHomeomorphExtension
    (f : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1) :
    closedBall (0 : E) 1 ≃ₜ closedBall (0 : F) 1 :=
  (sphereRadialHomeomorph f).subtype fun x => by
    simp only [mem_closedBall, dist_zero_right, norm_sphereRadialHomeomorph]

@[simp]
theorem closedBallHomeomorphExtension_apply_sphere
    (f : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1) (x : sphere (0 : E) 1) :
    closedBallHomeomorphExtension f ⟨x, sphere_subset_closedBall x.property⟩ =
      ⟨f x, sphere_subset_closedBall (f x).property⟩ := by
  apply Subtype.ext
  exact sphereRadialHomeomorph_apply_sphere f x

end DifferentialGeometry.Topology
