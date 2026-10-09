/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLImage
import Mathlib.LinearAlgebra.Basis.VectorSpace

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem exists_isPLHomeomorphOn_affine_of_subset_affineSubspace
    {P : Set E} (hP : IsPolyhedron P) (s : AffineSubspace ℝ E) (hs : (s : Set E).Nonempty)
    (hdim : Module.finrank ℝ s.direction = Module.finrank ℝ F) (hPs : P ⊆ s) :
    ∃ (A : E →ᵃ[ℝ] F) (B : F →ᵃ[ℝ] E),
      IsPLHomeomorphOn A P (A '' P) ∧ EqOn (B ∘ A) id P := by
  classical
  obtain ⟨p, hp⟩ := hs
  let e : s.direction ≃ₗ[ℝ] F := LinearEquiv.ofFinrankEq _ _ hdim
  obtain ⟨r, hr⟩ := s.direction.subtype.exists_leftInverse_of_injective s.direction.ker_subtype
  let A : E →ᵃ[ℝ] F := (e.toLinearMap.comp r).toAffineMap.comp
    (AffineMap.id ℝ E - AffineMap.const ℝ E p)
  let B : F →ᵃ[ℝ] E := (s.direction.subtype.comp e.symm.toLinearMap).toAffineMap + AffineMap.const ℝ
      F p
  have hBA : EqOn (B ∘ A) id P := by
    intro x hx
    change (e.symm (e (r (x - p))) : E) + p = x
    rw [e.symm_apply_apply]
    have hxp : x - p ∈ s.direction := s.vsub_mem_direction (hPs hx) hp
    have hrxp : r (x - p) = ⟨x - p, hxp⟩ := LinearMap.congr_fun hr ⟨x - p, hxp⟩
    rw [hrxp]
    exact sub_add_cancel x p
  have hinj : InjOn A P := by
    intro x hx y hy hxy
    exact (hBA hx).symm.trans ((congrArg B hxy).trans (hBA hy))
  refine ⟨A, B, ?_, hBA⟩
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hP
    ((isPiecewiseAffineOn_of_affine A isOpen_univ).mono_of_isPolyhedron hP (subset_univ _))
    ⟨fun x hx => mem_image_of_mem A hx, hinj, fun _ hx => hx⟩

end DifferentialGeometry.Topology.PiecewiseLinear
