/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.LinearAlgebra.Determinant

open scoped ContDiff Manifold

namespace IsLocalDiffeomorphAt

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {n : WithTop ℕ∞} {f : E → E} {x : E}

theorem det_fderiv_ne_zero (hf : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) n f x)
    (hn : n ≠ 0) : LinearMap.det (fderiv 𝕜 f x : E →ₗ[𝕜] E) ≠ 0 := by
  let e : E ≃L[𝕜] E :=
    (NormedSpace.fromTangentSpace (𝕜 := 𝕜) x).symm.trans
      ((hf.mfderivToContinuousLinearEquiv hn).trans
        (NormedSpace.fromTangentSpace (𝕜 := 𝕜) (f x)))
  have he : (e : E →L[𝕜] E) = fderiv 𝕜 f x := by
    change (NormedSpace.fromTangentSpace (𝕜 := 𝕜) (f x)).toContinuousLinearMap ∘L
      (hf.mfderivToContinuousLinearEquiv hn : _).toContinuousLinearMap ∘L
        (NormedSpace.fromTangentSpace (𝕜 := 𝕜) x).symm.toContinuousLinearMap = fderiv 𝕜 f x
    rw [hf.mfderivToContinuousLinearEquiv_coe hn, mfderiv_eq_fderiv]
    ext v
    simp
  rw [← he]
  exact e.toLinearEquiv.isUnit_det'.ne_zero

end IsLocalDiffeomorphAt
