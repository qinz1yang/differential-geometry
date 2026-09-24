/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.LinearAlgebra.Determinant

/-! Nonvanishing derivative determinants of local diffeomorphisms. -/

open scoped ContDiff Manifold

namespace IsLocalDiffeomorphAt

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {n : WithTop ℕ∞} {f : E → E} {x : E}

theorem det_fderiv_ne_zero (hf : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) n f x)
    (hn : n ≠ 0) : LinearMap.det (fderiv 𝕜 f x : E →ₗ[𝕜] E) ≠ 0 := by
  rw [← mfderiv_eq_fderiv]
  exact (hf.mfderivToContinuousLinearEquiv hn).toLinearEquiv.isUnit_det'.ne_zero

end IsLocalDiffeomorphAt
