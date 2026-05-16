import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

set_option autoImplicit false

/-!
# RicciFlower metrics

This file contains the RicciFlower-facing alias for smooth Riemannian metrics.
It is not a realized object; realized metric families import this definition.
-/

namespace RicciFlower

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]

/-- RicciFlower-facing alias for a smooth Riemannian metric on `TM`. -/
abbrev SmoothRiemannianMetric
    (I : ModelWithCorners Real E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] : Type _ :=
  Bundle.ContMDiffRiemannianMetric I ⊤ E (TangentSpace I : M -> Type _)

end RicciFlower
