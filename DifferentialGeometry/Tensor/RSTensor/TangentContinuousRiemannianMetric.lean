import DifferentialGeometry.Integral.Measure.ChartDensity
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Riemannian

/-!
# `ContinuousRiemannianMetric` from `SmoothRiemannianMetric`

Given a smooth Riemannian metric `g` on a manifold `M` (encoded as a
`SmoothRiemannianMetric I M`, i.e., a
`Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I)`), this file produces
the corresponding `Bundle.ContinuousRiemannianMetric E (TangentSpace I)` by
forgetting smoothness down to continuity.

The construction is essentially Mathlib's
`ContMDiffRiemannianMetric.toContinuousRiemannianMetric`. It is wrapped here
under a project-local name so that downstream code that consumes the
continuous-bundle layer can refer to it without having to unfold the
`SmoothRiemannianMetric` abbreviation.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace Tensor
namespace RSTensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The continuous Riemannian metric on the tangent bundle associated to a
smooth Riemannian metric.

This is `Bundle.ContMDiffRiemannianMetric.toContinuousRiemannianMetric`
applied to `g`, repackaged under a project-local name. All five fields
(`inner`, `symm`, `pos`, `isVonNBounded`, `continuous`) come from `g`
without modification: the first four are shared between
`ContMDiffRiemannianMetric` and `ContinuousRiemannianMetric`, while the
`continuous` field is obtained from `g.contMDiff.continuous`. -/
noncomputable def tangentContinuousRiemannianMetric
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M) :
    Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
  g.toContinuousRiemannianMetric

@[simp] theorem tangentContinuousRiemannianMetric_inner
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (b : M) :
    (tangentContinuousRiemannianMetric (I := I) (M := M) g).inner b = g.inner b :=
  rfl

end RSTensor
end Tensor
end DifferentialGeometry

end
