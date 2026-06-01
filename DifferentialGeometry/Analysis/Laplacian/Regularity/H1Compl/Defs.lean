import DifferentialGeometry.Analysis.Laplacian.Regularity.SmoothScalar.PreH1
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.InnerProductSpace.Completion

/-!
# H¹ Hilbert space via Hausdorff completion

For a closed Riemannian manifold `(M, g)`, we define `H1Compl g` as the
Hausdorff completion of the seminormed inner-product space `SmoothScalar g` of
smooth real-valued functions equipped with the Riemannian H¹ inner product.
By Mathlib's automatic instances on completions of (semi-)inner-product
spaces, `H1Compl g` is a real Hilbert space.

The smooth-inclusion `smoothToH1Compl : SmoothScalar g →L[ℝ] H1Compl g` is
the canonical continuous linear embedding into the completion.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-- The H¹ Hilbert space of `(M, g)` defined as the Hausdorff completion of
the pre-Hilbert space of smooth scalars with the Riemannian H¹ inner product.

By the standard theory of completions of inner-product spaces, `H1Compl g`
inherits `NormedAddCommGroup`, `NormedSpace ℝ`, `InnerProductSpace ℝ`, and
`CompleteSpace`, making it a real Hilbert space. -/
abbrev H1Compl (g : SmoothRiemannianMetric I M) : Type _ :=
  UniformSpace.Completion (SmoothScalar g)

/-- The canonical embedding `SmoothScalar g →L[ℝ] H1Compl g` of smooth scalars
into the H¹ completion as a continuous linear map. -/
noncomputable def smoothToH1Compl (g : SmoothRiemannianMetric I M) :
    SmoothScalar g →L[ℝ] H1Compl g :=
  UniformSpace.Completion.toComplL

@[simp] lemma smoothToH1Compl_apply (g : SmoothRiemannianMetric I M)
    (f : SmoothScalar g) :
    smoothToH1Compl (I := I) (M := M) g f = (f : H1Compl g) :=
  rfl

example (g : SmoothRiemannianMetric I M) : Type _ := H1Compl g

example (g : SmoothRiemannianMetric I M) :
    NormedAddCommGroup (H1Compl g) := inferInstance

example (g : SmoothRiemannianMetric I M) :
    InnerProductSpace ℝ (H1Compl g) := inferInstance

example (g : SmoothRiemannianMetric I M) :
    CompleteSpace (H1Compl g) := inferInstance

end Laplacian
end Analysis
end DifferentialGeometry

end
