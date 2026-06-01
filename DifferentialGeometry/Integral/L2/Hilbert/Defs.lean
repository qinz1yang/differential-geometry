import DifferentialGeometry.Integral.L2.SmoothSections.Defs
import DifferentialGeometry.Integral.L2.SmoothSections.PreHilbert
import DifferentialGeometry.Integral.L2.SmoothSections.Integrability
import DifferentialGeometry.Integral.L2.Pairing.Defs
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.InnerProductSpace.Completion

/-!
# The metric `L²` Hilbert space of mixed `(r, s)`-tensor fields

Let `M` be a smooth finite-dimensional manifold modelled on a real
inner-product space `E`, equipped with a smooth Riemannian metric `g`.
The space `SmoothCcTensor g r s` of compactly-supported smooth
`(r, s)`-tensor sections carries a pre-inner-product space structure
whose seminorm is the `L²` norm
`tensorL2Norm g r s = √(∫_M ⟨S, S⟩_g dμ_g)`. The seminorm fails to be a
norm on `SmoothCcTensor g r s` itself, since any section vanishing
almost everywhere with respect to the Riemannian volume measure has
seminorm zero.

The standard remedy is to pass to the Hausdorff completion of this
seminormed space: this simultaneously quotients out the kernel of the
seminorm (yielding a genuine norm) and adjoins limits of all Cauchy
sequences (yielding completeness). The result is the metric `L²`
Hilbert space of `(r, s)`-tensor fields.

## Main definitions

* `TensorL2 r s g` — the `L²` Hilbert space of mixed `(r, s)`-tensor
  fields associated with the Riemannian metric `g`, defined as the
  Hausdorff completion of `SmoothCcTensor g r s` for the seminorm
  arising from the global metric-induced `L²` inner product.

The Hilbert-space structure (norm, inner product, completeness) is
synthesised automatically by Mathlib from the corresponding instances on
the completion of a (semi-)inner-product space; see
`Inherited.lean` for the materialisation tests.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Manifold MeasureTheory Set Filter Bundle Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Integral
namespace L2

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The metric `L²` Hilbert space of mixed `(r, s)`-tensor fields on a
smooth Riemannian manifold `(M, g)`, defined as the Hausdorff completion
of the seminormed space `SmoothCcTensor g r s` of compactly-supported
smooth `(r, s)`-tensor sections.

Mathematically this is the textbook `L²` space `L²(M, T^{(r,s)} M)`
relative to the Riemannian volume measure `μ_g`. Two sections agreeing
almost everywhere are identified, and limits of Cauchy sequences in the
`L²` norm are adjoined.

This is an `abbrev` for `UniformSpace.Completion (SmoothCcTensor g r s)`
so that Mathlib's automatic instances on the completion of a normed /
inner-product space (`NormedAddCommGroup`, `NormedSpace ℝ`,
`InnerProductSpace ℝ`, `CompleteSpace`) are visible to typeclass
inference without further wrapping. -/
abbrev TensorL2
    [T2Space M] [SigmaCompactSpace M] [InnerProductSpace ℝ E]
    (r s : ℕ) (g : SmoothRiemannianMetric I M) : Type _ :=
  UniformSpace.Completion (SmoothCcTensor g r s)

section ElaborationTests

variable [T2Space M] [SigmaCompactSpace M] [InnerProductSpace ℝ E]

example (g : SmoothRiemannianMetric I M) (r s : ℕ) : Type _ := TensorL2 r s g

example (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) : TensorL2 r s g :=
  (S : UniformSpace.Completion (SmoothCcTensor g r s))

end ElaborationTests

end L2
end Integral
end DifferentialGeometry

end
