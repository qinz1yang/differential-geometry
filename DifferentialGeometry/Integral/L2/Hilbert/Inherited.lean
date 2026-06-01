import DifferentialGeometry.Integral.L2.Hilbert.Defs
import DifferentialGeometry.Integral.L2.SmoothSections.PreHilbert
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.InnerProductSpace.Completion

/-!
# Inherited Hilbert-space instances on `TensorL2 r s g`

This file records that the four key analytic instances on the metric
`L²` Hilbert space `TensorL2 r s g` are obtained automatically by
typeclass inference from Mathlib's instances on the Hausdorff completion
of a (semi-)inner-product space:

* `NormedAddCommGroup (TensorL2 r s g)` — the textbook `L²` norm,
  obtained from `UniformSpace.Completion.instNormedAddCommGroup`. The
  completion automatically quotients out the kernel of the original
  seminorm, so the resulting structure is a genuine norm.
* `NormedSpace ℝ (TensorL2 r s g)` — real-scalar compatibility of the
  norm, from the completion's normed-space instance.
* `InnerProductSpace ℝ (TensorL2 r s g)` — the textbook `L²` inner
  product, from `UniformSpace.Completion.innerProductSpace`. Together
  with the previous two instances this means `TensorL2 r s g` is an
  inner-product space whose norm equals
  `√(⟪x, x⟫_ℝ)`.
* `CompleteSpace (TensorL2 r s g)` — completeness, from
  `UniformSpace.Completion.completeSpace`. Combined with the previous
  instances this realises the textbook fact that `TensorL2 r s g` is a
  Hilbert space.

The point of recording these as `example`s is twofold: first, to confirm
explicitly that the instance chain set up in the prior layer
(`SmoothSections.PreHilbert`) and the choice of `abbrev` for `TensorL2`
in `Defs.lean` together expose Mathlib's automatic instances without
further intervention; second, to act as a build-time test that catches
any future Mathlib refactor that would break the inference chain.

Materialisation is via `inferInstance`: each instance is a one-liner
that simply asks Lean to find it.
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

section InheritedInstances

variable [T2Space M] [SigmaCompactSpace M] [InnerProductSpace ℝ E]

/-- The textbook `L²` norm on the metric Hilbert space of mixed
`(r, s)`-tensor fields. -/
example (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    NormedAddCommGroup (TensorL2 r s g) := inferInstance

/-- Compatibility of the `L²` norm with real scalar multiplication. -/
example (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    NormedSpace ℝ (TensorL2 r s g) := inferInstance

/-- The textbook `L²` inner product on the metric Hilbert space of
mixed `(r, s)`-tensor fields. Together with the norm instance above this
makes `TensorL2 r s g` an inner-product space whose norm satisfies
`‖x‖^2 = ⟪x, x⟫_ℝ`. -/
example (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    InnerProductSpace ℝ (TensorL2 r s g) := inferInstance

/-- Completeness of the `L²` norm: every Cauchy sequence in
`TensorL2 r s g` converges. Combined with the previous three instances
this materialises the fact that `TensorL2 r s g` is a Hilbert space. -/
example (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    CompleteSpace (TensorL2 r s g) := inferInstance

end InheritedInstances

end L2
end Integral
end DifferentialGeometry

end
