import DifferentialGeometry.Integral.Measure.Properties
import DifferentialGeometry.Integral.L2.Basic
import DifferentialGeometry.Integral.L2.PointwiseInner.Defs
import DifferentialGeometry.Integral.L2.PointwiseInner.DualMetric
import DifferentialGeometry.Integral.L2.PointwiseInner.Algebra
import DifferentialGeometry.Tensor.RSTensor.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Data.Real.Sqrt

/-!
# Global metric-induced `L²` pairing on tensor section fields

Let `M` be a smooth finite-dimensional manifold modelled on a real normed
space `E` equipped with a smooth Riemannian metric `g`. Each fiber of the
mixed `(r, s)`-tensor bundle is the fixed normed space
`TensorRSModel r s ℝ E`. A section is a function
`M → TensorRSModel r s ℝ E` together with appropriate regularity.

This file introduces the global metric-induced `L²` pairing on such
sections, defined as the Bochner integral of the pointwise inner product
against the canonical Riemannian volume measure, the membership predicate
selecting square-integrable sections, and the associated `L²` norm.

* `tensorL2Inner g r s S T = ∫_M ⟨S(x), T(x)⟩_{g(x)} dμ_g(x)` is the
  global `L²` pairing on sections, with the Bochner-integral convention
  (zero when the integrand is non-integrable).
* `MemL2 g r s S` is the proposition that `x ↦ ⟨S(x), S(x)⟩_{g(x)}` is
  Bochner-integrable. Equivalently, `S` has finite `L²` norm.
* `tensorL2Norm g r s S = √(tensorL2Inner g r s S S)` is the global
  `L²` norm, well-defined as a non-negative real for any section.

Algebraic properties of the pairing (additivity, scalar homogeneity,
symmetry, non-negativity), `MemL2` closure properties, and the global
Cauchy–Schwarz inequality live in companion files.
-/

noncomputable section

open Manifold MeasureTheory Set Filter Bundle Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix

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

/-- The global `L²` inner product on mixed `(r, s)`-tensor section fields,
realised as functions `M → TensorRSModel r s ℝ E`, against the canonical
Riemannian volume measure. -/
noncomputable def tensorL2Inner
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : M → TensorRSModel r s ℝ E) : ℝ :=
  ∫ x, tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x)
    ∂(riemannianVolumeMeasure (I := I) (M := M) g)

/-- `MemL2 g r s S` says that the diagonal pointwise pairing
`x ↦ ⟨S(x), S(x)⟩_{g(x)}` is Bochner-integrable against the Riemannian
volume measure. Equivalently, `S` has finite `L²` norm. -/
def MemL2
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : M → TensorRSModel r s ℝ E) : Prop :=
  MeasureTheory.Integrable
    (fun x => tensorInnerPointwise (I := I) (M := M) g r s x (S x) (S x))
    (riemannianVolumeMeasure (I := I) (M := M) g)

set_option linter.unusedSectionVars false in
/-- Direct unfolding: a member of the `L²` space has integrable diagonal
pointwise pairing. -/
lemma MemL2.integrable_inner_self
    [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {S : M → TensorRSModel r s ℝ E} (hS : MemL2 (I := I) (M := M) g r s S) :
    MeasureTheory.Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) g r s x (S x) (S x))
      (riemannianVolumeMeasure (I := I) (M := M) g) := hS

set_option linter.unusedSectionVars false in
/-- The zero section field is square-integrable: its diagonal pointwise
pairing is identically zero, which is trivially Bochner-integrable. -/
theorem MemL2.zero
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    MemL2 (I := I) (M := M) g r s (fun _ : M => (0 : TensorRSModel r s ℝ E)) := by
  unfold MemL2
  have hzero :
      (fun x : M => tensorInnerPointwise (I := I) (M := M) g r s x
          ((fun _ : M => (0 : TensorRSModel r s ℝ E)) x)
          ((fun _ : M => (0 : TensorRSModel r s ℝ E)) x))
        = (fun _ : M => (0 : ℝ)) := by
    funext x
    exact tensorInnerPointwise_zero_left (I := I) (M := M) g r s x 0
  rw [hzero]
  exact MeasureTheory.integrable_zero M ℝ
    (riemannianVolumeMeasure (I := I) (M := M) g)

/-- The global metric-induced `L²` norm on a mixed `(r, s)`-tensor section
field, defined as the square root of the diagonal `L²` inner product. -/
noncomputable def tensorL2Norm
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : M → TensorRSModel r s ℝ E) : ℝ :=
  Real.sqrt (tensorL2Inner (I := I) (M := M) g r s S S)

set_option linter.unusedSectionVars false in
/-- Unfolding lemma for the global `L²` norm. -/
lemma tensorL2Norm_def
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : M → TensorRSModel r s ℝ E) :
    tensorL2Norm (I := I) (M := M) g r s S =
      Real.sqrt (tensorL2Inner (I := I) (M := M) g r s S S) := rfl

set_option linter.unusedSectionVars false in
/-- The global `L²` norm is non-negative. -/
theorem tensorL2Norm_nonneg
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : M → TensorRSModel r s ℝ E) :
    0 ≤ tensorL2Norm (I := I) (M := M) g r s S :=
  Real.sqrt_nonneg _

end L2
end Integral
end DifferentialGeometry

end
