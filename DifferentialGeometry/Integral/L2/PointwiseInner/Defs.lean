import DifferentialGeometry.Integral.L2.PointwiseInner.DualMetric
import DifferentialGeometry.Tensor.RSTensor.Defs
import Mathlib.Data.Real.Sqrt

/-!
# Pointwise metric-induced inner product on tensor fibers

Let `M` be a smooth finite-dimensional manifold modelled on a real normed
space `E` equipped with a smooth Riemannian metric `g`. The pointwise
inner product on tensor fibers is built in two layers:

* `tensorInnerPointwise_0s` for covariant `(0, s)`-tensors, defined by
  recursion on `s` via the inverse Gram matrix of the Riemannian metric on
  the canonical model basis.
* `tensorInnerPointwise` for mixed `(r, s)`-tensors, defined by lowering
  the `r` upper slots through the metric (via `lowerAllUpperIndices`) and
  reducing to the covariant case at arity `r + s`.

The associated metric-induced pointwise norm `tensorPointwiseNorm` is the
square root of the diagonal pointwise inner product.

This file contains only the bare definitions and unfolding lemmas; the
algebraic properties (additivity, homogeneity, symmetry, non-negativity,
zero-iff) and the integrability / global `L²` machinery live in companion
files.
-/

noncomputable section

open Manifold Set Filter Bundle Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace L2

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The pointwise inner product on `(0, s)`-tensors induced by `g(x)`,
defined by recursion on `s`.

* `s = 0`: multilinear maps on the empty tuple are scalars; the inner
  product is ordinary multiplication.
* `s + 1`: `S` and `T` curry to continuous linear maps
  `E → ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ`; pair the `E`-input
  indices via the Gram-matrix inverse `(G(x))⁻¹` and pair the resulting
  `(0, s)`-tensor outputs recursively. -/
noncomputable def tensorInnerPointwise_0s :
    (s : ℕ) → SmoothRiemannianMetric I M → (x : M) →
      ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ →
      ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ → ℝ
  | 0, _g, _x, S, T =>
      S (fun i => Fin.elim0 i) * T (fun i => Fin.elim0 i)
  | s + 1, g, x, S, T =>
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
          tensorInnerPointwise_0s s g x
            (S.curryLeft ((chartModelBasis E) i))
            (T.curryLeft ((chartModelBasis E) j))

lemma tensorInnerPointwise_0s_zero_arity
    (g : SmoothRiemannianMetric I M) (x : M)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) :
    tensorInnerPointwise_0s (I := I) (M := M) 0 g x S T =
      S (fun i => Fin.elim0 i) * T (fun i => Fin.elim0 i) := rfl

lemma tensorInnerPointwise_0s_succ
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ) :
    tensorInnerPointwise_0s (I := I) (M := M) (s + 1) g x S T =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
          tensorInnerPointwise_0s (I := I) (M := M) s g x
            (S.curryLeft ((chartModelBasis E) i))
            (T.curryLeft ((chartModelBasis E) j)) := rfl

/-- The pointwise inner product on mixed `(r, s)`-tensors induced by `g(x)`:
lower both tensors to covariant `(0, r + s)`-tensors via the metric and
take the covariant pointwise inner product of the results. -/
noncomputable def tensorInnerPointwise
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (S T : TensorRSModel r s ℝ E) : ℝ :=
  tensorInnerPointwise_0s (I := I) (M := M) (r + s) g x
    (lowerAllUpperIndices (I := I) (M := M) g r s x S)
    (lowerAllUpperIndices (I := I) (M := M) g r s x T)

/-- The pointwise metric-induced norm on a mixed `(r, s)`-tensor at `x`,
defined as the square root of the diagonal pointwise inner product. -/
noncomputable def tensorPointwiseNorm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (S : TensorRSModel r s ℝ E) : ℝ :=
  Real.sqrt (tensorInnerPointwise (I := I) (M := M) g r s x S S)

end L2
end Integral
end DifferentialGeometry

end
