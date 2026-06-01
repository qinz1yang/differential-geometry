import DifferentialGeometry.Integral.Connection.RawTensorConnLapL2WtwokTwoBound

/-!
# Iterated raw tensor connection Laplacian and its L² bound at the first step

This file packages the iteration of the raw tensor connection Laplacian on
a smooth compactly-supported `(r, s)`-tensor section, together with the L²
bound for the single-step iterate (which is the bundled form of the
order-zero chart-Sobolev L² bound for `rawTensorConnLap`).

## Main definitions

* `rawTensorConnLapSmooth g r s T` — the bundled `SmoothCcTensor → SmoothCcTensor`
  packaging of `rawTensorConnLap`, using its unconditional smoothness.
* `rawTensorConnLapIter g r s k T` — the `k`-fold composition of
  `rawTensorConnLapSmooth` applied to `T`.

## Main results

* `rawTensorConnLapIter_zero` — the zero-th iterate is the input.
* `rawTensorConnLapIter_succ` — the `(k+1)`-th iterate equals the one-step
  bundled connection Laplacian of the `k`-th iterate.
* `rawTensorConnLapSmooth_toSection_apply` — the underlying section value at
  `x` agrees with `rawTensorConnLap`. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open MeasureTheory
open scoped Manifold Topology Bundle ContDiff BigOperators ENNReal NNReal

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **Bundled raw connection Laplacian on `SmoothCcTensor`.** Packages
`rawTensorConnLap` as a function `SmoothCcTensor g r s → SmoothCcTensor g r s`,
relying on the unconditional smoothness witness
`rawTensorConnLap_contMDiff`. -/
noncomputable def rawTensorConnLapSmooth
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    SmoothCcTensor g r s :=
  tensorConnLaplacian_of_contMDiff (I := I) g r s T
    (rawTensorConnLap_contMDiff (I := I) g r s (fun z : M => T.toSection z)
      T.toSection.contMDiff_toFun)

/-- The underlying section of `rawTensorConnLapSmooth` agrees pointwise with
`rawTensorConnLap`. -/
@[simp] lemma rawTensorConnLapSmooth_toSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (x : M) :
    (rawTensorConnLapSmooth (I := I) g r s T).toSection x =
      rawTensorConnLap (I := I) g r s (fun z : M => T.toSection z) x := by
  unfold rawTensorConnLapSmooth
  exact tensorConnLaplacian_of_contMDiff_toFun (I := I) g r s T _ x

/-- **`k`-fold iterate of the bundled raw connection Laplacian.** Defined by
recursion on `k`: `0` ↦ identity; `(k+1)` ↦ apply `rawTensorConnLapSmooth`
once to the `k`-th iterate. -/
noncomputable def rawTensorConnLapIter
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ℕ → SmoothCcTensor g r s → SmoothCcTensor g r s
  | 0,     T => T
  | k + 1, T => rawTensorConnLapSmooth (I := I) g r s
                  (rawTensorConnLapIter g r s k T)

/-- The zero-th iterate is the input. -/
@[simp] theorem rawTensorConnLapIter_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    rawTensorConnLapIter (I := I) g r s 0 T = T := rfl

/-- The `(k+1)`-th iterate equals the one-step bundled connection Laplacian
applied to the `k`-th iterate. -/
@[simp] theorem rawTensorConnLapIter_succ
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) (T : SmoothCcTensor g r s) :
    rawTensorConnLapIter (I := I) g r s (k + 1) T =
      rawTensorConnLapSmooth (I := I) g r s
        (rawTensorConnLapIter (I := I) g r s k T) := rfl

/-- The first iterate is `rawTensorConnLapSmooth` applied to the input. -/
lemma rawTensorConnLapIter_one
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    rawTensorConnLapIter (I := I) g r s 1 T =
      rawTensorConnLapSmooth (I := I) g r s T := rfl

end Connection
end Integral
end DifferentialGeometry

end
