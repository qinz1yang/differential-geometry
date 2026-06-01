import DifferentialGeometry.Integral.Connection.Order2DefectGradientSlotLeibniz

/-!
# Metric-compatibility intertwining of the partial metric trace

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product space `E`, the
intrinsic partial metric trace `metricTrace2 g r s (tensorSecondCovDeriv g r s)` of the two leading
Hessian direction slots is, pointwise, the rough Laplacian `Δ_∇ = rawTensorConnLap g r s`
(`rawTensorConnLap_eq_metricTrace2`). This file records the metric-compatibility intertwining for
that trace: the outer covariant derivative passes through the `g_x`-orthonormal-frame diagonal trace
*without differentiating the moving frame*.

The diagonal trace `y ↦ metricTrace2 g r s (tensorSecondCovDeriv g r s) T y` reads the second
covariant derivative against the *moving* `g_y`-orthonormal frame `Cʸᵢ := smoothOrthoFrame g y i`.
The escape from differentiating that moving frame is the `x`-frozen reading: near `x`, the trace
agrees with the *fixed-frame* diagonal sum against the `x`-centred frame `Bᵢ := smoothOrthoFrame g x
i`, which is `g_y`-orthonormal at every `y` in the orthonormality neighbourhood. The outer covariant
derivative of the fixed-frame sum distributes over the finite frame sum with no frame derivative.
The moving-frame correction `∑ᵢⱼ (∇_w g(Bᵢ, Bⱼ)) • firstSlotHessMap …` — the term where the outer
derivative would hit the metric coefficient `g(Bᵢ, Bⱼ)` of the `g`-weighted reading
`metricTrace2_eq_gWeighted` — vanishes by the cometric skew core `cometric_skew_core` (the
metric-parallel property `∇g⁻¹ = 0` read on the orthonormal frame).

## What this file establishes

* `metricTrace2_covDeriv_comm` — the metric-compatibility intertwining in directional form. The
  outer covariant derivative of the partial metric trace at `x`, in a direction `w`, equals the
  fixed-frame diagonal sum of the directional covariant derivatives of the per-summand second
  covariant derivatives:
  ```
  ∇_w (metricTrace2 g r s (tensorSecondCovDeriv g r s) T) (x)
    = ∑ᵢ ∇_w (y ↦ ∇²_{Bᵢ, Bᵢ} T y) (x),    Bᵢ := smoothOrthoFrame g x i.
  ```
  The right-hand side is the `x`-frozen metric trace of the directional covariant derivatives of the
  Hessian-direction data; the moving frame is never differentiated.

* `metricTrace2_covDeriv_comm_map` — the continuous-linear-map upgrade: the directional covariant
  derivative `w ↦ ∇_w (metricTrace2 …) (x)`, read as a continuous-linear map of the direction,
  equals the fixed-frame sum of the per-summand directional maps.

## Sign / convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` for the rough Laplacian; the partial metric trace
`metricTrace2 g r s (tensorSecondCovDeriv g r s)` is this rough Laplacian read as the intrinsic
`g⁻¹`-trace of the two Hessian direction slots.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SNabla
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **The metric-compatibility intertwining of the partial metric trace (directional form).** With
`Bᵢ := smoothOrthoFrame g x i`, the outer covariant derivative of the partial metric trace of the
second-covariant-derivative Hessian family, in a direction `w`, equals the `x`-frozen frame sum of
the directional covariant derivatives of the per-summand second covariant derivatives:
```
∇_w (metricTrace2 g r s (tensorSecondCovDeriv g r s) T) (x)
  = ∑ᵢ ∇_w (y ↦ ∇²_{Bᵢ, Bᵢ} T y) (x).
```
The right-hand side is the `x`-frozen partial metric trace of the directional covariant derivatives
of the Hessian-direction data: the outer derivative passes through the intrinsic `g⁻¹`-trace, and the
moving-frame correction `∑ᵢⱼ (∇_w g(Bᵢ, Bⱼ)) • firstSlotHessMap …` of the `g`-weighted reading
vanishes by `cometric_skew_core`. The proof rewrites the metric-trace section to the rough Laplacian
section (`rawTensorConnLap_eq_metricTrace2`) and applies the gradient-slot Leibniz commutation
`covDeriv_rawConnLap_eq_frozenFrameTrace_sum`, whose frame-frozen mechanism is exactly the
moving-frame discharge. -/
theorem metricTrace2_covDeriv_comm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (x : M) (w : TangentSpace I x) :
    (tensorCov (I := I) g r s).toFun
        (fun y : M => metricTrace2 (I := I) g r s (tensorSecondCovDeriv (I := I) g r s)
          (fun z : M => T.toSection z) y) x w =
      ∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g r s).toFun
          (fun y : M => tensorSecondCovDeriv (I := I) g r s
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (fun z : M => T.toSection z) y) x w := by
  have hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T.toSection y)) :=
    T.toSection.contMDiff
  rw [show (fun y : M => metricTrace2 (I := I) g r s (tensorSecondCovDeriv (I := I) g r s)
        (fun z : M => T.toSection z) y) =
      (fun y : M => rawTensorConnLap (I := I) g r s (fun z : M => T.toSection z) y) from by
    funext y
    exact (rawTensorConnLap_eq_metricTrace2 (I := I) g r s
      (fun z : M => T.toSection z) y).symm]
  exact covDeriv_rawConnLap_eq_frozenFrameTrace_sum (I := I) g r s hT x w

/-- **The metric-compatibility intertwining of the partial metric trace (continuous-linear-map
form).** The directional covariant derivative `w ↦ ∇_w (metricTrace2 g r s (tensorSecondCovDeriv g r
s) T) (x)`, read as a continuous-linear map of the direction, equals the `x`-frozen frame sum of the
per-summand directional covariant-derivative maps:
```
∇·(metricTrace2 g r s (tensorSecondCovDeriv g r s) T) (x)
  = ∑ᵢ ∇·(y ↦ ∇²_{Bᵢ, Bᵢ} T y) (x),    Bᵢ := smoothOrthoFrame g x i.
```
This is the continuous-linear-map upgrade of `metricTrace2_covDeriv_comm` (equality of values for
each direction `w`), obtained by `ContinuousLinearMap.ext`. -/
theorem metricTrace2_covDeriv_comm_map
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (x : M) :
    (tensorCov (I := I) g r s).toFun
        (fun y : M => metricTrace2 (I := I) g r s (tensorSecondCovDeriv (I := I) g r s)
          (fun z : M => T.toSection z) y) x =
      ∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g r s).toFun
          (fun y : M => tensorSecondCovDeriv (I := I) g r s
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (fun z : M => T.toSection z) y) x := by
  refine ContinuousLinearMap.ext (fun w => ?_)
  rw [ContinuousLinearMap.sum_apply]
  exact metricTrace2_covDeriv_comm (I := I) g r s T x w

end Connection
end Integral
end DifferentialGeometry

end
