import DifferentialGeometry.Integral.Connection.RawTensorConnLapIntrinsicL2LePouSobolevNorm
import DifferentialGeometry.Integral.Connection.RawTensorConnLapIterL2WtwokTwoBound

/-!
# Intrinsic L² bound on the first iterate of the raw tensor connection Laplacian
by the squared partition-of-unity-weighted chart-Sobolev norm

For a smooth closed Riemannian manifold `(M, g)` and fixed ranks `(r, s)`, this
file ships the intrinsic L² control of the first iterate
`rawTensorConnLapIter g r s 1 T`: there exists a single constant
`C : ℝ≥0∞ \ {⊤}`, uniform in the smooth compactly-supported tensor section `T`,
such that

```
∫⁻ b, ENNReal.ofReal
        (riemannianFiberNormSq g r s b
          ((rawTensorConnLapIter g r s 1 T).toSection b))
    ∂(riemannianVolumeMeasure g)
  ≤ C * (tensorPouSobolevNorm g 1 T) ^ 2.
```

This is the bundled-iterate counterpart of the headline
`rawTensorConnLap_intrinsicL2_le_tensorPouSobolevNorm_sq`. At `k = 1` the
iterate's underlying section value equals `rawTensorConnLap g r s T` pointwise,
so the inequality follows by `lintegral_congr` and the base headline.
-/

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
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **Intrinsic L² bound on the first iterate of the raw tensor connection
Laplacian by the squared partition-of-unity-weighted chart-Sobolev norm.**

For a smooth closed Riemannian manifold `(M, g)` and fixed ranks `(r, s)`,
there exists a finite constant `C : ℝ≥0∞ \ {⊤}` such that for every smooth
compactly-supported `(r, s)`-tensor section `T`,

```
∫⁻ b, ENNReal.ofReal
        (riemannianFiberNormSq g r s b
          ((rawTensorConnLapIter g r s 1 T).toSection b))
    ∂(riemannianVolumeMeasure g)
  ≤ C * (tensorPouSobolevNorm g 1 T) ^ 2.
```

The constant depends only on `g`, `r`, `s`, and the chart-atlas partition of
unity; it is uniform in the input section `T`. -/
theorem rawTensorConnLapIter_intrinsicL2_le_tensorPouSobolevNorm_sq_one
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ (T : SmoothCcTensor g r s),
        ∫⁻ b, ENNReal.ofReal
            (riemannianFiberNormSq (I := I) (M := M) g r s b
              ((rawTensorConnLapIter (I := I) g r s 1 T).toSection b))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
        C * (tensorPouSobolevNorm (I := I) (M := M) g 1 T) ^ 2 := by
  classical
  obtain ⟨C, hC_ne_top, hbound⟩ :=
    rawTensorConnLap_intrinsicL2_le_tensorPouSobolevNorm_sq (I := I) (M := M) g r s
  refine ⟨C, hC_ne_top, ?_⟩
  intro T
  have h_iter_section : ∀ x : M,
      (rawTensorConnLapIter (I := I) g r s 1 T).toSection x =
        rawTensorConnLap (I := I) g r s (fun z : M => T.toSection z) x := by
    intro x
    rw [rawTensorConnLapIter_one]
    exact rawTensorConnLapSmooth_toSection_apply (I := I) g r s T x
  have h_integral_eq :
      ∫⁻ b, ENNReal.ofReal
          (riemannianFiberNormSq (I := I) (M := M) g r s b
            ((rawTensorConnLapIter (I := I) g r s 1 T).toSection b))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫⁻ b, ENNReal.ofReal
          (riemannianFiberNormSq (I := I) (M := M) g r s b
            (rawTensorConnLap (I := I) g r s
              (fun z : M => T.toSection z) b))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine lintegral_congr ?_
    intro b
    rw [h_iter_section b]
  rw [h_integral_eq]
  exact hbound T

end Connection
end Integral
end DifferentialGeometry

end
