import DifferentialGeometry.Integral.Connection.RawTensorConnLapChartFrameTrace
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.Components

/-!
# Chart-α (Idx, Jdx)-projection of the chart-frame trace identity

For a smooth closed Riemannian manifold `(M, g)`, fixed ranks `(r, s)`, a smooth
compactly-supported `(r, s)`-tensor section `T₀ : SmoothCcTensor g r s`, a chart
base point `α : M`, and multi-indices `Idx, Jdx`, this file ships the identity
that distributes the chart-α (Idx, Jdx) scalar projection (built from the
trivialization-at-`α` and the model-fiber dual projection) through the
frame-trace expansion of the raw tensor connection Laplacian.

Concretely, applying

```
tensorChartComponentProjection r s Idx Jdx ∘
  (trivializationAt _ _ α).continuousLinearMapAt ℝ b
```

— a continuous linear functional `TensorRSSpace r s I b →L[ℝ] ℝ` — to both sides
of the chart-α frame trace identity
`rawTensorConnLap_via_chartFrameNormGlobalSmooth` yields a finite sum
representation of the chart-α (Idx, Jdx) scalar projection of the trivialized
raw tensor connection Laplacian, valid at every base point `b` in the
intersection of the chart-α partition-of-unity tsupport with the chart-α
Levi-Civita good set. No predicate on the atlas is required: the identity
relies solely on linearity of the projecting composition and on the existing
unconditional frame trace identity.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **Chart-α (Idx, Jdx)-projection of the chart-frame trace identity for
`rawTensorConnLap`.** Applying the continuous linear functional

```
tensorChartComponentProjection r s Idx Jdx ∘
  (trivializationAt _ _ α).continuousLinearMapAt ℝ b
```

to both sides of `rawTensorConnLap_via_chartFrameNormGlobalSmooth` and using
linearity (`map_sum`), the chart-α (Idx, Jdx) scalar component of the
trivialized raw tensor connection Laplacian at a base point `b` in the
chart-α partition-of-unity tsupport intersected with the chart-α Levi-Civita
good set is the finite sum over the chart-frame index `i` of the chart-α
(Idx, Jdx) scalar component of the trivialized `i`-th frame trace summand.

No predicate on the atlas is required. -/
theorem tensorChartComponentRaw_rawTensorConnLap_eq_chart_frame_trace_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M}
    (hb : b ∈ tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
      chartLeviCivitaGoodSet (I := I) α) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (rawTensorConnLap (I := I) g r s
            (fun z : M => T₀.toSection z) b)) =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorChartComponentProjection (E := E) r s Idx Jdx
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g)).toFun
                (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g))
                  (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                  (fun z : M => T₀.toSection z)) b
                ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b) -
              (TensorRSNabla.tensorRSCovariantDerivative I M r s
                  (LeviCivita (I := I) g)).toFun
                (fun z : M => T₀.toSection z) b
                ((LeviCivita (I := I) g).toFun
                  (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
                  ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)))) := by
  classical
  have hExp :
      rawTensorConnLap (I := I) g r s
          (fun z : M => T₀.toSection z) b =
        rawTensorConnLap_fixedFrame (I := I) g r s
          (fun i : Fin (Module.finrank ℝ E) =>
            (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun)
          (fun z : M => T₀.toSection z) b :=
    rawTensorConnLap_via_chartFrameNormGlobalSmooth
      (I := I) (M := M) g r s T₀ α hb
  have hSum :
      rawTensorConnLap_fixedFrame (I := I) g r s
          (fun i : Fin (Module.finrank ℝ E) =>
            (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun)
          (fun z : M => T₀.toSection z) b =
        ∑ i : Fin (Module.finrank ℝ E),
          ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
              (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g))
                (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                (fun z : M => T₀.toSection z)) b
              ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b) -
            (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
              (fun z : M => T₀.toSection z) b
              ((LeviCivita (I := I) g).toFun
                (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
                ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))) :=
    rawTensorConnLap_fixedFrame_def (I := I) g r s
      (fun i : Fin (Module.finrank ℝ E) =>
        (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun)
      (fun z : M => T₀.toSection z) b
  have hRaw_sum :
      rawTensorConnLap (I := I) g r s
          (fun z : M => T₀.toSection z) b =
        ∑ i : Fin (Module.finrank ℝ E),
          ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
              (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g))
                (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                (fun z : M => T₀.toSection z)) b
              ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b) -
            (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
              (fun z : M => T₀.toSection z) b
              ((LeviCivita (I := I) g).toFun
                (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
                ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b))) :=
    hExp.trans hSum
  set L : TensorRSSpace r s I b →L[ℝ] ℝ :=
    (tensorChartComponentProjection (E := E) r s Idx Jdx).comp
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b) with hL
  have hApply : L (rawTensorConnLap (I := I) g r s
        (fun z : M => T₀.toSection z) b) =
      L (∑ i : Fin (Module.finrank ℝ E),
          ((TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
              (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g))
                (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun
                (fun z : M => T₀.toSection z)) b
              ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b) -
            (TensorRSNabla.tensorRSCovariantDerivative I M r s
                (LeviCivita (I := I) g)).toFun
              (fun z : M => T₀.toSection z) b
              ((LeviCivita (I := I) g).toFun
                (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b
                ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)))) :=
    congrArg L hRaw_sum
  rw [map_sum] at hApply
  simpa [hL, ContinuousLinearMap.comp_apply] using hApply

end Connection
end Integral
end DifferentialGeometry
