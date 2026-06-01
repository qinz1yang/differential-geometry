import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivative
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TrivProj.Bridge
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.Components

/-!
# Chart-component formula for the upper/lower Christoffel slot corrections

For a smooth Riemannian manifold `(M, g)` modelled on `(E, H)` with model `I`,
a chart center `α : M`, a smooth tangent vector field `B`, an `(r, s)`-tensor
section `T`, and a base point `b` in the chart `α` source, this file expresses
the `(Idx, Jdx)`-chart-frame component of

* `chartTensorRSInputSlotCorrection r s g α T B b k`
  (the `k`-th upper-slot Christoffel correction), and
* `chartTensorRSOutputSlotCorrection r s g α T B b l`
  (the `l`-th lower-slot Christoffel correction),

projected by the chart-α trivialisation, in closed form as a multilinear value
built from:

* `chartLeviCivitaParallelCLM g α b B`, the chart-`α` Levi-Civita parallel CLM,
  which itself unfolds (via `chartLeviCivitaParallelCLM_apply` and
  `christoffelCorrection_apply`) to a polynomial in chart-Christoffel data
  `chartChristoffel g α i j k` and B's chart components
  `(chartModelBasis E).repr (trivToE α b (B b))`,
* T's chart-frame action `(T b) ω' (chartJinv α b ∘ chartModelBasis ∘ Jdx)`
  applied to a `(0, r)`-CMM input `ω'` and a tuple of chart-frame vectors,
  which evaluated on the chart-frame basis yields T's chart components.

The formulae make no expansion choices: the closed-form RHS exposes the
slot-CLM `chartLeviCivitaParallelCLM g α b B` and the chart-Jacobians
`chartJ α b` / `chartJinv α b` so that any further expansion (into
Christoffel symbols, B's components, T's components) is a direct
substitution of the corresponding `_apply` lemmas of the building blocks.

## Main results

* `chartTensorRSInputSlotCorrection_chartComp_formula` — the closed-form
  chart-component formula for the upper-slot Christoffel correction.
* `chartTensorRSOutputSlotCorrection_chartComp_formula` — the closed-form
  chart-component formula for the lower-slot Christoffel correction.

The right-hand sides are polynomials in chart-Christoffel data, B's chart
components, and T's chart components in the sense described above.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Tensor.Tensor0SRiemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **Closed-form chart-frame component of the upper-slot Christoffel
correction.** For a smooth Riemannian manifold `(M, g)`, a chart center `α`,
a tangent vector field `B`, an `(r, s)`-tensor section `T`, a base point `b`
in the chart `α` source, an input-slot index `k : Fin r`, and a pair of
chart-frame multi-indices `Idx : Fin r → Fin n` and `Jdx : Fin s → Fin n`,
the `(Idx, Jdx)`-chart-frame component of the `triv-α`-projected upper-slot
Christoffel correction at `b` equals the explicit closed-form value

```
((T b)  ((dualCovariantCMM r Idx).compContinuousLinearMap
            (fun i : Fin r => (chartJ α b).comp
              (tangentSlotCLM r k (chartLeviCivitaParallelCLM g α b B) i))))
  (fun j : Fin s => chartJinv α b (chartModelBasis E (Jdx j)))
```

This is a polynomial in chart-Christoffel data, B's chart components, and
T's chart components in the sense described in the file-level docstring. -/
theorem chartTensorRSInputSlotCorrection_chartComp_formula
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (B : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) (k : Fin r)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSInputSlotCorrection (I := I) r s g α T B b k)) =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ from
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          ((dualCovariantCMM (E := E) r Idx).compContinuousLinearMap
            (fun i : Fin r =>
              (chartJ (I := I) (M := M) α b).comp
                (tangentSlotCLM (I := I) r k
                  (chartLeviCivitaParallelCLM (I := I) g α b B) i))))
        (fun j : Fin s =>
          chartJinv (I := I) (M := M) α b ((chartModelBasis E) (Jdx j))) := by
  classical
  rw [triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
    r s α hb (chartTensorRSInputSlotCorrection (I := I) r s g α T B b k)]
  rw [tensorChartComponentProjection_apply]
  rw [chartRSTwistInv_apply]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change (((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
              chartTensorRSInputSlotCorrection (I := I) r s g α T B b k)
            ((dualCovariantCMM (E := E) r Idx).compContinuousLinearMap
              (fun _ : Fin r => chartJ (I := I) (M := M) α b)))
          : ContinuousMultilinearMap ℝ
              (fun _ : Fin s => TangentSpace I b) ℝ)
        (fun j : Fin s =>
          chartJinv (I := I) (M := M) α b ((chartModelBasis E) (Jdx j))) = _
  rw [chartTensorRSInputSlotCorrection_apply (I := I) r s g α T B b k
    ((dualCovariantCMM (E := E) r Idx).compContinuousLinearMap
      (fun _ : Fin r => chartJ (I := I) (M := M) α b))
    (fun j : Fin s =>
      chartJinv (I := I) (M := M) α b ((chartModelBasis E) (Jdx j)))]
  have hsubst :
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin r => TangentSpace I b) ℝ from
        tensorSlotSubstCLM (I := I) r b
          (tangentSlotCLM (I := I) r k
            (chartLeviCivitaParallelCLM (I := I) g α b B))
          ((dualCovariantCMM (E := E) r Idx).compContinuousLinearMap
            (fun _ : Fin r => chartJ (I := I) (M := M) α b))) =
      ((dualCovariantCMM (E := E) r Idx).compContinuousLinearMap
          (fun i : Fin r => (chartJ (I := I) (M := M) α b).comp
            (tangentSlotCLM (I := I) r k
              (chartLeviCivitaParallelCLM (I := I) g α b B) i))) := by
    refine ContinuousMultilinearMap.ext ?_
    intro w
    rw [tensorSlotSubstCLM_apply (I := I) r b
      (tangentSlotCLM (I := I) r k
        (chartLeviCivitaParallelCLM (I := I) g α b B))
      ((dualCovariantCMM (E := E) r Idx).compContinuousLinearMap
        (fun _ : Fin r => chartJ (I := I) (M := M) α b)) w]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    rfl
  have hsubst_fiber :
      (tensorSlotSubstCLM (I := I) r b
          (tangentSlotCLM (I := I) r k
            (chartLeviCivitaParallelCLM (I := I) g α b B))
          ((dualCovariantCMM (E := E) r Idx).compContinuousLinearMap
            (fun _ : Fin r => chartJ (I := I) (M := M) α b))
        : Tensor0SSpace r I b) =
      ((dualCovariantCMM (E := E) r Idx).compContinuousLinearMap
          (fun i : Fin r => (chartJ (I := I) (M := M) α b).comp
            (tangentSlotCLM (I := I) r k
              (chartLeviCivitaParallelCLM (I := I) g α b B) i))) :=
    hsubst
  rw [hsubst_fiber]

/-- **Closed-form chart-frame component of the lower-slot Christoffel
correction.** For a smooth Riemannian manifold `(M, g)`, a chart center `α`,
a tangent vector field `B`, an `(r, s)`-tensor section `T`, a base point `b`
in the chart `α` source, an output-slot index `l : Fin s`, and a pair of
chart-frame multi-indices `Idx : Fin r → Fin n` and `Jdx : Fin s → Fin n`,
the `(Idx, Jdx)`-chart-frame component of the `triv-α`-projected lower-slot
Christoffel correction at `b` equals the explicit closed-form value

```
((T b)  ((dualCovariantCMM r Idx).compContinuousLinearMap
            (fun _ : Fin r => chartJ α b)))
  (fun j : Fin s =>
    tangentSlotCLM s l (chartLeviCivitaParallelCLM g α b B) j
      (chartJinv α b (chartModelBasis E (Jdx j))))
```

This is a polynomial in chart-Christoffel data, B's chart components, and
T's chart components in the sense described in the file-level docstring. -/
theorem chartTensorRSOutputSlotCorrection_chartComp_formula
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (B : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) (l : Fin s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSOutputSlotCorrection (I := I) r s g α T B b l)) =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ from
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          ((dualCovariantCMM (E := E) r Idx).compContinuousLinearMap
            (fun _ : Fin r => chartJ (I := I) (M := M) α b)))
        (fun j : Fin s =>
          tangentSlotCLM (I := I) s l
            (chartLeviCivitaParallelCLM (I := I) g α b B) j
            (chartJinv (I := I) (M := M) α b ((chartModelBasis E) (Jdx j)))) := by
  classical
  rw [triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
    r s α hb (chartTensorRSOutputSlotCorrection (I := I) r s g α T B b l)]
  rw [tensorChartComponentProjection_apply]
  rw [chartRSTwistInv_apply]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change (((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
              chartTensorRSOutputSlotCorrection (I := I) r s g α T B b l)
            ((dualCovariantCMM (E := E) r Idx).compContinuousLinearMap
              (fun _ : Fin r => chartJ (I := I) (M := M) α b)))
          : ContinuousMultilinearMap ℝ
              (fun _ : Fin s => TangentSpace I b) ℝ)
        (fun j : Fin s =>
          chartJinv (I := I) (M := M) α b ((chartModelBasis E) (Jdx j))) = _
  exact chartTensorRSOutputSlotCorrection_apply (I := I) r s g α T B b l
    ((dualCovariantCMM (E := E) r Idx).compContinuousLinearMap
      (fun _ : Fin r => chartJ (I := I) (M := M) α b))
    (fun j : Fin s =>
      chartJinv (I := I) (M := M) α b ((chartModelBasis E) (Jdx j)))

example (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, TensorRSSpace 1 2 I b')
    (B : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) (k : Fin 1)
    (Idx : Fin 1 → Fin (Module.finrank ℝ E))
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    tensorChartComponentProjection (E := E) 1 2 Idx Jdx
        ((trivializationAt (TensorRSModel 1 2 ℝ E)
            (fun y : M => TensorRSSpace 1 2 I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSInputSlotCorrection (I := I) 1 2 g α T B b k)) =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin 2 => TangentSpace I b) ℝ from
        (show Tensor0SSpace 1 I b →L[ℝ] Tensor0SSpace 2 I b from T b)
          ((dualCovariantCMM (E := E) 1 Idx).compContinuousLinearMap
            (fun i : Fin 1 =>
              (chartJ (I := I) (M := M) α b).comp
                (tangentSlotCLM (I := I) 1 k
                  (chartLeviCivitaParallelCLM (I := I) g α b B) i))))
        (fun j : Fin 2 =>
          chartJinv (I := I) (M := M) α b ((chartModelBasis E) (Jdx j))) :=
  chartTensorRSInputSlotCorrection_chartComp_formula (I := I) (M := M)
    g 1 2 α T B hb k Idx Jdx

example (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, TensorRSSpace 1 2 I b')
    (B : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) (l : Fin 2)
    (Idx : Fin 1 → Fin (Module.finrank ℝ E))
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    tensorChartComponentProjection (E := E) 1 2 Idx Jdx
        ((trivializationAt (TensorRSModel 1 2 ℝ E)
            (fun y : M => TensorRSSpace 1 2 I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSOutputSlotCorrection (I := I) 1 2 g α T B b l)) =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin 2 => TangentSpace I b) ℝ from
        (show Tensor0SSpace 1 I b →L[ℝ] Tensor0SSpace 2 I b from T b)
          ((dualCovariantCMM (E := E) 1 Idx).compContinuousLinearMap
            (fun _ : Fin 1 => chartJ (I := I) (M := M) α b)))
        (fun j : Fin 2 =>
          tangentSlotCLM (I := I) 2 l
            (chartLeviCivitaParallelCLM (I := I) g α b B) j
            (chartJinv (I := I) (M := M) α b ((chartModelBasis E) (Jdx j)))) :=
  chartTensorRSOutputSlotCorrection_chartComp_formula (I := I) (M := M)
    g 1 2 α T B hb l Idx Jdx

end Connection
end Integral
end DifferentialGeometry
