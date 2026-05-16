import RicciFlower.Curvature.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Realized curvature wrappers

This file keeps only realization-facing wrappers and predicates.  The intrinsic
curvature operator and trace formulas live in `RicciFlower.Curvature.Basic`.
-/

noncomputable section

namespace RicciFlower
namespace Realized

open Bundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Wrapper for the non-realized tangent-field alias. -/
abbrev TangentField := RicciFlower.Curvature.TangentField (I := I) (M := M)

/-- Wrapper for the non-realized two-tensor field alias. -/
abbrev TwoTensorField := RicciFlower.Curvature.TwoTensorField (I := I) (M := M)

/-- Wrapper for the non-realized four-tensor field alias. -/
abbrev FourTensorField := RicciFlower.Curvature.FourTensorField (I := I) (M := M)

/-- Wrapper for static inverse metric components. -/
abbrev InverseMetricComponents := RicciFlower.Curvature.InverseMetricComponents

/-- Wrapper for the non-realized curvature operator. -/
abbrev connectionRiemannCurvatureField
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Y Z : TangentField (I := I) (M := M)) :
    TangentField (I := I) (M := M) :=
  RicciFlower.Curvature.connectionRiemannCurvatureField (I := I) cov X Y Z

/-- Wrapper for inverse-metric component compatibility in a frame. -/
abbrev InverseMetricComponentsInFrame {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  RicciFlower.Curvature.InverseMetricComponentsInFrame (I := I) g gInv frame

section MetricTrace

variable {Idx : Type*} [Fintype Idx]

/-- Wrapper for the non-realized lowered-Riemann trace. -/
abbrev ricciFromRiemann04TraceInFrame
    (Riemann04 : FourTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    TwoTensorField (I := I) (M := M) :=
  RicciFlower.Curvature.ricciFromRiemann04TraceInFrame (I := I) Riemann04 gInv frame

@[simp]
theorem ricciFromRiemann04TraceInFrame_apply
    (Riemann04 : FourTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (x : M) (X Y : TangentSpace I x) :
    ricciFromRiemann04TraceInFrame (I := I) Riemann04 gInv frame x X Y =
      ∑ k : Idx, ∑ l : Idx,
        gInv x k l * Riemann04 x (frame k x) X Y (frame l x) :=
  RicciFlower.Curvature.ricciFromRiemann04TraceInFrame_apply (I := I)
    Riemann04 gInv frame x X Y

/-- A pointwise Ricci field realizes the frame trace of a lowered Riemann field. -/
def RicciRealizesRm04TraceInFrame
    (Ric : TwoTensorField (I := I) (M := M))
    (Riemann04 : FourTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall x X Y, Ric x X Y =
    ricciFromRiemann04TraceInFrame (I := I) Riemann04 gInv frame x X Y

theorem ricci_comp_eq_trace
    (Ric : TwoTensorField (I := I) (M := M))
    (Riemann04 : FourTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRic : RicciRealizesRm04TraceInFrame (I := I) Ric Riemann04 gInv frame)
    (x : M) (i j : Idx) :
    Ric x (frame i x) (frame j x) =
      ∑ k : Idx, ∑ l : Idx,
        gInv x k l * Riemann04 x (frame k x) (frame i x) (frame j x)
          (frame l x) := by
  simpa [ricciFromRiemann04TraceInFrame] using hRic x (frame i x) (frame j x)


/-- Wrapper for the non-realized Ricci trace. -/
abbrev scalarFromRicciTraceInFrame
    (Ric : TwoTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : M -> Real :=
  RicciFlower.Curvature.scalarFromRicciTraceInFrame (I := I) Ric gInv frame

@[simp]
theorem scalarFromRicciTraceInFrame_apply
    (Ric : TwoTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) (x : M) :
    scalarFromRicciTraceInFrame (I := I) Ric gInv frame x =
      ∑ i : Idx, ∑ j : Idx, gInv x i j * Ric x (frame i x) (frame j x) :=
  RicciFlower.Curvature.scalarFromRicciTraceInFrame_apply (I := I) Ric gInv frame x

/-- Canonical scalar curvature obtained by tracing Ricci in a supplied frame. -/
abbrev scalarCurvatureFromRicciTraceInFrame
    (Ric : TwoTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : M -> Real :=
  scalarFromRicciTraceInFrame (I := I) Ric gInv frame

@[simp]
theorem scalarCurvatureFromRicciTraceInFrame_apply
    (Ric : TwoTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) (x : M) :
    scalarCurvatureFromRicciTraceInFrame (I := I) Ric gInv frame x =
      ∑ i : Idx, ∑ j : Idx, gInv x i j * Ric x (frame i x) (frame j x) := by
  exact scalarFromRicciTraceInFrame_apply (I := I) Ric gInv frame x

/-- A scalar curvature function realizes the frame trace of Ricci. -/
def ScalarRealizesRicciTraceInFrame
    (scalar : M -> Real)
    (Ric : TwoTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall x, scalar x = scalarFromRicciTraceInFrame (I := I) Ric gInv frame x

theorem scalar_eq_trace
    (scalar : M -> Real)
    (Ric : TwoTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hScalar : ScalarRealizesRicciTraceInFrame (I := I) scalar Ric gInv frame)
    (x : M) :
    scalar x =
      ∑ i : Idx, ∑ j : Idx, gInv x i j * Ric x (frame i x) (frame j x) := by
  simpa [scalarFromRicciTraceInFrame] using hScalar x

/-- The canonical scalar curvature trace realizes the scalar trace predicate. -/
theorem scalarCurvatureFromRicciTraceInFrame_realizes
    (Ric : TwoTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    ScalarRealizesRicciTraceInFrame (I := I)
      (scalarCurvatureFromRicciTraceInFrame (I := I) Ric gInv frame)
      Ric gInv frame := by
  intro x
  rfl

end MetricTrace

end Realized
end RicciFlower
