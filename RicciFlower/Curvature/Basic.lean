import RicciFlower.Metric.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Static curvature operators and coordinate traces

This file contains only static, one-manifold curvature-facing interfaces.
Parameterized metric data and flow hypotheses belong in later modules.
-/

noncomputable section

namespace RicciFlower
namespace Curvature

open Bundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A static tangent field on one manifold. -/
abbrev TangentField :=
  (x : M) -> TangentSpace I x

/-- A static covariant two-tensor field, represented by pointwise evaluation. -/
abbrev TwoTensorField :=
  (x : M) -> TangentSpace I x -> TangentSpace I x -> Real

/-- A static covariant four-tensor field, represented by pointwise evaluation. -/
abbrev FourTensorField :=
  (x : M) -> TangentSpace I x -> TangentSpace I x -> TangentSpace I x ->
    TangentSpace I x -> Real

/-- Static inverse-metric components in a chosen frame. -/
abbrev InverseMetricComponents (M : Type*) (Idx : Type*) :=
  M -> Idx -> Idx -> Real

/-- The curvature operator of a realized covariant derivative, evaluated on static
tangent fields.

This is intentionally still operator-level.  The tensor-section construction
from this operator is a separate tensoriality theorem frontier. -/
def connectionRiemannCurvatureField
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Y Z : TangentField (I := I) (M := M)) :
    TangentField (I := I) (M := M) :=
  fun x =>
    (cov (fun y => (cov Z y) (Y y)) x) (X x) -
      (cov (fun y => (cov Z y) (X y)) x) (Y x) -
        (cov Z x) (VectorField.mlieBracket I X Y x)

/-- The connection curvature operator is skew in its two direction slots. -/
theorem connectionRiemannCurvatureField_swap
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Y Z : TangentField (I := I) (M := M)) (x : M) :
    connectionRiemannCurvatureField (I := I) cov Y X Z x =
      -connectionRiemannCurvatureField (I := I) cov X Y Z x := by
  unfold connectionRiemannCurvatureField
  rw [VectorField.mlieBracket_swap_apply (I := I) (V := Y) (W := X) (x := x)]
  simp [map_neg, sub_eq_add_neg]
  abel

section MetricTrace

variable {Idx : Type*} [Fintype Idx]

/-- The supplied inverse-metric components invert the metric Gram matrix of a
static frame at every point.  This is a frame/basis hypothesis, not a theorem
that an arbitrary family of vectors is a frame. -/
def InverseMetricComponentsInFrame [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall x i j,
    (∑ k : Idx, gInv x i k * g.inner x (frame k x) (frame j x)) =
        (if i = j then 1 else 0) ∧
      (∑ k : Idx, g.inner x (frame i x) (frame k x) * gInv x k j) =
        (if i = j then 1 else 0)

/-- Ricci curvature as the metric trace of lowered Riemann curvature in a static
frame, with slot convention `Ric_ij = g^{kl} R_{k i j l}`. -/
def ricciFromRiemann04TraceInFrame
    (Riemann04 : FourTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    TwoTensorField (I := I) (M := M) :=
  fun x X Y =>
    ∑ k : Idx, ∑ l : Idx, gInv x k l * Riemann04 x (frame k x) X Y (frame l x)

@[simp]
theorem ricciFromRiemann04TraceInFrame_apply
    (Riemann04 : FourTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (x : M) (X Y : TangentSpace I x) :
    ricciFromRiemann04TraceInFrame (I := I) Riemann04 gInv frame x X Y =
      ∑ k : Idx, ∑ l : Idx,
        gInv x k l * Riemann04 x (frame k x) X Y (frame l x) :=
  rfl

/-- Scalar curvature as the metric trace of Ricci in a static frame. -/
def scalarFromRicciTraceInFrame
    (Ric : TwoTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : M -> Real :=
  fun x => ∑ i : Idx, ∑ j : Idx, gInv x i j * Ric x (frame i x) (frame j x)

@[simp]
theorem scalarFromRicciTraceInFrame_apply
    (Ric : TwoTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) (x : M) :
    scalarFromRicciTraceInFrame (I := I) Ric gInv frame x =
      ∑ i : Idx, ∑ j : Idx, gInv x i j * Ric x (frame i x) (frame j x) :=
  rfl

end MetricTrace

end Curvature
end RicciFlower
