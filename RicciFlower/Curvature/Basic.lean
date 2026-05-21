import RicciFlower.Metric.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Mul
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

/-- A raw static tangent field on one manifold, represented only by pointwise
evaluation.  It carries no smoothness or bundled-section data. -/
abbrev RawTangentField :=
  (x : M) -> TangentSpace I x

/-- A raw static covariant two-tensor field, represented only by pointwise
evaluation.  It carries no smoothness, tensoriality, or bundled-section data. -/
abbrev RawTwoTensorField :=
  (x : M) -> TangentSpace I x -> TangentSpace I x -> Real

/-- A raw static covariant four-tensor field, represented only by pointwise
evaluation. -/
abbrev RawFourTensorField :=
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
    (X Y Z : RawTangentField (I := I) (M := M)) :
    RawTangentField (I := I) (M := M) :=
  fun x =>
    (cov (fun y => (cov Z y) (Y y)) x) (X x) -
      (cov (fun y => (cov Z y) (X y)) x) (Y x) -
        (cov Z x) (VectorField.mlieBracket I X Y x)

/-- The connection curvature operator is skew in its two direction slots. -/
theorem connectionRiemannCurvatureField_swap
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Y Z : RawTangentField (I := I) (M := M)) (x : M) :
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

/-- A two-sided inverse of a symmetric frame Gram matrix is symmetric. -/
theorem invComp_symm [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hinv : InverseMetricComponentsInFrame (I := I) g gInv frame) :
    forall x i j, gInv x i j = gInv x j i := by
  classical
  intro x i j
  let A : Matrix Idx Idx Real := fun i j => gInv x i j
  let G : Matrix Idx Idx Real := fun i j => g.inner x (frame i x) (frame j x)
  have hAG : A * G = 1 := by
    ext a b
    simpa [A, G, Matrix.mul_apply] using (hinv x a b).1
  have hGA : G * A = 1 := by
    ext a b
    simpa [A, G, Matrix.mul_apply] using (hinv x a b).2
  have hGt : Matrix.transpose G = G := by
    ext a b
    simpa [G] using g.symm x (frame b x) (frame a x)
  have hAtG : Matrix.transpose A * G = 1 := by
    calc
      Matrix.transpose A * G = Matrix.transpose A * Matrix.transpose G := by rw [hGt]
      _ = Matrix.transpose (G * A) := by rw [Matrix.transpose_mul]
      _ = 1 := by rw [hGA]; simp
  have hAt : Matrix.transpose A = A := by
    calc
      Matrix.transpose A = Matrix.transpose A * 1 := by simp
      _ = Matrix.transpose A * (G * A) := by rw [hGA]
      _ = (Matrix.transpose A * G) * A := by rw [← Matrix.mul_assoc]
      _ = 1 * A := by rw [hAtG]
      _ = A := by simp
  have hentry := congrArg (fun B : Matrix Idx Idx Real => B j i) hAt
  simpa [A] using hentry

/-- Ricci curvature as the metric trace of lowered Riemann curvature in a static
frame, with slot convention `Ric_ij = g^{kl} R_{k i j l}`. -/
def ricciFromRiemann04TraceInFrame
    (Riemann04 : RawFourTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    RawTwoTensorField (I := I) (M := M) :=
  fun x X Y =>
    ∑ k : Idx, ∑ l : Idx, gInv x k l * Riemann04 x (frame k x) X Y (frame l x)

@[simp]
theorem ricciFromRiemann04TraceInFrame_apply
    (Riemann04 : RawFourTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (x : M) (X Y : TangentSpace I x) :
    ricciFromRiemann04TraceInFrame (I := I) Riemann04 gInv frame x X Y =
      ∑ k : Idx, ∑ l : Idx,
        gInv x k l * Riemann04 x (frame k x) X Y (frame l x) :=
  rfl

/-- Scalar curvature as the metric trace of Ricci in a static frame. -/
def scalarFromRicciTraceInFrame
    (Ric : RawTwoTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : M -> Real :=
  fun x => ∑ i : Idx, ∑ j : Idx, gInv x i j * Ric x (frame i x) (frame j x)

@[simp]
theorem scalarFromRicciTraceInFrame_apply
    (Ric : RawTwoTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) (x : M) :
    scalarFromRicciTraceInFrame (I := I) Ric gInv frame x =
      ∑ i : Idx, ∑ j : Idx, gInv x i j * Ric x (frame i x) (frame j x) :=
  rfl

end MetricTrace

end Curvature
end RicciFlower
