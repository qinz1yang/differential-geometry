import DifferentialGeometry.Geometry.Curvature.Metric
import DifferentialGeometry.Geometry.Curvature.AlgebraicCurvatureOperatorConeMetric
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Geometry.Connection.LeviCivita.Scaling
import DifferentialGeometry.Geometry.Operator.Scaling
open DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [SigmaCompactSpace M] [T2Space M]

omit [SigmaCompactSpace M] in
theorem metricRm_scale
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M) :
    metricRm04 (I := I) (M := M) (scaleMetric (I := I) c hc g) x =
      c • metricRm04 (I := I) (M := M) g x := by
  ext v
  have hv :
      v = vec4 (I := I) (v 0) (v 1) (v 2) (v 3) := by
    funext i
    fin_cases i <;> simp [vec4]
  rw [hv]
  simp [metricRm04, metricCov, scaleMetric_inner, lcConn_scaleMetric,
    smul_eq_mul]

omit [SigmaCompactSpace M] in
theorem metricRmStd_scale
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M)
    (X Y Z W : TangentSpace I x) :
    metricRm04StdAt (I := I) (M := M) (scaleMetric (I := I) c hc g)
        x X Y Z W =
      c * metricRm04StdAt (I := I) (M := M) g x X Y Z W := by
  have h := congrArg
    (fun Rm : Tensor04At (I := I) (M := M) x =>
      Rm (vec4 (I := I) X Y Z W))
    (metricRm_scale (I := I) c hc g x)
  simpa [metricRm04_apply, metricRm04StdAt_apply, smul_eq_mul] using h

omit [SigmaCompactSpace M] in
theorem metricAlgebraicCurvatureTensorAt_scaleMetric
    [IsManifold I 2 M] [IsManifold I 3 M]
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M) :
    metricAlgebraicCurvatureTensorAt (I := I) (M := M)
        (scaleMetric (I := I) c hc g) x =
      c • metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x := by
  apply Subtype.ext
  change metricRm04At (I := I) (M := M) (scaleMetric (I := I) c hc g) x =
    ((c • metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x :
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
        Tensor04At (I := I) (M := M) x)
  rw [Submodule.coe_smul_of_tower, metricAlgebraicCurvatureTensorAt_coe]
  simpa only [metricRm04_apply] using metricRm_scale (I := I) c hc g x

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M]
    [SigmaCompactSpace M] [T2Space M] in
theorem algebraicCurvatureIdentityQuadraticEval_scaleMetric
    (a : Real) (ha : 0 < a) (g : SmoothRiemannianMetric I M)
    {x : M} {n : Nat} (c : Fin n → Real)
    (v w : Fin n → TangentSpace I x) :
    algebraicCurvatureIdentityQuadraticEval (I := I)
        (scaleMetric (I := I) a ha g) c v w =
      a ^ 2 * algebraicCurvatureIdentityQuadraticEval (I := I) g c v w := by
  unfold algebraicCurvatureIdentityQuadraticEval
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [scaleMetric_inner]
  ring

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M]
    [SigmaCompactSpace M] [T2Space M] in
theorem algebraicCurvatureOperatorQuadraticEval_smul
    (a : Real) {x : M} {n : Nat}
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (c : Fin n → Real) (v w : Fin n → TangentSpace I x) :
    algebraicCurvatureOperatorQuadraticEval (I := I) (M := M) (a • A) c v w =
      a * algebraicCurvatureOperatorQuadraticEval (I := I) (M := M) A c v w := by
  unfold algebraicCurvatureOperatorQuadraticEval
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Submodule.coe_smul_of_tower, tensor04StdAt, Tensor0SSpace.smul_apply,
    smul_eq_mul]
  ring

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M]
    [SigmaCompactSpace M] [T2Space M] in
theorem curvatureOperatorLowerBoundAt_scaleMetric
    {a : Real} (ha : 0 < a) {g : SmoothRiemannianMetric I M} {x : M}
    {A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x} {K : Real} :
    curvatureOperatorLowerBoundAt (I := I) (scaleMetric (I := I) a ha g) x (a • A) K ↔
      curvatureOperatorLowerBoundAt (I := I) g x A (a * K) := by
  constructor
  · intro h n c v w
    have hbound := h n c v w
    rw [algebraicCurvatureOperatorQuadraticEval_smul,
      algebraicCurvatureIdentityQuadraticEval_scaleMetric] at hbound
    nlinarith
  · intro h n c v w
    have hbound := h n c v w
    rw [algebraicCurvatureOperatorQuadraticEval_smul,
      algebraicCurvatureIdentityQuadraticEval_scaleMetric]
    nlinarith

end DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Curvature

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem metricRicciAt_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M) :
    metricRicciAt (I := I) (M := M) (scaleMetric (I := I) c hc g) x =
      metricRicciAt (I := I) (M := M) g x := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  ext slots
  simp [metricRicciAt, metricCov, lcConn_scaleMetric]

theorem metricScalarAt_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (x : M) :
    metricScalarAt (I := I) (M := M) (scaleMetric (I := I) c hc g) x =
      c⁻¹ * metricScalarAt (I := I) (M := M) g x := by
  rw [metricScalarAt_def, metricScalarAt_def,
    DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_scaleMetric]
  rw [metricRicciAt_scaleMetric]

section

variable [T2Space M] [I.Boundaryless]

theorem ricciTensor_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    ricciTensor (I := I) (scaleMetric (I := I) c hc g) x v w =
      ricciTensor (I := I) g x v w := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  simp [ricciTensor_apply, ricciEndo, LeviCivita, lcConn_scaleMetric]

end

end DifferentialGeometry.Geometry.Curvature
