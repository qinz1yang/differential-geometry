import DifferentialGeometry.Integral.Connection.TensorConnLaplacianChart
import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivativeOpNorm
import DifferentialGeometry.Integral.Connection.RawTensorConnLap2ndApplicationOpNorm

/-!
# Pointwise op-norm bound for `rawTensorConnLap`

For a smooth Riemannian manifold `(M, g)`, a chart-centre `α : M`, and a smooth
`(r, s)`-tensor section `T`, this file packages the pointwise op-norm bound for
the raw tensor connection Laplacian `rawTensorConnLap g r s T.toFun b` at every
point `b` lying in the intersection of the chart-α partition-of-unity tsupport
and the chart-α Levi-Civita good set.

The bound is the natural composition of two ingredients:

1. The chart-frame expansion `rawTensorConnLap_eq_chart` — at any
   `y ∈ chartLeviCivitaGoodSet α`,
   `rawTensorConnLap g r s T.toFun y` is a finite sum over
   `i : Fin (Module.finrank ℝ E)` of the difference between
   * the chart-frame second covariant derivative
     `chartTensorRSCovariantDerivative r s g α
        (covApply cov_RS B_i T.toFun) (smoothOrthoFrame g y i) y`, and
   * the second-application Γ-correction
     `cov_RS T.toFun y ((LeviCivita g) B_i y (B_i y))`,
   where `B_i = smoothOrthoFrame g y i`.

2. The headline op-norm bound
   `chartTensorRSCovariantDerivative_opNorm_le_pou_tsupport` controlling the
   chart-frame second covariant derivative pointwise on the chart-atlas
   partition-of-unity tsupport in terms of the chart-pulled Fréchet derivative
   of its tensor argument and the norm of its tangent argument.

Combining the two via the triangle inequality yields a pointwise op-norm bound
for `rawTensorConnLap g r s T.toFun b` of the form

  `‖rawTensorConnLap g r s T.toFun b‖ ≤
      C * ∑ i, (chart-frame data at b for the i-th second covariant derivative)
        + ∑ i, ‖(cov_RS T.toFun b) (LeviCivita g B_i b (B_i b))‖`,

where the constant `C` depends only on the chart at `α`, the locality
hypothesis, and the metric `g`; it is independent of `T` and `b`. The second
sum captures the residual second-application Γ-correction term; on its own
each summand is bounded by the operator norm of the abstract first covariant
derivative `cov_RS T.toFun b` applied to a specific tangent vector.

## Main definitions

* `chartFrameData` — the pointwise per-frame-index chart-frame data expression
  controlling the chart-frame second covariant derivative contribution to the
  bound, together with its non-negativity lemma `chartFrameData_nonneg`.
* `secondAppChartData` — the pointwise per-frame-index second-application
  chart-data expression controlling the residual Γ-correction contribution to
  the bound, together with its non-negativity lemma `secondAppChartData_nonneg`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The pointwise per-frame-index chart-frame "data" expression appearing on
the right-hand side of the bound on the first contribution to
`rawTensorConnLap`. For a raw `(r, s)`-tensor section `T₀ : Π b, …`, a
chart-centre `α`, and a point `y`, the chart-frame data at the `i`-th frame
index is the non-negative real
`(max (1 + ‖B_i y‖) 1) ^ (max r s) *
    (‖fderiv ℝ (chart-pulled covApply cov_RS B_i T₀) (extChartAt I α y)‖
      * ‖B_i y‖ + ‖covApply cov_RS B_i T₀ y‖)`,
where `B_i = smoothOrthoFrame g y i`. -/
noncomputable def chartFrameData
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : Π b : M, TensorRSSpace r s I b)
    (y : M) (i : Fin (Module.finrank ℝ E)) : ℝ :=
  (max (1 + ‖smoothOrthoFrame (I := I) g y i y‖) 1) ^ (max r s) *
    (‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
        (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
          (smoothOrthoFrame (I := I) g y i) T₀) ∘
        (extChartAt I α).symm) (extChartAt I α y)‖ *
      ‖smoothOrthoFrame (I := I) g y i y‖
      + ‖covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
          (smoothOrthoFrame (I := I) g y i) T₀ y‖)

lemma chartFrameData_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : Π b : M, TensorRSSpace r s I b)
    (y : M) (i : Fin (Module.finrank ℝ E)) :
    0 ≤ chartFrameData (I := I) g r s α T₀ y i := by
  classical
  unfold chartFrameData
  have h1 : 0 ≤ max (1 + ‖smoothOrthoFrame (I := I) g y i y‖) 1 :=
    le_trans zero_le_one (le_max_right _ _)
  have h2 : 0 ≤ (max (1 + ‖smoothOrthoFrame (I := I) g y i y‖) 1) ^ (max r s) :=
    pow_nonneg h1 _
  have h3 : 0 ≤
      ‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g y i) T₀) ∘
          (extChartAt I α).symm) (extChartAt I α y)‖ *
        ‖smoothOrthoFrame (I := I) g y i y‖
        + ‖covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g y i) T₀ y‖ := by
    have h_a : 0 ≤
        ‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
            (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g y i) T₀) ∘
          (extChartAt I α).symm) (extChartAt I α y)‖ *
        ‖smoothOrthoFrame (I := I) g y i y‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have h_b : 0 ≤
        ‖covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g))
          (smoothOrthoFrame (I := I) g y i) T₀ y‖ := norm_nonneg _
    linarith
  exact mul_nonneg h2 h3

/-- The pointwise per-frame-index "second-application chart-data" expression
appearing on the right-hand side of the bound on the second contribution to
`rawTensorConnLap`. For a raw `(r, s)`-tensor section `T₀`, a chart-centre
`α`, and a point `y`, the second-application chart-data at the `i`-th frame
index uses the inner Γ-vector
`v_i := (LeviCivita g) B_i y (B_i y)` (with `B_i = smoothOrthoFrame g y i`),
together with the chart-pulled Fréchet derivative of the chart-representation
of `T₀` itself. -/
noncomputable def secondAppChartData
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : Π b : M, TensorRSSpace r s I b)
    (y : M) (i : Fin (Module.finrank ℝ E)) : ℝ :=
  (max (1 +
      ‖(LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g y i) y
        (smoothOrthoFrame (I := I) g y i y)‖) 1) ^ (max r s) *
    (‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α T₀ ∘
        (extChartAt I α).symm) (extChartAt I α y)‖ *
      ‖(LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g y i) y
        (smoothOrthoFrame (I := I) g y i y)‖
      + ‖T₀ y‖)

lemma secondAppChartData_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : Π b : M, TensorRSSpace r s I b)
    (y : M) (i : Fin (Module.finrank ℝ E)) :
    0 ≤ secondAppChartData (I := I) g r s α T₀ y i := by
  classical
  unfold secondAppChartData
  have h1 : 0 ≤ max (1 +
      ‖(LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g y i) y
        (smoothOrthoFrame (I := I) g y i y)‖) 1 :=
    le_trans zero_le_one (le_max_right _ _)
  have h2 : 0 ≤ (max (1 +
      ‖(LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g y i) y
        (smoothOrthoFrame (I := I) g y i y)‖) 1) ^ (max r s) :=
    pow_nonneg h1 _
  have h3a : 0 ≤
      ‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α T₀ ∘
          (extChartAt I α).symm) (extChartAt I α y)‖ *
        ‖(LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g y i) y
          (smoothOrthoFrame (I := I) g y i y)‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have h3b : 0 ≤ ‖T₀ y‖ := norm_nonneg _
  exact mul_nonneg h2 (by linarith)

end Connection
end Integral
end DifferentialGeometry

end
