import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
import DifferentialGeometry.Geometry.Curvature.OperatorScaling

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem NormalizedSequence.curvatureOperatorLowerBoundAt_scaleMetric
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (i : ℕ)
    {Q : ℝ} (hQ : 0 < Q) (t : ℝ) (ht : t / Q ∈ (X.interval i).carrier)
    (y : (X.term i).M) :
    let g := scaleMetric Q hQ ((X.term i).S.base.metric (t / Q))
    curvatureOperatorLowerBoundAt g y (metricAlgebraicCurvatureTensorAt g y)
      (rescalePinchingFunction (Q * X.scale i) Phi (metricScalarAt g y)) := by
  let g := (X.term i).S.base.metric (t / Q)
  have hbase := X.pinching i (t / Q) ht y
  have hp : curvatureOperatorLowerBoundAt g y (metricAlgebraicCurvatureTensorAt g y)
      (rescalePinchingFunction (X.scale i) Phi (metricScalarAt g y)) := by
    exact hbase
  dsimp only
  rw [curvatureOperatorLowerBoundAt_scaleMetric_iff]
  have hcoefficient : Q * rescalePinchingFunction (Q * X.scale i) Phi
      (metricScalarAt (scaleMetric Q hQ g) y) =
      rescalePinchingFunction (X.scale i) Phi (metricScalarAt g y) := by
    rw [metricScalarAt_scaleMetric, rescalePinchingFunction, rescalePinchingFunction]
    rw [show Q * X.scale i * (Q⁻¹ * metricScalarAt g y) =
      X.scale i * metricScalarAt g y by field_simp]
    rw [mul_inv]
    field_simp
  change curvatureOperatorLowerBoundAt g y (metricAlgebraicCurvatureTensorAt g y) _
  rw [hcoefficient]
  exact hp

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
