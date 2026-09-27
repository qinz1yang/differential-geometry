import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.DiagonalCylinderDistance
import DifferentialGeometry.Geometry.Comparison.Toponogov.BoundedCrossAngle

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn

universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted PointedFlowData.smooth
  PointedFlowData.t2 PointedFlowData.sigmaCompact

variable {P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval}

theorem ShrinkingCylinderCover.tendsto_rays_comparisonAngle_zero_of_diagonalModel
    (C : ShrinkingCylinderCover P) (hdiag : C.DiagonalModel)
    (hbase : PointedFlowScalarAtBase P 1) (p : P.M)
    (a b : ℝ≥0 → P.M)
    (ha : ∀ s, metricDistance (P.S.base.metric 0) p (a s) = s)
    (hb : ∀ s, metricDistance (P.S.base.metric 0) p (b s) = s) :
    Tendsto (fun s : ℝ≥0 => Geometry.Comparison.Toponogov.comparisonAngle s s
      (metricDistance (P.S.base.metric 0) (a s) (b s))) atTop (𝓝 0) := by
  obtain ⟨B, _, hB⟩ := C.exists_cross_distance_bound_of_diagonalModel hdiag hbase p
  exact Geometry.Comparison.Toponogov.tendsto_comparisonAngle_zero_of_bounded_cross_distance
    (fun _ => ENNReal.toReal_nonneg) (fun s => hB (a s) (b s) ((ha s).trans (hb s).symm))

theorem ShrinkingCylinderCover.not_eventually_comparisonAngle_lower_of_diagonalModel
    (C : ShrinkingCylinderCover P) (hdiag : C.DiagonalModel)
    (hbase : PointedFlowScalarAtBase P 1) (p : P.M)
    (a b : ℝ≥0 → P.M)
    (ha : ∀ s, metricDistance (P.S.base.metric 0) p (a s) = s)
    (hb : ∀ s, metricDistance (P.S.base.metric 0) p (b s) = s)
    {theta : ℝ} (htheta : 0 < theta) :
    ¬ ∀ᶠ s : ℝ≥0 in atTop, theta ≤ Geometry.Comparison.Toponogov.comparisonAngle s s
      (metricDistance (P.S.base.metric 0) (a s) (b s)) := by
  intro hbound
  have hlim := C.tendsto_rays_comparisonAngle_zero_of_diagonalModel hdiag hbase p a b ha hb
  have hh : theta ≤ 0 := ge_of_tendsto hlim hbound
  exact (not_le_of_gt htheta) hh

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
