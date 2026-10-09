import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Metric.Proper

set_option autoImplicit false

open scoped Manifold ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

theorem ProperMetricOn.metric_complete (Y : PointedRiemannianManifold I)
    (P : ProperMetricOn Y) : MetricComplete Y := by
  have hem :
      (letI : MetricSpace Y.M := P.ms; (inferInstance : PseudoEMetricSpace Y.M)) =
      (letI : EMetricSpace Y.M := Y.emetricSpace; (inferInstance : PseudoEMetricSpace Y.M)) := by
    apply PseudoEMetricSpace.ext
    ext x y
    change (letI : MetricSpace Y.M := P.ms; edist x y) =
      (letI : EMetricSpace Y.M := Y.emetricSpace; edist x y)
    rw [P.realizes x y]
    have hdist :
        (letI : MetricSpace Y.M := P.ms; edist x y) =
          ENNReal.ofReal (letI : MetricSpace Y.M := P.ms; dist x y) := by
      let : MetricSpace Y.M := P.ms
      exact edist_dist x y
    exact hdist
  have hU := congrArg (fun m : PseudoEMetricSpace Y.M => m.toUniformSpace) hem
  change @CompleteSpace Y.M Y.emetricSpace.toUniformSpace
  rw [← hU]
  let : MetricSpace Y.M := P.ms
  let : ProperSpace Y.M := P.proper
  infer_instance

theorem ProperMetricOn.properSpace_aligned (Y : PointedRiemannianManifold I)
    (P : ProperMetricOn Y) :
    let : MetricSpace Y.M := P.alignedMetricSpace Y
    ProperSpace Y.M := by
  let : MetricSpace Y.M := P.alignedMetricSpace Y
  constructor
  intro x r
  have hc : @IsCompact Y.M P.ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (letI : MetricSpace Y.M := P.ms; Metric.closedBall x r) := by
    let : MetricSpace Y.M := P.ms
    let : ProperSpace Y.M := P.proper
    exact isCompact_closedBall x r
  rw [P.top_eq Y] at hc
  exact hc

end DifferentialGeometry.CheegerGromovCompactness
