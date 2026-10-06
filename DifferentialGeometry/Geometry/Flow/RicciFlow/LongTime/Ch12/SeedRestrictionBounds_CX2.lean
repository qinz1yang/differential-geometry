import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TraceRestrictionBack_CX2

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

/-- Transport a moving-ball curvature bound along the same actual seed
trace, from an observation prefix to its source tower history. -/
theorem seed_trace_ball_bound_of_restriction_CX2 (H : ObservedHistory.{u})
    (cut : Icc (0 : ℝ) H.horizon) {a t : Icc (0 : ℝ) (H.restrict cut).horizon} {hat : a ≤ t}
    {y : ((H.restrict cut).stageAt t).Carrier}
    (Y : BackwardPointTrace (H.restrict cut) ((H.restrict cut).activeStage a)
      ((H.restrict cut).activeStage t) ((H.restrict cut).activeStage_mono hat) y)
    {R B : ℝ}
    (hbound : ∀ (v : Icc (0 : ℝ) (H.restrict cut).horizon) (hav : a ≤ v) (hvt : v ≤ t),
      ∀ q ∈ riemannianBallOf ((H.restrict cut).stageMetric ((H.restrict cut).activeStage v) v)
        (Y.point ((H.restrict cut).activeStage v) ((H.restrict cut).activeStage_mono hav)
          ((H.restrict cut).activeStage_mono hvt)) R,
      Real.sqrt (normSq0S ((H.restrict cut).stageMetric ((H.restrict cut).activeStage v) v) q 4
        (metricRm04At ((H.restrict cut).stageMetric ((H.restrict cut).activeStage v) v) q)) ≤ B) :
    ∀ (v : Icc (0 : ℝ) H.horizon) (hav : restrictTime_CX2 H cut a ≤ v)
      (hvt : v ≤ restrictTime_CX2 H cut t),
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
        ((traceAtOfRestriction_CX2 H cut (hat := hat) Y).point (H.activeStage v)
          (H.activeStage_mono hav) (H.activeStage_mono hvt)) R,
      Real.sqrt (normSq0S (H.stageMetric (H.activeStage v) v) q 4
        (metricRm04At (H.stageMetric (H.activeStage v) v) q)) ≤ B := by
  intro v hav hvt q hq
  let v' : Icc (0 : ℝ) (H.restrict cut).horizon :=
    ⟨v.val, v.property.1, (show v.val ≤ t.val from hvt).trans t.property.2⟩
  have hav' : a ≤ v' := hav
  have hvt' : v' ≤ t := hvt
  obtain ⟨q', rfl⟩ := restrictPoint_surjective_CX2 H cut v' q
  have hc := traceAtOfRestriction_point_heq_CX2 H cut (hat := hat) Y v' hav' hvt'
  have hq' := (metricBall_heq_CX2 (H.restrict_stageAt cut v') (H.restrict_sliceMetric cut v')
    hc.symm (restrictPoint_heq_CX2 H cut v' q').symm R).mpr hq
  have heq := rmNormSq_heq_CX2 (H.restrict_stageAt cut v') (H.restrict_sliceMetric cut v')
    (restrictPoint_heq_CX2 H cut v' q').symm
  exact (congrArg Real.sqrt heq).symm.trans_le (hbound v' hav' hvt' q' hq')

end GC.LongTime.Ch12
