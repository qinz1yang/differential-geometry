import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CentreTrace_S138
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TraceRestrictionBack_CX2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MacroWholeBallWbd01

/-!
# CH12-S138, group 2a: slice <-> tower bridges for the centre trace

* `top_scalar_S138`: the scalar of `s.metric` at `q` equals the tower top scalar at `restrictPoint q'` (`HEq q' q`);
* `toRestriction_scalar_S138`: the scalar along the trace `traceAtToRestriction_CX2 A` of the restricted history
  equals the scalar along the tower trace `A` (so the pointwise bound of `centreTrace_S138` transports to `s.history`).
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

theorem metricScalarAt_heq_S138 {A B : OrientedThreeStage.{u}} (h : A = B) (gA : A.Metric)
    (gB : B.Metric) (hg : HEq gA gB) (x : A.Carrier) (y : B.Carrier) (hxy : HEq x y) :
    metricScalarAt gA x = metricScalarAt gB y := by
  subst h
  rw [eq_of_heq hg, eq_of_heq hxy]

theorem top_scalar_S138 {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (s : RegularSlice F.observation) (q' : (s.history.stageAt (sliceTop_S8 s)).Carrier)
    (q : s.stage.Carrier) (hq : HEq q' q) :
    metricScalarAt s.metric q = metricScalarAt ((sliceTowerHistory_CX2 s).stageMetric
      ((sliceTowerHistory_CX2 s).activeStage (sliceTowerTime_CX2 s)) (sliceTowerTime_CX2 s))
      (restrictPoint_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s) q') := by
  have hact : s.history.activeStage (sliceTop_S8 s) = Fin.last s.history.eventCount :=
    s.history.activeStage_at_horizon
  have hstage : s.stage = (sliceTowerHistory_CX2 s).stageAt
      (restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s)) :=
    (congrArg s.history.stage hact.symm).trans
      ((sliceTowerHistory_CX2 s).restrict_stageAt (sliceTowerTime_CX2 s) (sliceTop_S8 s))
  have h1 : HEq s.metric (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) := by
    rw [hact]; exact HEq.rfl
  have hmetric := h1.trans
    ((sliceTowerHistory_CX2 s).restrict_sliceMetric (sliceTowerTime_CX2 s) (sliceTop_S8 s))
  exact metricScalarAt_heq_S138 hstage _ _ hmetric q _
    (hq.symm.trans (restrictPoint_heq_CX2 _ _ _ q').symm)

theorem toRestriction_point_heq_S138 (H : ObservedHistory.{u}) (cut : Icc (0 : ℝ) H.horizon)
    {a t : Icc (0 : ℝ) (H.restrict cut).horizon} {hat : a ≤ t}
    {x : ((H.restrict cut).stageAt t).Carrier}
    (A : BackwardPointTrace H (H.activeStage (restrictTime_CX2 H cut a))
      (H.activeStage (restrictTime_CX2 H cut t))
      (H.activeStage_mono (show restrictTime_CX2 H cut a ≤ restrictTime_CX2 H cut t from hat))
      (restrictPoint_CX2 H cut t x))
    (v : Icc (0 : ℝ) (H.restrict cut).horizon) (hav : a ≤ v) (hvt : v ≤ t) :
    HEq ((traceAtToRestriction_CX2 H cut (hat := hat) A).point ((H.restrict cut).activeStage v)
        ((H.restrict cut).activeStage_mono hav) ((H.restrict cut).activeStage_mono hvt))
      (A.point (H.activeStage (restrictTime_CX2 H cut v))
        (H.activeStage_mono (show restrictTime_CX2 H cut a ≤ restrictTime_CX2 H cut v from hav))
        (H.activeStage_mono (show restrictTime_CX2 H cut v ≤ restrictTime_CX2 H cut t from hvt))) := by
  have hA : traceAtOfRestriction_CX2 H cut (hat := hat)
      (traceAtToRestriction_CX2 H cut (hat := hat) A) = A := Subsingleton.elim _ _
  have h := traceAtOfRestriction_point_heq_CX2 H cut (hat := hat)
    (traceAtToRestriction_CX2 H cut (hat := hat) A) v hav hvt
  rw [hA] at h
  exact h.symm

theorem toRestriction_scalar_S138 (H : ObservedHistory.{u}) (cut : Icc (0 : ℝ) H.horizon)
    {a t : Icc (0 : ℝ) (H.restrict cut).horizon} {hat : a ≤ t}
    {x : ((H.restrict cut).stageAt t).Carrier}
    (A : BackwardPointTrace H (H.activeStage (restrictTime_CX2 H cut a))
      (H.activeStage (restrictTime_CX2 H cut t))
      (H.activeStage_mono (show restrictTime_CX2 H cut a ≤ restrictTime_CX2 H cut t from hat))
      (restrictPoint_CX2 H cut t x))
    (v : Icc (0 : ℝ) (H.restrict cut).horizon) (hav : a ≤ v) (hvt : v ≤ t) :
    metricScalarAt ((H.restrict cut).stageMetric ((H.restrict cut).activeStage v) v)
      ((traceAtToRestriction_CX2 H cut (hat := hat) A).point ((H.restrict cut).activeStage v)
        ((H.restrict cut).activeStage_mono hav) ((H.restrict cut).activeStage_mono hvt)) =
    metricScalarAt (H.stageMetric (H.activeStage (restrictTime_CX2 H cut v))
        (restrictTime_CX2 H cut v))
      (A.point (H.activeStage (restrictTime_CX2 H cut v))
        (H.activeStage_mono (show restrictTime_CX2 H cut a ≤ restrictTime_CX2 H cut v from hav))
        (H.activeStage_mono (show restrictTime_CX2 H cut v ≤ restrictTime_CX2 H cut t from hvt))) :=
  metricScalarAt_heq_S138 (H.restrict_stageAt cut v) _ _ (H.restrict_sliceMetric cut v) _ _
    (toRestriction_point_heq_S138 H cut A v hav hvt)

end GC.LongTime.Ch12
