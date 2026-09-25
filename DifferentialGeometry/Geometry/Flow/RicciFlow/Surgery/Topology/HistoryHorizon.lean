import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryAction.AbsoluteContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MasterFlowCompatibility

noncomputable section
open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory
universe u
variable {P : OrientedThreeStage.{u}} (H : RetainedCoreHistory P)

private theorem stageMetric_cast_eq (A : RetainedCoreHistory P) (i : Fin A.eventCount) (v : ℝ) :
    A.toHistory.stageMetric i.castSucc v = (A.coreEvent i).toMetricCutCapEvent.incoming.flow.base.metric v := by
  simp only [ObservedHistory.stageMetric, Fin.lastCases_castSucc]

theorem stageMetric_closedPrefixes_eq
    {s t u : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hinit : G.flow.base.metric (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount))
    (ht : H.horizon < t) (hu : H.horizon < u) (hts : t < s) (hus : u < s)
    (j : Fin (H.eventCount + 1)) (v : ℝ) :
    (H.extendHorizon t ht.le (G.closedPrefix t (H.time_le_horizon.trans_lt ht) hts) hinit).toHistory.stageMetric j v =
      (H.extendHorizon u hu.le (G.closedPrefix u (H.time_le_horizon.trans_lt hu) hus) hinit).toHistory.stageMetric j v := by
  let A := H.extendHorizon t ht.le (G.closedPrefix t (H.time_le_horizon.trans_lt ht) hts) hinit
  let U := H.extendHorizon u hu.le (G.closedPrefix u (H.time_le_horizon.trans_lt hu) hus) hinit
  change A.toHistory.stageMetric j v = U.toHistory.stageMetric j v
  cases j using Fin.lastCases with
  | last =>
    exact (A.toHistory.stageMetric_last_of_lt (h := H.time_le_horizon.trans_lt ht) v).trans
      (U.toHistory.stageMetric_last_of_lt (h := H.time_le_horizon.trans_lt hu) v).symm
  | cast i =>
    exact (stageMetric_cast_eq A i v).trans (stageMetric_cast_eq U i v).symm


theorem isParabolicallyRmControlledBall_closedPrefixes_iff
    {s t u : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hinit : G.flow.base.metric (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount))
    (ht : H.horizon < t) (htu : t ≤ u) (hus : u < s)
    (time : Icc (0 : ℝ) t) (r : ℝ) :
    let htstart := H.time_le_horizon.trans_lt ht
    let hustart := htstart.trans_le htu
    let A := H.extendHorizon t ht.le (G.closedPrefix t htstart (htu.trans_lt hus)) hinit
    let U := H.extendHorizon u (ht.le.trans htu) (G.closedPrefix u hustart hus) hinit
    let time' : Icc (0 : ℝ) u := ⟨time.val, time.property.1, time.property.2.trans htu⟩
    ∀ p : (A.toHistory.stageAt time).Carrier,
      A.toHistory.isParabolicallyRmControlledBall time p r ↔
        U.toHistory.isParabolicallyRmControlledBall time' p r := by
  intro htstart hustart A U time' p
  have hmetric (j : Fin (H.eventCount + 1)) (v : ℝ) :
      A.toHistory.stageMetric j v = U.toHistory.stageMetric j v :=
    stageMetric_closedPrefixes_eq H G hinit ht (ht.trans_le htu) (htu.trans_lt hus) hus j v
  constructor
  · intro hball
    obtain ⟨hr, a, hat, ha, htrace⟩ := hball
    let a' : Icc (0 : ℝ) u := ⟨a.val, a.property.1, a.property.2.trans htu⟩
    refine ⟨hr, a', hat, ha, ?_⟩
    intro x hx
    have hx' : x ∈ riemannianBallOf (A.toHistory.stageMetric (A.toHistory.activeStage time) time) p r := by
      change x ∈ riemannianBallOf (U.toHistory.stageMetric (A.toHistory.activeStage time) time.val) p r at hx
      rw [← hmetric (A.toHistory.activeStage time) time.val] at hx
      exact hx
    obtain ⟨B, hB⟩ := htrace x hx'
    let B' : BackwardPointTrace U.toHistory (U.toHistory.activeStage a')
        (U.toHistory.activeStage time') (U.toHistory.activeStage_mono hat) x :=
      ⟨B.point, B.endpoint_eq, B.crossing⟩
    refine ⟨B', ?_, ?_⟩
    · intro v hav hvt
      let w : Icc (0 : ℝ) t := ⟨v.val, v.property.1, (show v.val ≤ time.val from hvt).trans time.property.2⟩
      have hh := hB.1 w hav hvt
      change r ^ 4 * normSq0S (U.toHistory.stageMetric (A.toHistory.activeStage w) w.val)
        (B.point (A.toHistory.activeStage w) (A.toHistory.activeStage_mono hav)
          (A.toHistory.activeStage_mono hvt)) 4
        (metricRm04At (U.toHistory.stageMetric (A.toHistory.activeStage w) w.val)
          (B.point (A.toHistory.activeStage w) (A.toHistory.activeStage_mono hav)
            (A.toHistory.activeStage_mono hvt))) ≤ 1
      rw [← hmetric (A.toHistory.activeStage w) w.val]
      exact hh
    · intro i hfi hil
      exact hB.2 i hfi hil
  · intro hball
    obtain ⟨hr, a', hat, ha, htrace⟩ := hball
    let a : Icc (0 : ℝ) t :=
      ⟨a'.val, a'.property.1, (show a'.val ≤ time.val from hat).trans time.property.2⟩
    refine ⟨hr, a, hat, ha, ?_⟩
    intro x hx
    have hx' : x ∈ riemannianBallOf (U.toHistory.stageMetric (U.toHistory.activeStage time') time') p r := by
      change x ∈ riemannianBallOf (U.toHistory.stageMetric (A.toHistory.activeStage time) time.val) p r
      rw [← hmetric (A.toHistory.activeStage time) time.val]
      exact hx
    obtain ⟨B, hB⟩ := htrace x hx'
    let B' : BackwardPointTrace A.toHistory (A.toHistory.activeStage a)
        (A.toHistory.activeStage time) (A.toHistory.activeStage_mono hat) x :=
      ⟨B.point, B.endpoint_eq, B.crossing⟩
    refine ⟨B', ?_, ?_⟩
    · intro v hav hvt
      let w : Icc (0 : ℝ) u := ⟨v.val, v.property.1, v.property.2.trans htu⟩
      have hh := hB.1 w hav hvt
      change r ^ 4 * normSq0S (A.toHistory.stageMetric (U.toHistory.activeStage w) w.val)
        (B.point (U.toHistory.activeStage w) (U.toHistory.activeStage_mono hav)
          (U.toHistory.activeStage_mono hvt)) 4
        (metricRm04At (A.toHistory.stageMetric (U.toHistory.activeStage w) w.val)
          (B.point (U.toHistory.activeStage w) (U.toHistory.activeStage_mono hav)
            (U.toHistory.activeStage_mono hvt))) ≤ 1
      rw [hmetric (U.toHistory.activeStage w) w.val]
      exact hh
    · intro i hfi hil
      exact hB.2 i hfi hil

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

end

noncomputable section
open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

universe u
variable {P : OrientedThreeStage.{u}}

private theorem stageDomain_last_eq (A : RetainedCoreHistory P) :
    A.toHistory.stageDomain (Fin.last A.eventCount) = Icc (A.time (Fin.last A.eventCount)) A.horizon := by
  simp only [ObservedHistory.stageDomain, Fin.lastCases_last]

private theorem stageDomain_cast_eq (A : RetainedCoreHistory P) (i : Fin A.eventCount) :
    A.toHistory.stageDomain i.castSucc = Ico (A.time i.castSucc) (A.time i.succ) := by
  simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc]

private theorem stageEndTime_last_eq (A : RetainedCoreHistory P) :
    A.toHistory.stageEndTime (Fin.last A.eventCount) = A.horizon := by
  simp only [ObservedHistory.stageEndTime, Fin.lastCases_last]

private theorem stageEndTime_cast_eq (A : RetainedCoreHistory P) (i : Fin A.eventCount) :
    A.toHistory.stageEndTime i.castSucc = A.time i.succ := by
  simp only [ObservedHistory.stageEndTime, Fin.lastCases_castSucc]

variable {P : OrientedThreeStage.{u}} (H : RetainedCoreHistory P) {s t u : ℝ}
  (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
  (hinit : G.flow.base.metric (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount))
  (ht : H.horizon < t) (htu : t ≤ u) (hus : u < s)

private theorem incoming_prefix_stageDomain_eq (j : Fin (H.eventCount + 1)) {v : ℝ} (hv : v ≤ t) :
    v ∈ (H.extendHorizon t ht.le (G.closedPrefix t (H.time_le_horizon.trans_lt ht) (htu.trans_lt hus)) hinit).toHistory.stageDomain j ↔ v ∈ (H.extendHorizon u (ht.trans_le htu).le (G.closedPrefix u (H.time_le_horizon.trans_lt (ht.trans_le htu)) hus) hinit).toHistory.stageDomain j := by
  let A := H.extendHorizon t ht.le (G.closedPrefix t (H.time_le_horizon.trans_lt ht) (htu.trans_lt hus)) hinit
  let U := H.extendHorizon u (ht.trans_le htu).le (G.closedPrefix u (H.time_le_horizon.trans_lt (ht.trans_le htu)) hus) hinit
  change v ∈ A.toHistory.stageDomain j ↔ v ∈ U.toHistory.stageDomain j
  cases j using Fin.lastCases with
  | last =>
    have hA := (congrArg (fun V : Set ℝ => v ∈ V) (stageDomain_last_eq A)).to_iff
    have hU := (congrArg (fun V : Set ℝ => v ∈ V) (stageDomain_last_eq U)).to_iff
    exact hA.trans ((show (H.time (Fin.last H.eventCount) ≤ v ∧ v ≤ t) ↔
      (H.time (Fin.last H.eventCount) ≤ v ∧ v ≤ u) from
        ⟨fun h => ⟨h.1, hv.trans htu⟩, fun h => ⟨h.1, hv⟩⟩).trans hU.symm)
  | cast i =>
    exact (congrArg (fun V : Set ℝ => v ∈ V)
      ((stageDomain_cast_eq A i).trans (stageDomain_cast_eq U i).symm)).to_iff

private theorem incoming_prefix_stage_upper_eq (j : Fin (H.eventCount + 1)) {v : ℝ} (hv : v ≤ t) :
    v ∈ Icc ((H.extendHorizon t ht.le (G.closedPrefix t (H.time_le_horizon.trans_lt ht) (htu.trans_lt hus)) hinit).toHistory.time j) ((H.extendHorizon t ht.le (G.closedPrefix t (H.time_le_horizon.trans_lt ht) (htu.trans_lt hus)) hinit).toHistory.stageEndTime j) ↔ v ∈ Icc ((H.extendHorizon u (ht.trans_le htu).le (G.closedPrefix u (H.time_le_horizon.trans_lt (ht.trans_le htu)) hus) hinit).toHistory.time j) ((H.extendHorizon u (ht.trans_le htu).le (G.closedPrefix u (H.time_le_horizon.trans_lt (ht.trans_le htu)) hus) hinit).toHistory.stageEndTime j) := by
  let A := H.extendHorizon t ht.le (G.closedPrefix t (H.time_le_horizon.trans_lt ht) (htu.trans_lt hus)) hinit
  let U := H.extendHorizon u (ht.trans_le htu).le (G.closedPrefix u (H.time_le_horizon.trans_lt (ht.trans_le htu)) hus) hinit
  change v ∈ Icc (A.toHistory.time j) (A.toHistory.stageEndTime j) ↔
    v ∈ Icc (U.toHistory.time j) (U.toHistory.stageEndTime j)
  cases j using Fin.lastCases with
  | last =>
    have hA := (congrArg (fun z : ℝ => v ∈ Icc (H.time (Fin.last H.eventCount)) z)
      (stageEndTime_last_eq A)).to_iff
    have hU := (congrArg (fun z : ℝ => v ∈ Icc (H.time (Fin.last H.eventCount)) z)
      (stageEndTime_last_eq U)).to_iff
    exact hA.trans ((show (H.time (Fin.last H.eventCount) ≤ v ∧ v ≤ t) ↔
      (H.time (Fin.last H.eventCount) ≤ v ∧ v ≤ u) from
        ⟨fun h => ⟨h.1, hv.trans htu⟩, fun h => ⟨h.1, hv⟩⟩).trans hU.symm)
  | cast i =>
    exact (congrArg (fun z : ℝ => v ∈ Icc (H.time i.castSucc) z)
      ((stageEndTime_cast_eq A i).trans (stageEndTime_cast_eq U i).symm)).to_iff

private theorem incoming_prefix_regularizedStageStart_eq (T a : ℝ)
    (hclock : T - a ^ 2 ≤ t) (j : Fin (H.eventCount + 1)) :
    (H.extendHorizon t ht.le (G.closedPrefix t (H.time_le_horizon.trans_lt ht) (htu.trans_lt hus)) hinit).toHistory.regularizedStageStart T a j = (H.extendHorizon u (ht.trans_le htu).le (G.closedPrefix u (H.time_le_horizon.trans_lt (ht.trans_le htu)) hus) hinit).toHistory.regularizedStageStart T a j := by
  let A := H.extendHorizon t ht.le (G.closedPrefix t (H.time_le_horizon.trans_lt ht) (htu.trans_lt hus)) hinit
  let U := H.extendHorizon u (ht.trans_le htu).le (G.closedPrefix u (H.time_le_horizon.trans_lt (ht.trans_le htu)) hus) hinit
  change A.toHistory.regularizedStageStart T a j = U.toHistory.regularizedStageStart T a j
  cases j using Fin.lastCases with
  | last =>
    exact (congrArg (fun z : ℝ => Real.sqrt (T - min (T - a ^ 2) z)) (stageEndTime_last_eq A)).trans
      ((show Real.sqrt (T - min (T - a ^ 2) t) = Real.sqrt (T - min (T - a ^ 2) u) by
        rw [min_eq_left hclock, min_eq_left (hclock.trans htu)]).trans
          (congrArg (fun z : ℝ => Real.sqrt (T - min (T - a ^ 2) z)) (stageEndTime_last_eq U)).symm)
  | cast i =>
    exact congrArg (fun z : ℝ => Real.sqrt (T - min (T - a ^ 2) z))
      ((stageEndTime_cast_eq A i).trans (stageEndTime_cast_eq U i).symm)

private theorem incoming_prefix_stageRegularizedLagrangian_eq (j : Fin (H.eventCount + 1))
    (T : ℝ) (α : ℝ → (H.stage j).Carrier) :
    (H.extendHorizon t ht.le (G.closedPrefix t (H.time_le_horizon.trans_lt ht) (htu.trans_lt hus)) hinit).toHistory.stageRegularizedLagrangian j T α = (H.extendHorizon u (ht.trans_le htu).le (G.closedPrefix u (H.time_le_horizon.trans_lt (ht.trans_le htu)) hus) hinit).toHistory.stageRegularizedLagrangian j T α := by
  funext v
  simp only [ObservedHistory.stageRegularizedLagrangian]
  have he := stageMetric_closedPrefixes_eq H G hinit ht (ht.trans_le htu) (htu.trans_lt hus) hus j (T - v ^ 2)
  convert congrArg (fun g : SmoothRiemannianMetric ThreeModel (H.stage j).Carrier =>
    (1 / 2 : ℝ) * g.inner (α v) (lVelocity α v) (lVelocity α v) +
      2 * v ^ 2 * metricScalarAt g (α v)) he using 1 <;> rfl

private theorem incoming_prefix_stageRegularizedAction_eq (j : Fin (H.eventCount + 1))
    (T : ℝ) (α : ℝ → (H.stage j).Carrier) (a b : ℝ) :
    (H.extendHorizon t ht.le (G.closedPrefix t (H.time_le_horizon.trans_lt ht) (htu.trans_lt hus)) hinit).toHistory.stageRegularizedAction j T α a b = (H.extendHorizon u (ht.trans_le htu).le (G.closedPrefix u (H.time_le_horizon.trans_lt (ht.trans_le htu)) hus) hinit).toHistory.stageRegularizedAction j T α a b := by
  simp only [ObservedHistory.stageRegularizedAction, incoming_prefix_stageRegularizedLagrangian_eq H G hinit ht htu hus]

private theorem incoming_prefix_stageRegularizedExtendedAction_eq (j : Fin (H.eventCount + 1))
    (T B : ℝ) (α : ℝ → (H.stage j).Carrier) (a b : ℝ) :
    (H.extendHorizon t ht.le (G.closedPrefix t (H.time_le_horizon.trans_lt ht) (htu.trans_lt hus)) hinit).toHistory.stageRegularizedExtendedAction j T B α a b = (H.extendHorizon u (ht.trans_le htu).le (G.closedPrefix u (H.time_le_horizon.trans_lt (ht.trans_le htu)) hus) hinit).toHistory.stageRegularizedExtendedAction j T B α a b := by
  simp only [ObservedHistory.stageRegularizedExtendedAction, incoming_prefix_stageRegularizedLagrangian_eq H G hinit ht htu hus]

private theorem incoming_prefix_regularizedStageEnd_eq (T b : ℝ) (j : Fin (H.eventCount + 1)) :
    (H.extendHorizon t ht.le (G.closedPrefix t (H.time_le_horizon.trans_lt ht) (htu.trans_lt hus)) hinit).toHistory.regularizedStageEnd T b j = (H.extendHorizon u (ht.trans_le htu).le (G.closedPrefix u (H.time_le_horizon.trans_lt (ht.trans_le htu)) hus) hinit).toHistory.regularizedStageEnd T b j := rfl

private theorem incoming_prefix_integrability_eq (j : Fin (H.eventCount + 1))
    (T a b : ℝ) (hclock : T - a ^ 2 ≤ t) (α : ℝ → (H.stage j).Carrier) :
    IntervalIntegrable ((H.extendHorizon t ht.le (G.closedPrefix t (H.time_le_horizon.trans_lt ht) (htu.trans_lt hus)) hinit).toHistory.stageRegularizedLagrangian j T α) volume
      ((H.extendHorizon t ht.le (G.closedPrefix t (H.time_le_horizon.trans_lt ht) (htu.trans_lt hus)) hinit).toHistory.regularizedStageStart T a j) ((H.extendHorizon t ht.le (G.closedPrefix t (H.time_le_horizon.trans_lt ht) (htu.trans_lt hus)) hinit).toHistory.regularizedStageEnd T b j) ↔
    IntervalIntegrable ((H.extendHorizon u (ht.trans_le htu).le (G.closedPrefix u (H.time_le_horizon.trans_lt (ht.trans_le htu)) hus) hinit).toHistory.stageRegularizedLagrangian j T α) volume
      ((H.extendHorizon u (ht.trans_le htu).le (G.closedPrefix u (H.time_le_horizon.trans_lt (ht.trans_le htu)) hus) hinit).toHistory.regularizedStageStart T a j) ((H.extendHorizon u (ht.trans_le htu).le (G.closedPrefix u (H.time_le_horizon.trans_lt (ht.trans_le htu)) hus) hinit).toHistory.regularizedStageEnd T b j) := by
  exact ((congrArg (fun L => IntervalIntegrable L volume _ _)
    (incoming_prefix_stageRegularizedLagrangian_eq H G hinit ht htu hus j T α)).trans
    (congrArg₂ (fun x y => IntervalIntegrable _ volume x y)
      (incoming_prefix_regularizedStageStart_eq H G hinit ht htu hus T a hclock j)
      (incoming_prefix_regularizedStageEnd_eq H G hinit ht htu hus T b j))).to_iff

private theorem incoming_prefix_absolutelyContinuous_eq (j : Fin (H.eventCount + 1))
    (T a b : ℝ) (hclock : T - a ^ 2 ≤ t) (α : ℝ → (H.stage j).Carrier) :
    Manifold.absolutelyContinuousOnInterval ThreeModel α
      ((H.extendHorizon t ht.le (G.closedPrefix t (H.time_le_horizon.trans_lt ht) (htu.trans_lt hus)) hinit).toHistory.regularizedStageStart T a j) ((H.extendHorizon t ht.le (G.closedPrefix t (H.time_le_horizon.trans_lt ht) (htu.trans_lt hus)) hinit).toHistory.regularizedStageEnd T b j) ↔
    Manifold.absolutelyContinuousOnInterval ThreeModel α
      ((H.extendHorizon u (ht.trans_le htu).le (G.closedPrefix u (H.time_le_horizon.trans_lt (ht.trans_le htu)) hus) hinit).toHistory.regularizedStageStart T a j) ((H.extendHorizon u (ht.trans_le htu).le (G.closedPrefix u (H.time_le_horizon.trans_lt (ht.trans_le htu)) hus) hinit).toHistory.regularizedStageEnd T b j) := by
  exact (congrArg₂ (fun x y => Manifold.absolutelyContinuousOnInterval ThreeModel α x y)
    (incoming_prefix_regularizedStageStart_eq H G hinit ht htu hus T a hclock j)
    (incoming_prefix_regularizedStageEnd_eq H G hinit ht htu hus T b j)).to_iff

private theorem incoming_prefix_sum_action_eq
    (first last : Fin (H.eventCount + 1)) (T a b : ℝ) (hclock : T - a ^ 2 ≤ t)
    (α : (j : H.toHistory.StageInterval first last) → ℝ → (H.stage j.val).Carrier) :
    (∑ j : H.toHistory.StageInterval first last, (H.extendHorizon t ht.le (G.closedPrefix t (H.time_le_horizon.trans_lt ht) (htu.trans_lt hus)) hinit).toHistory.stageRegularizedAction j.val T (α j)
      ((H.extendHorizon t ht.le (G.closedPrefix t (H.time_le_horizon.trans_lt ht) (htu.trans_lt hus)) hinit).toHistory.regularizedStageStart T a j.val) ((H.extendHorizon t ht.le (G.closedPrefix t (H.time_le_horizon.trans_lt ht) (htu.trans_lt hus)) hinit).toHistory.regularizedStageEnd T b j.val)) =
    ∑ j : H.toHistory.StageInterval first last, (H.extendHorizon u (ht.trans_le htu).le (G.closedPrefix u (H.time_le_horizon.trans_lt (ht.trans_le htu)) hus) hinit).toHistory.stageRegularizedAction j.val T (α j)
      ((H.extendHorizon u (ht.trans_le htu).le (G.closedPrefix u (H.time_le_horizon.trans_lt (ht.trans_le htu)) hus) hinit).toHistory.regularizedStageStart T a j.val) ((H.extendHorizon u (ht.trans_le htu).le (G.closedPrefix u (H.time_le_horizon.trans_lt (ht.trans_le htu)) hus) hinit).toHistory.regularizedStageEnd T b j.val) := by
  apply Finset.sum_congr rfl
  intro j _
  exact (incoming_prefix_stageRegularizedAction_eq H G hinit ht htu hus j.val T (α j) _ _).trans
    (congrArg₂ ((H.extendHorizon u (ht.trans_le htu).le (G.closedPrefix u (H.time_le_horizon.trans_lt (ht.trans_le htu)) hus) hinit).toHistory.stageRegularizedAction j.val T (α j))
      (incoming_prefix_regularizedStageStart_eq H G hinit ht htu hus T a hclock j.val)
      (incoming_prefix_regularizedStageEnd_eq H G hinit ht htu hus T b j.val))

private theorem incoming_prefix_regularizedExtendedAction_eq
    (first last : Fin (H.eventCount + 1)) (T B a b : ℝ) (hclock : T - a ^ 2 ≤ t)
    (α : (j : H.toHistory.StageInterval first last) → ℝ → (H.stage j.val).Carrier) :
    (H.extendHorizon t ht.le (G.closedPrefix t (H.time_le_horizon.trans_lt ht) (htu.trans_lt hus)) hinit).toHistory.regularizedExtendedAction first last T B a b α =
      (H.extendHorizon u (ht.trans_le htu).le (G.closedPrefix u (H.time_le_horizon.trans_lt (ht.trans_le htu)) hus) hinit).toHistory.regularizedExtendedAction first last T B a b α := by
  apply Finset.sum_congr rfl
  intro j _
  exact (incoming_prefix_stageRegularizedExtendedAction_eq H G hinit ht htu hus j.val T B (α j) _ _).trans
    (congrArg₂ ((H.extendHorizon u (ht.trans_le htu).le (G.closedPrefix u (H.time_le_horizon.trans_lt (ht.trans_le htu)) hus) hinit).toHistory.stageRegularizedExtendedAction j.val T B (α j))
      (incoming_prefix_regularizedStageStart_eq H G hinit ht htu hus T a hclock j.val)
      (incoming_prefix_regularizedStageEnd_eq H G hinit ht htu hus T b j.val))

theorem regularizedC1ActionValues_closedPrefixes_eq
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T a b : ℝ} (hclock : T - a ^ 2 ≤ t)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) :
    (H.extendHorizon t ht.le (G.closedPrefix t (H.time_le_horizon.trans_lt ht) (htu.trans_lt hus)) hinit).toHistory.regularizedC1ActionValues first last hle T a b p q =
      (H.extendHorizon u (ht.trans_le htu).le (G.closedPrefix u (H.time_le_horizon.trans_lt (ht.trans_le htu)) hus) hinit).toHistory.regularizedC1ActionValues first last hle T a b p q := by
  ext value
  constructor
  · rintro ⟨ha', hab', hupper, hlower, α, hα, hint, hstart, hend, hnode, hsum⟩
    have hlow : T - b ^ 2 ≤ t := (sub_le_sub_left (pow_le_pow_left₀ ha' hab' 2) T).trans hclock
    refine ⟨ha', hab', (incoming_prefix_stage_upper_eq H G hinit ht htu hus last hclock).mp hupper,
      (incoming_prefix_stageDomain_eq H G hinit ht htu hus first hlow).mp hlower,
      α, hα, ?_, hstart, hend, hnode, ?_⟩
    · intro j
      exact (incoming_prefix_integrability_eq H G hinit ht htu hus j.val T a b hclock (α j)).mp (hint j)
    · exact (incoming_prefix_sum_action_eq H G hinit ht htu hus first last T a b hclock α).symm.trans hsum
  · rintro ⟨ha', hab', hupper, hlower, α, hα, hint, hstart, hend, hnode, hsum⟩
    have hlow : T - b ^ 2 ≤ t := (sub_le_sub_left (pow_le_pow_left₀ ha' hab' 2) T).trans hclock
    refine ⟨ha', hab', (incoming_prefix_stage_upper_eq H G hinit ht htu hus last hclock).mpr hupper,
      (incoming_prefix_stageDomain_eq H G hinit ht htu hus first hlow).mpr hlower,
      α, hα, ?_, hstart, hend, hnode, ?_⟩
    · intro j
      exact (incoming_prefix_integrability_eq H G hinit ht htu hus j.val T a b hclock (α j)).mpr (hint j)
    · exact (incoming_prefix_sum_action_eq H G hinit ht htu hus first last T a b hclock α).trans hsum

theorem regularizedActionValues_closedPrefixes_eq
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B a b : ℝ} (hclock : T - a ^ 2 ≤ t)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) :
    (H.extendHorizon t ht.le (G.closedPrefix t (H.time_le_horizon.trans_lt ht) (htu.trans_lt hus)) hinit).toHistory.regularizedActionValues first last hle T B a b p q =
      (H.extendHorizon u (ht.trans_le htu).le (G.closedPrefix u (H.time_le_horizon.trans_lt (ht.trans_le htu)) hus) hinit).toHistory.regularizedActionValues first last hle T B a b p q := by
  ext value
  constructor
  · rintro ⟨ha', hab', hupper, hlower, α, hα, hstart, hend, hnode, hsum⟩
    have hlow : T - b ^ 2 ≤ t := (sub_le_sub_left (pow_le_pow_left₀ ha' hab' 2) T).trans hclock
    refine ⟨ha', hab', (incoming_prefix_stage_upper_eq H G hinit ht htu hus last hclock).mp hupper,
      (incoming_prefix_stageDomain_eq H G hinit ht htu hus first hlow).mp hlower,
      α, ?_, hstart, hend, hnode, ?_⟩
    · intro j
      exact (incoming_prefix_absolutelyContinuous_eq H G hinit ht htu hus j.val T a b hclock (α j)).mp (hα j)
    · exact (incoming_prefix_regularizedExtendedAction_eq H G hinit ht htu hus first last T B a b hclock α).symm.trans hsum
  · rintro ⟨ha', hab', hupper, hlower, α, hα, hstart, hend, hnode, hsum⟩
    have hlow : T - b ^ 2 ≤ t := (sub_le_sub_left (pow_le_pow_left₀ ha' hab' 2) T).trans hclock
    refine ⟨ha', hab', (incoming_prefix_stage_upper_eq H G hinit ht htu hus last hclock).mpr hupper,
      (incoming_prefix_stageDomain_eq H G hinit ht htu hus first hlow).mpr hlower,
      α, ?_, hstart, hend, hnode, ?_⟩
    · intro j
      exact (incoming_prefix_absolutelyContinuous_eq H G hinit ht htu hus j.val T a b hclock (α j)).mpr (hα j)
    · exact (incoming_prefix_regularizedExtendedAction_eq H G hinit ht htu hus first last T B a b hclock α).trans hsum

theorem regularizedC1Cost_closedPrefixes_eq
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T a b : ℝ} (hclock : T - a ^ 2 ≤ t)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) :
    (H.extendHorizon t ht.le (G.closedPrefix t (H.time_le_horizon.trans_lt ht) (htu.trans_lt hus)) hinit).toHistory.regularizedC1Cost first last hle T a b p q =
      (H.extendHorizon u (ht.trans_le htu).le (G.closedPrefix u (H.time_le_horizon.trans_lt (ht.trans_le htu)) hus) hinit).toHistory.regularizedC1Cost first last hle T a b p q := by
  exact congrArg (fun V : Set ℝ => sInf ((fun x : ℝ => (x : WithTop ℝ)) '' V))
    (regularizedC1ActionValues_closedPrefixes_eq H G hinit ht htu hus first last hle hclock p q)

theorem regularizedCost_closedPrefixes_eq
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B a b : ℝ} (hclock : T - a ^ 2 ≤ t)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) :
    (H.extendHorizon t ht.le (G.closedPrefix t (H.time_le_horizon.trans_lt ht) (htu.trans_lt hus)) hinit).toHistory.regularizedCost first last hle T B a b p q =
      (H.extendHorizon u (ht.trans_le htu).le (G.closedPrefix u (H.time_le_horizon.trans_lt (ht.trans_le htu)) hus) hinit).toHistory.regularizedCost first last hle T B a b p q := by
  exact congrArg sInf
    (regularizedActionValues_closedPrefixes_eq H G hinit ht htu hus first last hle hclock p q)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

end
