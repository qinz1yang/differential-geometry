import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HistoryPathEstimates_CX2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.GlobalSurgeryPath_CX2

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
  DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- Concrete intermediate data in the finite backward path induction. The
current incoming slab and its terminal curve are supplied as actual data;
only the already traversed part of the endpoint trace is bounded here.
Constructors are provided by the initial closed slab and by one surgery step. -/
structure PathState_CX2 (H : ObservedHistory.{u}) (a t : Icc (0 : ℝ) H.horizon) (hat : a ≤ t)
    {y : (H.stageAt t).Carrier}
    (Y : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) y)
    (x : (H.stageAt t).Carrier) (B r : ℝ) (j : Fin (H.eventCount + 1)) where
  lower : H.activeStage a ≤ j
  upper : j ≤ H.activeStage t
  top : ℝ
  after_lower : a.val < top
  before_top : top ≤ t.val
  slab : (H.stage j).IncomingSlab (H.time j) top
  terminal : slab.TerminalLimitMetric
  active : ∀ v : Icc (0 : ℝ) H.horizon, H.time j ≤ v.val → v.val < top → H.activeStage v = j
  metric : ∀ v ∈ Ico (H.time j) top, H.stageMetric j v = slab.flow.base.metric v
  trace : BackwardPointTrace H j (H.activeStage t) upper x
  curve : ℝ → slab.terminalRegularOpen
  smooth : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 curve
  clip : ∀ z, curve z = curve (projIcc (0 : ℝ) 1 zero_le_one z)
  center : (curve 0).val = Y.point j lower upper
  endpoint : (curve 1).val = trace.point j le_rfl upper
  length : metricPathELength terminal.metric curve 0 1 ≤ ENNReal.ofReal (pathBudget_CX2 B r t top)
  terminal_bound : ∀ z ∈ Icc (0 : ℝ) 1,
    Real.sqrt (normSq0S terminal.metric (curve z) 4 (metricRm04At terminal.metric (curve z))) ≤ B
  above : ∀ (v : Icc (0 : ℝ) H.horizon) (_ : a ≤ v) (hvt : v ≤ t) (htop : top ≤ v.val),
    normSq0S (H.stageMetric (H.activeStage v) v)
      (trace.point (H.activeStage v) (H.le_activeStage v j (slab.lt.le.trans htop))
        (H.activeStage_mono hvt)) 4
      (metricRm04At (H.stageMetric (H.activeStage v) v)
        (trace.point (H.activeStage v) (H.le_activeStage v j (slab.lt.le.trans htop))
          (H.activeStage_mono hvt))) ≤ B ^ 2
  seams : ∀ (i : Fin H.eventCount) (hf : j ≤ i.castSucc) (hl : i.succ ≤ H.activeStage t),
    let q : (H.event i).incoming.terminalRegularOpen :=
      ⟨trace.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl),
        (trace.crossing i hf hl).mem_terminalRegularRegion (H.event i)⟩
    normSq0S (H.event i).terminal.metric q 4 (metricRm04At (H.event i).terminal.metric q) ≤ B ^ 2

variable {H : ObservedHistory.{u}} {a t : Icc (0 : ℝ) H.horizon} {hat : a ≤ t}
  {y : (H.stageAt t).Carrier}
  {Y : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) y}
  {x : (H.stageAt t).Carrier} {B r : ℝ}

/-- The state at the initial index supplies the entire bounded trace. -/
theorem pathState_finish_CX2 (hr : 0 < r) (hB : 0 ≤ B)
    (hroom : pathBudget_CX2 B r t a < 20 * r)
    (hbound : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
        (Y.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) (20 * r),
      Real.sqrt (normSq0S (H.stageMetric (H.activeStage v) v) q 4
        (metricRm04At (H.stageMetric (H.activeStage v) v) q)) ≤ B)
    (S : PathState_CX2 H a t hat Y x B r (H.activeStage a)) :
    S.trace.isRmBoundedBy (hat := hat) B := by
  have he := history_path_slab_estimate_CX2 H (hat := hat) Y hr hB hroom hbound _ S.lower S.upper
    S.after_lower S.before_top S.slab S.terminal S.active S.metric S.curve S.smooth
    S.center S.length S.terminal_bound
  constructor
  · intro v hav hvt
    by_cases htop : S.top ≤ v.val
    · exact S.above v hav hvt htop
    · have hvtop : v.val < S.top := lt_of_not_ge htop
      have hvj : H.time (H.activeStage a) ≤ v.val := (H.activeStage_time_le a).trans hav
      have hv : v.val ∈ Ico (max a.val (H.time (H.activeStage a))) S.top :=
        ⟨max_le hav hvj, hvtop⟩
      have hcurv := (he v hv).2 1 ⟨zero_le_one, le_rfl⟩
      have hi : H.activeStage v = H.activeStage a := S.active v hvj hvtop
      change Real.sqrt (normSq0S (S.slab.flow.base.metric v) (S.curve 1).val 4
        (metricRm04At (S.slab.flow.base.metric v) (S.curve 1).val)) ≤ B at hcurv
      rw [← S.metric v ⟨hvj, hvtop⟩, S.endpoint] at hcurv
      have heq := trace_rmNormSq_at_stage_CX2 H S.trace hi
        (H.activeStage_mono hav) (H.activeStage_mono hvt) le_rfl S.upper v
      exact heq.trans_le (Real.sqrt_le_iff.mp hcurv).2
  · exact S.seams

end GC.LongTime.Ch12
