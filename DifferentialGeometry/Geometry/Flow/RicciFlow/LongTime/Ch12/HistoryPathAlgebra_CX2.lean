import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TraceRestriction_CX2

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

/-- One cumulative length budget, indexed by physical time. -/
def pathBudget_CX2 (B r t v : ℝ) : ℝ := 3 * r * Real.exp (9 * B * (t - v))

theorem pathBudget_pos_CX2 (B t v : ℝ) {r : ℝ} (hr : 0 < r) :
    0 < pathBudget_CX2 B r t v := by unfold pathBudget_CX2; positivity

theorem pathBudget_comp_CX2 (B r t b v : ℝ) :
    Real.exp (9 * B * (b - v)) * pathBudget_CX2 B r t b = pathBudget_CX2 B r t v := by
  unfold pathBudget_CX2
  rw [show Real.exp (9 * B * (b - v)) * (3 * r * Real.exp (9 * B * (t - b))) =
    3 * r * (Real.exp (9 * B * (b - v)) * Real.exp (9 * B * (t - b))) by ring,
    ← Real.exp_add]
  congr 2
  ring

theorem pathBudget_antitone_CX2 {B r t v w : ℝ} (hB : 0 ≤ B) (hr : 0 ≤ r) (hvw : v ≤ w) :
    pathBudget_CX2 B r t w ≤ pathBudget_CX2 B r t v := by
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  nlinarith [mul_nonneg hB (sub_nonneg.mpr hvw)]

theorem activeStage_on_event_CX2 (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    (v : Icc (0 : ℝ) H.horizon) (hv : v.val ∈ Ico (H.time i.castSucc) (H.time i.succ)) :
    H.activeStage v = i.castSucc := by
  apply H.activeStage_eq_of_maximal v i.castSucc hv.1
  intro j hj
  by_contra hn
  have hij : i.succ ≤ j := Fin.castSucc_lt_iff_succ_le.mp (lt_of_not_ge hn)
  exact (not_le_of_gt hv.2) ((H.time_strictMono.monotone hij).trans hj)

theorem time_lt_of_activeStage_lt_CX2 (H : ObservedHistory.{u})
    (v : Icc (0 : ℝ) H.horizon) (j : Fin (H.eventCount + 1)) (hj : H.activeStage v < j) :
    v.val < H.time j := by
  by_contra h
  exact (not_le_of_gt hj) (H.le_activeStage v j (le_of_not_gt h))

/-- Reindex a scalar curvature norm at an equal physical stage. -/
theorem trace_rmNormSq_at_stage_CX2 (H : ObservedHistory.{u})
    {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {x : (H.stage last).Carrier}
    (A : BackwardPointTrace H first last hle x) {j k : Fin (H.eventCount + 1)}
    (hjk : j = k) (hf : first ≤ j) (hl : j ≤ last) (hf' : first ≤ k) (hl' : k ≤ last)
    (v : ℝ) :
    normSq0S (H.stageMetric j v) (A.point j hf hl) 4 (metricRm04At (H.stageMetric j v) (A.point j hf hl)) =
      normSq0S (H.stageMetric k v) (A.point k hf' hl') 4
        (metricRm04At (H.stageMetric k v) (A.point k hf' hl')) := by
  subst k
  rfl

/-- Prepending one crossing leaves every later physical point unchanged. -/
theorem prepend_point_tail_CX2 (H : ObservedHistory.{u}) {i : Fin H.eventCount}
    {last : Fin (H.eventCount + 1)} {hle : i.succ ≤ last} {x : (H.stage last).Carrier}
    (A : BackwardPointTrace H i.succ last hle x) (p : (H.stage i.castSucc).Carrier)
    (hc : (H.event i).RegularCrossing p (A.point i.succ le_rfl hle))
    (j : Fin (H.eventCount + 1)) (hj : i.succ ≤ j) (hl : j ≤ last) :
    (A.prepend p hc).point j (i.castSucc_lt_succ.le.trans hj) hl = A.point j hj hl := by
  have hne : j ≠ i.castSucc := ne_of_gt (i.castSucc_lt_succ.trans_le hj)
  simp only [BackwardPointTrace.prepend, dite_eq_right hne]

/-- The moving-ball hypothesis can be used at the fixed carrier of a slab. -/
theorem seed_ball_bound_at_stage_CX2 (H : ObservedHistory.{u})
    {a t : Icc (0 : ℝ) H.horizon} {hat : a ≤ t} {y : (H.stageAt t).Carrier}
    (Y : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) y)
    {r B : ℝ}
    (hbound : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
        (Y.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) (20 * r),
      Real.sqrt (normSq0S (H.stageMetric (H.activeStage v) v) q 4
        (metricRm04At (H.stageMetric (H.activeStage v) v) q)) ≤ B)
    (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t)
    (j : Fin (H.eventCount + 1)) (hj : H.activeStage v = j)
    (hf : H.activeStage a ≤ j) (hl : j ≤ H.activeStage t)
    (q : (H.stage j).Carrier)
    (hq : q ∈ riemannianBallOf (H.stageMetric j v) (Y.point j hf hl) (20 * r)) :
    Real.sqrt (normSq0S (H.stageMetric j v) q 4 (metricRm04At (H.stageMetric j v) q)) ≤ B := by
  subst j
  exact hbound v hav hvt q hq

end GC.LongTime.Ch12
