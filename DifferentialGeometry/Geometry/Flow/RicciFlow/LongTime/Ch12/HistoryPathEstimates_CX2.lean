import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TerminalPath_CX2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HistoryPathAlgebra_CX2

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
  DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- One complete incoming slab, including a singular terminal metric, with
its share of the cumulative length estimate from the final observation time. -/
theorem history_path_slab_estimate_CX2 (H : ObservedHistory.{u})
    {a t : Icc (0 : ℝ) H.horizon} {hat : a ≤ t} {y : (H.stageAt t).Carrier}
    (Y : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) y)
    {r B : ℝ} (hr : 0 < r) (hB : 0 ≤ B)
    (hroom : pathBudget_CX2 B r t a < 20 * r)
    (hbound : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
        (Y.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) (20 * r),
      Real.sqrt (normSq0S (H.stageMetric (H.activeStage v) v) q 4
        (metricRm04At (H.stageMetric (H.activeStage v) v) q)) ≤ B)
    (j : Fin (H.eventCount + 1)) (haj : H.activeStage a ≤ j) (hjt : j ≤ H.activeStage t)
    {b : ℝ} (hab : a.val < b) (hbt : b ≤ t.val)
    (G : (H.stage j).IncomingSlab (H.time j) b) (L : G.TerminalLimitMetric)
    (hactive : ∀ v : Icc (0 : ℝ) H.horizon, H.time j ≤ v.val → v.val < b → H.activeStage v = j)
    (hmetric : ∀ v ∈ Ico (H.time j) b, H.stageMetric j v = G.flow.base.metric v)
    (γ : ℝ → G.terminalRegularOpen) (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ)
    (hγ0 : (γ 0).val = Y.point j haj hjt)
    (hlen : metricPathELength L.metric γ 0 1 ≤ ENNReal.ofReal (pathBudget_CX2 B r t b))
    (hterminal : ∀ z ∈ Icc (0 : ℝ) 1,
      Real.sqrt (normSq0S L.metric (γ z) 4 (metricRm04At L.metric (γ z))) ≤ B) :
    ∀ v ∈ Ico (max a.val (H.time j)) b,
      metricPathELength (G.flow.base.metric v)
        ((Subtype.val : G.terminalRegularOpen → (H.stage j).Carrier) ∘ γ) 0 1 ≤
          ENNReal.ofReal (pathBudget_CX2 B r t v) ∧
      ∀ z ∈ Icc (0 : ℝ) 1,
        Real.sqrt (normSq0S (G.flow.base.metric v) (γ z).val 4 (G.flow.base.rm04 v (γ z).val)) ≤ B := by
  let c := max a.val (H.time j)
  have hac : H.time j ≤ c := le_max_right _ _
  have hcb : c < b := max_lt hab G.lt
  have hbudget : Real.exp (9 * B * (b - c)) * pathBudget_CX2 B r t b < 20 * r := by
    rw [pathBudget_comp_CX2]
    exact (pathBudget_antitone_CX2 hB hr.le (le_max_left _ _)).trans_lt hroom
  have hlocal : ∀ v ∈ Ico c b,
      ∀ q ∈ riemannianBallOf (G.flow.base.metric v) (γ 0).val (20 * r),
        Real.sqrt (normSq0S (G.flow.base.metric v) q 4 (G.flow.base.rm04 v q)) ≤ B := by
    intro v hv q hq
    have hvj : H.time j ≤ v := hac.trans hv.1
    let v' : Icc (0 : ℝ) H.horizon :=
      ⟨v, (H.time_nonneg j).trans hvj, hv.2.le.trans (hbt.trans t.property.2)⟩
    have hav : a ≤ v' := show a.val ≤ v from (le_max_left a.val (H.time j)).trans hv.1
    have hvt : v' ≤ t := hv.2.le.trans hbt
    have hj : H.activeStage v' = j := hactive v' hvj hv.2
    have hq' : q ∈ riemannianBallOf (H.stageMetric j v') (Y.point j haj hjt) (20 * r) := by
      rw [hmetric v ⟨hvj, hv.2⟩, ← hγ0]
      exact hq
    have hb := seed_ball_bound_at_stage_CX2 H (hat := hat) Y hbound v' hav hvt j hj haj hjt q hq'
    rw [hmetric v ⟨hvj, hv.2⟩] at hb
    exact hb
  have hresult := incoming_path_estimate_CX2 G L hac hcb.le hB
    (pathBudget_pos_CX2 B t b hr).le γ hγ hlen hbudget hterminal hlocal
  intro v hv
  obtain ⟨hL, hcurv⟩ := hresult v hv
  refine ⟨?_, hcurv⟩
  calc
    metricPathELength (G.flow.base.metric v) (Subtype.val ∘ γ) 0 1 ≤
        ENNReal.ofReal (Real.exp (9 * B * (b - v))) * metricPathELength L.metric γ 0 1 := hL
    _ ≤ ENNReal.ofReal (Real.exp (9 * B * (b - v))) *
        ENNReal.ofReal (pathBudget_CX2 B r t b) := mul_le_mul' le_rfl hlen
    _ = ENNReal.ofReal (pathBudget_CX2 B r t v) := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, pathBudget_comp_CX2]

end GC.LongTime.Ch12
