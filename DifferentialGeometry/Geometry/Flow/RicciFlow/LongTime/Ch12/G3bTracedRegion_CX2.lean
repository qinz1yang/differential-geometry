import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HistoryPathInduction_CX2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.WindowConstants_CX2

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- G3b on an actual history: moving seed-centred curvature bounds and the
records' thresholds produce all traces in the doubled final test ball. -/
theorem record_seed_tracedRegion_CX2 (H : ObservedHistory.{u}) (params : CutoffParameters)
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i params)
    {a t : Icc (0 : ℝ) H.horizon} {τ r K Λ : ℝ}
    (hτ : 0 < τ) (hr : 0 < r) (hK : 0 < K) (hΛ : 1 ≤ Λ)
    (hKΛ : 2 * (9 * K) < Λ ^ 2) (hexp : Real.exp (9 * K * τ) < 2)
    (ha : a.val = t.val - τ * r ^ 2) (hat : a ≤ t)
    (hregular : H.time (H.activeStage t) < t.val)
    {p y : (H.stageAt t).Carrier}
    (hy : y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r)
    (Y : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) y)
    (hbound : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
        (Y.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) (20 * r),
      Real.sqrt (normSq0S (H.stageMetric (H.activeStage v) v) q 4
        (metricRm04At (H.stageMetric (H.activeStage v) v) q)) ≤ K / r ^ 2)
    (hδ : ∀ (i : Fin H.eventCount), H.activeStage a ≤ i.castSucc → i.succ ≤ H.activeStage t →
      ∀ j, (records i).delta j ≤ 1 / 8646)
    (hnom : ∀ (i : Fin H.eventCount), H.activeStage a ≤ i.castSucc → i.succ ≤ H.activeStage t →
      ∀ h, Λ * (records i).nominalRadius h ≤ r) :
    H.isTracedRegion t p (2 * r) (τ * r ^ 2) (K / r ^ 2) := by
  have hdepth : 0 < τ * r ^ 2 := by positivity
  have hat' : a < t := show a.val < t.val from by rw [ha]; linarith
  have hroom : pathBudget_CX2 (K / r ^ 2) r t a < 20 * r := by
    have he : 9 * (K / r ^ 2) * (t.val - a.val) = 9 * K * τ := by
      rw [ha]
      field_simp
      ring
    unfold pathBudget_CX2
    rw [he]
    exact (six_radius_length_CX2 hr hexp).1.trans (six_radius_length_CX2 hr hexp).2
  refine ⟨by positivity, hdepth, a, hat, ha, ?_⟩
  intro x hx
  apply bounded_trace_of_seed_path_CX2 H hat' hregular Y hr (by positivity) hy hroom hbound ?_ x hx
  intro i hf hl γ hγ hclip hRm q hcross
  exact lift_global_outgoing_path_CX2 (records i) hr hΛ hKΛ (hδ i hf hl) (hnom i hf hl)
    γ hγ hclip hRm q hcross

end GC.LongTime.Ch12
