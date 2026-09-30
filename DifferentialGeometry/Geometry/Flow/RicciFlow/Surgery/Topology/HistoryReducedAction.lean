import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.MetricAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.PDE.RicciFlow.Perelman

universe u

variable (H : ObservedHistory.{u})

theorem exists_stage_reducedAction_minimizer
    (t : Icc (0 : ℝ) H.horizon) (ht : H.time (H.activeStage t) < t.val)
    (T τ : ℝ) (hτ : 0 < τ)
    (hleft : H.time (H.activeStage t) < T - τ) (hright : T < t.val)
    (x y : (H.stage (H.activeStage t)).Carrier)
    (α₀ : ℝ → (H.stage (H.activeStage t)).Carrier)
    (hα₀ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α₀)
    (h₀ : α₀ 0 = x) (h₁ : α₀ (Real.sqrt τ) = y) :
    ∃ α : ℝ → (H.stage (H.activeStage t)).Carrier,
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ α ∧ α 0 = x ∧ α (Real.sqrt τ) = y ∧
      isRegularizedAdmissible (squareRootReparametrization α) ∧
      reducedAction (H.stageMetric (H.activeStage t)) T τ (squareRootReparametrization α) =
        reducedLength (H.stageMetric (H.activeStage t)) T isRegularizedAdmissible x τ y := by
  have hreg : Icc (T - τ) T ⊆
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closed
        (H.time (H.activeStage t)) t.val ht.le).regular :=
    fun s hs => ⟨hleft.trans_le hs.1,hs.2.trans_lt hright⟩
  obtain ⟨α,hα,h0,h1,hadm,hact⟩ := exists_reducedAction_minimizer_of_regular_interval
    (H.closedPrefixAt t ht).flow (H.closedPrefixAt t ht).equation T τ hτ hreg x y α₀ hα₀ h₀ h₁
  have hmetric : (H.closedPrefixAt t ht).flow.base.metric = H.stageMetric (H.activeStage t) :=
    funext (H.closedPrefixAt_metric t ht)
  exact ⟨α,hα,h0,h1,hadm,hmetric ▸ hact⟩

theorem exists_stage_reducedAction_minimizer_at_scale
    (t : Icc (0 : ℝ) H.horizon) (ht : H.time (H.activeStage t) < t.val)
    (T r : ℝ) (hr : 0 < r)
    (hleft : H.time (H.activeStage t) < T - r ^ 2) (hright : T < t.val)
    (x y : (H.stage (H.activeStage t)).Carrier)
    (α₀ : ℝ → (H.stage (H.activeStage t)).Carrier)
    (hα₀ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α₀)
    (h₀ : α₀ 0 = x) (h₁ : α₀ r = y) :
    ∃ α : ℝ → (H.stage (H.activeStage t)).Carrier,
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ α ∧ α 0 = x ∧ α r = y ∧
      isRegularizedAdmissible (squareRootReparametrization α) ∧
      reducedAction (H.stageMetric (H.activeStage t)) T (r ^ 2) (squareRootReparametrization α) =
        reducedLength (H.stageMetric (H.activeStage t)) T isRegularizedAdmissible x (r ^ 2) y := by
  simpa only [Real.sqrt_sq hr.le] using H.exists_stage_reducedAction_minimizer
    t ht T (r ^ 2) (sq_pos_of_pos hr) hleft hright x y α₀ hα₀ h₀
    (by simpa only [Real.sqrt_sq hr.le] using h₁)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
