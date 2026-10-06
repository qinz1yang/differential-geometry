import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HistoryPathStep_CX2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HistoryPathInit_CX2

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
  DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- Finite backward induction across all actual events, with a single
cumulative path-length budget. -/
theorem bounded_trace_of_seed_path_CX2 (H : ObservedHistory.{u})
    {a t : Icc (0 : ℝ) H.horizon} (hat : a < t)
    (hregular : H.time (H.activeStage t) < t.val)
    {y p : (H.stageAt t).Carrier}
    (Y : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat.le) y)
    {r B : ℝ} (hr : 0 < r) (hB : 0 ≤ B)
    (hy : y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r)
    (hroom : pathBudget_CX2 B r t a < 20 * r)
    (hbound : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
        (Y.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) (20 * r),
      Real.sqrt (normSq0S (H.stageMetric (H.activeStage v) v) q 4
        (metricRm04At (H.stageMetric (H.activeStage v) v) q)) ≤ B)
    (hprotect : ∀ (i : Fin H.eventCount), H.activeStage a ≤ i.castSucc → i.succ ≤ H.activeStage t →
      ∀ γ : ℝ → (H.stage i.succ).Carrier,
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ →
      (∀ z, γ z = γ (projIcc (0 : ℝ) 1 zero_le_one z)) →
      (∀ z ∈ Icc (0 : ℝ) 1,
        Real.sqrt (normSq0S (H.event i).outputMetric (γ z) 4
          (metricRm04At (H.event i).outputMetric (γ z))) ≤ B) →
      ∀ q : (H.event i).incoming.terminalRegularOpen,
        (H.event i).RegularCrossing q.val (γ 0) →
      ∃ η : ℝ → (H.event i).incoming.terminalRegularOpen,
        ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η ∧
        (∀ z, η z = η (projIcc (0 : ℝ) 1 zero_le_one z)) ∧ η 0 = q ∧
        (∀ z ∈ Icc (0 : ℝ) 1, (H.event i).RegularCrossing (η z).val (γ z)) ∧
        metricPathELength (H.event i).terminal.metric η 0 1 =
          metricPathELength (H.event i).outputMetric γ 0 1 ∧
        ∀ z ∈ Icc (0 : ℝ) 1,
          Real.sqrt (normSq0S (H.event i).terminal.metric (η z) 4
            (metricRm04At (H.event i).terminal.metric (η z))) ≤ B)
    (x : (H.stageAt t).Carrier) (hx : x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (2 * r)) :
    ∃ A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat.le) x,
      A.isRmBoundedBy (hat := hat.le) B := by
  have hfinish (j : Fin (H.eventCount + 1)) :
      PathState_CX2 H a t hat.le Y x B r j →
      ∃ A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat.le) x,
        A.isRmBoundedBy (hat := hat.le) B := by
    induction j using Fin.inductionOn with
    | zero =>
      intro S
      have hj : (0 : Fin (H.eventCount + 1)) = H.activeStage a :=
        le_antisymm (Fin.zero_le _) S.lower
      let S' : PathState_CX2 H a t hat.le Y x B r (H.activeStage a) :=
        cast (congrArg (PathState_CX2 H a t hat.le Y x B r) hj) S
      exact ⟨S'.trace, pathState_finish_CX2 hr hB hroom hbound S'⟩
    | succ i ih =>
      intro S
      by_cases hj : i.succ = H.activeStage a
      · let S' : PathState_CX2 H a t hat.le Y x B r (H.activeStage a) :=
          cast (congrArg (PathState_CX2 H a t hat.le Y x B r) hj) S
        exact ⟨S'.trace, pathState_finish_CX2 hr hB hroom hbound S'⟩
      · have hai : H.activeStage a ≤ i.castSucc := by
          apply Fin.le_iff_val_le_val.mpr
          change (H.activeStage a).val ≤ i.val
          have hlo : (H.activeStage a).val ≤ i.val + 1 := S.lower
          have hne : i.val + 1 ≠ (H.activeStage a).val := fun h => hj (Fin.ext h)
          omega
        obtain ⟨S'⟩ := pathState_prepend_CX2 hr hB hroom hbound i hai S (hprotect i hai S.upper)
        exact ih S'
  obtain ⟨γ, hγ0, hγ1, hγ, hclip, hlen⟩ := exists_global_seed_path_CX2 (H.stageAt t)
    (H.stageMetric (H.activeStage t) t) hr hy hx
  have htop : ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) y (20 * r),
      Real.sqrt (normSq0S (H.stageMetric (H.activeStage t) t) q 4
        (metricRm04At (H.stageMetric (H.activeStage t) t) q)) ≤ B := by
    have h := hbound t hat.le le_rfl
    rw [Y.endpoint_eq] at h
    exact h
  obtain ⟨S⟩ := pathState_initial_CX2 H hat hregular Y hr htop γ hγ0 hγ1 hγ hclip hlen.le
  exact hfinish _ S

end GC.LongTime.Ch12
