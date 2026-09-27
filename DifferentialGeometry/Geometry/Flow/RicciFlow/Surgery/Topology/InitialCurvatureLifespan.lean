import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingCurvatureLifespan
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.History
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalNorm

noncomputable section
open Set DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

private theorem initial_curvature_bound_of_identification
    {P : OrientedThreeStage.{u}} {g : P.Metric} {H : ObservedHistory.{u}}
    (A : InitialIdentification P g H) {K : ℝ}
    (hbound : ∀ x : P.Carrier, normSq0S g x 4 (metricRm04At g x) ≤ K) :
    ∀ x : (H.stage 0).Carrier,
      normSq0S (H.initialMetric 0) x 4 (metricRm04At (H.initialMetric 0) x) ≤ K := by
  have hg : localPullMetric (H.initialMetric 0) A.map A.map.isLocalDiffeomorph = g := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [localPullMetric_inner]
    exact A.metric_eq x v w
  intro y
  obtain ⟨x,rfl⟩ := A.map.surjective y
  have heq := normSq0S_metricRm04At_localPullMetric (H.initialMetric 0) A.map
    A.map.isLocalDiffeomorph x
  rw [hg] at heq
  exact heq ▸ hbound x

theorem exists_pos_le_singular_incoming_time_of_initialIdentification
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ a : ℝ, 0 < a ∧
      ∀ (H : ObservedHistory.{u}), InitialIdentification P g H →
      (∀ j : Fin H.eventCount, (H.event j).incoming.SingularEndpoint) →
      ∀ (last : Fin (H.eventCount + 1)) (s : ℝ)
        (G : (H.stage last).IncomingSlab (H.time last) s),
      G.flow.base.metric (H.time last) = H.initialMetric last →
      G.SingularEndpoint → a ≤ s := by
  obtain ⟨K, hK, hbound⟩ := exists_rm04_bound g
  let Q := Real.sqrt K + 1
  have hQ : 0 < Q := by dsimp [Q]; positivity
  refine ⟨1/(2592*Q), by positivity, ?_⟩
  intro H A hsing last s G hinit hG
  have hzero := initial_curvature_bound_of_identification A hbound
  have hzero' (x : (H.stage 0).Carrier) :
      Real.sqrt (normSq0S (H.initialMetric 0) x 4 (metricRm04At (H.initialMetric 0) x)) ≤ Q := by
    exact (Real.sqrt_le_sqrt (hzero x)).trans (by dsimp [Q]; linarith)
  cases last using Fin.cases with
  | zero =>
    have hh := G.one_div_le_endpoint_sub_of_initial_curvature_bound hG hQ
      (fun x => by
        change Real.sqrt (normSq0S (G.flow.base.metric (H.time 0)) x 4
          (metricRm04At (G.flow.base.metric (H.time 0)) x)) ≤ Q
        rw [hinit]
        exact hzero' x)
    simpa only [H.time_zero, sub_zero] using hh
  | succ i =>
    let j : Fin H.eventCount := ⟨0, Nat.zero_lt_of_lt i.isLt⟩
    have hj : j.castSucc = 0 := Fin.ext rfl
    have hh := (H.event j).incoming.one_div_le_endpoint_sub_of_initial_curvature_bound
      (hsing j) hQ (fun x => by
        change Real.sqrt (normSq0S ((H.event j).incoming.flow.base.metric (H.time j.castSucc)) x 4
          (metricRm04At ((H.event j).incoming.flow.base.metric (H.time j.castSucc)) x)) ≤ Q
        rw [H.event_initial j]
        have hz : ∀ y : (H.stage j.castSucc).Carrier,
            Real.sqrt (normSq0S (H.initialMetric j.castSucc) y 4
              (metricRm04At (H.initialMetric j.castSucc) y)) ≤ Q := by
          exact hj.symm ▸ hzero'
        exact hz x)
    have hjtime : H.time j.castSucc = 0 := hj ▸ H.time_zero
    rw [hjtime, sub_zero] at hh
    exact hh.trans ((H.time_strictMono.monotone
      (show j.succ ≤ i.succ from Nat.succ_le_succ (Nat.zero_le _))).trans G.lt.le)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
