import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedSlabProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompactUniformExistence

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem exists_closedSlab_control_time_zero (P : OrientedThreeStage.{u})
    (g : P.Metric) (K : ℝ)
    (hK : ∀ x : P.Carrier, Real.sqrt (normSq0S g x 4 (metricRm04 g x)) ≤ K) :
    ∃ G : P.ClosedSlab 0 (compactCurvatureControlTime 3 K),
      G.flow.base.metric 0 = g ∧
      ∀ t ∈ Icc 0 (compactCurvatureControlTime 3 K), ∀ x : P.Carrier,
        Real.sqrt (normSq0S (G.flow.base.metric t) x 4 (metricRm04 (G.flow.base.metric t) x)) ≤
          Real.sqrt (2 * K ^ 2 + 1) := by
  obtain ⟨τ, hτ, ⟨F⟩⟩ := exists_compact_flow_beyond_control_time g (by simp : Module.finrank ℝ ThreeSpace = 3) K hK
  have hT : 0 < compactCurvatureControlTime 3 K := compactCurvatureControlTime_pos 3 K
  have hτ' : compactCurvatureControlTime 3 K < τ := by simpa only [finrank_euclideanSpace_fin] using hτ
  have hjoint := metricCLMSection_jointContMDiffOn_of_chartGram_on
    F.S.family.metric (Ico 0 τ) F.joint
  let G := OrientedThreeStage.ClosedSlab.ofClosedOpen P F.time_pos F.S F.isSolution hjoint hT hτ'
  refine ⟨G, F.start, ?_⟩
  have hsub : Icc 0 (compactCurvatureControlTime 3 K) ⊆ (RealTimeInterval.closedOpen 0 τ F.time_pos).carrier :=
    fun t ht => ⟨ht.1, ht.2.trans_lt hτ'⟩
  exact curvature_bound_from_initial_compact (compactCurvatureControlTime 3 K) hT.le K
    (by simp) _ F.S F.isSolution hsub
    (fun t ht => ⟨ht.1, ht.2.trans hτ'⟩)
    (fun x i j => (F.joint x i j).mono (Set.prod_mono hsub subset_rfl))
    (fun x => by
      have hstart : F.S.base.metric 0 = g := F.start
      rw [hstart]
      exact hK x)

theorem exists_closedSlab_of_curvature_bound (P : OrientedThreeStage.{u})
    (g : P.Metric) (K : ℝ)
    (hK : ∀ x : P.Carrier, Real.sqrt (normSq0S g x 4 (metricRm04 g x)) ≤ K) (a : ℝ) :
    ∃ G : P.ClosedSlab a (a + compactCurvatureControlTime 3 K),
      G.flow.base.metric a = g ∧
      ∀ t ∈ Icc a (a + compactCurvatureControlTime 3 K), ∀ x : P.Carrier,
        Real.sqrt (normSq0S (G.flow.base.metric t) x 4 (metricRm04 (G.flow.base.metric t) x)) ≤
          Real.sqrt (2 * K ^ 2 + 1) := by
  obtain ⟨G, hG, hbound⟩ := exists_closedSlab_control_time_zero P g K hK
  have h : ∃ H : P.ClosedSlab (0 + a) (compactCurvatureControlTime 3 K + a),
      H.flow.base.metric a = g ∧
      ∀ t ∈ Icc a (a + compactCurvatureControlTime 3 K), ∀ x : P.Carrier,
        Real.sqrt (normSq0S (H.flow.base.metric t) x 4 (metricRm04 (H.flow.base.metric t) x)) ≤
          Real.sqrt (2 * K ^ 2 + 1) := by
    refine ⟨G.timeTranslate a, ?_, ?_⟩
    · rw [OrientedThreeStage.ClosedSlab.timeTranslate_metric, sub_self]
      exact hG
    · intro t ht x
      rw [OrientedThreeStage.ClosedSlab.timeTranslate_metric]
      exact hbound (t - a) ⟨sub_nonneg.mpr ht.1, by linarith [ht.2]⟩ x
  rw [zero_add, add_comm (compactCurvatureControlTime 3 K) a] at h
  exact h

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ}

theorem exists_closedSlab_restart_of_curvature_bound (E : MetricCutCapEvent P Q a s)
    (K : ℝ) (hK : ∀ x : Q.Carrier,
      Real.sqrt (normSq0S E.outputMetric x 4 (metricRm04 E.outputMetric x)) ≤ K) :
    ∃ G : Q.ClosedSlab s (s + compactCurvatureControlTime 3 K),
      G.flow.base.metric s = E.outputMetric ∧
      ∀ t ∈ Icc s (s + compactCurvatureControlTime 3 K), ∀ x : Q.Carrier,
        Real.sqrt (normSq0S (G.flow.base.metric t) x 4 (metricRm04 (G.flow.base.metric t) x)) ≤
          Real.sqrt (2 * K ^ 2 + 1) :=
  exists_closedSlab_of_curvature_bound Q E.outputMetric K hK s

end MetricCutCapEvent
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
