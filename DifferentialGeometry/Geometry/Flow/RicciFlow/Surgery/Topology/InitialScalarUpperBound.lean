import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySlices
import DifferentialGeometry.Geometry.Curvature.EmbeddingIsometry

noncomputable section

open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- The bound is chosen from the original compact metric before the history and
its initial marking. No outgoing slab is required. -/
theorem exists_scalar_lt_at_initial_metric
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ Q₀ : ℝ, 0 < Q₀ ∧ ∀ H : ObservedHistory.{u}, InitialIdentification P g H →
      ∀ y : (H.stage 0).Carrier, metricScalarAt (H.initialMetric 0) y < Q₀ := by
  obtain ⟨B, hB⟩ := (isCompact_univ.image (metricScalar_smooth g).continuous).bddAbove
  refine ⟨max B 0 + 1, ?_, ?_⟩
  · have hnonneg : 0 ≤ max B 0 := le_max_right _ _
    linarith
  · intro H A y
    let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
    obtain ⟨x, rfl⟩ := A.map.surjective y
    have hscalar := (curvature_of_injective_local_isometry g (H.initialMetric 0) A.map
      A.map.isLocalDiffeomorph A.map.injective
      (fun x v w => (A.metric_eq x v w).symm) x).1
    erw [← hscalar]
    have hx := hB ⟨x, mem_univ x, rfl⟩
    have hmax := le_max_left B 0
    linarith

/-- This is the actual time-zero slice, including a history of horizon zero. -/
theorem exists_scalar_lt_at_time_zero
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ Q₀ : ℝ, 0 < Q₀ ∧ ∀ H : ObservedHistory.{u}, InitialIdentification P g H →
      ∀ t : Icc (0 : ℝ) H.horizon, (t : ℝ) = 0 →
      ∀ x : (H.stageAt t).Carrier,
        metricScalarAt (H.stageMetric (H.activeStage t) t) x < Q₀ := by
  obtain ⟨Q₀, hQ₀, hbound⟩ := exists_scalar_lt_at_initial_metric P g
  refine ⟨Q₀, hQ₀, ?_⟩
  intro H A t ht
  have hact : H.activeStage t = 0 := by
    apply le_antisymm _ (Fin.zero_le _)
    apply H.time_strictMono.le_iff_le.mp
    simpa only [ht, H.time_zero] using H.activeStage_time_le t
  have hmetric : H.stageMetric 0 0 = H.initialMetric 0 := by
    simpa only [H.time_zero] using H.stageMetric_initial 0
  change ∀ x : (H.stage (H.activeStage t)).Carrier,
    metricScalarAt (H.stageMetric (H.activeStage t) t) x < Q₀
  generalize hk : H.activeStage t = k
  have hk0 : k = 0 := hk.symm.trans hact
  clear hk
  subst k
  simpa only [ht, hmetric] using hbound H A

/-- A threshold enlarged by the original initial bound has no high-scalar points
at time zero. The same bound works before every birth threshold and fine history. -/
theorem exists_time_zero_high_threshold_vacuity
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ Q₀ : ℝ, 0 < Q₀ ∧ ∀ (Qbirth : ℝ) (H : ObservedHistory.{u}),
      InitialIdentification P g H →
      ∀ t : Icc (0 : ℝ) H.horizon, (t : ℝ) = 0 →
      ∀ x : (H.stageAt t).Carrier, ∀ {q : ℝ}, max Qbirth Q₀ ≤ q →
        ¬ q < metricScalarAt (H.stageMetric (H.activeStage t) t) x := by
  obtain ⟨Q₀, hQ₀, hbound⟩ := exists_scalar_lt_at_time_zero P g
  refine ⟨Q₀, hQ₀, ?_⟩
  intro Qbirth H A t ht x q hq
  have hscalar := hbound H A t ht x
  have hthreshold : Q₀ ≤ q := (le_max_right Qbirth Q₀).trans hq
  exact not_lt_of_ge (hscalar.le.trans hthreshold)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
