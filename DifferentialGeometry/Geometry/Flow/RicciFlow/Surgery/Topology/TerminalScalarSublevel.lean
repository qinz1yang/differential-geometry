import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCanonicalCapture
import Mathlib.Topology.Connected.LocallyConnected
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingModelCoverage

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

private theorem exists_scalar_time_derivative_bound (G : P.IncomingSlab a s) :
    ∃ q : ℝ, 0 < q ∧ ∃ C : ℝ≥0,
      ∀ x : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
        |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2 := by
  obtain ⟨ε, hε, hw⟩ := G.exists_all_point_canonical_neighborhoods
  obtain ⟨C1, C2, q, _, hC2, hq, hc⟩ := hw ε hε le_rfl
  refine ⟨q, hq, ⟨C2, zero_le_one.trans hC2⟩, ?_⟩
  intro x t ht hx
  exact (hc x t ⟨ht.1.le, ht.2⟩ hx.le).some.time_derivative


theorem TerminalLimitMetric.isCompact_scalar_sublevel
    (L : G.TerminalLimitMetric) (A : ℝ) :
    IsCompact {x : G.terminalRegularOpen | metricScalarAt L.metric x ≤ A} := by
  obtain ⟨q, hq, C, hbound⟩ := exists_scalar_time_derivative_bound G
  obtain ⟨Phi, hPhi, hpinch⟩ :=
    exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen
      G.lt G.flow G.equation (by simp [ThreeSpace])
  exact L.isCompact_scalar_sublevel_of_time_derivative_bound hq hbound hPhi hpinch A

theorem TerminalLimitMetric.exists_scalar_gt_on_connectedComponent_of_not_isCompact_of_time_derivative_bound
    (L : G.TerminalLimitMetric) {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (hbound : ∀ x : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2)
    (x : G.terminalRegularOpen)
    (hnoncompact : ¬ IsCompact (connectedComponent x)) (A : ℝ) :
    ∃ y ∈ connectedComponent x, A < metricScalarAt L.metric y := by
  obtain ⟨Phi, hPhi, hpinch⟩ :=
    exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen
      G.lt G.flow G.equation (by simp [ThreeSpace])
  by_contra! h
  exact hnoncompact ((L.isCompact_scalar_sublevel_of_time_derivative_bound hq hbound hPhi hpinch A).of_isClosed_subset
    isClosed_connectedComponent h)

theorem TerminalLimitMetric.exists_scalar_gt_on_connectedComponent_of_not_isCompact
    (L : G.TerminalLimitMetric) (x : G.terminalRegularOpen)
    (hnoncompact : ¬ IsCompact (connectedComponent x)) (A : ℝ) :
    ∃ y ∈ connectedComponent x, A < metricScalarAt L.metric y := by
  obtain ⟨q, hq, C, hbound⟩ := exists_scalar_time_derivative_bound G
  exact L.exists_scalar_gt_on_connectedComponent_of_not_isCompact_of_time_derivative_bound hq hbound x hnoncompact A

theorem TerminalLimitMetric.finite_components_meeting_scalar_sublevel_of_time_derivative_bound
    (L : G.TerminalLimitMetric) {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (hbound : ∀ x : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2)
    (A : ℝ) :
    {c : ConnectedComponents G.terminalRegularOpen |
      ∃ x : G.terminalRegularOpen, ConnectedComponents.mk x = c ∧
        metricScalarAt L.metric x ≤ A}.Finite := by
  obtain ⟨Phi, hPhi, hpinch⟩ :=
    exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen
      G.lt G.flow G.equation (by simp [ThreeSpace])
  let : LocallyConnectedSpace G.terminalRegularOpen :=
    ChartedSpace.locallyConnectedSpace ThreeSpace G.terminalRegularOpen
  have hcompact := (L.isCompact_scalar_sublevel_of_time_derivative_bound hq hbound hPhi hpinch A).image
    ConnectedComponents.continuous_coe
  have heq : ConnectedComponents.mk '' {x : G.terminalRegularOpen |
      metricScalarAt L.metric x ≤ A} =
      {c : ConnectedComponents G.terminalRegularOpen |
        ∃ x : G.terminalRegularOpen, ConnectedComponents.mk x = c ∧
          metricScalarAt L.metric x ≤ A} := by
    ext c
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, rfl, hx⟩
    · rintro ⟨x, hxc, hx⟩
      exact ⟨x, hx, hxc⟩
  exact heq ▸ hcompact.finite ⟨inferInstance⟩

theorem TerminalLimitMetric.finite_components_meeting_scalar_sublevel
    (L : G.TerminalLimitMetric) (A : ℝ) :
    {c : ConnectedComponents G.terminalRegularOpen |
      ∃ x : G.terminalRegularOpen, ConnectedComponents.mk x = c ∧
        metricScalarAt L.metric x ≤ A}.Finite := by
  obtain ⟨q, hq, C, hbound⟩ := exists_scalar_time_derivative_bound G
  exact L.finite_components_meeting_scalar_sublevel_of_time_derivative_bound hq hbound A

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
