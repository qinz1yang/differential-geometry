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

private theorem TerminalLimitMetric.isCompact_scalar_sublevel_of_time_derivative_bound
    (L : G.TerminalLimitMetric) {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (hbound : ∀ x : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : PhiAlmostNonnegative G.flow (Ico a s) Phi) (A : ℝ) :
    IsCompact {x : G.terminalRegularOpen | metricScalarAt L.metric x ≤ A} := by
  obtain ⟨K, hK, hKreg, d, hd, hcapture⟩ :=
    G.exists_compact_subset_terminalRegularRegion_containing_scalar_sublevels
      hq hbound hPhi hpinch (A + 1)
  let K' : Set G.terminalRegularOpen := Subtype.val ⁻¹' K
  have himage : Subtype.val '' K' = K := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      exact ⟨⟨y, hKreg hy⟩, hy, rfl⟩
  have hK' : IsCompact K' := by
    rw [_root_.Topology.IsEmbedding.isCompact_iff
      (_root_.Topology.IsEmbedding.subtypeVal (p := fun y => y ∈ G.terminalRegularOpen))]
    exact himage ▸ hK
  apply hK'.of_isClosed_subset
    (isClosed_le (metricScalar_smooth L.metric).continuous continuous_const)
  intro x hx
  have hclose : ∀ᶠ t in 𝓝[<] s, G.flow.scalar t x.val < A + 1 :=
    (L.tendsto_metricScalarAt x).eventually_lt_const (hx.trans_lt (lt_add_one A))
  have hlate : ∀ᶠ t in 𝓝[<] s, t ∈ Ioo d s := Ioo_mem_nhdsLT hd.2
  obtain ⟨t, ht, hscalar⟩ := (hlate.and hclose).exists
  exact hcapture t ht x.val hscalar.le

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

theorem TerminalLimitMetric.finite_components_meeting_scalar_sublevel
    (L : G.TerminalLimitMetric) (A : ℝ) :
    {c : ConnectedComponents G.terminalRegularOpen |
      ∃ x : G.terminalRegularOpen, ConnectedComponents.mk x = c ∧
        metricScalarAt L.metric x ≤ A}.Finite := by
  let : LocallyConnectedSpace G.terminalRegularOpen :=
    ChartedSpace.locallyConnectedSpace ThreeSpace G.terminalRegularOpen
  have hcompact := (L.isCompact_scalar_sublevel A).image
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

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
