import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarSublevel
import DifferentialGeometry.Topology.CompactSetConnectedNeighborhood

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.exists_connected_compact_neighborhood_scalar_sublevel_component
    (L : G.TerminalLimitMetric) (A : ℝ) (c : ConnectedComponents G.terminalRegularOpen)
    (hc : ∃ x : G.terminalRegularOpen, ConnectedComponents.mk x = c ∧
      metricScalarAt L.metric x ≤ A) :
    ∃ U : Set G.terminalRegularOpen,
      IsOpen U ∧ IsConnected U ∧ IsCompact (closure U) ∧
      closure U ⊆ {x | ConnectedComponents.mk x = c} ∧
      {x | ConnectedComponents.mk x = c ∧ metricScalarAt L.metric x ≤ A} ⊆ U ∧
      ∀ x ∈ frontier (closure U), A < metricScalarAt L.metric x := by
  obtain ⟨x, rfl, hx⟩ := hc
  let : LocallyConnectedSpace G.terminalRegularOpen :=
    ChartedSpace.locallyConnectedSpace ThreeSpace G.terminalRegularOpen
  let : LocallyPathConnectedSpace G.terminalRegularOpen :=
    ChartedSpace.locallyPathConnectedSpace ThreeSpace G.terminalRegularOpen
  let C : TopologicalSpace.Opens G.terminalRegularOpen :=
    ⟨connectedComponent x, isOpen_connectedComponent⟩
  let : LocallyPathConnectedSpace C := ChartedSpace.locallyPathConnectedSpace ThreeSpace C
  let : LocallyCompactSpace C := ChartedSpace.locallyCompactSpace ThreeSpace C
  let : ConnectedSpace C := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have hCclosed : IsClosed (C : Set G.terminalRegularOpen) := isClosed_connectedComponent
  let K : Set C := {y | metricScalarAt L.metric y.val ≤ A}
  have hK : IsCompact K := by
    have hclosed : _root_.Topology.IsClosedEmbedding (Subtype.val : C → G.terminalRegularOpen) :=
      ⟨_root_.Topology.IsEmbedding.subtypeVal, by
        have heq : range (Subtype.val : C → G.terminalRegularOpen) = (C : Set _) := by
          ext z
          exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hz => ⟨⟨z, hz⟩, rfl⟩⟩
        rw [heq]
        exact hCclosed⟩
    exact hclosed.isCompact_preimage (L.isCompact_scalar_sublevel A)
  obtain ⟨V, hVopen, hVconn, _, hKV, hVcompact⟩ :=
    DifferentialGeometry.exists_isOpen_isConnected_isCompact_closure_superset
      (⟨x, mem_connectedComponent⟩ : C) hK
  let U : Set G.terminalRegularOpen := Subtype.val '' V
  have hUopen : IsOpen U := C.isOpenEmbedding'.isOpenMap _ hVopen
  have hUconn : IsConnected U := hVconn.image Subtype.val continuous_subtype_val.continuousOn
  have hcompact : IsCompact (Subtype.val '' closure V : Set G.terminalRegularOpen) :=
    hVcompact.image continuous_subtype_val
  have hclosure : closure U ⊆ Subtype.val '' closure V :=
    closure_minimal (image_mono subset_closure) hcompact.isClosed
  have hcomp : closure U ⊆ {z | ConnectedComponents.mk z = ConnectedComponents.mk x} := by
    intro z hz
    obtain ⟨y, _, rfl⟩ := hclosure hz
    exact ConnectedComponents.coe_eq_coe'.mpr y.property
  have hlow : {z | ConnectedComponents.mk z = ConnectedComponents.mk x ∧
      metricScalarAt L.metric z ≤ A} ⊆ U := by
    intro z hz
    have hzC : z ∈ C := ConnectedComponents.coe_eq_coe'.mp hz.1
    exact ⟨⟨z, hzC⟩, hKV hz.2, rfl⟩
  refine ⟨U, hUopen, hUconn, hcompact.of_isClosed_subset isClosed_closure hclosure,
    hcomp, hlow, ?_⟩
  intro z hz
  apply lt_of_not_ge
  intro hR
  have hzU := hlow ⟨hcomp (isClosed_closure.frontier_subset hz), hR⟩
  exact hz.2 (interior_maximal subset_closure hUopen hzU)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
