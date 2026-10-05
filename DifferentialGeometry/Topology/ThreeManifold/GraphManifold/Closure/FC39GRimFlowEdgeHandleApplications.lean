import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimFlowEdgeHandle

/-!
# FC39 GROUP G, RIMBOX route B: consumers of the new flow edge handle

Lane FC39-G-RIMBOXc. `EdgeComponentModels.exists_edgeHandleLink_GRIM`: the new edge handle of an
interval component with exactly the four link clauses of `EdgeComponentsLink` (the form G8 uses;
planned statement (A) of `build-logs/scratch/FC39-G-RIMBOX/TargetsHandleChart.lean`);
`EdgeComponentModels.exists_edgeHandleFamily_GRIM`: one such handle for EVERY interval component.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

local instance diskChartsFEHA_GRIM : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

variable {W : CompactCarrier.{u}}

/-- **The new edge handle of an interval component with the four link clauses.** -/
theorem EdgeComponentModels.exists_edgeHandleLink_GRIM {P : EdgeBundle W}
    (M : EdgeComponentModels P) (i : Fin M.intervalCount) :
    ∃ H : EdgeHandle W,
      range H.map = P.wholeComponent (M.componentEquiv (.inl i)) ∧
      (∀ w t, ∃ hx : H.map (w, t) ∈ P.source,
        P.proj ⟨H.map (w, t), hx⟩ = M.intervalBase i t) ∧
      (∀ t, range (fun w => H.map (w, t)) = P.disk (M.intervalBase i t)) ∧
      (∀ t, (fun w => H.map (w, t)) '' diskRim = P.rim (M.intervalBase i t)) := by
  obtain ⟨V, hV, φ, ε, hε, hrange, hφ, hφβ, hφinj, hφs, hφV, hrest⟩ :=
    M.exists_flowEdgeHandle_GRIM i
  obtain ⟨H, Hm, hHm, hwhole, hproj, hdisk, hrim, hflow⟩ := hrest
  exact ⟨H, hwhole, hproj, hdisk, hrim⟩

/-- **A new edge handle for every interval component**, with the four link clauses. -/
theorem EdgeComponentModels.exists_edgeHandleFamily_GRIM {P : EdgeBundle W}
    (M : EdgeComponentModels P) :
    ∃ H : Fin M.intervalCount → EdgeHandle W, ∀ i,
      range (H i).map = P.wholeComponent (M.componentEquiv (.inl i)) ∧
      (∀ w t, ∃ hx : (H i).map (w, t) ∈ P.source,
        P.proj ⟨(H i).map (w, t), hx⟩ = M.intervalBase i t) ∧
      (∀ t, range (fun w => (H i).map (w, t)) = P.disk (M.intervalBase i t)) ∧
      (∀ t, (fun w => (H i).map (w, t)) '' diskRim = P.rim (M.intervalBase i t)) := by
  choose H hH using M.exists_edgeHandleLink_GRIM
  exact ⟨H, hH⟩

end GC.GraphManifold.Assembly.FC39P0
