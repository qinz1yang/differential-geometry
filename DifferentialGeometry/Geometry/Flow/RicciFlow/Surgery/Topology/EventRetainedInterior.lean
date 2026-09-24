import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingInteriorImage

set_option autoImplicit false

noncomputable section

open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

theorem exists_oldTerminal_eq_of_mem_interior_old
    (x : E.incoming.terminalRegularOpen)
    (hx : x.1 ∈ interior (Subtype.val '' E.old)) :
    letI : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
    ∃ w : E.old, E.oldTerminal w = x ∧ (𝓡∂ 3).IsInteriorPoint w ∧
      E.RegularCrossing x.1 (E.oldOutput w) := by
  let : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
  obtain ⟨z, hz, hzx⟩ := interior_subset hx
  let w : E.old := ⟨z, hz⟩
  have hrange : Set.range (fun y : E.old => (y.1.1 : P.Carrier)) =
      Subtype.val '' E.old := by
    ext p
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.1, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hw : (𝓡∂ 3).IsInteriorPoint w :=
    E.old_induced.isInteriorPoint_of_mem_interior_range rfl (by
      change z.1 ∈ interior _
      rw [hrange, hzx]
      exact hx) BoundarylessManifold.isInteriorPoint
  exact ⟨w, Subtype.ext ((E.oldTerminal_eq w).trans hzx), hw, w, hw, hzx, rfl⟩

theorem exists_oldTerminal_eq_of_mem_interior_retained
    (hOld : E.old = E.transition.trace.retainedCore)
    (x : E.incoming.terminalRegularOpen)
    (hx : x.1 ∈ interior (Subtype.val '' E.transition.trace.retainedCore)) :
    ∃ z : E.old, E.oldTerminal z = x ∧ E.RegularCrossing x.val (E.oldOutput z) ∧
      E.transition.trace.presentation (E.transition.trace.capping.coreInclusion z.val) =
        Sum.inl (E.oldOutput z) := by
  rw [← hOld] at hx
  obtain ⟨z, hz, _, hcross⟩ := E.exists_oldTerminal_eq_of_mem_interior_old x hx
  exact ⟨z, hz, hcross, E.oldOutput_eq z⟩

end MetricCutCapEvent

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
