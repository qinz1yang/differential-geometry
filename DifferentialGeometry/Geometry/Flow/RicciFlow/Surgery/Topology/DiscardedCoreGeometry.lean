import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticNeckChildCore

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

include G

theorem scalar_gt_protected_of_not_mem_retainedCore
    (x : (H.event i).incoming.terminalRegularOpen)
    (hx : x.1 ∈ (H.event i).transition.trace.tubes.core)
    (hdiscard : (⟨x.1, hx⟩ : (H.event i).transition.trace.tubes.core) ∉
      (H.event i).transition.trace.retainedCore) :
    ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ <
      metricScalarAt (H.event i).terminal.metric x := by
  apply lt_of_not_ge
  intro hscalar
  obtain ⟨y, hy, heq⟩ := interior_subset (G.protected_interior x hscalar)
  have hyx : y = (⟨x.1, hx⟩ : (H.event i).transition.trace.tubes.core) :=
    Subtype.ext heq
  exact hdiscard (hyx ▸ hy)

theorem scalar_gt_protected_of_presentation_eq_inr
    (x : (H.event i).incoming.terminalRegularOpen)
    (hx : x.1 ∈ (H.event i).transition.trace.tubes.core)
    (d : (H.event i).discarded.Carrier)
    (hdiscard : (H.event i).transition.trace.presentation
      ((H.event i).transition.trace.capping.coreInclusion ⟨x.1, hx⟩) = Sum.inr d) :
    ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ <
      metricScalarAt (H.event i).terminal.metric x := by
  apply G.scalar_gt_protected_of_not_mem_retainedCore x hx
  rintro ⟨q, hq⟩
  exact Sum.inr_ne_inl (hdiscard.symm.trans hq)

theorem scalar_gt_protected_on_discarded_core_component
    (z : (H.event i).transition.trace.tubes.core)
    (hz : z ∉ (H.event i).transition.trace.retainedCore)
    (x : (H.event i).incoming.terminalRegularOpen)
    (hx : x.1 ∈ (H.event i).transition.trace.tubes.core)
    (hcomponent : ConnectedComponents.mk (⟨x.1, hx⟩ : (H.event i).transition.trace.tubes.core) =
      ConnectedComponents.mk z) :
    ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ <
      metricScalarAt (H.event i).terminal.metric x := by
  apply G.scalar_gt_protected_of_not_mem_retainedCore x hx
  exact (H.event i).transition.trace.connectedComponent_subset_compl_retainedCore z hz
    (ConnectedComponents.coe_eq_coe'.mp hcomponent)

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
