import DifferentialGeometry.Topology.ThreeManifold.PoincareStandard
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FiniteHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

universe u

namespace FiniteSurgeryHistory

def poincareControlled (H : FiniteSurgeryHistory.{u}) : Prop := H.cutCapTrace.poincareControlled

theorem poincareControlled_iff (H : FiniteSurgeryHistory.{u}) :
    H.poincareControlled ↔ H.controlledBy Topology.componentIsPoincareStandard := Iff.rfl

theorem discarded_poincareStandard (H : FiniteSurgeryHistory.{u}) (h : H.poincareControlled)
    (i : Fin H.eventCount) (C : ConnectedComponents (H.event i).transition.discarded.Carrier) :
    Topology.isPoincareStandard ((H.event i).transition.discarded.component C).Carrier := h i C

theorem extinct_poincareControlled_trace (H : FiniteSurgeryHistory.{u})
    (h : H.poincareControlled) {T : ℝ} (hext : H.extinctAt T) :
    H.cutCapTrace.poincareControlled ∧ H.cutCapTrace.extinct := ⟨h, H.extinct_trace hext⟩

end FiniteSurgeryHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery
