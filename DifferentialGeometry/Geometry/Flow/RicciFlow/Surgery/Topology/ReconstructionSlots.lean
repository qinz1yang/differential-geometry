import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedDiscardedLabels
namespace GC.Surgery
open DifferentialGeometry.Topology
set_option autoImplicit false
universe u
variable {M Q : ClosedOrientedManifold.{u} 3} {E : SphericalCutCapTransition M Q}
  (R : CutCapSumData E)

def componentSlot : (Σ w : R.Group, Fin (R.factors w).length) →
    ConnectedComponents E.capped.Carrier := fun x => (R.factors x.1).get x.2

theorem componentSlot_bijective : Function.Bijective (componentSlot R) := by
  constructor
  · rintro ⟨v, i⟩ ⟨w, j⟩ h
    have hv := (R.mem_factors v ((R.factors v).get i)).mp (List.get_mem _ _)
    have hw := (R.mem_factors w ((R.factors w).get j)).mp (List.get_mem _ _)
    change (R.factors v).get i = (R.factors w).get j at h
    have hvw : v = w := hv.symm.trans ((congrArg R.assign h).trans hw)
    subst w
    have hij := (R.nodup_factors v).injective_get h
    cases hij
    rfl
  · intro K
    have hK := (R.mem_factors (R.assign K) K).mpr rfl
    obtain ⟨i, hi⟩ := List.get_of_mem hK
    exact ⟨⟨R.assign K, i⟩, hi⟩

theorem actual_target_slot_bijective : Function.Bijective
    (presentationComponentEquiv E ∘ componentSlot R) :=
  (presentationComponentEquiv E).bijective.comp (componentSlot_bijective R)

end GC.Surgery
