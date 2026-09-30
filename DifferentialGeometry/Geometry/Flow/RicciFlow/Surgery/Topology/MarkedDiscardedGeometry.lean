import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedComponentGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MarkedReconstruction
namespace GC.Surgery
open DifferentialGeometry DifferentialGeometry.Topology
open GC.Geometry
set_option autoImplicit false
noncomputable section
universe u
variable {M Q : ClosedOrientedManifold.{u} 3}

structure DiscardedSlotGeometry (E : SphericalCutCapTransition M Q)
    (K : ConnectedComponents E.capped.Carrier) where
  point : E.discarded.Carrier
  target_label : presentationComponentEquiv E K = ConnectedComponents.mk (Sum.inr point)
  comparison : ClosedOrientedManifold.OrientedDiffeomorph
    (E.capped.component K).toClosedOrientedManifold
    (E.discarded.component (ConnectedComponents.mk point)).toClosedOrientedManifold
  geometric : StandardGeometricPresentation
    (E.discarded.component (ConnectedComponents.mk point)).toClosedOrientedManifold

def DiscardedSlotGeometry.atCap
    {E : SphericalCutCapTransition M Q} {K : ConnectedComponents E.capped.Carrier}
    (D : DiscardedSlotGeometry E K) :
    StandardGeometricPresentation (E.capped.component K).toClosedOrientedManifold :=
  D.geometric.pullback D.comparison

theorem DiscardedSlotGeometry.atCap_data
    {E : SphericalCutCapTransition M Q} {K : ConnectedComponents E.capped.Carrier}
    (D : DiscardedSlotGeometry E K) :
    D.atCap.presentation.diffeomorph = D.comparison.trans D.geometric.presentation.diffeomorph ∧
    D.atCap.presentation.factors = D.geometric.presentation.factors ∧
    D.atCap.model = D.geometric.model ∧ D.atCap.metric = D.geometric.metric ∧
    Nonempty (Fin D.atCap.presentation.factors.length) := by
  obtain ⟨hl,hm,ht,hg⟩ := D.geometric.pullback_data D.comparison
  exact ⟨hm,hl,ht,hg,D.atCap.factor_index_nonempty⟩

theorem marked_reconstruction_with_discarded_geometry
    (E : SphericalCutCapTransition M Q) (h : E.poincareControlled) :
    ∃ R : CutCapSumData E,
      Function.Bijective (presentationComponentEquiv E ∘ componentSlot R) ∧
      ∀ s : (Σ w : R.Group, Fin (R.factors w).length),
        (∃ q : Q.Carrier,
          presentationComponentEquiv E (componentSlot R s) = ConnectedComponents.mk (Sum.inl q) ∧
          Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
            (E.capped.component (componentSlot R s)).toClosedOrientedManifold
            (Q.component (ConnectedComponents.mk q)).toClosedOrientedManifold)) ∨
        ∃ D : DiscardedSlotGeometry E (componentSlot R s),
          D.atCap.presentation.diffeomorph =
            D.comparison.trans D.geometric.presentation.diffeomorph ∧
          Nonempty (Fin D.atCap.presentation.factors.length) := by
  obtain ⟨R,hR,hslots⟩ := exists_classified_reconstruction E
  refine ⟨R,hR,fun s => ?_⟩
  rcases hslots s with hret | ⟨d,hd,⟨f⟩⟩
  · exact Or.inl hret
  · obtain ⟨G⟩ := spherical_event_discarded_geometry E h (ConnectedComponents.mk d)
    let D : DiscardedSlotGeometry E (componentSlot R s) := ⟨d,hd,f,G⟩
    exact Or.inr ⟨D,D.atCap_data.1,D.atCap_data.2.2.2.2⟩

theorem terminal_reconstruction_has_geometric_slot
    (E : SphericalCutCapTransition M Q) (h : E.poincareControlled) [IsEmpty Q.Carrier] :
    ∃ R : CutCapSumData E,
      Function.Bijective (presentationComponentEquiv E ∘ componentSlot R) ∧
      ∃ (s : Σ w : R.Group, Fin (R.factors w).length)
        (D : DiscardedSlotGeometry E (componentSlot R s)),
        D.atCap.presentation.diffeomorph =
          D.comparison.trans D.geometric.presentation.diffeomorph ∧
        Nonempty (Fin D.atCap.presentation.factors.length) := by
  obtain ⟨R,hR,hslots⟩ := marked_reconstruction_with_discarded_geometry E h
  let w := (R.reconstruct (Classical.choice E.source_nonempty)).1
  have hlen : 0 < (R.factors w).length := List.length_pos_iff.mpr (R.nonempty_factors w)
  let s : Σ w : R.Group, Fin (R.factors w).length := ⟨w,⟨0,hlen⟩⟩
  rcases hslots s with ⟨q,-⟩ | hd
  · exact isEmptyElim q
  · exact ⟨R,hR,s,hd⟩

end
end GC.Surgery
