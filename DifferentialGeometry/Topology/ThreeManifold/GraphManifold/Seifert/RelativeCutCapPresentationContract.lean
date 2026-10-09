import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ContractAlongPresentation

/-!
# Exact retained data for selected contraction

The actual selected contraction indexes every omitted seam by its original seam index.
Its signed collar and matching are unchanged. External collars agree on their
whole original source, and reconstruction commutes with the actual map of original cut points.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.TorusPresentation

variable {W : CompactCarrier.{u}} (T : TorusPresentation W)
  (S : Finset (Fin T.components.count)) (K : Finset (Fin T.pairing.count))
  (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
  (hext : ∀ i, T.externalPiece i ∉ S) (hk : T.cutCarrier.kind = .withBoundary)
  (hconn : IsConnected ((T.restrictAlongCarrier S K hK hext).interior :
    Set (T.restrictAlongPairing S K hK).QuotientSpace))

def contractAlongRetainedSeamEquiv : T.AlongUnpairedSeam K ≃
    Fin (T.contractAlong S K hK hext hk hconn).pairing.count :=
  Fintype.equivFin (T.AlongUnpairedSeam K)

theorem contractAlong_retained_seam (a : T.AlongUnpairedSeam K) :
    (T.contractAlong S K hK hext hk hconn).seam
      (T.contractAlongRetainedSeamEquiv S K hK hext hk hconn a) = T.seam a.val := by
  change T.seam ((Fintype.equivFin (T.AlongUnpairedSeam K)).symm
    ((Fintype.equivFin (T.AlongUnpairedSeam K)) a)).val = T.seam a.val
  rw [Equiv.symm_apply_apply]

theorem contractAlong_retained_matching (a : T.AlongUnpairedSeam K) :
    (T.contractAlong S K hK hext hk hconn).pairing.matching
      (T.contractAlongRetainedSeamEquiv S K hK hext hk hconn a) =
      T.pairing.matching a.val := by
  change T.pairing.matching ((Fintype.equivFin (T.AlongUnpairedSeam K)).symm
    ((Fintype.equivFin (T.AlongUnpairedSeam K)) a)).val = T.pairing.matching a.val
  rw [Equiv.symm_apply_apply]

theorem contractAlong_retained_externalCount :
    (T.contractAlong S K hK hext hk hconn).externalCount = T.externalCount := rfl

theorem contractAlong_retained_external_collar (r : Fin T.externalCount)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    (T.contractAlong S K hK hext hk hconn).external.collar r p =
      T.external.collar r p := by
  let hc := T.restrictAlong_hconn_complement S K hK hext hconn
  let A := T.alongCutSystem S K hK hext hk hc
  change A.toTorusPresentation.external.collar r p = T.external.collar r p
  refine (A.toTorusPresentation_external_collar r p).trans ?_
  refine (A.fold_sideCollar (A.externalSide r) p).trans ?_
  exact (T.alongGeometryFinite_map_collar S K hK hext hk hc
    (T.alongLedgerSideSum K (.inr r)) hp).trans (T.marked_collar r p hp)

theorem contractAlong_retained_reconstruction (x : T.cutCarrier.Carrier) :
    (T.contractAlong S K hK hext hk hconn).reconstruction
      ((T.contractAlong S K hK hext hk hconn).pairing.quotientMap
        (T.contractAlongMap S K hK hext hk hconn x)) =
      T.reconstruction (T.pairing.quotientMap x) :=
  T.contractAlong_reconstruction_eq S K hK hext hk hconn x

end GC.Seifert.TorusPresentation
