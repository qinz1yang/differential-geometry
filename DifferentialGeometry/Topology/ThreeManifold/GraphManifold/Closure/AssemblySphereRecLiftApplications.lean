import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecLift

/-!
# Consumers of packet S2, first group (lane ASM-SPH)

* `SphereCutCapped.exists_transport`: the one transport map of a sphere cut, as data: a partial
  diffeomorphism from the complement of the seam sphere onto the complement of the caps, carrying
  the external ports of `W` onto the retained ports on the whole collar.
* `SphereCutCapped.exists_liftPiece`: a piece on one side of the seam lifts to a piece of the
  capped carrier over it (fold ∘ core⁻¹ recovers the old map), equal to the transport off the seam.
* `SphereCutCapped.exists_lift_protected`: a handle, an edge-circle piece, a sphere seam and a
  torus seam avoiding the seam sphere lift simultaneously by the same transport.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace SphereCutCapped

variable {W : CompactCarrier.{u}} {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
  (X : SphereCutCapped W S E)

/-- **The transport of a sphere cut.** -/
theorem exists_transport :
    ∃ T : PartialDiffeomorph W.model X.Q.model W.Carrier X.Q.Carrier ∞,
      T.source = S.zeroSphereᶜ ∧ T.target = (⋃ j, range (X.capping.cap j))ᶜ ∧
      (∀ x, X.fold (X.coreInverse (T x)) = x) ∧
      ∀ i, ∀ p ∈ halfCollarSource,
        T (E.collar i p) = X.capping.retained.collar (Fin.cast X.hn.symm i) p :=
  ⟨X.transport, X.transport_source, X.transport_target,
    fun x => by rw [transport_apply, X.coreInverse_core, X.fold_cutInverse],
    fun i _ hp => X.transport_externalCollar i hp⟩

/-- **A piece on one side of the seam lifts.** -/
theorem exists_liftPiece (P : PieceEmbedding W) (j : Fin 2)
    (hside : ∀ q p, p ∈ S.collar.source → P.map q = S.collar p → 0 ≤ cutSideSign j * p.2) :
    ∃ P' : PieceEmbedding X.Q, ∃ e : P'.Piece ≃ P.Piece,
      (∀ q, X.fold (X.coreInverse (P'.map q)) = P.map (e q)) ∧
      (∀ q, P.map (e q) ∉ S.zeroSphere → P'.map q = X.transport (P.map (e q))) ∧
      ∀ q z, P.map (e q) = S.collar (z, 0) → P'.map q = X.capping.core (X.cutSphere j z) :=
  ⟨X.liftPiece P j hside, Equiv.refl _, X.fold_coreInverse_liftPiece P j hside,
    fun _ hq => X.liftPiece_map_of_notMem P j hside hq,
    fun _ _ hq => X.liftPiece_map_of_mem P j hside hq⟩

/-- **The protected data lift simultaneously by the same transport.** -/
theorem exists_lift_protected (H : EdgeHandle W) (hH : range H.map ⊆ S.zeroSphereᶜ)
    (P : EdgeCirclePiece W) (hP : range P.piece.map ⊆ S.zeroSphereᶜ)
    (S' : SphereSeam W) (hS' : S'.collar.target ⊆ S.zeroSphereᶜ)
    (T : TorusSeam W) (hT : T.collar.target ⊆ S.zeroSphereᶜ) :
    ∃ (H' : EdgeHandle X.Q) (P' : EdgeCirclePiece X.Q) (S'' : SphereSeam X.Q) (T' : TorusSeam X.Q),
      (∀ p, H'.map p = X.transport (H.map p)) ∧
      range P'.piece.map = X.transport '' range P.piece.map ∧
      (∀ p, S''.collar p = X.transport (S'.collar p)) ∧
      ∀ p, T'.collar p = X.transport (T.collar p) :=
  ⟨X.liftEdgeHandle H hH, X.liftEdgeCirclePiece P hP, X.liftSphereSeam S' hS',
    X.liftTorusSeam T hT, X.liftEdgeHandle_map H hH, X.range_liftPieceAway P.piece hP,
    X.liftSphereSeam_collar_apply S' hS', X.liftTorusSeam_collar_apply T hT⟩

end SphereCutCapped

end GC.GraphManifold.Assembly
