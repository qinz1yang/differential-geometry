import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecSides

/-!
# Consumers of packet S2, certificate level (lane ASM-SPH)

* `DecompositionCertificate.exists_liftedData`: for a sphere seam `c` of a certificate and the
  cut-and-capped data `X` of that seam, every vertex, handle, edge-circle piece, torus seam and rim
  chart lifts into the capped carrier by the one transport / side lift: the fold undoes the vertex
  lifts, the vertices that are not sides are moved by the transport alone, the two sides land on
  their own copies of the cut sphere, and the other data are transported with unchanged sources.
* `DecompositionCertificate.sphereSeam_sides`: the two sides of every sphere seam are different
  vertices and each stays (weakly) on its own side of the collar.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- **The sides of a sphere seam.** -/
theorem sphereSeam_sides (c : Fin D.sphereSeamCount) :
    D.sphereSide c true ≠ D.sphereSide c false ∧
      ∀ (b : Bool) (q : (D.vertex (D.sphereSide c b)).piece.Piece) (p : ClosureSphere.{u} × ℝ),
        p ∈ (D.sphereSeam c).collar.source →
          (D.vertex (D.sphereSide c b)).piece.map q = (D.sphereSeam c).collar p →
            0 ≤ (if b then (-1 : ℝ) else 1) * p.2 :=
  ⟨D.sphereSide_true_ne_false c, fun b _ _ hp h => by
    rw [← cutSideSign_sideCopy]
    exact D.sideVertex_side c b hp h⟩

/-- **All certificate data lift across the cut, by one transport.** -/
theorem exists_liftedData (c : Fin D.sphereSeamCount)
    (X : SphereCutCapped W (D.sphereSeam c) E) :
    ∃ (V : Fin D.vertexCount → PieceEmbedding X.Q) (H : Fin D.handleCount → EdgeHandle X.Q)
      (C : Fin D.edgeCircleCount → EdgeCirclePiece X.Q) (T : Fin D.torusSeamCount → TorusSeam X.Q)
      (R : Fin D.handleCount → Bool →
        PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) X.Q.model (Circle × (ℝ × ℝ)) X.Q.Carrier ∞),
      (∀ k, ∃ e : (V k).Piece ≃ (D.vertex k).piece.Piece,
        ∀ q, X.fold (X.coreInverse ((V k).map q)) = (D.vertex k).piece.map (e q)) ∧
      (∀ k, k ≠ D.sphereSide c true → k ≠ D.sphereSide c false →
        range (V k).map = X.transport '' (D.vertex k).image) ∧
      (∀ h p, (H h).map p = X.transport ((D.handle h).map p)) ∧
      (∀ e, range (C e).piece.map = X.transport '' range (D.edgeCircle e).piece.map) ∧
      (∀ d p, (T d).collar p = X.transport ((D.torusSeam d).collar p)) ∧
      ∀ h b, (R h b).source = (D.rimChart h b).source ∧
        ∀ p, R h b p = X.transport (D.rimChart h b p) :=
  ⟨D.liftVertex c X, D.liftHandle c X, D.liftEdgeCircle c X, D.liftTorusSeam c X,
    D.liftRimChart c X,
    fun k => ⟨Equiv.refl _, D.fold_coreInverse_liftVertex c X k⟩,
    fun _ h1 h2 => D.range_liftVertex_of_ne c X h1 h2,
    fun _ p => X.liftEdgeHandle_map _ _ p,
    fun e => X.range_liftPieceAway _
      (D.subset_compl_zeroSphere_of_disjoint (D.edgeCircle_image_disjoint_sphereCollar c e)),
    fun _ p => X.liftTorusSeam_collar_apply _ _ p,
    fun h b => ⟨D.liftRimChart_source c X h b, D.liftRimChart_apply c X h b⟩⟩

end DecompositionCertificate

end GC.GraphManifold.Assembly
