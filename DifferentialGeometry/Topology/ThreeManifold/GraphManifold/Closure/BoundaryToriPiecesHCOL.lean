import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.BoundaryToriHCOL
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyPieces

/-!
# Consumer of `boundaryTori_of_embeddings_HCOL`: the BD0 skeleton shape (lane S-COLLAR, G2)

`boundaryTori_of_pieces_HCOL`: for `CuspCores.piece / product` (`PieceEmbedding`s and the labelled
products onto them) whose composite `T² × [0, 1] → W` is a smooth embedding, with the ends
`T² × {0}` on `∂W` and pairwise disjoint pieces: a `BoundaryTori` `Et` with EXACTLY the three
compatibilities the inner `∀ Et` of the BD0 skeleton asks for
(`cuspCoresData_of_same_product_BGR`, `cuspCoresDataLevel_BGR`):
`(piece i).map (product i (t, 0)) = Et.torusMap i t`, `(Et.collar i).target ⊆ range (piece i).map`,
`closure (Et.collar i).target` disjoint from `(piece i).map (product i (T² × {1}))`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff
open Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.GraphManifold.Assembly

namespace DifferentialGeometry.Topology.HalfCollarHCOL

universe u

/-- **The three port-collar compatibilities of the BD0 skeleton, produced.** -/
theorem boundaryTori_of_pieces_HCOL (W : CompactCarrier.{u}) {n : ℕ}
    (piece : Fin n → PieceEmbedding W)
    (product : ∀ i, (Torus × Icc (0 : ℝ) 1) ≃ₘ⟮torusModel.prod (𝓡∂ 1), 𝓡∂ 3⟯ (piece i).Piece)
    (hΦ : ∀ i, IsSmoothEmbedding (torusModel.prod (𝓡∂ 1)) W.model ∞
      (fun p => (piece i).map (product i p)))
    (h0 : ∀ i t, W.model.IsBoundaryPoint ((piece i).map (product i (t, iccEnd false))))
    (hdisj : Pairwise fun i j => Disjoint (range (piece i).map) (range (piece j).map)) :
    ∃ Et : BoundaryTori W n,
      (∀ i t, (piece i).map (product i (t, iccEnd false)) = Et.torusMap i t) ∧
      (∀ i, (Et.collar i).target ⊆ range (piece i).map) ∧
      (∀ i, Disjoint (closure (Et.collar i).target)
        (range fun t : Torus => (piece i).map (product i (t, iccEnd true)))) := by
  have hrange : ∀ i, range (fun p => (piece i).map (product i p)) = range (piece i).map :=
    fun i => by
      rw [show (fun p => (piece i).map (product i p)) = (piece i).map ∘ (product i) from rfl,
        range_comp, show range (product i) = univ from (product i).toEquiv.surjective.range_eq,
        image_univ]
  obtain ⟨Et, h1, h2, h3⟩ := boundaryTori_of_embeddings_HCOL W
    (fun i p => (piece i).map (product i p)) hΦ h0
    (fun i j hij => by
      change Disjoint (range fun p => (piece i).map (product i p))
        (range fun p => (piece j).map (product j p))
      rw [hrange, hrange]
      exact hdisj hij)
  exact ⟨Et, h1, fun i => (h2 i).trans (hrange i).subset, h3⟩

end DifferentialGeometry.Topology.HalfCollarHCOL
