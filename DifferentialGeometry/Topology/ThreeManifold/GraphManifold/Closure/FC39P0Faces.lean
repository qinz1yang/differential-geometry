import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Junctions

/-!
# FC39 producer, packet P0 (gate 1), §2: seams and faces jointly

Task-47 draft §2 (disposition D5). The dry `SeamLayer` / `SeamLink` allowed a pseudo-seam inside a
vertex (regression test B). Here:

* `FC39RowsV2.rowVertex` and `VertexModelLink` (open choice 4: the vertex IS the row vertex with
  the row model — an equality in `Vertex W`, from which the piece equality follows), `PortModelLink`
  (the port `i` is owned by the cusp core `i`);
* the actual shared faces `FC39RowsV2.SharedFace` with their ambient set, shape and neighbour;
* `SharedSafe` — prescribed safe open neighbourhoods of the shared faces;
* `SeamFacesLink` — the seam indices in bijection with the actual shared spheres / tori; for EACH
  side of every seam an actual model boundary component of the owner with a smooth embedded
  parametrization of the standard face whose image under the owner's piece map is the zero slice of
  the seam collar (the common inclusion); the two owners are the slim piece of the shared end and
  the neighbour of `endKind`; the zero slice is both the slim end and the neighbour face; every
  torus side is a vertex; the closed collar lies in the prescribed neighbourhood; the face catalog
  `Fin faceCount ≃ Σ v, ModelBoundaryFace (vertex v).piece` with owners and images, and the kind
  rule (seam sides ⇔ `.sphereSeam` / `.torusSeam`, external model faces ⇔ `.external`, every other
  face `.partitioned` — a whole vertex–circle torus included, D5).

The joint stub `exists_seams_faces` is a TARGET (`build-logs/scratch/FC39-P0/Targets.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

namespace FC39RowsV2

variable (Rw : FC39RowsV2 W E)

/-- The vertex of a row index, with the row's model. -/
def rowVertex : Rw.slim.RowIndex → Vertex W
  | .inl i =>
    match Rw.zero.model i with
    | .inl m => .zero (Rw.zero.piece i) m
    | .inr Cz => .closedZero Cz.1
  | .inr (.inl b) => .cuspCore (Rw.cusp.piece b) (Rw.cusp.product b)
  | .inr (.inr j) => .slim (Rw.slim.piece j) (Rw.slim.model j)

/-- The piece of a row index. -/
def rowPiece : Rw.slim.RowIndex → PieceEmbedding W
  | .inl i => Rw.zero.piece i
  | .inr (.inl b) => Rw.cusp.piece b
  | .inr (.inr j) => Rw.slim.piece j

theorem rowVertex_piece (a : Rw.slim.RowIndex) : (Rw.rowVertex a).piece = Rw.rowPiece a := by
  rcases a with i | b | j
  · simp only [rowVertex, rowPiece]
    rcases Rw.zero.model i with m | Cz
    · rfl
    · exact Cz.2
  · rfl
  · rfl

theorem rowVertex_image (a : Rw.slim.RowIndex) : (Rw.rowVertex a).image = Rw.slim.rowSet a := by
  rcases a with i | b | j
  · simp only [rowVertex, SlimPiecesV2.rowSet]
    rcases Rw.zero.model i with m | Cz
    · rfl
    · change range Cz.1.piece.map = _
      rw [Cz.2]
  · rfl
  · rfl

/-- The actual shared faces of the rows. -/
abbrev SharedFace : Type :=
  ActualSharedFace Rw.slim

/-- The ambient set of a shared face (the whole slim end). -/
def sharedSet (σ : Rw.SharedFace) : Set W.Carrier :=
  Rw.slim.endSet σ.1

/-- The shape of a shared face. -/
def sharedShape (σ : Rw.SharedFace) : FaceShape :=
  Rw.slim.endShape σ.1

/-- The neighbour model face of a shared face. -/
def sharedNeighbour (σ : Rw.SharedFace) : NeighbourFace Rw.zero Rw.cusp :=
  (Rw.slim.endKind σ.1).get σ.2

/-- The row index of the owner of a neighbour face. -/
def neighbourIndex : NeighbourFace Rw.zero Rw.cusp → Rw.slim.RowIndex
  | .inl F => .inl F.1
  | .inr F => .inr (.inl F.1)

/-- The row index of the slim owner of a shared face. -/
def slimIndex (σ : Rw.SharedFace) : Rw.slim.RowIndex :=
  .inr (.inr σ.1.1.1)

end FC39RowsV2

/-- **§2.1 `VertexModelLink`** (strengthening of the dry `VertexLink`): a bijection of the vertex
indices with the row indices, and every vertex IS the row vertex with the row's model (open choice
4: equality of vertices, hence of pieces — `vertex_piece` — not only of ambient images). -/
structure VertexModelLink (Rw : FC39RowsV2 W E) (V : VertexLayer W) where
  index : Fin V.vertexCount ≃ Rw.slim.RowIndex
  vertex_eq : ∀ k, V.vertex k = Rw.rowVertex (index k)

theorem VertexModelLink.vertex_piece {Rw : FC39RowsV2 W E} {V : VertexLayer W}
    (VL : VertexModelLink Rw V) (k : Fin V.vertexCount) :
    (V.vertex k).piece = Rw.rowPiece (VL.index k) := by
  rw [VL.vertex_eq k, Rw.rowVertex_piece]

/-- The port `i` is owned by the vertex of the cusp core `i`. -/
structure PortModelLink (Rw : FC39RowsV2 W E) {V : VertexLayer W} (VL : VertexModelLink Rw V)
    (O : PortLayer W E V) : Prop where
  owner_index : ∀ i, VL.index (O.externalOwner i) = .inr (.inl i)

/-- **Prescribed safe neighbourhoods of the shared faces** (§2.3): each shared face lies in its
open neighbourhood (a compact set in an open one), the closures are pairwise disjoint, and avoid the
edge piece, the circle region and the external collars. -/
structure SharedSafe (Rw : FC39RowsV2 W E) (N : Rw.SharedFace → TopologicalSpace.Opens W.Carrier) :
    Prop where
  face_subset : ∀ σ, Rw.sharedSet σ ⊆ N σ
  closure_disjoint : Pairwise fun σ τ =>
    Disjoint (closure (N σ : Set W.Carrier)) (closure (N τ : Set W.Carrier))
  off_edge : ∀ σ, Disjoint (closure (N σ : Set W.Carrier)) Rw.edge.edgePiece
  off_region : ∀ σ, Disjoint (closure (N σ : Set W.Carrier)) Rw.circle.region
  off_external : ∀ σ i, Disjoint (closure (N σ : Set W.Carrier)) (E.collar i).target

/-- **§2.2–§2.3 The joint seam–face link.** -/
structure SeamFacesLink (Rw : FC39RowsV2 W E) (V : VertexLayer W) (VL : VertexModelLink Rw V)
    (O : PortLayer W E V) {circ : CircleRegion W} (S : SeamLayer W V circ)
    (F : FaceLayer W E V S O) (N : Rw.SharedFace → TopologicalSpace.Opens W.Carrier) where
  sphereEquiv : Fin S.sphereSeamCount ≃ {σ : Rw.SharedFace // Rw.sharedShape σ = .sphere}
  torusEquiv : Fin S.torusSeamCount ≃ {σ : Rw.SharedFace // Rw.sharedShape σ = .torus}
  sphere_slim : ∀ c,
    range (fun z => (S.sphereSeam c).collar (z, 0)) = Rw.sharedSet (sphereEquiv c).1
  sphere_neighbour : ∀ c, range (fun z => (S.sphereSeam c).collar (z, 0)) =
    neighbourSet (Rw.sharedNeighbour (sphereEquiv c).1)
  sphere_owner : ∀ c, ∃ b, VL.index (S.sphereSide c b) = Rw.slimIndex (sphereEquiv c).1 ∧
    VL.index (S.sphereSide c (!b)) = Rw.neighbourIndex (Rw.sharedNeighbour (sphereEquiv c).1)
  sphereSideFace : ∀ c b, ModelBoundaryFace (V.vertex (S.sphereSide c b)).piece
  sphereSideParam : ∀ c b, ClosureSphere.{u} → (V.vertex (S.sphereSide c b)).piece.Piece
  sphereSideParam_embedding : ∀ c b, IsSmoothEmbedding (𝓡 2) (𝓡∂ 3) ∞ (sphereSideParam c b)
  sphereSideParam_range : ∀ c b, range (sphereSideParam c b) = (sphereSideFace c b).1
  sphereSide_map : ∀ c b z,
    (V.vertex (S.sphereSide c b)).piece.map (sphereSideParam c b z) =
      (S.sphereSeam c).collar (z, 0)
  sphere_closure : ∀ c,
    closure (S.sphereSeam c).collar.target ⊆ (N (sphereEquiv c).1 : Set W.Carrier)
  torusOwner : Fin S.torusSeamCount → Bool → Fin V.vertexCount
  torusSide_eq : ∀ c b, S.torusSide c b = some (torusOwner c b)
  torus_slim : ∀ c,
    range (fun t => (S.torusSeam c).collar (t, 0)) = Rw.sharedSet (torusEquiv c).1
  torus_neighbour : ∀ c, range (fun t => (S.torusSeam c).collar (t, 0)) =
    neighbourSet (Rw.sharedNeighbour (torusEquiv c).1)
  torus_owner : ∀ c, ∃ b, VL.index (torusOwner c b) = Rw.slimIndex (torusEquiv c).1 ∧
    VL.index (torusOwner c (!b)) = Rw.neighbourIndex (Rw.sharedNeighbour (torusEquiv c).1)
  torusSideFace : ∀ c b, ModelBoundaryFace (V.vertex (torusOwner c b)).piece
  torusSideParam : ∀ c b, Torus → (V.vertex (torusOwner c b)).piece.Piece
  torusSideParam_embedding : ∀ c b, IsSmoothEmbedding torusModel (𝓡∂ 3) ∞ (torusSideParam c b)
  torusSideParam_range : ∀ c b, range (torusSideParam c b) = (torusSideFace c b).1
  torusSide_map : ∀ c b t,
    (V.vertex (torusOwner c b)).piece.map (torusSideParam c b t) = (S.torusSeam c).collar (t, 0)
  torus_closure : ∀ c,
    closure (S.torusSeam c).collar.target ⊆ (N (torusEquiv c).1 : Set W.Carrier)
  externalSideFace : ∀ i, ModelBoundaryFace (V.vertex (O.externalOwner i)).piece
  externalSideFace_image : ∀ i,
    (V.vertex (O.externalOwner i)).piece.map '' (externalSideFace i).1 = range (E.torusMap i)
  faceEquiv : Fin F.faceCount ≃ Σ v : Fin V.vertexCount, ModelBoundaryFace (V.vertex v).piece
  faceEquiv_owner : ∀ f, (faceEquiv f).1 = F.faceOwner f
  face_image : ∀ f, F.face f = (V.vertex (faceEquiv f).1).piece.map '' (faceEquiv f).2.1
  kind_sphere : ∀ {f c b},
    F.faceKind f = .sphereSeam c b ↔ faceEquiv f = ⟨S.sphereSide c b, sphereSideFace c b⟩
  kind_torus : ∀ {f c b},
    F.faceKind f = .torusSeam c b ↔ faceEquiv f = ⟨torusOwner c b, torusSideFace c b⟩
  kind_external : ∀ {f i},
    F.faceKind f = .external i ↔ faceEquiv f = ⟨O.externalOwner i, externalSideFace i⟩

end GC.GraphManifold.Assembly.FC39P0
