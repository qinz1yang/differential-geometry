import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GCoverVerticalProtection
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Strong

/-!
# FC39 GROUP G, the assembler of `stub_exists_strongCertificate` (lane FC39-G-CVP)

The last step of the GROUP G order (dispositions of external review 56, lane plan): the SAME layers
plus `A.product` give ONE `ofLayers` output with its rim-product clause.

* `strongCertificateOfLayers_GCVP` — the strong certificate of the prepared rows `Pr`, the safe
  neighbourhoods, the adapted edge–rim package `A`, the vertex layer with its link, the port layer,
  the seam and face layers with their joint seam–face link (shared neighbourhoods `safe.shared`),
  the handle-end layer, the rim-region layer and the arc layer: the certificate is
  `ofLayers V A.edges A.circ O S F HE A.rims Arc Cv Vt RR Pt`, where cover / vertical / protection
  are the three lemmas of `FC39GCoverVerticalProtection.lean`, and the rim-product clause is `A.product`
  through `ofLayers_rimProduct_iff` (the actual rim layer `A.rims` of the same package);
* the identity constraints on the SAME output (D56-7): any other proofs of the three Prop layers
  give the same certificate (`_val`); the edge layer, circle region, rim charts and vertices are those of
  `A` and `V` (`_handle`, `_circ`, `_rimChart`, `_vertex` with the row model through `vertex_eq`);
  every handle and edge-circle piece is the WHOLE inverse image of its component under the labelled
  registration (`_handle_whole`, `_edgeCircle_whole`, through `components_eq`); the circle region is
  the row region (`_region`); the end vertex of every handle end is the owner of the actual
  horizontal face (`_handleEnd_index`, by the general owner identification
  `AdaptedEdgeRimData.handleEnd_index_eq`, no owner equation taken);
* `exists_strongCertificate_of_layers_GCVP` — the existence form.

The frozen `stub_exists_strongCertificate (Pr)` (`T:369–371`) is this assembler fed with the
existence theorems of the other GROUP G lanes (safe neighbourhoods, adapted data (gate 2), seams and
faces, handle ends, rim region, arcs); nothing here reads `Pr.globalFaces`.
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

/-- **The assembler**: ONE `ofLayers` output of the given layers, with the rim-product clause of
the actual rim layer `A.rims` (`A.product`). -/
def strongCertificateOfLayers_GCVP (Pr : FC39Prepared W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) (A : AdaptedEdgeRimData Pr safe)
    (V : VertexLayer W) (vlink : VertexModelLink Pr.rows V) (O : PortLayer W E V)
    (S : SeamLayer W V A.circ) (F : FaceLayer W E V S O)
    (sf : SeamFacesLink Pr.rows V vlink O S F safe.shared)
    (HE : HandleEndLayer W V A.edges F) (RR : RimRegionLayer W V A.edges A.circ HE A.rims)
    (Arc : ArcLayer W A.edges A.circ F HE A.rims) : StrongCertificate W E :=
  ⟨ofLayers V A.edges A.circ O S F HE A.rims Arc (coverLayer_of_adapted_GCVP Pr safe A V vlink)
      (verticalLayer_of_adapted_GCVP Pr safe A) RR (protectionLayer_of_adapted_GCVP Pr safe A S sf),
    ofLayers_rimProduct_iff.2 A.product⟩

section Identities

variable (Pr : FC39Prepared W E) (safe : ProducerSafeNeighbourhoods Pr.rows)
  (A : AdaptedEdgeRimData Pr safe) (V : VertexLayer W) (vlink : VertexModelLink Pr.rows V)
  (O : PortLayer W E V) (S : SeamLayer W V A.circ) (F : FaceLayer W E V S O)
  (sf : SeamFacesLink Pr.rows V vlink O S F safe.shared)
  (HE : HandleEndLayer W V A.edges F) (RR : RimRegionLayer W V A.edges A.circ HE A.rims)
  (Arc : ArcLayer W A.edges A.circ F HE A.rims)

/-- The assembled certificate is `ofLayers` of the given layers, for ANY proofs of the cover,
vertical and protection layers. -/
theorem strongCertificateOfLayers_GCVP_val (Cv : CoverLayer W V A.edges A.circ)
    (Vt : VerticalLayer W A.edges A.circ) (Pt : ProtectionLayer W E A.edges A.circ S A.rims) :
    (strongCertificateOfLayers_GCVP Pr safe A V vlink O S F sf HE RR Arc).1 =
      ofLayers V A.edges A.circ O S F HE A.rims Arc Cv Vt RR Pt :=
  rfl

/-- The rim-product clause of the assembled certificate. -/
theorem strongCertificateOfLayers_GCVP_rimProduct :
    (strongCertificateOfLayers_GCVP Pr safe A V vlink O S F sf HE RR Arc).1.RimProduct :=
  (strongCertificateOfLayers_GCVP Pr safe A V vlink O S F sf HE RR Arc).2

/-- The circle region of the certificate is the circle region of the adapted package. -/
theorem strongCertificateOfLayers_GCVP_circ :
    (strongCertificateOfLayers_GCVP Pr safe A V vlink O S F sf HE RR Arc).1.circ = A.circ :=
  rfl

/-- The handles of the certificate are the handles of the adapted package. -/
theorem strongCertificateOfLayers_GCVP_handle (h : Fin A.edges.handleCount) :
    (strongCertificateOfLayers_GCVP Pr safe A V vlink O S F sf HE RR Arc).1.handle h =
      A.edges.handle h :=
  rfl

/-- The rim charts of the certificate are the rim charts of the adapted package. -/
theorem strongCertificateOfLayers_GCVP_rimChart (h : Fin A.edges.handleCount) (b : Bool) :
    (strongCertificateOfLayers_GCVP Pr safe A V vlink O S F sf HE RR Arc).1.rimChart h b =
      A.rims.rimChart h b :=
  rfl

/-- Every vertex of the certificate IS the row vertex (row piece and row model) of its index. -/
theorem strongCertificateOfLayers_GCVP_vertex (k : Fin V.vertexCount) :
    (strongCertificateOfLayers_GCVP Pr safe A V vlink O S F sf HE RR Arc).1.vertex k =
      Pr.rows.rowVertex (vlink.index k) :=
  vlink.vertex_eq k

/-- **Whole preimages.** Every handle of the certificate is the WHOLE inverse image of the base
component of its labelled registration (`components_eq`). -/
theorem strongCertificateOfLayers_GCVP_handle_whole (h : Fin A.edges.handleCount) :
    range ((strongCertificateOfLayers_GCVP Pr safe A V vlink O S F sf HE RR Arc).1.handle h).map =
      Pr.rows.edge.wholeComponent
        (Pr.rows.edgeModels.componentEquiv (.inl (A.labelled.edgeLink.handleEquiv h))) := by
  rw [A.components_eq]
  exact A.components.handle_whole h

/-- **Whole preimages.** Every edge-circle piece of the certificate is the WHOLE inverse image of
the base component of its labelled registration (`components_eq`). -/
theorem strongCertificateOfLayers_GCVP_edgeCircle_whole (j : Fin A.edges.edgeCircleCount) :
    range ((strongCertificateOfLayers_GCVP Pr safe A V vlink O S F sf HE RR Arc).1.edgeCircle
        j).piece.map =
      Pr.rows.edge.wholeComponent
        (Pr.rows.edgeModels.componentEquiv (.inr (A.labelled.edgeLink.circleEquiv j))) := by
  rw [A.components_eq]
  exact A.components.circle_whole j

/-- The circle region of the certificate is the row circle region. -/
theorem strongCertificateOfLayers_GCVP_region :
    (strongCertificateOfLayers_GCVP Pr safe A V vlink O S F sf HE RR Arc).1.circ.region =
      Pr.rows.circle.region :=
  A.circle.region_eq

/-- **Actual horizontal owner.** The end vertex of every handle end of the certificate is the
owner of the actual horizontal face of that end (general owner identification, no owner equation
taken). -/
theorem strongCertificateOfLayers_GCVP_handleEnd_index (h : Fin A.edges.handleCount) (b : Bool) :
    vlink.index ((strongCertificateOfLayers_GCVP Pr safe A V vlink O S F sf HE RR Arc).1.handleEnd
      h b) = A.labelled.handleEndOwner h b :=
  A.handleEnd_index_eq vlink HE h b

end Identities

/-- **The existence form of the assembler** (`stub_exists_strongCertificate` with the layers of
the other GROUP G lanes as inputs). -/
theorem exists_strongCertificate_of_layers_GCVP (Pr : FC39Prepared W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) (A : AdaptedEdgeRimData Pr safe)
    (V : VertexLayer W) (vlink : VertexModelLink Pr.rows V) (O : PortLayer W E V)
    (S : SeamLayer W V A.circ) (F : FaceLayer W E V S O)
    (sf : SeamFacesLink Pr.rows V vlink O S F safe.shared)
    (HE : HandleEndLayer W V A.edges F) (RR : RimRegionLayer W V A.edges A.circ HE A.rims)
    (Arc : ArcLayer W A.edges A.circ F HE A.rims) : Nonempty (StrongCertificate W E) :=
  ⟨strongCertificateOfLayers_GCVP Pr safe A V vlink O S F sf HE RR Arc⟩

end GC.GraphManifold.Assembly.FC39P0
