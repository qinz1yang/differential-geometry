import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GStrongAssembly
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0FixOwnerV2

/-!
# FC39 GROUP G over the prepared rows V2: cover / vertical / protection and the assembler (G1b)

Lane FC39-G-GFF(b), D58-1. The Pr-indexed theorems of `FC39GCoverVerticalProtection.lean` and
`FC39GStrongAssembly.lean` (lane FC39-G-CVP, frozen `T:359–366`, `T:369–371`) for
`AdaptedEdgeRimDataV2` over `Pr : FC39PreparedV2 W E`. The three layer lemmas are the accepted
KERNEL forms (`coverLayer_of_links_GCVP`, `verticalLayer_of_links_GCVP` on the rows and links, and
the row-level protection facts) applied to the links of the V2 package — nothing is re-proved:

* `coverLayer_of_adapted_GGFF`, `verticalLayer_of_adapted_GGFF`, `protectionLayer_of_adapted_GGFF`,
  `cover_vertical_protection_GGFF` (the V2 form of `stub_cover_vertical_protection`);
* `strongCertificateOfLayers_GGFF` with the identity constraints `_val`, `_rimProduct`, `_circ`,
  `_handle`, `_rimChart`, `_vertex`, `_handle_whole`, `_edgeCircle_whole`, `_region`,
  `_handleEnd_index`, and `exists_strongCertificate_of_layers_GGFF`;
* `strongCertificateOfLayers_GGFF_toV2` — on the forgetful image of an old adapted package the V2
  assembler IS the old one (definitional).
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

/-! ## Cover, vertical faces, protection (adapted forms over V2) -/

/-- **Cover (adapted form, V2)**, through the package's own links `A.components`, `A.circle`. -/
theorem coverLayer_of_adapted_GGFF (Pr : FC39PreparedV2 W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) (A : AdaptedEdgeRimDataV2 Pr safe)
    (V : VertexLayer W) (vlink : VertexModelLink Pr.rows V) : CoverLayer W V A.edges A.circ :=
  coverLayer_of_links_GCVP Pr.rows V vlink A.edges A.components A.circ A.circle

/-- **Vertical faces (adapted form, V2).** -/
theorem verticalLayer_of_adapted_GGFF (Pr : FC39PreparedV2 W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) (A : AdaptedEdgeRimDataV2 Pr safe) :
    VerticalLayer W A.edges A.circ :=
  verticalLayer_of_links_GCVP Pr.rows A.edges A.components A.circ A.circle

/-- A rim target lies in the closure of the safe corner tube of its endpoint (V2). -/
theorem AdaptedEdgeRimDataV2.rim_target_subset_GCVP {Pr : FC39PreparedV2 W E}
    {safe : ProducerSafeNeighbourhoods Pr.rows} (A : AdaptedEdgeRimDataV2 Pr safe)
    (h : Fin A.edges.handleCount) (b : Bool) :
    (A.rims.rimChart h b).target ⊆
      closure (safe.corner (A.labelled.edgeLink.endOfHandle h b)) :=
  subset_closure.trans ((A.rim_closure_in_safe h b).trans subset_closure)

/-- **Protection (V2).** From the SAME adapted package, the seam–face link with the prescribed
shared neighbourhoods `safe.shared`, and the safe corner tubes (an input). -/
theorem protectionLayer_of_adapted_GGFF (Pr : FC39PreparedV2 W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) (A : AdaptedEdgeRimDataV2 Pr safe)
    {V : VertexLayer W} {vlink : VertexModelLink Pr.rows V} {O : PortLayer W E V}
    (S : SeamLayer W V A.circ) {F : FaceLayer W E V S O}
    (sf : SeamFacesLink Pr.rows V vlink O S F safe.shared) :
    ProtectionLayer W E A.edges A.circ S A.rims where
  external_region_disjoint i := by
    rw [A.circle.region_eq]
    exact disjoint_collar_region_GCVP Pr.rows i
  external_handle_disjoint i h := disjoint_collar_handle_GCVP Pr.rows A.components i h
  external_edgeCircle_disjoint i e := disjoint_collar_edgeCircle_GCVP Pr.rows A.components i e
  external_torusSeam_disjoint i c :=
    ((safe.shared_safe.off_external _ i).mono_left (sf.torus_target_subset_GCVP c)).symm
  external_sphereSeam_disjoint i c :=
    ((safe.shared_safe.off_external _ i).mono_left (sf.sphere_target_subset_GCVP c)).symm
  rim_external_disjoint h b i :=
    (safe.corner_off_external _ i).mono_left (A.rim_target_subset_GCVP h b)
  rim_torusSeam_disjoint h b c :=
    (safe.corner_off_shared _ _).mono (A.rim_target_subset_GCVP h b)
      (sf.torus_target_subset_GCVP c)
  rim_sphereSeam_disjoint h b c :=
    (safe.corner_off_shared _ _).mono (A.rim_target_subset_GCVP h b)
      (sf.sphere_target_subset_GCVP c)
  sphereSeam_region_disjoint c := by
    rw [A.circle.region_eq]
    exact (safe.shared_safe.off_region _).mono_left (sf.sphere_target_subset_GCVP c)
  sphereSeam_handle_disjoint c h :=
    (safe.shared_safe.off_edge _).mono (sf.sphere_target_subset_GCVP c)
      (A.components.range_handle_subset_edgePiece_GCVP h)

/-- **GROUP G, `stub_cover_vertical_protection` over V2** (frozen `T:359–366`, D58-1 edit). -/
theorem cover_vertical_protection_GGFF (Pr : FC39PreparedV2 W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) (A : AdaptedEdgeRimDataV2 Pr safe)
    (V : VertexLayer W) (vlink : VertexModelLink Pr.rows V)
    (O : PortLayer W E V) (S : SeamLayer W V A.circ) (F : FaceLayer W E V S O)
    (sf : SeamFacesLink Pr.rows V vlink O S F safe.shared) :
    CoverLayer W V A.edges A.circ ∧ VerticalLayer W A.edges A.circ ∧
      ProtectionLayer W E A.edges A.circ S A.rims :=
  ⟨coverLayer_of_adapted_GGFF Pr safe A V vlink, verticalLayer_of_adapted_GGFF Pr safe A,
    protectionLayer_of_adapted_GGFF Pr safe A S sf⟩

/-! ## The assembler over V2 -/

/-- **The assembler (V2)**: ONE `ofLayers` output of the given layers, with the rim-product clause
of the actual rim layer `A.rims` (`A.product`). -/
def strongCertificateOfLayers_GGFF (Pr : FC39PreparedV2 W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) (A : AdaptedEdgeRimDataV2 Pr safe)
    (V : VertexLayer W) (vlink : VertexModelLink Pr.rows V) (O : PortLayer W E V)
    (S : SeamLayer W V A.circ) (F : FaceLayer W E V S O)
    (sf : SeamFacesLink Pr.rows V vlink O S F safe.shared)
    (HE : HandleEndLayer W V A.edges F) (RR : RimRegionLayer W V A.edges A.circ HE A.rims)
    (Arc : ArcLayer W A.edges A.circ F HE A.rims) : StrongCertificate W E :=
  ⟨ofLayers V A.edges A.circ O S F HE A.rims Arc (coverLayer_of_adapted_GGFF Pr safe A V vlink)
      (verticalLayer_of_adapted_GGFF Pr safe A) RR (protectionLayer_of_adapted_GGFF Pr safe A S sf),
    ofLayers_rimProduct_iff.2 A.product⟩

section Identities

variable (Pr : FC39PreparedV2 W E) (safe : ProducerSafeNeighbourhoods Pr.rows)
  (A : AdaptedEdgeRimDataV2 Pr safe) (V : VertexLayer W) (vlink : VertexModelLink Pr.rows V)
  (O : PortLayer W E V) (S : SeamLayer W V A.circ) (F : FaceLayer W E V S O)
  (sf : SeamFacesLink Pr.rows V vlink O S F safe.shared)
  (HE : HandleEndLayer W V A.edges F) (RR : RimRegionLayer W V A.edges A.circ HE A.rims)
  (Arc : ArcLayer W A.edges A.circ F HE A.rims)

/-- The assembled certificate is `ofLayers` of the given layers, for ANY proofs of the cover,
vertical and protection layers (V2). -/
theorem strongCertificateOfLayers_GGFF_val (Cv : CoverLayer W V A.edges A.circ)
    (Vt : VerticalLayer W A.edges A.circ) (Pt : ProtectionLayer W E A.edges A.circ S A.rims) :
    (strongCertificateOfLayers_GGFF Pr safe A V vlink O S F sf HE RR Arc).1 =
      ofLayers V A.edges A.circ O S F HE A.rims Arc Cv Vt RR Pt :=
  rfl

/-- The rim-product clause of the assembled certificate (V2). -/
theorem strongCertificateOfLayers_GGFF_rimProduct :
    (strongCertificateOfLayers_GGFF Pr safe A V vlink O S F sf HE RR Arc).1.RimProduct :=
  (strongCertificateOfLayers_GGFF Pr safe A V vlink O S F sf HE RR Arc).2

/-- The circle region of the certificate is the circle region of the adapted package (V2). -/
theorem strongCertificateOfLayers_GGFF_circ :
    (strongCertificateOfLayers_GGFF Pr safe A V vlink O S F sf HE RR Arc).1.circ = A.circ :=
  rfl

/-- The handles of the certificate are the handles of the adapted package (V2). -/
theorem strongCertificateOfLayers_GGFF_handle (h : Fin A.edges.handleCount) :
    (strongCertificateOfLayers_GGFF Pr safe A V vlink O S F sf HE RR Arc).1.handle h =
      A.edges.handle h :=
  rfl

/-- The rim charts of the certificate are the rim charts of the adapted package (V2). -/
theorem strongCertificateOfLayers_GGFF_rimChart (h : Fin A.edges.handleCount) (b : Bool) :
    (strongCertificateOfLayers_GGFF Pr safe A V vlink O S F sf HE RR Arc).1.rimChart h b =
      A.rims.rimChart h b :=
  rfl

/-- Every vertex of the certificate IS the row vertex of its index (V2). -/
theorem strongCertificateOfLayers_GGFF_vertex (k : Fin V.vertexCount) :
    (strongCertificateOfLayers_GGFF Pr safe A V vlink O S F sf HE RR Arc).1.vertex k =
      Pr.rows.rowVertex (vlink.index k) :=
  vlink.vertex_eq k

/-- **Whole preimages (V2).** Every handle of the certificate is the WHOLE inverse image of the
base component of its labelled registration. -/
theorem strongCertificateOfLayers_GGFF_handle_whole (h : Fin A.edges.handleCount) :
    range ((strongCertificateOfLayers_GGFF Pr safe A V vlink O S F sf HE RR Arc).1.handle h).map =
      Pr.rows.edge.wholeComponent
        (Pr.rows.edgeModels.componentEquiv (.inl (A.labelled.edgeLink.handleEquiv h))) := by
  rw [A.components_eq]
  exact A.components.handle_whole h

/-- **Whole preimages (V2).** Every edge-circle piece of the certificate is the WHOLE inverse image
of the base component of its labelled registration. -/
theorem strongCertificateOfLayers_GGFF_edgeCircle_whole (j : Fin A.edges.edgeCircleCount) :
    range ((strongCertificateOfLayers_GGFF Pr safe A V vlink O S F sf HE RR Arc).1.edgeCircle
        j).piece.map =
      Pr.rows.edge.wholeComponent
        (Pr.rows.edgeModels.componentEquiv (.inr (A.labelled.edgeLink.circleEquiv j))) := by
  rw [A.components_eq]
  exact A.components.circle_whole j

/-- The circle region of the certificate is the row circle region (V2). -/
theorem strongCertificateOfLayers_GGFF_region :
    (strongCertificateOfLayers_GGFF Pr safe A V vlink O S F sf HE RR Arc).1.circ.region =
      Pr.rows.circle.region :=
  A.circle.region_eq

/-- **Actual horizontal owner (V2).** The end vertex of every handle end of the certificate is the
owner of the actual horizontal face of that end. -/
theorem strongCertificateOfLayers_GGFF_handleEnd_index (h : Fin A.edges.handleCount) (b : Bool) :
    vlink.index ((strongCertificateOfLayers_GGFF Pr safe A V vlink O S F sf HE RR Arc).1.handleEnd
      h b) = A.labelled.handleEndOwner h b :=
  A.handleEnd_index_eq vlink HE h b

end Identities

/-- **The existence form of the assembler (V2).** -/
theorem exists_strongCertificate_of_layers_GGFF (Pr : FC39PreparedV2 W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) (A : AdaptedEdgeRimDataV2 Pr safe)
    (V : VertexLayer W) (vlink : VertexModelLink Pr.rows V) (O : PortLayer W E V)
    (S : SeamLayer W V A.circ) (F : FaceLayer W E V S O)
    (sf : SeamFacesLink Pr.rows V vlink O S F safe.shared)
    (HE : HandleEndLayer W V A.edges F) (RR : RimRegionLayer W V A.edges A.circ HE A.rims)
    (Arc : ArcLayer W A.edges A.circ F HE A.rims) : Nonempty (StrongCertificate W E) :=
  ⟨strongCertificateOfLayers_GGFF Pr safe A V vlink O S F sf HE RR Arc⟩

/-- On the forgetful image of an old adapted package, the V2 assembler IS the old one. -/
theorem strongCertificateOfLayers_GGFF_toV2 (Pr : FC39Prepared W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) (A : AdaptedEdgeRimData Pr safe)
    (V : VertexLayer W) (vlink : VertexModelLink Pr.rows V) (O : PortLayer W E V)
    (S : SeamLayer W V A.circ) (F : FaceLayer W E V S O)
    (sf : SeamFacesLink Pr.rows V vlink O S F safe.shared)
    (HE : HandleEndLayer W V A.edges F) (RR : RimRegionLayer W V A.edges A.circ HE A.rims)
    (Arc : ArcLayer W A.edges A.circ F HE A.rims) :
    strongCertificateOfLayers_GGFF Pr.toV2 safe A.toV2 V vlink O S F sf HE RR Arc =
      strongCertificateOfLayers_GCVP Pr safe A V vlink O S F sf HE RR Arc :=
  rfl

end GC.GraphManifold.Assembly.FC39P0
