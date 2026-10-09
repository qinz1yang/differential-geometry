import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GStrongAssemblyV2
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GHandleEndRimV2
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GSafeNeighbourhoods
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GVertexPortLayers

/-!
# FC39 GROUP G: the final assembly modulo the four remaining layers (lane FC39-G-FINAL)

The frozen final target `stub_exists_strongCertificate` (`Targets.lean.txt:369–371`) on the V2
contract of D58-1 (`FC39PreparedV2`), assembled from the PROVED layers

* vertex and port layers `exists_vertexLayer_portLayer_G1` (lane FC39-G1),
* safe neighbourhoods `exists_safeNeighbourhoods_GSAFE` (lane FC39-G-SAFE),
* the handle-end layer `AdaptedEdgeRimDataV2.handleEndLayer_GHR` with its owner equation and the
  rim region `rimRegionLayer_of_labelled_GGFF` (lanes FC39-G-HE-RIM, FC39-G-GFF(b)),
* cover / vertical / protection and the assembler `strongCertificateOfLayers_GGFF` (lanes
  FC39-G-CVP, FC39-G-GFF(b)),

with the four layers that are still being proved taken as EXPLICIT FUNCTION ARGUMENTS whose types
are exactly the frozen V2 statements (`build-logs/scratch/FC39-G-GFF/TargetsV2.lean`, `T:289–299`):

* `seamsFaces` — `stub_exists_seams_faces` (`T:289–299`, rows only, unchanged by D58-1);
* `globalFaces` — `stubV2_exists_globalFaceFunctions` (D58-1 V2 form of `T:302–303`);
* `adapted` — `stubV2_exists_adaptedEdgeRimData` (V2 form of `T:306–309`);
* `arc` — `stubV2_exists_arcLayer` (V2 form of `T:349–356`, arbitrary `HE`).

Main results:

* `strongCertificateOfRemaining_GFIN` — the data form: the certificate of the given safe
  neighbourhoods, vertex link, port layer, global face functions `GF`, adapted data `A`, seam–face
  link `sf`, a handle-end layer with the owner equation and an arc layer (the rim region is
  computed); `strongCertificateOfRemaining_GFIN_eq` (definitional: it IS `strongCertificateOfLayers_GGFF`);
* `strongCertificateOfRemainingLabelled_GFIN` — the same with the handle-end layer COMPUTED from
  the labelled compatibility (`A.handleEndLayer_GHR vlink sf`);
* `strongCertificate_of_remaining_layers_GFIN` — **the final assembly from the rows**, the four
  frozen statements as arguments;
* `strongCertificate_of_prepared_remaining_layers_GFIN` — the frozen V2 final target
  `stubV2_exists_strongCertificate (Pr)` from the three statements that a prepared row package does
  not already contain (its global face functions are `Pr.globalFaces`);
* `strongCertificate_of_remaining_layers_V1_GFIN` — the frozen V1 final target
  `stub_exists_strongCertificate (Pr : FC39Prepared W E)` verbatim, through `FC39Prepared.toV2`, from
  the same three V2 statements.

No new named `Prop`, no `sorry`: each argument is a ∀-statement written out verbatim, and when the
four lanes deliver, the final theorem is ONE application (template
`build-logs/scratch/FC39-G-FINAL/FinalLanding.lean.txt`).
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

/-! ## The data form -/

/-- **The certificate of the remaining layers (data form).** From the rows `Rw` with their global
face functions `GF` (the prepared rows `⟨Rw, GF⟩`), safe neighbourhoods, vertex link, port layer,
the adapted data `A` over `⟨Rw, GF⟩`, the seam–face link `sf` with the prescribed shared
neighbourhoods `safe.shared`, ANY handle-end layer `HE` with the owner equation (D58-6: any given
`HE` is accepted) and an arc layer over `HE`: the rim region is computed from the owner equation
(`rimRegionLayer_of_labelled_GGFF`), cover / vertical / protection inside the assembler. -/
def strongCertificateOfRemaining_GFIN (Rw : FC39RowsV2 W E) (GF : GlobalFaceFunctionsV2 Rw)
    (safe : ProducerSafeNeighbourhoods Rw) (V : VertexLayer W) (vlink : VertexModelLink Rw V)
    (O : PortLayer W E V) (A : AdaptedEdgeRimDataV2 ⟨Rw, GF⟩ safe)
    (S : SeamLayer W V A.circ) (F : FaceLayer W E V S O)
    (sf : SeamFacesLink Rw V vlink O S F safe.shared) (HE : HandleEndLayer W V A.edges F)
    (hHE : ∀ h b, vlink.index (HE.handleEnd h b) = A.labelled.handleEndOwner h b)
    (Arc : ArcLayer W A.edges A.circ F HE A.rims) : StrongCertificate W E :=
  strongCertificateOfLayers_GGFF ⟨Rw, GF⟩ safe A V vlink O S F sf HE
    (rimRegionLayer_of_labelled_GGFF ⟨Rw, GF⟩ safe A V vlink HE hHE) Arc

/-- The data form IS the V2 assembler with the computed rim region (definitional). -/
theorem strongCertificateOfRemaining_GFIN_eq (Rw : FC39RowsV2 W E) (GF : GlobalFaceFunctionsV2 Rw)
    (safe : ProducerSafeNeighbourhoods Rw) (V : VertexLayer W) (vlink : VertexModelLink Rw V)
    (O : PortLayer W E V) (A : AdaptedEdgeRimDataV2 ⟨Rw, GF⟩ safe)
    (S : SeamLayer W V A.circ) (F : FaceLayer W E V S O)
    (sf : SeamFacesLink Rw V vlink O S F safe.shared) (HE : HandleEndLayer W V A.edges F)
    (hHE : ∀ h b, vlink.index (HE.handleEnd h b) = A.labelled.handleEndOwner h b)
    (RR : RimRegionLayer W V A.edges A.circ HE A.rims)
    (Arc : ArcLayer W A.edges A.circ F HE A.rims) :
    strongCertificateOfRemaining_GFIN Rw GF safe V vlink O A S F sf HE hHE Arc =
      strongCertificateOfLayers_GGFF ⟨Rw, GF⟩ safe A V vlink O S F sf HE RR Arc :=
  rfl

/-- The handle ends of the data form are read from the actual horizontal labels. -/
theorem strongCertificateOfRemaining_GFIN_handleEnd_index (Rw : FC39RowsV2 W E)
    (GF : GlobalFaceFunctionsV2 Rw) (safe : ProducerSafeNeighbourhoods Rw) (V : VertexLayer W)
    (vlink : VertexModelLink Rw V) (O : PortLayer W E V) (A : AdaptedEdgeRimDataV2 ⟨Rw, GF⟩ safe)
    (S : SeamLayer W V A.circ) (F : FaceLayer W E V S O)
    (sf : SeamFacesLink Rw V vlink O S F safe.shared) (HE : HandleEndLayer W V A.edges F)
    (hHE : ∀ h b, vlink.index (HE.handleEnd h b) = A.labelled.handleEndOwner h b)
    (Arc : ArcLayer W A.edges A.circ F HE A.rims) (h : Fin A.edges.handleCount) (b : Bool) :
    vlink.index ((strongCertificateOfRemaining_GFIN Rw GF safe V vlink O A S F sf HE hHE
      Arc).1.handleEnd h b) = A.labelled.handleEndOwner h b :=
  hHE h b

/-- **The data form with the handle-end layer computed** from the labelled compatibility
(`A.handleEndLayer_GHR vlink sf`, owner equation `handleEndLayer_GHR_index`). -/
def strongCertificateOfRemainingLabelled_GFIN (Rw : FC39RowsV2 W E) (GF : GlobalFaceFunctionsV2 Rw)
    (safe : ProducerSafeNeighbourhoods Rw) (V : VertexLayer W) (vlink : VertexModelLink Rw V)
    (O : PortLayer W E V) (A : AdaptedEdgeRimDataV2 ⟨Rw, GF⟩ safe)
    (S : SeamLayer W V A.circ) (F : FaceLayer W E V S O)
    (sf : SeamFacesLink Rw V vlink O S F safe.shared)
    (Arc : ArcLayer W A.edges A.circ F (A.handleEndLayer_GHR vlink sf) A.rims) :
    StrongCertificate W E :=
  strongCertificateOfRemaining_GFIN Rw GF safe V vlink O A S F sf (A.handleEndLayer_GHR vlink sf)
    (A.handleEndLayer_GHR_index vlink sf) Arc

/-- Transport of the arc input along an equality of handle-end layers: the assembled certificate
does not see which proof of the owner equation, nor which equal `HE`, was used. -/
theorem strongCertificateOfRemaining_GFIN_congr (Rw : FC39RowsV2 W E)
    (GF : GlobalFaceFunctionsV2 Rw) (safe : ProducerSafeNeighbourhoods Rw) (V : VertexLayer W)
    (vlink : VertexModelLink Rw V) (O : PortLayer W E V) (A : AdaptedEdgeRimDataV2 ⟨Rw, GF⟩ safe)
    (S : SeamLayer W V A.circ) (F : FaceLayer W E V S O)
    (sf : SeamFacesLink Rw V vlink O S F safe.shared) {HE HE' : HandleEndLayer W V A.edges F}
    (hEq : HE = HE')
    (hHE : ∀ h b, vlink.index (HE.handleEnd h b) = A.labelled.handleEndOwner h b)
    (hHE' : ∀ h b, vlink.index (HE'.handleEnd h b) = A.labelled.handleEndOwner h b)
    (Arc : ArcLayer W A.edges A.circ F HE A.rims) :
    strongCertificateOfRemaining_GFIN Rw GF safe V vlink O A S F sf HE' hHE' (hEq ▸ Arc) =
      strongCertificateOfRemaining_GFIN Rw GF safe V vlink O A S F sf HE hHE Arc := by
  subst hEq
  rfl

/-! ## The final assembly with the four remaining statements as arguments -/

/-- **GROUP G, the final assembly modulo the four remaining layers (from the rows).** For prepared
raw rows `Rw` (V2 contract, D58-1) and the four frozen statements still being proved —
seams / faces (`T:289–299`), global face functions V2, adapted edge–rim data V2, arc layer V2 —
given as explicit arguments, the rows carry a strong certificate. Chain (D56 lane plan / D58-6):
vertex and port layers; global face functions `GF`, the prepared rows `⟨Rw, GF⟩`; safe
neighbourhoods (shared ones FIRST); adapted data `A`; seams and faces on `(V, O, A.circ,
safe.shared)`; the handle-end layer of the labels; the arc layer of THAT `HE`; the rim region and
cover / vertical / protection inside `strongCertificateOfRemaining_GFIN`. -/
theorem strongCertificate_of_remaining_layers_GFIN (Rw : FC39RowsV2 W E)
    (seamsFaces : ∀ (Rw : FC39RowsV2 W E) (V : VertexLayer W) (vlink : VertexModelLink Rw V)
      (circ : CircleRegion W), CircleRestrictionLink Rw.circle circ →
      ∀ O : PortLayer W E V, PortModelLink Rw vlink O →
      ∀ N : Rw.SharedFace → TopologicalSpace.Opens W.Carrier, SharedSafe Rw N →
      ∃ S : SeamLayer W V circ, ∃ F : FaceLayer W E V S O,
        Nonempty (SeamFacesLink Rw V vlink O S F N))
    (globalFaces : ∀ Rw : FC39RowsV2 W E, Nonempty (GlobalFaceFunctionsV2 Rw))
    (adapted : ∀ (Pr : FC39PreparedV2 W E) (safe : ProducerSafeNeighbourhoods Pr.rows),
      Nonempty (AdaptedEdgeRimDataV2 Pr safe))
    (arc : ∀ (Pr : FC39PreparedV2 W E) (safe : ProducerSafeNeighbourhoods Pr.rows)
      (A : AdaptedEdgeRimDataV2 Pr safe) (V : VertexLayer W) (vlink : VertexModelLink Pr.rows V)
      (O : PortLayer W E V) (S : SeamLayer W V A.circ) (F : FaceLayer W E V S O),
      SeamFacesLink Pr.rows V vlink O S F safe.shared → ∀ HE : HandleEndLayer W V A.edges F,
      Nonempty (ArcLayer W A.edges A.circ F HE A.rims)) :
    Nonempty (StrongCertificate W E) := by
  obtain ⟨V, vlink, O, olink⟩ := exists_vertexLayer_portLayer_G1 Rw
  obtain ⟨GF⟩ := globalFaces Rw
  obtain ⟨safe⟩ := exists_safeNeighbourhoods_GSAFE Rw
  obtain ⟨A⟩ := adapted ⟨Rw, GF⟩ safe
  obtain ⟨S, F, ⟨sf⟩⟩ :=
    seamsFaces Rw V vlink A.circ A.circle O olink safe.shared safe.shared_safe
  obtain ⟨Arc⟩ := arc ⟨Rw, GF⟩ safe A V vlink O S F sf (A.handleEndLayer_GHR vlink sf)
  exact ⟨strongCertificateOfRemainingLabelled_GFIN Rw GF safe V vlink O A S F sf Arc⟩

/-- **The frozen V2 final target `stubV2_exists_strongCertificate (Pr)`** modulo the three remaining
statements a prepared row package does not contain (its global face functions are
`Pr.globalFaces`). -/
theorem strongCertificate_of_prepared_remaining_layers_GFIN (Pr : FC39PreparedV2 W E)
    (seamsFaces : ∀ (Rw : FC39RowsV2 W E) (V : VertexLayer W) (vlink : VertexModelLink Rw V)
      (circ : CircleRegion W), CircleRestrictionLink Rw.circle circ →
      ∀ O : PortLayer W E V, PortModelLink Rw vlink O →
      ∀ N : Rw.SharedFace → TopologicalSpace.Opens W.Carrier, SharedSafe Rw N →
      ∃ S : SeamLayer W V circ, ∃ F : FaceLayer W E V S O,
        Nonempty (SeamFacesLink Rw V vlink O S F N))
    (adapted : ∀ (Pr : FC39PreparedV2 W E) (safe : ProducerSafeNeighbourhoods Pr.rows),
      Nonempty (AdaptedEdgeRimDataV2 Pr safe))
    (arc : ∀ (Pr : FC39PreparedV2 W E) (safe : ProducerSafeNeighbourhoods Pr.rows)
      (A : AdaptedEdgeRimDataV2 Pr safe) (V : VertexLayer W) (vlink : VertexModelLink Pr.rows V)
      (O : PortLayer W E V) (S : SeamLayer W V A.circ) (F : FaceLayer W E V S O),
      SeamFacesLink Pr.rows V vlink O S F safe.shared → ∀ HE : HandleEndLayer W V A.edges F,
      Nonempty (ArcLayer W A.edges A.circ F HE A.rims)) :
    Nonempty (StrongCertificate W E) := by
  obtain ⟨V, vlink, O, olink⟩ := exists_vertexLayer_portLayer_G1 Pr.rows
  obtain ⟨safe⟩ := exists_safeNeighbourhoods_GSAFE Pr.rows
  obtain ⟨A⟩ := adapted Pr safe
  obtain ⟨S, F, ⟨sf⟩⟩ :=
    seamsFaces Pr.rows V vlink A.circ A.circle O olink safe.shared safe.shared_safe
  obtain ⟨Arc⟩ := arc Pr safe A V vlink O S F sf (A.handleEndLayer_GHR vlink sf)
  exact ⟨strongCertificateOfRemainingLabelled_GFIN Pr.rows Pr.globalFaces safe V vlink O A S F sf
    Arc⟩

/-- **The frozen V1 final target `stub_exists_strongCertificate (Pr : FC39Prepared W E)`
(`T:369–371`) verbatim**, from the same three V2 statements, through the forgetful map
`FC39Prepared.toV2` (D58-1: the V2 contract is weaker, so the V1 target is a corollary). -/
theorem strongCertificate_of_remaining_layers_V1_GFIN (Pr : FC39Prepared W E)
    (seamsFaces : ∀ (Rw : FC39RowsV2 W E) (V : VertexLayer W) (vlink : VertexModelLink Rw V)
      (circ : CircleRegion W), CircleRestrictionLink Rw.circle circ →
      ∀ O : PortLayer W E V, PortModelLink Rw vlink O →
      ∀ N : Rw.SharedFace → TopologicalSpace.Opens W.Carrier, SharedSafe Rw N →
      ∃ S : SeamLayer W V circ, ∃ F : FaceLayer W E V S O,
        Nonempty (SeamFacesLink Rw V vlink O S F N))
    (adapted : ∀ (Pr : FC39PreparedV2 W E) (safe : ProducerSafeNeighbourhoods Pr.rows),
      Nonempty (AdaptedEdgeRimDataV2 Pr safe))
    (arc : ∀ (Pr : FC39PreparedV2 W E) (safe : ProducerSafeNeighbourhoods Pr.rows)
      (A : AdaptedEdgeRimDataV2 Pr safe) (V : VertexLayer W) (vlink : VertexModelLink Pr.rows V)
      (O : PortLayer W E V) (S : SeamLayer W V A.circ) (F : FaceLayer W E V S O),
      SeamFacesLink Pr.rows V vlink O S F safe.shared → ∀ HE : HandleEndLayer W V A.edges F,
      Nonempty (ArcLayer W A.edges A.circ F HE A.rims)) :
    Nonempty (StrongCertificate W E) :=
  strongCertificate_of_prepared_remaining_layers_GFIN Pr.toV2 seamsFaces adapted arc

end GC.GraphManifold.Assembly.FC39P0
