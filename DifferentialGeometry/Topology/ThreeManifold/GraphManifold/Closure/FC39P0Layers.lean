import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1WSideRimProduct

/-!
# FC39 producer, packet P0 (gate 1): the certificate in layers

The fields of `DecompositionCertificate` (`AssemblyCertificate.lean:64–248`) split into layers, as
in the dry assembly (`build-logs/scratch/FC39-DRY/FC39Dry.lean`, §2) — copied VERBATIM, but NEW
declarations here (disposition D1: nothing of the dry file is installed). The repaired contract
(task-47 draft §1–§3, §8) links the rows to `VertexLayer`, `EdgeLayer`, `PortLayer`, `SeamLayer`,
`FaceLayer` and `RimChartLayer`; the Prop layers `CoverLayer`, `VerticalLayer`, `HandleEndLayer`,
`ArcLayer`, `RimRegionLayer`, `ProtectionLayer` carry the remaining certificate fields (the targets
of the producer packets, `build-logs/scratch/FC39-P0/Targets.lean`). The constructor
`DecompositionCertificate.ofLayers` reassembles a certificate from the layers.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

local instance diskChartsLayers_FC39P0 : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

/-- **L1 — vertices and their models.** -/
structure VertexLayer (W : CompactCarrier.{u}) where
  vertexCount : ℕ
  vertex : Fin vertexCount → Vertex W

/-- **L2 — handles and edge-circle pieces.** -/
structure EdgeLayer (W : CompactCarrier.{u}) where
  handleCount : ℕ
  handle : Fin handleCount → EdgeHandle W
  edgeCircleCount : ℕ
  edgeCircle : Fin edgeCircleCount → EdgeCirclePiece W

/-- **L0 — ports.** -/
structure PortLayer (W : CompactCarrier.{u}) {n : ℕ} (E : BoundaryTori W n) (V : VertexLayer W)
    where
  external_exhausted : W.model.boundary W.Carrier = E.image
  externalOwner : Fin n → Fin V.vertexCount
  external_owned : ∀ i, (E.collar i).target ⊆ (V.vertex (externalOwner i)).image

/-- **L4 — actual cover and disjoint ambient interiors.** -/
structure CoverLayer (W : CompactCarrier.{u}) (V : VertexLayer W) (H : EdgeLayer W)
    (circ : CircleRegion W) : Prop where
  cover : (⋃ k, (V.vertex k).image) ∪ (⋃ h, range (H.handle h).map) ∪
      (⋃ e, range (H.edgeCircle e).piece.map) ∪ circ.region = univ
  vertex_disjoint : Pairwise fun k k' =>
    Disjoint (interior (V.vertex k).image) (interior (V.vertex k').image)
  handle_disjoint : Pairwise fun h h' =>
    Disjoint (interior (range (H.handle h).map)) (interior (range (H.handle h').map))
  edgeCircle_disjoint : Pairwise fun e e' =>
    Disjoint (range (H.edgeCircle e).piece.map) (range (H.edgeCircle e').piece.map)
  vertex_handle_disjoint : ∀ k h,
    Disjoint (interior (V.vertex k).image) (interior (range (H.handle h).map))
  edgeCircle_vertex_disjoint : ∀ e k,
    Disjoint (interior (range (H.edgeCircle e).piece.map)) (interior (V.vertex k).image)
  edgeCircle_handle_disjoint : ∀ e h,
    Disjoint (interior (range (H.edgeCircle e).piece.map)) (interior (range (H.handle h).map))
  circ_vertex_disjoint : ∀ k, Disjoint (interior circ.region) (interior (V.vertex k).image)
  circ_handle_disjoint : ∀ h, Disjoint (interior circ.region) (interior (range (H.handle h).map))
  circ_edgeCircle_disjoint : ∀ e,
    Disjoint (interior circ.region) (interior (range (H.edgeCircle e).piece.map))

/-- **L5 — vertical faces (EDP06).** -/
structure VerticalLayer (W : CompactCarrier.{u}) (H : EdgeLayer W) (circ : CircleRegion W) :
    Prop where
  vertical_fibre : ∀ h (t : Icc (0 : ℝ) 1), ∃ b : circ.Base,
    (fun x : ClosedCell 2 => (H.handle h).map (x, t)) '' diskRim =
      Subtype.val '' (circ.proj ⁻¹' {b})
  edgeCircle_vertical : ∀ e, (H.edgeCircle e).piece.map ''
      {q | (𝓡∂ 3).IsBoundaryPoint q} ⊆ circ.region

/-- **L6 — whole torus and sphere seams with their collars.** -/
structure SeamLayer (W : CompactCarrier.{u}) (V : VertexLayer W) (circ : CircleRegion W) where
  torusSeamCount : ℕ
  torusSeam : Fin torusSeamCount → TorusSeam W
  torusSide : Fin torusSeamCount → Bool → Option (Fin V.vertexCount)
  torusSide_neg : ∀ c t s, -1 < s → s ≤ 0 →
    (torusSeam c).collar (t, s) ∈ (torusSide c true).elim circ.region fun k => (V.vertex k).image
  torusSide_pos : ∀ c t s, 0 ≤ s → s < 1 →
    (torusSeam c).collar (t, s) ∈ (torusSide c false).elim circ.region fun k => (V.vertex k).image
  torusSeam_disjoint : Pairwise fun c d =>
    Disjoint (torusSeam c).collar.target (torusSeam d).collar.target
  sphereSeamCount : ℕ
  sphereSeam : Fin sphereSeamCount → SphereSeam W
  sphereSide : Fin sphereSeamCount → Bool → Fin V.vertexCount
  sphereSide_neg : ∀ c z s, s ≤ 0 → -1 < s →
    (sphereSeam c).collar (z, s) ∈ (V.vertex (sphereSide c true)).image
  sphereSide_pos : ∀ c z s, 0 ≤ s → s < 1 →
    (sphereSeam c).collar (z, s) ∈ (V.vertex (sphereSide c false)).image
  sphereSeam_disjoint : Pairwise fun c d =>
    Disjoint (sphereSeam c).collar.target (sphereSeam d).collar.target
  sphere_torus_seam_disjoint : ∀ c d,
    Disjoint (sphereSeam c).collar.target (torusSeam d).collar.target

/-- **L8 — the per-vertex model-boundary partition into whole faces.** -/
structure FaceLayer (W : CompactCarrier.{u}) {n : ℕ} (E : BoundaryTori W n) (V : VertexLayer W)
    {circ : CircleRegion W} (S : SeamLayer W V circ) (O : PortLayer W E V) where
  faceCount : ℕ
  face : Fin faceCount → Set W.Carrier
  faceOwner : Fin faceCount → Fin V.vertexCount
  faceModel : (f : Fin faceCount) →
    (face f ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ⊕ (face f ≃ₜ Circle × Circle)
  face_exhausted : ∀ k, (⋃ (f : Fin faceCount) (_ : faceOwner f = k), face f) =
    (V.vertex k).boundaryImage
  faceKind : Fin faceCount → FaceKind n S.torusSeamCount S.sphereSeamCount
  face_disjoint : ∀ f f', f ≠ f' →
    (∀ c b, ¬ (faceKind f = .sphereSeam c b ∧ faceKind f' = .sphereSeam c (!b))) →
    (∀ c b, ¬ (faceKind f = .torusSeam c b ∧ faceKind f' = .torusSeam c (!b))) →
    Disjoint (face f) (face f')
  face_external : ∀ f i, faceKind f = .external i →
    face f = range (E.torusMap i) ∧ O.externalOwner i = faceOwner f
  external_face : ∀ i, ∃ f, faceKind f = .external i
  face_torusSeam : ∀ f c b, faceKind f = .torusSeam c b →
    face f = range (fun t => (S.torusSeam c).collar (t, 0)) ∧ S.torusSide c b = some (faceOwner f)
  torusSeam_face : ∀ c b k, S.torusSide c b = some k →
    ∃ f, faceOwner f = k ∧ faceKind f = .torusSeam c b
  face_sphereSeam : ∀ f c b, faceKind f = .sphereSeam c b →
    face f = range (fun z => (S.sphereSeam c).collar (z, 0)) ∧ S.sphereSide c b = faceOwner f
  sphereSeam_face : ∀ c b, ∃ f, faceOwner f = S.sphereSide c b ∧ faceKind f = .sphereSeam c b

/-- **L11a — rim charts (the JOINT output with the handles).** Corners = handle rims, genuine rim
charts in `W` over the corner charts of the base, rim labels, disjoint targets. -/
structure RimChartLayer (W : CompactCarrier.{u}) (H : EdgeLayer W) (circ : CircleRegion W) where
  handleCorner : Fin H.handleCount → Bool → Fin circ.cornerCount
  handleCorner_bijective : Bijective fun hb : Fin H.handleCount × Bool => handleCorner hb.1 hb.2
  rimChart : Fin H.handleCount → Bool →
    PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) W.model (Circle × (ℝ × ℝ)) W.Carrier ∞
  rim_source : ∀ h b {p}, p ∈ (rimChart h b).source ↔ p.2 ∈ rimBox 2
  rim_proj : ∀ h b p, p ∈ (rimChart h b).source → ∃ hx : rimChart h b p ∈ circ.domain,
    circ.proj ⟨rimChart h b p, hx⟩ = circ.cornerChart (handleCorner h b) p.2
  rim_label : ∀ h b, rimChart h b '' {p | p.2 = (0, 0)} =
    (fun x : ClosedCell 2 => (H.handle h).map (x, iccEnd b)) '' diskRim
  rim_disjoint : ∀ h b h' b', (h, b) ≠ (h', b') →
    Disjoint (rimChart h b).target (rimChart h' b').target

/-- **L9 — handle ends: each end disk is a whole disk in ONE partitioned face.** -/
structure HandleEndLayer (W : CompactCarrier.{u}) {n : ℕ} {E : BoundaryTori W n}
    (V : VertexLayer W) (H : EdgeLayer W) {circ : CircleRegion W} {S : SeamLayer W V circ}
    {O : PortLayer W E V} (F : FaceLayer W E V S O) where
  handleEnd : Fin H.handleCount → Bool → Fin V.vertexCount
  handleFace : Fin H.handleCount → Bool → Fin F.faceCount
  handleFace_owner : ∀ h b, F.faceOwner (handleFace h b) = handleEnd h b
  handleFace_kind : ∀ h b, F.faceKind (handleFace h b) = .partitioned
  handleEnd_face : ∀ h b, (H.handle h).endDisk b ⊆ F.face (handleFace h b)
  endDisk_disjoint : ∀ h b h' b', (h, b) ≠ (h', b') →
    Disjoint ((H.handle h).endDisk b) ((H.handle h').endDisk b')

/-- **L10 — circle-region faces of partitioned faces (arcs, loops), the FC40 inputs.** -/
structure ArcLayer (W : CompactCarrier.{u}) {n : ℕ} {E : BoundaryTori W n} {V : VertexLayer W}
    (H : EdgeLayer W) (circ : CircleRegion W) {S : SeamLayer W V circ} {O : PortLayer W E V}
    (F : FaceLayer W E V S O) (HE : HandleEndLayer W V H F) (K : RimChartLayer W H circ) where
  arcFaceCount : ℕ
  arcFace : Fin arcFaceCount → Set W.Carrier
  arcOwner : Fin arcFaceCount → Fin F.faceCount
  arcOwner_kind : ∀ j, F.faceKind (arcOwner j) = .partitioned
  arcBase : Fin arcFaceCount → Icc (0 : ℝ) 1 → circ.Base
  arcBase_embedding : ∀ j, IsSmoothEmbedding (𝓡∂ 1) (𝓡 2) ∞ (arcBase j)
  arcFace_eq : ∀ j, arcFace j = Subtype.val '' (circ.proj ⁻¹' range (arcBase j))
  arcDefining : Fin arcFaceCount → Fin circ.definingCount
  arcBase_defining : ∀ j t, circ.defining (arcDefining j) (arcBase j t) = 0
  arcAnnulus : Fin arcFaceCount →
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Icc (0 : ℝ) 1 → W.Carrier
  arcAnnulus_continuous : ∀ j, Continuous (arcAnnulus j)
  arcAnnulus_injective : ∀ j, Injective (arcAnnulus j)
  arcAnnulus_range : ∀ j, range (arcAnnulus j) = arcFace j
  arcAnnulus_proj : ∀ j q, ∃ hx : arcAnnulus j q ∈ circ.domain,
    circ.proj ⟨arcAnnulus j q, hx⟩ = arcBase j q.2
  loopFaceCount : ℕ
  loopFace : Fin loopFaceCount → Set W.Carrier
  loopOwner : Fin loopFaceCount → Fin F.faceCount
  loopOwner_kind : ∀ j, F.faceKind (loopOwner j) = .partitioned
  loopBase : Fin loopFaceCount → Circle → circ.Base
  loopBase_embedding : ∀ j, IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (loopBase j)
  loopFace_eq : ∀ j, loopFace j = Subtype.val '' (circ.proj ⁻¹' range (loopBase j))
  loopDefining : Fin loopFaceCount → Fin circ.definingCount
  loopBase_defining : ∀ j z, circ.defining (loopDefining j) (loopBase j z) = 0
  loopFace_closed : ∀ j, IsClosed (loopFace j)
  loopFace_nonempty : ∀ j, (loopFace j).Nonempty
  arcFace_disjoint : Pairwise fun j j' => Disjoint (arcFace j) (arcFace j')
  loopFace_disjoint : Pairwise fun j j' => Disjoint (loopFace j) (loopFace j')
  arc_loop_disjoint : ∀ j j', Disjoint (arcFace j) (loopFace j')
  face_partition : ∀ f, F.faceKind f = .partitioned →
    (⋃ (h : Fin H.handleCount) (b : Bool) (_ : HE.handleFace h b = f), (H.handle h).endDisk b) ∪
      (⋃ (j : Fin arcFaceCount) (_ : arcOwner j = f), arcFace j) ∪
      (⋃ (j : Fin loopFaceCount) (_ : loopOwner j = f), loopFace j) = F.face f
  face_region_inter : ∀ f, F.faceKind f = .partitioned →
    F.face f ∩ circ.region = (⋃ (j : Fin arcFaceCount) (_ : arcOwner j = f), arcFace j) ∪
      (⋃ (j : Fin loopFaceCount) (_ : loopOwner j = f), loopFace j)
  handleArc : Fin H.handleCount → Bool → Fin arcFaceCount
  handleArc_owner : ∀ h b, arcOwner (handleArc h b) = HE.handleFace h b
  handleArc_meets : ∀ h b j, ((H.handle h).endDisk b ∩ arcFace j).Nonempty → handleArc h b = j
  endDisk_loop_disjoint : ∀ h b j, Disjoint ((H.handle h).endDisk b) (loopFace j)
  endDisk_rim : ∀ h b, (fun x : ClosedCell 2 => (H.handle h).map (x, iccEnd b)) '' diskRim =
    (H.handle h).endDisk b ∩ arcFace (handleArc h b)
  arcEnd : Fin arcFaceCount → Bool → Fin H.handleCount × Bool
  arcEnd_arc : ∀ j e, handleArc (arcEnd j e).1 (arcEnd j e).2 = j
  arcEnd_injective : ∀ j, Injective (arcEnd j)
  arcEnd_surjective : ∀ h b, ∃ e, arcEnd (handleArc h b) e = (h, b)
  arcAnnulus_end : ∀ j e, (H.handle (arcEnd j e).1).endDisk (arcEnd j e).2 ∩ arcFace j =
    arcAnnulus j '' {q | q.2 = iccEnd e}
  /-- (moved here from the rim block: it mentions both the arcs and the corners) -/
  arcBase_end : ∀ j e, arcBase j (iccEnd e) =
    circ.cornerChart (K.handleCorner (arcEnd j e).1 (arcEnd j e).2) (0, 0)

/-- **L11b — the rim region (RIMBOX-1, set part): on the WHOLE rim box, vertex ⇔ y ≤ 0,
handle ⇔ y ≥ 0 ∧ x ≤ 0, circle region ⇔ x, y ≥ 0.** -/
structure RimRegionLayer (W : CompactCarrier.{u}) {n : ℕ} {E : BoundaryTori W n}
    (V : VertexLayer W) (H : EdgeLayer W) (circ : CircleRegion W) {S : SeamLayer W V circ}
    {O : PortLayer W E V} {F : FaceLayer W E V S O} (HE : HandleEndLayer W V H F)
    (K : RimChartLayer W H circ) : Prop where
  rim_vertex : ∀ h b {p}, p ∈ (K.rimChart h b).source →
    (K.rimChart h b p ∈ (V.vertex (HE.handleEnd h b)).image ↔ p.2.2 ≤ 0)
  rim_handle : ∀ h b {p}, p ∈ (K.rimChart h b).source →
    (K.rimChart h b p ∈ range (H.handle h).map ↔ (0 ≤ p.2.2 ∧ p.2.1 ≤ 0))
  rim_region : ∀ h b {p}, p ∈ (K.rimChart h b).source →
    (K.rimChart h b p ∈ circ.region ↔ (0 ≤ p.2.1 ∧ 0 ≤ p.2.2))

/-- **L12 — protection of every port and every whole seam collar from every operation support.** -/
structure ProtectionLayer (W : CompactCarrier.{u}) {n : ℕ} (E : BoundaryTori W n)
    {V : VertexLayer W} (H : EdgeLayer W) (circ : CircleRegion W) (S : SeamLayer W V circ)
    (K : RimChartLayer W H circ) : Prop where
  external_region_disjoint : ∀ i, Disjoint (E.collar i).target circ.region
  external_handle_disjoint : ∀ i h, Disjoint (E.collar i).target (range (H.handle h).map)
  external_edgeCircle_disjoint : ∀ i e,
    Disjoint (E.collar i).target (range (H.edgeCircle e).piece.map)
  external_torusSeam_disjoint : ∀ i c,
    Disjoint (E.collar i).target (S.torusSeam c).collar.target
  external_sphereSeam_disjoint : ∀ i c,
    Disjoint (E.collar i).target (S.sphereSeam c).collar.target
  rim_external_disjoint : ∀ h b i, Disjoint (K.rimChart h b).target (E.collar i).target
  rim_torusSeam_disjoint : ∀ h b c, Disjoint (K.rimChart h b).target (S.torusSeam c).collar.target
  rim_sphereSeam_disjoint : ∀ h b c,
    Disjoint (K.rimChart h b).target (S.sphereSeam c).collar.target
  sphereSeam_region_disjoint : ∀ c, Disjoint (S.sphereSeam c).collar.target circ.region
  sphereSeam_handle_disjoint : ∀ c h,
    Disjoint (S.sphereSeam c).collar.target (range (H.handle h).map)

/-- **Reassembly** of a certificate from its layers (the record of the dry producer §4, without any
stub). -/
def ofLayers {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (V : VertexLayer W)
    (H : EdgeLayer W) (circ : CircleRegion W) (O : PortLayer W E V) (S : SeamLayer W V circ)
    (F : FaceLayer W E V S O) (HE : HandleEndLayer W V H F) (K : RimChartLayer W H circ)
    (A : ArcLayer W H circ F HE K) (Cv : CoverLayer W V H circ) (Vt : VerticalLayer W H circ)
    (RR : RimRegionLayer W V H circ HE K) (Pr : ProtectionLayer W E H circ S K) :
    DecompositionCertificate W E :=
  { external_exhausted := O.external_exhausted
    vertexCount := V.vertexCount
    vertex := V.vertex
    handleCount := H.handleCount
    handle := H.handle
    edgeCircleCount := H.edgeCircleCount
    edgeCircle := H.edgeCircle
    circ := circ
    cover := Cv.cover
    vertex_disjoint := Cv.vertex_disjoint
    handle_disjoint := Cv.handle_disjoint
    edgeCircle_disjoint := Cv.edgeCircle_disjoint
    vertex_handle_disjoint := Cv.vertex_handle_disjoint
    edgeCircle_vertex_disjoint := Cv.edgeCircle_vertex_disjoint
    edgeCircle_handle_disjoint := Cv.edgeCircle_handle_disjoint
    circ_vertex_disjoint := Cv.circ_vertex_disjoint
    circ_handle_disjoint := Cv.circ_handle_disjoint
    circ_edgeCircle_disjoint := Cv.circ_edgeCircle_disjoint
    vertical_fibre := Vt.vertical_fibre
    edgeCircle_vertical := Vt.edgeCircle_vertical
    torusSeamCount := S.torusSeamCount
    torusSeam := S.torusSeam
    torusSide := S.torusSide
    torusSide_neg := S.torusSide_neg
    torusSide_pos := S.torusSide_pos
    torusSeam_disjoint := S.torusSeam_disjoint
    sphereSeamCount := S.sphereSeamCount
    sphereSeam := S.sphereSeam
    sphereSide := S.sphereSide
    sphereSide_neg := S.sphereSide_neg
    sphereSide_pos := S.sphereSide_pos
    sphereSeam_disjoint := S.sphereSeam_disjoint
    sphere_torus_seam_disjoint := S.sphere_torus_seam_disjoint
    externalOwner := O.externalOwner
    external_owned := O.external_owned
    faceCount := F.faceCount
    face := F.face
    faceOwner := F.faceOwner
    faceModel := F.faceModel
    face_exhausted := F.face_exhausted
    faceKind := F.faceKind
    face_disjoint := F.face_disjoint
    face_external := F.face_external
    external_face := F.external_face
    face_torusSeam := F.face_torusSeam
    torusSeam_face := F.torusSeam_face
    face_sphereSeam := F.face_sphereSeam
    sphereSeam_face := F.sphereSeam_face
    handleEnd := HE.handleEnd
    handleFace := HE.handleFace
    handleFace_owner := HE.handleFace_owner
    handleFace_kind := HE.handleFace_kind
    handleEnd_face := HE.handleEnd_face
    endDisk_disjoint := HE.endDisk_disjoint
    arcFaceCount := A.arcFaceCount
    arcFace := A.arcFace
    arcOwner := A.arcOwner
    arcOwner_kind := A.arcOwner_kind
    arcBase := A.arcBase
    arcBase_embedding := A.arcBase_embedding
    arcFace_eq := A.arcFace_eq
    arcDefining := A.arcDefining
    arcBase_defining := A.arcBase_defining
    arcAnnulus := A.arcAnnulus
    arcAnnulus_continuous := A.arcAnnulus_continuous
    arcAnnulus_injective := A.arcAnnulus_injective
    arcAnnulus_range := A.arcAnnulus_range
    arcAnnulus_proj := A.arcAnnulus_proj
    loopFaceCount := A.loopFaceCount
    loopFace := A.loopFace
    loopOwner := A.loopOwner
    loopOwner_kind := A.loopOwner_kind
    loopBase := A.loopBase
    loopBase_embedding := A.loopBase_embedding
    loopFace_eq := A.loopFace_eq
    loopDefining := A.loopDefining
    loopBase_defining := A.loopBase_defining
    loopFace_closed := A.loopFace_closed
    loopFace_nonempty := A.loopFace_nonempty
    arcFace_disjoint := A.arcFace_disjoint
    loopFace_disjoint := A.loopFace_disjoint
    arc_loop_disjoint := A.arc_loop_disjoint
    face_partition := A.face_partition
    face_region_inter := A.face_region_inter
    handleArc := A.handleArc
    handleArc_owner := A.handleArc_owner
    handleArc_meets := A.handleArc_meets
    endDisk_loop_disjoint := A.endDisk_loop_disjoint
    endDisk_rim := A.endDisk_rim
    arcEnd := A.arcEnd
    arcEnd_arc := A.arcEnd_arc
    arcEnd_injective := A.arcEnd_injective
    arcEnd_surjective := A.arcEnd_surjective
    arcAnnulus_end := A.arcAnnulus_end
    handleCorner := K.handleCorner
    handleCorner_bijective := K.handleCorner_bijective
    arcBase_end := A.arcBase_end
    rimChart := K.rimChart
    rim_source := K.rim_source
    rim_proj := K.rim_proj
    rim_vertex := RR.rim_vertex
    rim_handle := RR.rim_handle
    rim_region := RR.rim_region
    rim_label := K.rim_label
    rim_disjoint := K.rim_disjoint
    external_region_disjoint := Pr.external_region_disjoint
    external_handle_disjoint := Pr.external_handle_disjoint
    external_edgeCircle_disjoint := Pr.external_edgeCircle_disjoint
    external_torusSeam_disjoint := Pr.external_torusSeam_disjoint
    external_sphereSeam_disjoint := Pr.external_sphereSeam_disjoint
    rim_external_disjoint := Pr.rim_external_disjoint
    rim_torusSeam_disjoint := Pr.rim_torusSeam_disjoint
    rim_sphereSeam_disjoint := Pr.rim_sphereSeam_disjoint
    sphereSeam_region_disjoint := Pr.sphereSeam_region_disjoint
    sphereSeam_handle_disjoint := Pr.sphereSeam_handle_disjoint }

/-- The rim-product clause of a reassembled certificate is the clause on its rim chart layer. -/
theorem ofLayers_rimProduct_iff {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}
    {V : VertexLayer W} {H : EdgeLayer W} {circ : CircleRegion W} {O : PortLayer W E V}
    {S : SeamLayer W V circ} {F : FaceLayer W E V S O} {HE : HandleEndLayer W V H F}
    {K : RimChartLayer W H circ} {A : ArcLayer W H circ F HE K} {Cv : CoverLayer W V H circ}
    {Vt : VerticalLayer W H circ} {RR : RimRegionLayer W V H circ HE K}
    {Pr : ProtectionLayer W E H circ S K} :
    (ofLayers V H circ O S F HE K A Cv Vt RR Pr).RimProduct ↔
      ∀ h b, RimProductAt (K.rimChart h b) (H.handle h) b :=
  Iff.rfl

end GC.GraphManifold.Assembly.FC39P0
