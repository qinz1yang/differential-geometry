import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GArcResidual
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GTraceRows
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0FixOwnerV2

/-!
# FC39 GROUP G arcs (A2, A7): the faces of the final circle region, end disks and corners

Lane FC39-G-ARC (external draft 58 §四 A2 and A7, disposition D58-5). For adapted edge–rim data
`A` (any), a seam–face link `sf` and ANY handle-end layer `HE`:

* `AdaptedEdgeRimDataV2.defIndex_GARC G` — the defining function of `A.circ` of the actual horizontal
  label `G` (through the ONE label system `faceIndex`, `actualFace`);
* `AdaptedEdgeRimDataV2.mem_traceSet_defIndex_iff_GARC` — its unrounded trace is the set of points of
  `C₁` whose whole fibre lies in the residual face `G`;
* **A2** `AdaptedEdgeRimDataV2.residualSet_inter_region_GARC` — the part of the residual face in the
  circle region is the whole circle preimage of that trace (saturation:
  `FC39RowsV2.residualSet_inter_region_eq_tube_GTR` of lane FC39-G-TRACE);
* the corner point `cornerPt_GARC h b` of the end `(h, b)`: it lies on the trace of the face
  `HE.handleFace h b` (identified by the accepted `face_handleFace_eq_residualSet`), it is a second
  zero there, and conversely every second zero of the trace of a partitioned face is the corner
  point of an end whose handle face is that face (`exists_handle_of_traceBd_GARC`);
* **A7** `AdaptedEdgeRimDataV2.endDisk_inter_region_GARC` — `endDisk ∩ R = ` the whole circle fibre
  over the corner point, which is also the rim (`rim_eq_fibre_GARC`);
* `AdaptedEdgeRimDataV2.face_diff_region_subset_GARC` — the part of a partitioned face off the circle
  region lies in the end disks of the handle ends with that face (`region_boundary`, `edge_faces`).
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
  {Pr : FC39PreparedV2 W E} {safe : ProducerSafeNeighbourhoods Pr.rows}

/-! ## The defining function of a residual label and its trace -/

/-- The defining function of `A.circ` attached to the actual horizontal label `G`. -/
def AdaptedEdgeRimDataV2.defIndex_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (G : Pr.rows.slim.ResidualFace) : Fin A.circ.definingCount :=
  A.labelled.globalFaces.faceIndex.symm (Pr.globalFaces.actualFace.symm (.horizontal G))

theorem AdaptedEdgeRimDataV2.faceOfDefining_defIndex_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (G : Pr.rows.slim.ResidualFace) :
    A.labelled.globalFaces.faceOfDefining (A.defIndex_GARC G) = .horizontal G := by
  unfold GlobalFaceLinkV2.faceOfDefining AdaptedEdgeRimDataV2.defIndex_GARC
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The trace of the defining function of `G`: the points of `C₁` whose whole fibre lies in the
residual face `G`. -/
theorem AdaptedEdgeRimDataV2.mem_traceSet_defIndex_iff_GARC {A : AdaptedEdgeRimDataV2 Pr safe}
    {G : Pr.rows.slim.ResidualFace} {c : A.circ.Base} :
    c ∈ A.circ.traceSet_GARC (A.defIndex_GARC G) ↔
      c ∈ A.circ.cornerBase ∧ A.circ.fibre_GARC c ⊆ Pr.rows.slim.residualSet G := by
  rw [A.labelled.globalFaces.mem_traceSet_iff_GARC, A.faceOfDefining_defIndex_GARC]
  rfl

/-- The whole circle preimage in `A.circ` of a set of its base is the row tube of its image. -/
theorem AdaptedEdgeRimDataV2.tube_eq_GARC (A : AdaptedEdgeRimDataV2 Pr safe) (K : Set A.circ.Base) :
    Subtype.val '' (A.circ.proj ⁻¹' K) = Pr.rows.circle.tube (A.labelled.circleLink.ι '' K) := by
  set Lk := A.labelled.circleLink
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨hx, hpx⟩ := Lk.proj_eq z
    exact ⟨⟨z, hx⟩, ⟨_, hz, hpx.symm⟩, rfl⟩
  · rintro ⟨y, ⟨c, hc, hyc⟩, rfl⟩
    have hyd : (y : W.Carrier) ∈ (A.circ.domain : Set W.Carrier) := by
      rw [Lk.domain_eq]
      exact ⟨y, ⟨c, hyc⟩, rfl⟩
    obtain ⟨hx, hpx⟩ := Lk.proj_eq ⟨y, hyd⟩
    refine ⟨⟨y, hyd⟩, ?_, rfl⟩
    have h1 : Pr.rows.circle.proj ⟨y, hx⟩ = Pr.rows.circle.proj y := rfl
    have : A.circ.proj ⟨y, hyd⟩ = c :=
      Lk.ι_isOpenEmbedding.injective (hpx.symm.trans (h1.trans hyc.symm))
    rw [mem_preimage, this]
    exact hc

/-- **A2 (saturation, on the final circle region).** The part of the residual face `G` in the
circle region is the whole circle preimage of the trace of its defining function. -/
theorem AdaptedEdgeRimDataV2.residualSet_inter_region_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (G : Pr.rows.slim.ResidualFace) :
    Pr.rows.slim.residualSet G ∩ A.circ.region =
      Subtype.val '' (A.circ.proj ⁻¹' A.circ.traceSet_GARC (A.defIndex_GARC G)) := by
  set Lk := A.labelled.circleLink
  rw [Lk.region_eq, Pr.rows.residualSet_inter_region_eq_tube_GTR G, A.tube_eq_GARC]
  congr 1
  ext c'
  constructor
  · intro hc'
    have hcb : c' ∈ Pr.rows.circle.cbase := hc'.1
    have hreg : Pr.rows.circle.fibre c' ⊆ Pr.rows.circle.region :=
      Pr.rows.circle.fibre_subset_region_GTR hcb
    obtain ⟨x, hx⟩ := Pr.rows.circle.fibre_nonempty_GSAFE c'
    have hxr := hreg hx
    rw [← Lk.region_eq] at hxr
    obtain ⟨z, hz, hzx⟩ := hxr
    obtain ⟨hx', hpx'⟩ := Lk.proj_eq z
    obtain ⟨y, hy, hyx⟩ := hx
    have hzy : (⟨z, hx'⟩ : Pr.rows.circle.domain) = y := Subtype.ext (hzx.trans hyx.symm)
    have hc'eq : Lk.ι (A.circ.proj z) = c' := by
      rw [← hpx', hzy]
      exact hy
    refine ⟨A.circ.proj z, ?_, hc'eq⟩
    rw [AdaptedEdgeRimDataV2.mem_traceSet_defIndex_iff_GARC, A.labelled.globalFaces.mem_cornerBase_iff_GARC,
      ← Lk.fibre_eq_GARC, hc'eq]
    exact hc'
  · rintro ⟨c, hc, rfl⟩
    rw [AdaptedEdgeRimDataV2.mem_traceSet_defIndex_iff_GARC, A.labelled.globalFaces.mem_cornerBase_iff_GARC,
      ← Lk.fibre_eq_GARC] at hc
    exact hc

/-! ## Partitioned faces -/

variable {V : VertexLayer W} {vlink : VertexModelLink Pr.rows V} {O : PortLayer W E V}
  {circ' : CircleRegion W} {S : SeamLayer W V circ'} {F : FaceLayer W E V S O}
  {N : Pr.rows.SharedFace → TopologicalSpace.Opens W.Carrier}

/-- The residual label chosen for a partitioned face. -/
def SeamFacesLink.resLabel_GARC (sf : SeamFacesLink Pr.rows V vlink O S F N)
    (f : {f : Fin F.faceCount // F.faceKind f = .partitioned}) : Pr.rows.slim.ResidualFace :=
  (sf.exists_residual_of_partitioned_GARC f.2).choose

theorem SeamFacesLink.face_eq_resLabel_GARC (sf : SeamFacesLink Pr.rows V vlink O S F N)
    (f : {f : Fin F.faceCount // F.faceKind f = .partitioned}) :
    F.face f.1 = Pr.rows.slim.residualSet (sf.resLabel_GARC f) :=
  (sf.exists_residual_of_partitioned_GARC f.2).choose_spec

/-- The trace of a partitioned face: the points of `C₁` whose whole fibre lies in the face. -/
theorem AdaptedEdgeRimDataV2.mem_traceSet_face_iff_GARC {A : AdaptedEdgeRimDataV2 Pr safe}
    (sf : SeamFacesLink Pr.rows V vlink O S F N)
    {f : {f : Fin F.faceCount // F.faceKind f = .partitioned}} {c : A.circ.Base} :
    c ∈ A.circ.traceSet_GARC (A.defIndex_GARC (sf.resLabel_GARC f)) ↔
      c ∈ A.circ.cornerBase ∧ A.circ.fibre_GARC c ⊆ F.face f.1 := by
  rw [AdaptedEdgeRimDataV2.mem_traceSet_defIndex_iff_GARC, sf.face_eq_resLabel_GARC]

/-- **A2 for a partitioned face.** -/
theorem AdaptedEdgeRimDataV2.face_inter_region_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N)
    (f : {f : Fin F.faceCount // F.faceKind f = .partitioned}) :
    F.face f.1 ∩ A.circ.region =
      Subtype.val '' (A.circ.proj ⁻¹' A.circ.traceSet_GARC (A.defIndex_GARC (sf.resLabel_GARC f))) := by
  rw [sf.face_eq_resLabel_GARC]
  exact A.residualSet_inter_region_GARC _

/-- The traces of distinct partitioned faces are disjoint. -/
theorem AdaptedEdgeRimDataV2.traceSet_disjoint_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N)
    {f f' : {f : Fin F.faceCount // F.faceKind f = .partitioned}} (h : f ≠ f') :
    Disjoint (A.circ.traceSet_GARC (A.defIndex_GARC (sf.resLabel_GARC f)))
      (A.circ.traceSet_GARC (A.defIndex_GARC (sf.resLabel_GARC f'))) := by
  refine Set.disjoint_left.2 fun c hc hc' => h ?_
  rw [AdaptedEdgeRimDataV2.mem_traceSet_face_iff_GARC sf] at hc hc'
  obtain ⟨x, hx⟩ := A.circ.fibre_nonempty_GARC c
  exact Subtype.ext (F.eq_of_partitioned_meet_GARC f.2 ⟨x, hc.2 hx, hc'.2 hx⟩)

/-! ## Corner points of the handle ends -/

/-- The corner point of the end `b` of the handle `h`. -/
def AdaptedEdgeRimDataV2.cornerPt_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (h : Fin A.edges.handleCount) (b : Bool) : A.circ.Base :=
  A.circ.cornerChart (A.rims.handleCorner h b) (0, 0)

theorem rimBox_two_zero_GARC : ((0 : ℝ), (0 : ℝ)) ∈ rimBox 2 := by
  simp [rimBox]

theorem AdaptedEdgeRimDataV2.defining_first_cornerPt_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (h : Fin A.edges.handleCount) (b : Bool) :
    A.circ.defining (A.circ.cornerFirst (A.rims.handleCorner h b)) (A.cornerPt_GARC h b) = 0 := by
  unfold AdaptedEdgeRimDataV2.cornerPt_GARC
  rw [A.circ.chart_first _ _ rimBox_two_zero_GARC]
  simp

theorem AdaptedEdgeRimDataV2.defining_second_cornerPt_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (h : Fin A.edges.handleCount) (b : Bool) :
    A.circ.defining (A.circ.cornerSecond (A.rims.handleCorner h b)) (A.cornerPt_GARC h b) = 0 := by
  unfold AdaptedEdgeRimDataV2.cornerPt_GARC
  rw [A.circ.chart_second _ _ rimBox_two_zero_GARC]
  simp

theorem AdaptedEdgeRimDataV2.cornerPt_mem_cornerBase_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (h : Fin A.edges.handleCount) (b : Bool) : A.cornerPt_GARC h b ∈ A.circ.cornerBase := by
  rw [A.circ.cornerBase_eq]
  intro l
  by_cases h1 : l = A.circ.cornerFirst (A.rims.handleCorner h b)
  · rw [h1, A.defining_first_cornerPt_GARC]
  by_cases h2 : l = A.circ.cornerSecond (A.rims.handleCorner h b)
  · rw [h2, A.defining_second_cornerPt_GARC]
  exact (A.circ.chart_other _ l _ h1 h2 rimBox_two_zero_GARC).le

/-- The corner points of distinct ends are distinct. -/
theorem AdaptedEdgeRimDataV2.cornerPt_injective_GARC (A : AdaptedEdgeRimDataV2 Pr safe) :
    Injective fun hb : Fin A.edges.handleCount × Bool => A.cornerPt_GARC hb.1 hb.2 := by
  intro hb hb' heq
  apply A.rims.handleCorner_bijective.injective
  by_contra hne
  have hd := A.circ.cornerChart_disjoint hne
  have hs : ((0 : ℝ), (0 : ℝ)) ∈ (A.circ.cornerChart (A.rims.handleCorner hb.1 hb.2)).source := by
    rw [A.circ.cornerChart_source]
    exact rimBox_two_zero_GARC
  have hs' : ((0 : ℝ), (0 : ℝ)) ∈ (A.circ.cornerChart (A.rims.handleCorner hb'.1 hb'.2)).source := by
    rw [A.circ.cornerChart_source]
    exact rimBox_two_zero_GARC
  refine Set.disjoint_left.1 hd ((A.circ.cornerChart _).map_source hs) ?_
  change A.cornerPt_GARC hb.1 hb.2 ∈ _
  rw [show A.cornerPt_GARC hb.1 hb.2 = A.cornerPt_GARC hb'.1 hb'.2 from heq]
  exact (A.circ.cornerChart _).map_source hs'

/-- The fibre over the corner point lies in the face of `HE` at that end. -/
theorem AdaptedEdgeRimDataV2.fibre_cornerPt_subset_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (HE : HandleEndLayer W V A.edges F)
    (h : Fin A.edges.handleCount) (b : Bool) :
    A.circ.fibre_GARC (A.cornerPt_GARC h b) ⊆ F.face (HE.handleFace h b) := by
  have hmem : A.cornerPt_GARC h b ∈ A.circ.traceSet_GARC
      (A.circ.cornerSecond (A.rims.handleCorner h b)) :=
    ⟨A.cornerPt_mem_cornerBase_GARC h b, A.defining_second_cornerPt_GARC h b⟩
  rw [A.labelled.globalFaces.mem_traceSet_iff_GARC, A.labelled.second_label] at hmem
  rw [A.face_handleFace_eq_residualSet vlink sf HE h b]
  exact hmem.2

/-- The handle face as a partitioned face. -/
def HandleEndLayer.pface_GARC {H : EdgeLayer W} (HE : HandleEndLayer W V H F)
    (h : Fin H.handleCount) (b : Bool) : {f : Fin F.faceCount // F.faceKind f = .partitioned} :=
  ⟨HE.handleFace h b, HE.handleFace_kind h b⟩

/-- **The corner point lies on the trace of the handle face.** -/
theorem AdaptedEdgeRimDataV2.cornerPt_mem_traceSet_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (HE : HandleEndLayer W V A.edges F)
    (h : Fin A.edges.handleCount) (b : Bool) :
    A.cornerPt_GARC h b ∈
      A.circ.traceSet_GARC (A.defIndex_GARC (sf.resLabel_GARC (HE.pface_GARC h b))) := by
  rw [AdaptedEdgeRimDataV2.mem_traceSet_face_iff_GARC sf]
  exact ⟨A.cornerPt_mem_cornerBase_GARC h b, A.fibre_cornerPt_subset_GARC sf HE h b⟩

/-- **The corner point is a second zero of the trace of any horizontal label.** -/
theorem AdaptedEdgeRimDataV2.traceBd_cornerPt_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (G : Pr.rows.slim.ResidualFace) (h : Fin A.edges.handleCount) (b : Bool) :
    A.circ.traceBd_GARC (A.defIndex_GARC G) (A.cornerPt_GARC h b) := by
  refine ⟨A.circ.cornerFirst (A.rims.handleCorner h b), fun heq => ?_,
    A.defining_first_cornerPt_GARC h b⟩
  have h1 := A.labelled.first_label h b
  rw [heq, A.faceOfDefining_defIndex_GARC] at h1
  cases h1

/-- **Conversely**, a second zero of the trace of a partitioned face is the corner point of an end
whose handle face is that face. -/
theorem AdaptedEdgeRimDataV2.exists_handle_of_traceBd_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (HE : HandleEndLayer W V A.edges F)
    (f : {f : Fin F.faceCount // F.faceKind f = .partitioned}) {c : A.circ.Base}
    (hc : c ∈ A.circ.traceSet_GARC (A.defIndex_GARC (sf.resLabel_GARC f)))
    (hbd : A.circ.traceBd_GARC (A.defIndex_GARC (sf.resLabel_GARC f)) c) :
    ∃ hb : Fin A.edges.handleCount × Bool,
      c = A.cornerPt_GARC hb.1 hb.2 ∧ HE.handleFace hb.1 hb.2 = f.1 := by
  obtain ⟨l, hl, hlc⟩ := hbd
  obtain ⟨k, hk⟩ := A.circ.corner_center c _ l hl.symm hc.2 hlc
  obtain ⟨hb, hhb⟩ := A.rims.handleCorner_bijective.surjective k
  have hck : c = A.cornerPt_GARC hb.1 hb.2 := by
    rw [hk, ← hhb]
    rfl
  refine ⟨hb, hck, ?_⟩
  rw [AdaptedEdgeRimDataV2.mem_traceSet_face_iff_GARC sf] at hc
  obtain ⟨x, hx⟩ := A.circ.fibre_nonempty_GARC c
  have hx' := hx
  rw [hck] at hx'
  exact (F.eq_of_partitioned_meet_GARC f.2
    ⟨x, hc.2 hx, A.fibre_cornerPt_subset_GARC sf HE hb.1 hb.2 hx'⟩).symm

/-! ## End disks and the circle region (A7) -/

/-- The row rim of the end `(h, b)` is the fibre of `A.circ` over the corner point. -/
theorem AdaptedEdgeRimDataV2.rimBase_eq_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (h : Fin A.edges.handleCount) (b : Bool) :
    Pr.rows.junctions.rimBase (A.labelled.edgeLink.endOfHandle h b).1 =
      A.labelled.circleLink.ι (A.cornerPt_GARC h b) := by
  rw [A.labelled.endpoint_label, AdaptedEdgeRimDataV2.cornerPt_GARC, A.labelled.corner_center]

theorem AdaptedEdgeRimDataV2.edgeRim_eq_fibre_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (h : Fin A.edges.handleCount) (b : Bool) :
    Pr.rows.edge.rim (A.labelled.edgeLink.endOfHandle h b).1 =
      A.circ.fibre_GARC (A.cornerPt_GARC h b) := by
  rw [Pr.rows.junctions.rim_fibre _ (Pr.rows.edge.mem_cbase_of_edgeEnd_GSAFE _), A.rimBase_eq_GARC,
    A.labelled.circleLink.fibre_eq_GARC]

/-- **The rim of the end `(h, b)` is the whole circle fibre over its corner point.** -/
theorem AdaptedEdgeRimDataV2.rim_eq_fibre_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (h : Fin A.edges.handleCount) (b : Bool) :
    (fun x : ClosedCell 2 => (A.edges.handle h).map (x, iccEnd b)) '' diskRim =
      A.circ.fibre_GARC (A.cornerPt_GARC h b) := by
  rw [A.labelled.edgeLink.handle_rim h (iccEnd b), ← A.edgeRim_eq_fibre_GARC,
    EdgeComponentsLink.endOfHandle, Pr.rows.edgeModels.endpointEquiv_apply]

/-- **A7: `endDisk ∩ R` is the whole fibre over the corner point (the rim).** -/
theorem AdaptedEdgeRimDataV2.endDisk_inter_region_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (h : Fin A.edges.handleCount) (b : Bool) :
    (A.edges.handle h).endDisk b ∩ A.circ.region = A.circ.fibre_GARC (A.cornerPt_GARC h b) := by
  set e := A.labelled.edgeLink.endOfHandle h b
  have he : e.1 ∈ Pr.rows.edge.cbase := Pr.rows.edge.mem_cbase_of_edgeEnd_GSAFE e
  rw [A.labelled.edgeLink.endDisk_eq, A.labelled.circleLink.region_eq, ← A.edgeRim_eq_fibre_GARC]
  apply Subset.antisymm
  · rintro x ⟨hxd, hxr⟩
    have hxv : x ∈ Pr.rows.edge.edgePiece ∩ Pr.rows.circle.region :=
      ⟨Pr.rows.edge.disk_subset_edgePiece_GSAFE he hxd, hxr⟩
    rw [Pr.rows.junctions.edge_region] at hxv
    obtain ⟨y, ⟨-, hyl⟩, rfl⟩ := hxv
    obtain ⟨y', ⟨hy'e, -⟩, hy'⟩ := hxd
    have hyy : y' = y := Subtype.ext hy'
    subst hyy
    exact ⟨y', ⟨hy'e, hyl⟩, rfl⟩
  · intro x hx
    exact ⟨Pr.rows.edge.rim_subset_disk_GSAFE _ hx, Pr.rows.rim_subset_region_GSAFE he hx⟩

/-- **The part of a partitioned face off the circle region lies in the end disks of the handle
ends with that face.** -/
theorem AdaptedEdgeRimDataV2.face_diff_region_subset_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (HE : HandleEndLayer W V A.edges F)
    (f : {f : Fin F.faceCount // F.faceKind f = .partitioned}) :
    F.face f.1 \ A.circ.region ⊆
      ⋃ (h : Fin A.edges.handleCount) (b : Bool) (_ : HE.handleFace h b = f.1),
        (A.edges.handle h).endDisk b := by
  rintro x ⟨hxf, hxr⟩
  have hxG := hxf
  rw [sf.face_eq_resLabel_GARC] at hxG
  set G := sf.resLabel_GARC f
  rw [A.labelled.circleLink.region_eq] at hxr
  have hxB : x ∈ Pr.rows.slim.boundaryM2 := mem_iUnion.2 ⟨G, hxG⟩
  have hxrel : x ∈ relInt Pr.rows.slim.boundaryM2 Pr.rows.edge.horizontalDisks := by
    by_contra hn
    have : x ∈ Pr.rows.circle.region ∩ Pr.rows.slim.boundaryM2 := by
      rw [Pr.rows.junctions.region_boundary]
      exact ⟨hxB, hn⟩
    exact hxr this.1
  obtain ⟨y, hy, rfl⟩ := hxrel
  have hyH : (y : W.Carrier) ∈ Pr.rows.edge.horizontalDisks :=
    (interior_subset hy : y ∈ Subtype.val ⁻¹' Pr.rows.edge.horizontalDisks)
  obtain ⟨e₀, he₀⟩ := mem_iUnion.1 hyH
  have hyP : (y : W.Carrier) ∈ Pr.rows.edge.edgePiece ∩ Pr.rows.slim.residualSet G :=
    ⟨Pr.rows.edge.disk_subset_edgePiece_GSAFE (Pr.rows.edge.mem_cbase_of_edgeEnd_GSAFE e₀) he₀, hxG⟩
  rw [Pr.rows.junctions.edge_faces G] at hyP
  obtain ⟨e', hye'⟩ := mem_iUnion.1 hyP
  obtain ⟨he'G, hye'⟩ := mem_iUnion.1 hye'
  set L := A.labelled.edgeLink
  let ib := Pr.rows.edgeModels.endpointEquiv.symm e'
  let h : Fin A.edges.handleCount := L.handleEquiv.symm ib.1
  have hend : L.endOfHandle h ib.2 = e' := by
    change Pr.rows.edgeModels.endpointEquiv (L.handleEquiv (L.handleEquiv.symm ib.1), ib.2) = e'
    rw [Equiv.apply_symm_apply]
    exact Pr.rows.edgeModels.endpointEquiv.apply_symm_apply e'
  have hface : HE.handleFace h ib.2 = f.1 := by
    have h1 := A.face_handleFace_eq_residualSet vlink sf HE h ib.2
    rw [hend, he'G] at h1
    obtain ⟨z, hz⟩ := sf.face_nonempty_GARC f.1
    refine (F.eq_of_partitioned_meet_GARC f.2 ⟨z, hz, ?_⟩).symm
    rw [h1, ← sf.face_eq_resLabel_GARC]
    exact hz
  refine mem_iUnion.2 ⟨h, mem_iUnion.2 ⟨ib.2, mem_iUnion.2 ⟨hface, ?_⟩⟩⟩
  rw [L.endDisk_eq, hend]
  exact hye'

end GC.GraphManifold.Assembly.FC39P0
