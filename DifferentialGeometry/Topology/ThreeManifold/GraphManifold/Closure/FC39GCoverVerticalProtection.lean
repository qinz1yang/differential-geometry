import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0FixOwner
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GVertexPortLayers

/-!
# FC39 GROUP G, target `stub_cover_vertical_protection` split in three (lane FC39-G-CVP)

The frozen target `T:359–366` (`docs/geometrization/chapter14/evidence/fc39-p0/Targets.lean.txt`),
split as decided in D56-7 (dispositions of external review 56) into three lemmas, each reading only
the data and links it needs:

* **cover** `coverLayer_of_links_GCVP` — from the rows' junctions (`cover`, `interiors_disjoint`),
  a vertex link, an edge components link and a circle restriction link; the adapted form
  `coverLayer_of_adapted_GCVP` takes the links of the SAME adapted package (`A.components`,
  `A.circle`, which `components_eq` / `circle_eq` identify with the labelled links);
* **vertical** `verticalLayer_of_links_GCVP` — every handle rim slice is a whole circle fibre of the
  final circle region: the slice rim is the whole rim of the edge bundle (`handle_rim`), that is a
  whole row fibre (`rim_fibre`); a rim point lies in the vertical face, hence in the region, hence
  in the domain of the final region, so the row fibre is the full preimage of one point of the
  final base (`CircleRestrictionLink.domain_eq`, `proj_eq`, injectivity of `ι`); the boundary of an
  edge-circle piece consists of whole rims, hence lies in the region (`edge_region`);
* **protection** `protectionLayer_of_adapted_GCVP` — from the SAME adapted package, the seam–face
  link and the prescribed safe neighbourhoods, which are an INPUT (never the final protection layer):
  rims lie in the closures of the safe corner tubes (`rim_closure_in_safe`), whose closures avoid
  the ports and the shared-face neighbourhoods; seam collars lie in the shared-face neighbourhoods
  (`torus_closure` / `sphere_closure`), whose closures avoid the ports, the region and the edge piece
  (`SharedSafe`); a port collar is open and lies in its cusp core, hence in the core's interior, so
  it misses the region (`region_eq`: `R = M₃ ⊆ M₁`) and every handle / edge-circle piece (a point of a
  full-rank image in an open set gives a point of that set in the interior of the image,
  `exists_mem_inter_interior_range`, then `interiors_disjoint`).

`cover_vertical_protection_GCVP` is the frozen statement, from the three lemmas. Nothing here reads
`Pr.globalFaces`: `Pr` enters only through `Pr.rows` and the type of the adapted package.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

local instance diskCharts_GCVP : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmooth_GCVP : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

/-! ## Elementary facts on the rows and the links -/

/-- A handle linked to the components lies in the edge piece. -/
theorem EdgeComponentsLink.range_handle_subset_edgePiece_GCVP {P : EdgeBundle W}
    {M : EdgeComponentModels P} {H : EdgeLayer W} (L : EdgeComponentsLink P M H)
    (h : Fin H.handleCount) : range (H.handle h).map ⊆ P.edgePiece := by
  rw [← L.iUnion_ranges_eq_edgePiece]
  exact fun x hx => Or.inl (mem_iUnion.2 ⟨h, hx⟩)

/-- An edge-circle piece linked to the components lies in the edge piece. -/
theorem EdgeComponentsLink.range_edgeCircle_subset_edgePiece_GCVP {P : EdgeBundle W}
    {M : EdgeComponentModels P} {H : EdgeLayer W} (L : EdgeComponentsLink P M H)
    (j : Fin H.edgeCircleCount) : range (H.edgeCircle j).piece.map ⊆ P.edgePiece := by
  rw [← L.iUnion_ranges_eq_edgePiece]
  exact fun x hx => Or.inr (mem_iUnion.2 ⟨j, hx⟩)

/-- Every fibre of a circle bundle is nonempty (from the local trivialization). -/
theorem CircleBundle.fibre_nonempty_GCVP (R : CircleBundle W) (c : R.Base) :
    (R.fibre c).Nonempty := by
  let x := (R.trivialization c).symm (⟨c, R.mem_neighborhood c⟩, (1 : Circle))
  have h := R.projection_trivialization c x
  rw [show R.trivialization c x = (⟨c, R.mem_neighborhood c⟩, (1 : Circle)) from
    (R.trivialization c).apply_symm_apply _] at h
  exact ⟨x.1.1, x.1, h.symm, rfl⟩

/-- The rim over a point of `C₂` lies in the vertical face. -/
theorem EdgeBundle.rim_subset_vertical_GCVP (P : EdgeBundle W) {c : P.Base} (hc : c ∈ P.cbase) :
    P.rim c ⊆ P.vertical := by
  rintro _ ⟨x, ⟨hx, hx'⟩, rfl⟩
  exact ⟨x, ⟨hx ▸ hc, hx'⟩, rfl⟩

/-- The vertical face lies in the row circle region (`edge_region`). -/
theorem FC39RowsV2.vertical_subset_region_GCVP (Rw : FC39RowsV2 W E) :
    Rw.edge.vertical ⊆ Rw.circle.region := by
  rw [← Rw.junctions.edge_region]
  exact inter_subset_right

/-- **Whole fibres under the restriction link.** A whole row fibre through a point of the final
domain is the full preimage of ONE point of the final base. -/
theorem CircleRestrictionLink.exists_fibre_eq_GCVP {R : CircleBundle W} {circ : CircleRegion W}
    (cl : CircleRestrictionLink R circ) {c : R.Base} {x : W.Carrier} (hx : x ∈ R.fibre c)
    (hxd : x ∈ (circ.domain : Set W.Carrier)) :
    ∃ b : circ.Base, Subtype.val '' (circ.proj ⁻¹' {b}) = R.fibre c := by
  obtain ⟨z, hz, rfl⟩ := hx
  obtain ⟨hx', hι⟩ := cl.proj_eq ⟨z.1, hxd⟩
  have hzc : R.proj z = c := hz
  have hcι : c = cl.ι (circ.proj ⟨z.1, hxd⟩) := by
    rw [← hzc, ← hι]
  refine ⟨circ.proj ⟨z.1, hxd⟩, Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨hw', hwι⟩ := cl.proj_eq w
    refine ⟨⟨w.1, hw'⟩, ?_, rfl⟩
    change R.proj ⟨w.1, hw'⟩ = c
    rw [hwι, hcι]
    exact congrArg cl.ι hw
  · rintro _ ⟨w, hw, rfl⟩
    have hwc : R.proj w = c := hw
    have hwd : w.1 ∈ (circ.domain : Set W.Carrier) := by
      rw [cl.domain_eq]
      exact ⟨w, ⟨circ.proj ⟨z.1, hxd⟩, by rw [hwc, hcι]⟩, rfl⟩
    obtain ⟨hw', hwι⟩ := cl.proj_eq ⟨w.1, hwd⟩
    refine ⟨⟨w.1, hwd⟩, ?_, rfl⟩
    apply cl.ι_isOpenEmbedding.injective
    rw [← hwι, ← hcι]
    exact hwc

/-! ## Cover -/

/-- **Cover (kernel).** The cover layer from the rows' junctions, a vertex link, an edge components
link and a circle restriction link. -/
theorem coverLayer_of_links_GCVP (Rw : FC39RowsV2 W E) (V : VertexLayer W)
    (vlink : VertexModelLink Rw V) (H : EdgeLayer W)
    (L : EdgeComponentsLink Rw.edge Rw.edgeModels H) (circ : CircleRegion W)
    (cl : CircleRestrictionLink Rw.circle circ) : CoverLayer W V H circ where
  cover := by
    refine eq_univ_of_forall fun x => ?_
    have hx : x ∈ ⋃ a, allPieces Rw.slim Rw.edge Rw.circle a := by
      rw [Rw.junctions.cover]
      exact mem_univ x
    obtain ⟨a, ha⟩ := mem_iUnion.1 hx
    rcases a with i | (_ | _)
    · refine Or.inl (Or.inl (Or.inl (mem_iUnion.2 ⟨vlink.index.symm i, ?_⟩)))
      rw [vlink.image_eq_G1, Equiv.apply_symm_apply]
      exact ha
    · change x ∈ Rw.circle.region at ha
      rw [← cl.region_eq] at ha
      exact Or.inr ha
    · change x ∈ Rw.edge.edgePiece at ha
      rw [← L.iUnion_ranges_eq_edgePiece] at ha
      rcases ha with h1 | h2
      · exact Or.inl (Or.inl (Or.inr h1))
      · exact Or.inl (Or.inr h2)
  vertex_disjoint k k' hne := by
    change Disjoint (interior (V.vertex k).image) (interior (V.vertex k').image)
    rw [vlink.image_eq_G1, vlink.image_eq_G1]
    exact Rw.junctions.interiors_disjoint (i := .inl (vlink.index k))
      (j := .inl (vlink.index k')) fun h => hne (vlink.index.injective (Sum.inl_injective h))
  handle_disjoint h h' hne :=
    (L.handle_ranges_disjoint_of_components hne).mono interior_subset interior_subset
  edgeCircle_disjoint := L.edgeCircle_ranges_disjoint_of_components
  vertex_handle_disjoint k h := by
    rw [vlink.image_eq_G1]
    exact (Rw.junctions.interiors_disjoint (i := .inl (vlink.index k)) (j := .inr true)
      Sum.inl_ne_inr).mono_right (interior_mono (L.range_handle_subset_edgePiece_GCVP h))
  edgeCircle_vertex_disjoint e k := by
    rw [vlink.image_eq_G1]
    exact (Rw.junctions.interiors_disjoint (i := .inr true) (j := .inl (vlink.index k))
      Sum.inr_ne_inl).mono_left (interior_mono (L.range_edgeCircle_subset_edgePiece_GCVP e))
  edgeCircle_handle_disjoint e h :=
    (L.handle_edgeCircle_disjoint_of_components h e).symm.mono interior_subset interior_subset
  circ_vertex_disjoint k := by
    rw [vlink.image_eq_G1, cl.region_eq]
    exact Rw.junctions.interiors_disjoint (i := .inr false) (j := .inl (vlink.index k))
      Sum.inr_ne_inl
  circ_handle_disjoint h := by
    rw [cl.region_eq]
    exact (Rw.junctions.interiors_disjoint (i := .inr false) (j := .inr true)
      (by simp)).mono_right (interior_mono (L.range_handle_subset_edgePiece_GCVP h))
  circ_edgeCircle_disjoint e := by
    rw [cl.region_eq]
    exact (Rw.junctions.interiors_disjoint (i := .inr false) (j := .inr true)
      (by simp)).mono_right (interior_mono (L.range_edgeCircle_subset_edgePiece_GCVP e))

/-- **Cover (adapted form).** The cover layer of the edge layer and circle region of the adapted
package, through its own links `A.components` and `A.circle`. -/
theorem coverLayer_of_adapted_GCVP (Pr : FC39Prepared W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) (A : AdaptedEdgeRimData Pr safe)
    (V : VertexLayer W) (vlink : VertexModelLink Pr.rows V) : CoverLayer W V A.edges A.circ :=
  coverLayer_of_links_GCVP Pr.rows V vlink A.edges A.components A.circ A.circle

/-! ## Vertical faces -/

/-- **Vertical faces (kernel).** Every handle rim slice is a whole circle fibre of the final circle
region, and the boundary of every edge-circle piece lies in the region. -/
theorem verticalLayer_of_links_GCVP (Rw : FC39RowsV2 W E) (H : EdgeLayer W)
    (L : EdgeComponentsLink Rw.edge Rw.edgeModels H) (circ : CircleRegion W)
    (cl : CircleRestrictionLink Rw.circle circ) : VerticalLayer W H circ where
  vertical_fibre h t := by
    have hc : Rw.edgeModels.intervalBase (L.handleEquiv h) t ∈ Rw.edge.cbase := by
      apply ActualComponent.subset
      rw [← Rw.edgeModels.intervalBase_range]
      exact mem_range_self t
    rw [L.handle_rim h t]
    obtain ⟨x, hx⟩ := Rw.circle.fibre_nonempty_GCVP
      (Rw.junctions.rimBase (Rw.edgeModels.intervalBase (L.handleEquiv h) t))
    have hxr : x ∈ Rw.edge.rim (Rw.edgeModels.intervalBase (L.handleEquiv h) t) := by
      rw [Rw.junctions.rim_fibre _ hc]
      exact hx
    have hxd : x ∈ (circ.domain : Set W.Carrier) := by
      apply circ.region_subset_domain
      rw [cl.region_eq]
      exact Rw.vertical_subset_region_GCVP (Rw.edge.rim_subset_vertical_GCVP hc hxr)
    obtain ⟨b, hb⟩ := cl.exists_fibre_eq_GCVP hx hxd
    exact ⟨b, by rw [Rw.junctions.rim_fibre _ hc, hb]⟩
  edgeCircle_vertical e := by
    rintro _ ⟨q, hq, rfl⟩
    have hz : Rw.edgeModels.circleBase (L.circleEquiv e) ((H.edgeCircle e).proj q) ∈
        Rw.edge.cbase := by
      apply ActualComponent.subset
      rw [← Rw.edgeModels.circleBase_range]
      exact mem_range_self _
    have hr : (H.edgeCircle e).piece.map q ∈
        Rw.edge.rim (Rw.edgeModels.circleBase (L.circleEquiv e) ((H.edgeCircle e).proj q)) := by
      rw [← L.circle_rim]
      exact ⟨q, ⟨rfl, hq⟩, rfl⟩
    rw [cl.region_eq]
    exact Rw.vertical_subset_region_GCVP (Rw.edge.rim_subset_vertical_GCVP hz hr)

/-- **Vertical faces (adapted form).** -/
theorem verticalLayer_of_adapted_GCVP (Pr : FC39Prepared W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) (A : AdaptedEdgeRimData Pr safe) :
    VerticalLayer W A.edges A.circ :=
  verticalLayer_of_links_GCVP Pr.rows A.edges A.components A.circ A.circle

/-! ## Protection -/

/-- A port collar lies in the interior of its cusp core (it is open and inside the core). -/
theorem CuspCores.collar_subset_interior_GCVP (C : CuspCores W E) (i : Fin n) :
    (E.collar i).target ⊆ interior (range (C.piece i).map) :=
  interior_maximal (C.collar_owned i) (E.collar i).open_target

/-- A port collar misses every handle linked to the components: a handle point in the open collar
gives a collar point in the interior of the handle image, hence in the interior of the edge piece,
which is disjoint from the interior of the cusp core. -/
theorem disjoint_collar_handle_GCVP (Rw : FC39RowsV2 W E) {H : EdgeLayer W}
    (L : EdgeComponentsLink Rw.edge Rw.edgeModels H) (i : Fin n) (h : Fin H.handleCount) :
    Disjoint (E.collar i).target (range (H.handle h).map) := by
  refine Set.disjoint_left.2 fun x hx hxh => ?_
  obtain ⟨p, rfl⟩ := hxh
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) = 3 := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
  obtain ⟨w, hwO, hwH⟩ := exists_mem_inter_interior_range (I := (𝓡∂ 2).prod (𝓡∂ 1)) hdim
    (H.handle h).smooth (H.handle h).mfderiv_bijective (E.collar i).open_target hx
  exact Set.disjoint_left.1 (Rw.junctions.interiors_disjoint (i := .inl (.inr (.inl i)))
    (j := .inr true) Sum.inl_ne_inr) (Rw.cusp.collar_subset_interior_GCVP i hwO)
    (interior_mono (L.range_handle_subset_edgePiece_GCVP h) hwH)

/-- A port collar misses every edge-circle piece linked to the components (same argument). -/
theorem disjoint_collar_edgeCircle_GCVP (Rw : FC39RowsV2 W E) {H : EdgeLayer W}
    (L : EdgeComponentsLink Rw.edge Rw.edgeModels H) (i : Fin n) (j : Fin H.edgeCircleCount) :
    Disjoint (E.collar i).target (range (H.edgeCircle j).piece.map) := by
  refine Set.disjoint_left.2 fun x hx hxh => ?_
  obtain ⟨p, rfl⟩ := hxh
  obtain ⟨w, hwO, hwH⟩ := exists_mem_inter_interior_range (I := 𝓡∂ 3) finrank_euclideanSpace_fin
    (H.edgeCircle j).piece.smooth (H.edgeCircle j).piece.mfderiv_bijective
    (E.collar i).open_target hx
  exact Set.disjoint_left.1 (Rw.junctions.interiors_disjoint (i := .inl (.inr (.inl i)))
    (j := .inr true) Sum.inl_ne_inr) (Rw.cusp.collar_subset_interior_GCVP i hwO)
    (interior_mono (L.range_edgeCircle_subset_edgePiece_GCVP j) hwH)

/-- A port collar misses the row circle region: `R = M₃ ⊆ M₁ = (int (Z ∪ C))ᶜ` (`region_eq`), and
the open collar lies in the cusp core. -/
theorem disjoint_collar_region_GCVP (Rw : FC39RowsV2 W E) (i : Fin n) :
    Disjoint (E.collar i).target Rw.circle.region := by
  rw [← Rw.junctions.region_eq]
  refine Set.disjoint_left.2 fun x hx hx3 => ?_
  have h1 : x ∈ regionM1 Rw.zero Rw.cusp := hx3.1.1
  exact h1 (interior_mono (fun y hy => Or.inr (mem_iUnion.2 ⟨i, hy⟩))
    (Rw.cusp.collar_subset_interior_GCVP i hx))

/-- A torus seam collar lies in the closure of its prescribed shared-face neighbourhood. -/
theorem SeamFacesLink.torus_target_subset_GCVP {Rw : FC39RowsV2 W E} {V : VertexLayer W}
    {vlink : VertexModelLink Rw V} {O : PortLayer W E V} {circ : CircleRegion W}
    {S : SeamLayer W V circ} {F : FaceLayer W E V S O}
    {N : Rw.SharedFace → TopologicalSpace.Opens W.Carrier} (sf : SeamFacesLink Rw V vlink O S F N)
    (c : Fin S.torusSeamCount) :
    (S.torusSeam c).collar.target ⊆ closure (N (sf.torusEquiv c).1 : Set W.Carrier) :=
  subset_closure.trans ((sf.torus_closure c).trans subset_closure)

/-- A sphere seam collar lies in the closure of its prescribed shared-face neighbourhood. -/
theorem SeamFacesLink.sphere_target_subset_GCVP {Rw : FC39RowsV2 W E} {V : VertexLayer W}
    {vlink : VertexModelLink Rw V} {O : PortLayer W E V} {circ : CircleRegion W}
    {S : SeamLayer W V circ} {F : FaceLayer W E V S O}
    {N : Rw.SharedFace → TopologicalSpace.Opens W.Carrier} (sf : SeamFacesLink Rw V vlink O S F N)
    (c : Fin S.sphereSeamCount) :
    (S.sphereSeam c).collar.target ⊆ closure (N (sf.sphereEquiv c).1 : Set W.Carrier) :=
  subset_closure.trans ((sf.sphere_closure c).trans subset_closure)

/-- A rim target lies in the closure of the safe corner tube of its endpoint. -/
theorem AdaptedEdgeRimData.rim_target_subset_GCVP {Pr : FC39Prepared W E}
    {safe : ProducerSafeNeighbourhoods Pr.rows} (A : AdaptedEdgeRimData Pr safe)
    (h : Fin A.edges.handleCount) (b : Bool) :
    (A.rims.rimChart h b).target ⊆
      closure (safe.corner (A.labelled.edgeLink.endOfHandle h b)) :=
  subset_closure.trans ((A.rim_closure_in_safe h b).trans subset_closure)

/-- **Protection.** From the SAME adapted package, the seam–face link with the prescribed shared
neighbourhoods `safe.shared`, and the safe corner tubes (an input; the final protection layer is
not a premise). -/
theorem protectionLayer_of_adapted_GCVP (Pr : FC39Prepared W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) (A : AdaptedEdgeRimData Pr safe)
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

/-! ## The frozen target -/

/-- **GROUP G, `stub_cover_vertical_protection` (frozen statement `T:359–366`)**, from the three
lemmas. -/
theorem cover_vertical_protection_GCVP (Pr : FC39Prepared W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) (A : AdaptedEdgeRimData Pr safe)
    (V : VertexLayer W) (vlink : VertexModelLink Pr.rows V)
    (O : PortLayer W E V) (S : SeamLayer W V A.circ) (F : FaceLayer W E V S O)
    (sf : SeamFacesLink Pr.rows V vlink O S F safe.shared) :
    CoverLayer W V A.edges A.circ ∧ VerticalLayer W A.edges A.circ ∧
      ProtectionLayer W E A.edges A.circ S A.rims :=
  ⟨coverLayer_of_adapted_GCVP Pr safe A V vlink, verticalLayer_of_adapted_GCVP Pr safe A,
    protectionLayer_of_adapted_GCVP Pr safe A S sf⟩

end GC.GraphManifold.Assembly.FC39P0
