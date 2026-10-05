import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Corners

/-!
# FC39 GROUP G: global face functions V2 (local canonical germs) and the prepared rows V2

External draft 58 §2.1–§2.2, lead disposition D58-1 (lane FC39-G-GFF). The field
`GlobalFaceFunctions.canonical_near_corner` asks the canonical equations `fn (vertical) = −X`,
`fn (horizontal) = −Y_e` on the WHOLE raw tube base `Rw.labelledTubes.base e`. That is too strong:
two raw tubes of different vertical labels may extend into the same slim piece (draft §2.1, the model
`S² × (ℝ/4ℤ)`, scratch note `build-logs/scratch/FC39-G-GFF/counterexample-S2xR4Z.md`), and then two
distinct functions share value and differential on an open set meeting every open `base ⊇ C₁`,
against `double_independent`. The repair is the LOCAL form of §2.2; since it is implied by the old
field, it goes into NEW structures (the accepted ones are untouched):

* `GlobalFaceFunctionsV2 Rw` — the fields of `GlobalFaceFunctions` with `canonical_near_corner`
  replaced by: for every actual endpoint `e` an open `V ∋ rimBase e` inside `base ∩ V_e` on which the
  two canonical equations hold;
* `GlobalFaceFunctions.toV2` — the forgetful map (old field ⇒ new field, `V = base ∩ V_e`; the rim
  base point lies in `C₁ ⊆ base` by `rimBase_mem_cbase_GGFF`);
* `FC39PreparedV2`, `FC39Prepared.toV2`;
* `GlobalFaceLinkV2`, `LabelledCornerCompatibilityV2` — the downstream structures indexed by the
  prepared rows, with the same fields; they read only `base`, `Face`, `actualFace`, `fn` of the global
  face functions, so every old object is an instance through the forgetful map
  (`GlobalFaceLink.toV2`, `LabelledCornerCompatibility.toV2`, all fields definitionally the old ones).
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

/-! ## The rim base points lie in the closed circle base -/

/-- Every point of the base of a circle bundle is the projection of a point (the trivialization). -/
theorem CircleBundle.proj_surjective_GGFF (R : CircleBundle W) : Surjective R.proj := fun c =>
  ⟨((R.trivialization c).symm (⟨c, R.mem_neighborhood c⟩, 1)).val, by
    rw [← R.projection_trivialization c ((R.trivialization c).symm (⟨c, R.mem_neighborhood c⟩, 1)),
      Diffeomorph.apply_symm_apply]⟩

/-- **The rim base point of an actual endpoint lies in `C₁`** (the region side equality of the
labelled tube at the centre `(0, 0)` of its chart). -/
theorem FC39RowsV2.rimBase_mem_cbase_GGFF (Rw : FC39RowsV2 W E) (e : Rw.edge.EdgeEnd) :
    Rw.junctions.rimBase e.1 ∈ Rw.circle.cbase := by
  obtain ⟨x, hx⟩ := Rw.circle.proj_surjective_GGFF (Rw.junctions.rimBase e.1)
  have hmem : Rw.circle.proj x ∈ Rw.labelledTubes.base e := by
    rw [hx]
    exact Rw.labelledTubes.rimBase_mem e
  have hreg := (Rw.labelledTubes.region_side hmem).2
  rw [hx, Rw.labelledTubes.chart_center e] at hreg
  obtain ⟨y, hy, hyx⟩ := hreg ⟨le_rfl, le_rfl⟩
  rw [← hx, ← Subtype.ext hyx]
  exact hy

/-! ## Global face functions V2 -/

/-- **§2.2 Global defining functions per actual face, V2** (D58-1): the fields of
`GlobalFaceFunctions` with the canonical equations required only on SOME open neighbourhood of each
rim base point inside `base ∩ V_e`. -/
structure GlobalFaceFunctionsV2 (Rw : FC39RowsV2 W E) where
  base : TopologicalSpace.Opens Rw.circle.Base
  cbase_subset : Rw.circle.cbase ⊆ base
  Face : Type u
  finite : Finite Face
  actualFace : Face ≃ Rw.CircleFace
  fn : Face → Rw.circle.Base → ℝ
  smooth : ∀ f, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fn f) base
  zero_regular : ∀ f, ∀ c ∈ base, fn f c = 0 → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fn f) c ≠ 0
  base_eq : Rw.circle.cbase = {c | c ∈ base ∧ ∀ f, fn f c ≤ 0}
  face_eq : ∀ f, {c | c ∈ Rw.circle.cbase ∧ fn f c = 0} = Rw.baseTrace (actualFace f)
  depth_le_two : ∀ c ∈ base, Set.ncard {f | fn f c = 0} ≤ 2
  double_independent : ∀ c ∈ base, ∀ f f', f ≠ f' → fn f c = 0 → fn f' c = 0 →
    Surjective fun w : TangentSpace (𝓡 2) c =>
      (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fn f) c w, mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fn f') c w)
  double_registered : ∀ c ∈ base, ∀ f f', f ≠ f' → fn f c = 0 → fn f' c = 0 →
    ∃ e : Rw.edge.EdgeEnd, c = Rw.junctions.rimBase e.1 ∧
      ((actualFace f = .vertical e.component ∧
          actualFace f' = .horizontal (Rw.junctions.horizontal e)) ∨
        (actualFace f = .horizontal (Rw.junctions.horizontal e) ∧
          actualFace f' = .vertical e.component)) ∧
      ∀ f'', f'' ≠ f → f'' ≠ f' → fn f'' c < 0
  canonical_near_corner : ∀ e : Rw.edge.EdgeEnd,
    ∃ V : TopologicalSpace.Opens Rw.circle.Base,
      Rw.junctions.rimBase e.1 ∈ V ∧
      (V : Set Rw.circle.Base) ⊆
        (base : Set Rw.circle.Base) ∩ (Rw.labelledTubes.base e : Set Rw.circle.Base) ∧
      ∀ c ∈ V,
        fn (actualFace.symm (.vertical e.component)) c = -(Rw.labelledTubes.chart e c).1 ∧
          fn (actualFace.symm (.horizontal (Rw.junctions.horizontal e))) c =
            -(Rw.labelledTubes.chart e c).2

/-- **The forgetful map V1 → V2**: the old canonical field on the whole raw tube base gives the
local one with `V = base ∩ V_e`. -/
def GlobalFaceFunctions.toV2 {Rw : FC39RowsV2 W E} (GF : GlobalFaceFunctions Rw) :
    GlobalFaceFunctionsV2 Rw where
  base := GF.base
  cbase_subset := GF.cbase_subset
  Face := GF.Face
  finite := GF.finite
  actualFace := GF.actualFace
  fn := GF.fn
  smooth := GF.smooth
  zero_regular := GF.zero_regular
  base_eq := GF.base_eq
  face_eq := GF.face_eq
  depth_le_two := GF.depth_le_two
  double_independent := GF.double_independent
  double_registered := GF.double_registered
  canonical_near_corner e :=
    ⟨GF.base ⊓ Rw.labelledTubes.base e,
      ⟨GF.cbase_subset (Rw.rimBase_mem_cbase_GGFF e), Rw.labelledTubes.rimBase_mem e⟩,
      subset_rfl, fun c hc => GF.canonical_near_corner e c hc.2⟩

/-- The canonical neighbourhood of `GF.toV2` is `base ∩ V_e` (the forgetful map loses nothing). -/
theorem GlobalFaceFunctions.toV2_canonical_witness {Rw : FC39RowsV2 W E}
    (GF : GlobalFaceFunctions Rw) (e : Rw.edge.EdgeEnd) :
    ∃ V : TopologicalSpace.Opens Rw.circle.Base,
      (V : Set Rw.circle.Base) = (GF.base : Set Rw.circle.Base) ∩ Rw.labelledTubes.base e ∧
      Rw.junctions.rimBase e.1 ∈ V ∧
      ∀ c ∈ V,
        GF.toV2.fn (GF.toV2.actualFace.symm (.vertical e.component)) c =
            -(Rw.labelledTubes.chart e c).1 ∧
          GF.toV2.fn (GF.toV2.actualFace.symm (.horizontal (Rw.junctions.horizontal e))) c =
            -(Rw.labelledTubes.chart e c).2 :=
  ⟨GF.base ⊓ Rw.labelledTubes.base e, rfl,
    ⟨GF.cbase_subset (Rw.rimBase_mem_cbase_GGFF e), Rw.labelledTubes.rimBase_mem e⟩,
    fun c hc => GF.canonical_near_corner e c hc.2⟩

/-- **The prepared rows V2**: the raw rows and the global face functions V2. -/
structure FC39PreparedV2 (W : CompactCarrier.{u}) {n : ℕ} (E : BoundaryTori W n) where
  rows : FC39RowsV2 W E
  globalFaces : GlobalFaceFunctionsV2 rows

/-- The forgetful map of the prepared rows. -/
def FC39Prepared.toV2 (Pr : FC39Prepared W E) : FC39PreparedV2 W E where
  rows := Pr.rows
  globalFaces := Pr.globalFaces.toV2

@[simp] theorem FC39Prepared.toV2_rows (Pr : FC39Prepared W E) : Pr.toV2.rows = Pr.rows :=
  rfl

@[simp] theorem FC39Prepared.toV2_globalFaces (Pr : FC39Prepared W E) :
    Pr.toV2.globalFaces = Pr.globalFaces.toV2 :=
  rfl

/-! ## The downstream structures V2 -/

/-- **`GlobalFaceLinkV2`** (= `GlobalFaceLink` over V2): the defining functions of the final circle
region are the global face functions through `ι`, under a bijection of indices. -/
structure GlobalFaceLinkV2 {Rw : FC39RowsV2 W E} (GF : GlobalFaceFunctionsV2 Rw)
    (circ : CircleRegion W) (L : CircleRestrictionLink Rw.circle circ) where
  range_subset : range L.ι ⊆ GF.base
  faceIndex : Fin circ.definingCount ≃ GF.Face
  defining_eq : ∀ i c, circ.defining i c = GF.fn (faceIndex i) (L.ι c)

/-- The actual face of a defining function (derived from `faceIndex`). -/
def GlobalFaceLinkV2.faceOfDefining {Rw : FC39RowsV2 W E} {GF : GlobalFaceFunctionsV2 Rw}
    {circ : CircleRegion W} {L : CircleRestrictionLink Rw.circle circ}
    (G : GlobalFaceLinkV2 GF circ L) (i : Fin circ.definingCount) : Rw.CircleFace :=
  GF.actualFace (G.faceIndex i)

/-- The old link is a V2 link through the forgetful map. -/
def GlobalFaceLink.toV2 {Rw : FC39RowsV2 W E} {GF : GlobalFaceFunctions Rw}
    {circ : CircleRegion W} {L : CircleRestrictionLink Rw.circle circ}
    (G : GlobalFaceLink GF circ L) : GlobalFaceLinkV2 GF.toV2 circ L where
  range_subset := G.range_subset
  faceIndex := G.faceIndex
  defining_eq := G.defining_eq

@[simp] theorem GlobalFaceLink.toV2_faceOfDefining {Rw : FC39RowsV2 W E}
    {GF : GlobalFaceFunctions Rw} {circ : CircleRegion W}
    {L : CircleRestrictionLink Rw.circle circ} (G : GlobalFaceLink GF circ L)
    (i : Fin circ.definingCount) : G.toV2.faceOfDefining i = G.faceOfDefining i :=
  rfl

/-- **`LabelledCornerCompatibilityV2`** (= `LabelledCornerCompatibility` over the prepared rows V2;
same fields, the global face link is `GlobalFaceLinkV2`). -/
structure LabelledCornerCompatibilityV2 (Pr : FC39PreparedV2 W E) (H : EdgeLayer W)
    (circ : CircleRegion W) (K : RimChartLayer W H circ) where
  edgeLink : EdgeComponentsLink Pr.rows.edge Pr.rows.edgeModels H
  circleLink : CircleRestrictionLink Pr.rows.circle circ
  globalFaces : GlobalFaceLinkV2 Pr.globalFaces circ circleLink
  endOfCorner : Fin circ.cornerCount ≃ Pr.rows.edge.EdgeEnd
  corner_center : ∀ k,
    circleLink.ι (circ.cornerChart k (0, 0)) = Pr.rows.junctions.rimBase (endOfCorner k).1
  endpoint_label : ∀ h b, edgeLink.endOfHandle h b = endOfCorner (K.handleCorner h b)
  first_label : ∀ h b, globalFaces.faceOfDefining (circ.cornerFirst (K.handleCorner h b)) =
    .vertical (edgeLink.componentOfHandle h)
  second_label : ∀ h b, globalFaces.faceOfDefining (circ.cornerSecond (K.handleCorner h b)) =
    .horizontal (Pr.rows.junctions.horizontal (edgeLink.endOfHandle h b))
  height_eq : ∀ h b p, p ∈ (K.rimChart h b).source →
    ∃ hx : K.rimChart h b p ∈ Pr.rows.edge.source,
      Pr.rows.edge.height ⟨K.rimChart h b p, hx⟩ - Pr.rows.edge.level =
        circ.cornerScale (K.handleCorner h b) * p.2.1
  horizontal_eq : ∀ h b p, p ∈ (K.rimChart h b).source →
    Pr.rows.slim.residualFn (Pr.rows.junctions.horizontal (edgeLink.endOfHandle h b))
      (K.rimChart h b p) = circ.cornerScale (K.handleCorner h b) * p.2.2
  target_full : ∀ h b, (K.rimChart h b).target =
    Subtype.val '' (circ.proj ⁻¹' (circ.cornerChart (K.handleCorner h b)).target)
  target_in_raw_tube : ∀ h b,
    (K.rimChart h b).target ⊆ Pr.rows.labelledTubes.tube (edgeLink.endOfHandle h b)

/-- The vertex owner of the end `b` of the handle `h`, read from the actual horizontal label. -/
def LabelledCornerCompatibilityV2.handleEndOwner {Pr : FC39PreparedV2 W E} {H : EdgeLayer W}
    {circ : CircleRegion W} {K : RimChartLayer W H circ}
    (L : LabelledCornerCompatibilityV2 Pr H circ K) (h : Fin H.handleCount) (b : Bool) :
    Pr.rows.slim.RowIndex :=
  Pr.rows.slim.residualOwner (Pr.rows.junctions.horizontal (L.edgeLink.endOfHandle h b))

/-- **The old labelled compatibility is a V2 one** through the forgetful map (all fields are the old
ones). -/
def LabelledCornerCompatibility.toV2 {Pr : FC39Prepared W E} {H : EdgeLayer W}
    {circ : CircleRegion W} {K : RimChartLayer W H circ}
    (L : LabelledCornerCompatibility Pr H circ K) : LabelledCornerCompatibilityV2 Pr.toV2 H circ K where
  edgeLink := L.edgeLink
  circleLink := L.circleLink
  globalFaces := L.globalFaces.toV2
  endOfCorner := L.endOfCorner
  corner_center := L.corner_center
  endpoint_label := L.endpoint_label
  first_label := L.first_label
  second_label := L.second_label
  height_eq := L.height_eq
  horizontal_eq := L.horizontal_eq
  target_full := L.target_full
  target_in_raw_tube := L.target_in_raw_tube

@[simp] theorem LabelledCornerCompatibility.toV2_edgeLink {Pr : FC39Prepared W E}
    {H : EdgeLayer W} {circ : CircleRegion W} {K : RimChartLayer W H circ}
    (L : LabelledCornerCompatibility Pr H circ K) : L.toV2.edgeLink = L.edgeLink :=
  rfl

@[simp] theorem LabelledCornerCompatibility.toV2_circleLink {Pr : FC39Prepared W E}
    {H : EdgeLayer W} {circ : CircleRegion W} {K : RimChartLayer W H circ}
    (L : LabelledCornerCompatibility Pr H circ K) : L.toV2.circleLink = L.circleLink :=
  rfl

theorem LabelledCornerCompatibility.toV2_handleEndOwner {Pr : FC39Prepared W E}
    {H : EdgeLayer W} {circ : CircleRegion W} {K : RimChartLayer W H circ}
    (L : LabelledCornerCompatibility Pr H circ K) (h : Fin H.handleCount) (b : Bool) :
    L.toV2.handleEndOwner h b = L.handleEndOwner h b :=
  rfl

end GC.GraphManifold.Assembly.FC39P0
