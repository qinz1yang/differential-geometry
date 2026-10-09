import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageGeometryA74

/-!
# Draft 74, package A0, part 2: the cut geometry `H`, the restricted edge and circle bundles

Lane S-JUNCTIONS (suffix `_JN74`). `StageCutGeometry74 A D` (draft 74 §4.1, `H`): the actual
saturation, face identities, regular-closed / collar facts, corner signs and whole-fibre
agreement of the chosen cut — the facts the row lanes produce (EDP04–06, FDC03 / FDC04, ZSP04–05,
BCF01, E3 / E4c, C0, R1). It is layered so that no structure carries more than eight large
`Prop` fields:

* `EdgeCutFacts74` / `CircleCutFacts74`: the cut-dependent fields of `EdgeBundle` / `CircleBundle`
  over the chosen good open base `↥D.edgeBaseOpen` / `↥D.circleBaseOpen` (D74-11 / D74-13); with
  them `edgeBundle74`, `circleBundle74` are the ACTUAL restrictions of `A.edge` / `A.circle`
  (`Base = ↥V`, parent `q⁻¹(V)`, restricted map, height, level, `cbase = C₂` / `C₁`);
* `SlimCutPieces74`: the slim pieces over the components of `D₃` (whole `f₃`-preimages);
* `StageCutRows74`: the four cut-dependent row structures (`edge`, `edgeModels`, `circle`, `slim`);
* `CutCoverFacts74` (FDC04 point-set cover), `JunctionFaceFacts74`, `JunctionRimFacts74`
  (EDP05 / EDP06 / FDC03 / ZSP05 exits), `CornerCutFacts74` (R1's inputs per actual endpoint).

Nothing in `H` is a `FC39RowsV2`, a `JunctionsV2` or a `LabelledCornerTubes`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

local instance diskChartsStageH74 : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

/-! ## The cut-dependent fields of the edge and circle bundles -/

/-- **The cut-dependent fields of `EdgeBundle` over the good open edge base** (EDP04 rank / whole
disk / properness, FDC02 compact base, EDP05 descended face function): the statements of
`EdgeBundle.rank_two / proper / fibre_disk / cbase_compact / cbase_domain` for the ACTUAL
restriction of `A.edge` to `D.edgeBaseOpen` with `cbase = C₂`. -/
structure EdgeCutFacts74 (A : SmoothStageGeometry74 W E) (D : StageCutChoice74 A) where
  rank_two : ∀ x : D.edgeSource, D.edgeHeight x = A.edge.level →
    Surjective fun v : TangentSpace W.model (x : W.Carrier) =>
      (mfderiv W.model (𝓡 1) (A.edge.restrictProj D.edgeBaseOpen) x v,
        mfderiv W.model 𝓘(ℝ, ℝ) D.edgeHeight x v)
  proper : ∀ K : Set D.edgeBaseOpen, IsCompact K →
    IsCompact (Subtype.val '' {x : D.edgeSource | A.edge.restrictProj D.edgeBaseOpen x ∈ K ∧
      D.edgeHeight x ≤ A.edge.level})
  fibre_disk : ∀ c : D.edgeBaseOpen, ∃ φ : ClosedCell 2 → W.Carrier,
    IsSmoothEmbedding (𝓡∂ 2) W.model ∞ φ ∧
      range φ = Subtype.val '' {x : D.edgeSource | A.edge.restrictProj D.edgeBaseOpen x = c ∧
        D.edgeHeight x ≤ A.edge.level}
  cbase_compact : IsCompact (Subtype.val ⁻¹' D.C₂ : Set D.edgeBaseOpen)
  cbase_domain : ∀ c ∈ frontier (Subtype.val ⁻¹' D.C₂ : Set D.edgeBaseOpen),
    ∃ U : TopologicalSpace.Opens D.edgeBaseOpen, c ∈ U ∧
      ∃ φ : D.edgeBaseOpen → ℝ, ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ φ U ∧ φ c = 0 ∧
        mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ c ≠ 0 ∧
        (Subtype.val ⁻¹' D.C₂ : Set D.edgeBaseOpen) ∩ U = {c' | c' ∈ U ∧ 0 ≤ φ c'}

/-- **The edge bundle of the rows** (D74-11): the ACTUAL restriction of `A.edge` to the good open
edge base `D.edgeBaseOpen` — base `↥D.edgeBaseOpen`, open parent `q₁⁻¹(V)`, restricted map and
height, the actual level, `cbase = C₂`. -/
def edgeBundle74 (A : SmoothStageGeometry74 W E) (D : StageCutChoice74 A)
    (F : EdgeCutFacts74 A D) : EdgeBundle W where
  Base := D.edgeBaseOpen
  source := D.edgeSource
  source_interior := fun _ hx => A.edge.parent_interior (A.edge.restrictParent_le _ hx)
  proj := A.edge.restrictProj D.edgeBaseOpen
  proj_smooth := A.edge.restrictProj_smooth _
  proj_submersion := A.edge.restrictProj_submersion _
  height := D.edgeHeight
  height_smooth := D.edgeHeight_smooth
  level := A.edge.level
  rank_two := F.rank_two
  proper := F.proper
  fibre_disk := F.fibre_disk
  cbase := Subtype.val ⁻¹' D.C₂
  cbase_compact := F.cbase_compact
  cbase_domain := F.cbase_domain

/-- **The cut-dependent fields of `CircleBundle` over the good open circle base** (GAF07 whole
circle fibres, C0 local trivializations, FDC03 saturation `M₃ = q₀⁻¹(C₁)`): the local smooth
trivializations over the good base, the whole-circle properness of the restricted map, the compact
remaining base and the saturation of `M₃`. -/
structure CircleCutFacts74 (A : SmoothStageGeometry74 W E) (D : StageCutChoice74 A) where
  neighborhood : D.circleBaseOpen → TopologicalSpace.Opens D.circleBaseOpen
  mem_neighborhood : ∀ c, c ∈ neighborhood c
  trivialization : (c : D.circleBaseOpen) →
    (TopologicalSpace.Opens.comap (A.circle.restrictProj D.circleBaseOpen) (neighborhood c))
      ≃ₘ⟮W.model, (𝓡 2).prod (𝓡 1)⟯ ((neighborhood c) × Circle)
  projection_trivialization : ∀ c x, ((trivialization c x).1).val =
    A.circle.restrictProj D.circleBaseOpen x.val
  proper : ∀ K : Set D.circleBaseOpen, IsCompact K →
    IsCompact (Subtype.val '' (A.circle.restrictProj D.circleBaseOpen ⁻¹' K))
  cbase_compact : IsCompact (Subtype.val ⁻¹' D.C₁ : Set D.circleBaseOpen)
  saturation : D.M₃ = D.circleRegion

/-- **The circle bundle of the rows** (D74-13): the ACTUAL restriction of `A.circle` to the good
open circle base — base `↥D.circleBaseOpen`, whole circle fibres, `cbase = C₁`. -/
def circleBundle74 (A : SmoothStageGeometry74 W E) (D : StageCutChoice74 A)
    (F : CircleCutFacts74 A D) : CircleBundle W where
  Base := D.circleBaseOpen
  domain := D.circleSource
  domain_interior := fun _ hx => A.circle.parent_interior (A.circle.restrictParent_le _ hx)
  proj := A.circle.restrictProj D.circleBaseOpen
  proj_smooth := A.circle.restrictProj_smooth _
  proj_submersion := A.circle.restrictProj_submersion _
  neighborhood := F.neighborhood
  mem_neighborhood := F.mem_neighborhood
  trivialization := F.trivialization
  projection_trivialization := F.projection_trivialization
  cbase := Subtype.val ⁻¹' D.C₁
  cbase_compact := F.cbase_compact

/-! ## The restricted bundles carry the cut sets -/

namespace StageCutChoice74

variable {A : SmoothStageGeometry74 W E} (D : StageCutChoice74 A)

/-- The edge piece of the restricted edge bundle is the cut's `M^edge`. -/
theorem edgePiece_edgeBundle74 (F : EdgeCutFacts74 A D) :
    (edgeBundle74 A D F).edgePiece = D.edgeSet := by
  ext x
  constructor
  · rintro ⟨y, ⟨hc, hh⟩, rfl⟩
    exact ⟨A.edge.restrictParent_le _ y.2, hc, hh⟩
  · rintro ⟨h, hc, hh⟩
    exact ⟨⟨x, A.edge.mem_restrictParent_of h (D.C₂_sub hc)⟩, ⟨hc, hh⟩, rfl⟩

/-- The circle region of the restricted circle bundle is `q₀⁻¹(C₁)`. -/
theorem region_circleBundle74 (F : CircleCutFacts74 A D) :
    (circleBundle74 A D F).region = D.circleRegion := by
  ext x
  constructor
  · rintro ⟨y, hc, rfl⟩
    exact ⟨A.circle.restrictParent_le _ y.2, hc⟩
  · rintro ⟨h, hc⟩
    exact ⟨⟨x, A.circle.mem_restrictParent_of h (D.C₁_sub hc)⟩, hc, rfl⟩

/-- The circle region of the restricted circle bundle is the cut's `M₃` (FDC03 saturation). -/
theorem region_circleBundle74_eq_M₃ (F : CircleCutFacts74 A D) :
    (circleBundle74 A D F).region = D.M₃ :=
  (D.region_circleBundle74 F).trans F.saturation.symm

end StageCutChoice74

/-! ## The slim pieces over the components of `D₃` and the cut-dependent rows -/

/-- **The slim pieces of the cut** (S2, ZSP04 / ZSP05 / BCF01): the pieces of `SlimPiecesV2`, in
bijection with the ACTUAL components of `D₃`, each with image the WHOLE `f₃`-preimage of its
component; and the whole shared-end identification (ZSP03 / BCG07 + the ZSP04 / BCF01 shared-end
classification: a shared end is the neighbouring model face). -/
structure SlimCutPieces74 (A : SmoothStageGeometry74 W E) (D : StageCutChoice74 A) where
  pieces : SlimPiecesV2 W A.zero A.cusp
  componentEquiv : Fin pieces.count ≃ ActualComponent D.D₃
  piece_range : ∀ j, range (pieces.piece j).map =
    {x | ∃ h : x ∈ A.slim.parent, A.slim.proj ⟨x, h⟩ ∈ (componentEquiv j).1}
  shared_eq : ∀ e F, pieces.endKind e = some F → pieces.endSet e = neighbourSet F

/-- **The four cut-dependent row structures that precede the junctions**: the slim pieces, the
facts of the edge and circle bundles over the good open bases, and the edge component export (E3 /
E4c) on the ACTUAL restricted edge bundle. -/
structure StageCutRows74 (A : SmoothStageGeometry74 W E) (D : StageCutChoice74 A) where
  slim : SlimCutPieces74 A D
  edgeFacts : EdgeCutFacts74 A D
  circleFacts : CircleCutFacts74 A D
  edgeModels : EdgeComponentModels (edgeBundle74 A D edgeFacts)

namespace StageCutRows74

variable {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A} (R : StageCutRows74 A D)

/-- The slim pieces of the rows. -/
abbrev slimPieces : SlimPiecesV2 W A.zero A.cusp :=
  R.slim.pieces

/-- The edge bundle of the rows (the actual restriction of `A.edge`). -/
abbrev edge : EdgeBundle W :=
  edgeBundle74 A D R.edgeFacts

/-- The circle bundle of the rows (the actual restriction of `A.circle`). -/
abbrev circle : CircleBundle W :=
  circleBundle74 A D R.circleFacts

end StageCutRows74

/-! ## The junction, rim and corner facts -/

/-- **FDC04's point-set cover and the separation facts** (`eventually_fdc04_cover_C14Z_FDC`):
`W = Z ∪ C ∪ slimSet ∪ M₂`; the slim set lies in `M₁`, the edge piece in `M₂`, zero domains and cusp
cores are disjoint. -/
structure CutCoverFacts74 (A : SmoothStageGeometry74 W E) (D : StageCutChoice74 A) where
  cover : ((⋃ i, range (A.zero.piece i).map) ∪ ⋃ b, range (A.cusp.piece b).map) ∪ D.slimSet ∪
    D.M₂ = univ
  slimSet_subset_M₁ : D.slimSet ⊆ regionM1 A.zero A.cusp
  edgeSet_subset_M₂ : D.edgeSet ⊆ D.M₂
  zero_cusp_disjoint : ∀ i b, Disjoint (range (A.zero.piece i).map) (range (A.cusp.piece b).map)

/-- **The face facts of the junctions** (EDP05 horizontal exit, ZSP05, FDC03 LastFaces, ZSP03):
the labelled horizontal map with whole end disks and the exhaustion of `P ∩ F`, `∂M₂` as the
union of the residual faces, `M₃ ∩ ∂M₂`, the slim ends of `M₂`, the removal of the shared faces. -/
structure JunctionFaceFacts74 (A : SmoothStageGeometry74 W E) (D : StageCutChoice74 A)
    (R : StageCutRows74 A D) where
  horizontal : R.edge.EdgeEnd → R.slimPieces.ResidualFace
  horizontal_disk : ∀ e, R.edge.disk e.1 ⊆ R.slimPieces.residualSet (horizontal e)
  edge_faces : ∀ F, D.edgeSet ∩ R.slimPieces.residualSet F =
    ⋃ (e : R.edge.EdgeEnd) (_ : horizontal e = F), R.edge.disk e.1
  frontier_M2 : frontier D.M₂ = R.slimPieces.boundaryM2
  region_boundary : D.M₃ ∩ R.slimPieces.boundaryM2 =
    R.slimPieces.boundaryM2 \ relInt R.slimPieces.boundaryM2 R.edge.horizontalDisks
  slim_M2 : D.slimSet ∩ D.M₂ = ⋃ e : R.slimPieces.NewEnd, R.slimPieces.endSet e.1
  shared_removed : ∀ σ : ActualSharedFace R.slimPieces,
    R.slimPieces.endSet σ.1 ⊆ relInt (regionM1 A.zero A.cusp) D.slimSet

/-- **The rim facts of the junctions** (EDP06 whole rim agreement, FDC03 surface-with-corners
exit): the smooth labelled `rimBase`, the whole rim equals the whole circle fibre, `P ∩ M₃ = V`,
and the labelled local faces of `C₁`. -/
structure JunctionRimFacts74 (A : SmoothStageGeometry74 W E) (D : StageCutChoice74 A)
    (R : StageCutRows74 A D) where
  rimBase : R.edge.Base → R.circle.Base
  rimBase_smooth : ContMDiffOn (𝓡 1) (𝓡 2) ∞ rimBase R.edge.cbase
  rim_fibre : ∀ c ∈ R.edge.cbase, R.edge.rim c = R.circle.fibre (rimBase c)
  edge_region : D.edgeSet ∩ D.M₃ = R.edge.vertical
  local_faces : ∀ c ∈ frontier R.circle.cbase, ∃ U : TopologicalSpace.Opens R.circle.Base,
    c ∈ U ∧
    ∃ (L : Finset (CircleFaceLabel R.slimPieces.ResidualFace R.edge.EdgeBaseComponent))
      (φ : CircleFaceLabel R.slimPieces.ResidualFace R.edge.EdgeBaseComponent →
        R.circle.Base → ℝ),
      1 ≤ L.card ∧ L.card ≤ 2 ∧
      (∀ f ∈ L, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (φ f) U ∧ φ f c = 0 ∧
        {c' | c' ∈ U ∧ c' ∈ R.circle.cbase ∧ φ f c' = 0} =
          {c' | c' ∈ U ∧ c' ∈ R.circle.cbase ∧
            R.circle.fibre c' ⊆ circleFaceSet R.slimPieces R.edge f}) ∧
      (Surjective fun w : TangentSpace (𝓡 2) c =>
        fun f : L => mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (φ f) c w) ∧
      R.circle.cbase ∩ U = {c' | c' ∈ U ∧ ∀ f ∈ L, φ f c' ≤ 0}

open scoped Classical in
/-- `T = height - level` on the edge source, read on the circle domain (`0` off the edge source;
the corner facts only use it on the buffer inside the edge source). -/
def StageCutRows74.cornerT {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A}
    (R : StageCutRows74 A D) (x : R.circle.domain) : ℝ :=
  if hx : (x : W.Carrier) ∈ R.edge.source then R.edge.height ⟨x, hx⟩ - R.edge.level else 0

/-- **R1, layers 1 and 2: the descent patch at an actual endpoint** (the base patch `V ∋ rimBase e`,
the descended `T̄`, `h̄` with `T = T̄ ∘ q₀`, `h_F = h̄ ∘ q₀` on the WHOLE preimage of the patch,
both vanishing at the rim base point). -/
structure CornerDescent74 {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A}
    {R : StageCutRows74 A D} (F : JunctionFaceFacts74 A D R) (G : JunctionRimFacts74 A D R)
    (e : R.edge.EdgeEnd) where
  patch : TopologicalSpace.Opens R.circle.Base
  rim_mem : G.rimBase e.1 ∈ patch
  Tb : R.circle.Base → ℝ
  hb : R.circle.Base → ℝ
  Tb_smooth : ContMDiffOn (𝓡 2) 𝓘(ℝ) ∞ Tb patch
  hb_smooth : ContMDiffOn (𝓡 2) 𝓘(ℝ) ∞ hb patch
  desc : ∀ x : R.circle.domain, R.circle.proj x ∈ patch →
    R.cornerT x = Tb (R.circle.proj x) ∧
      R.slimPieces.residualFn (F.horizontal e) x = hb (R.circle.proj x)
  center : Tb (G.rimBase e.1) = 0 ∧ hb (G.rimBase e.1) = 0

/-- **R1, layers 2 to 4: rank two and the three-sided sign model at an actual endpoint**: a point of
the rim fibre where `d(T, h_F)` has rank two (EDP04 + EDP05), an open set `N` containing the WHOLE
rim fibre inside the edge source and the residual buffer, and the vertex / edge component / `M₃`
sign model on `N`. -/
structure CornerRank74 {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A}
    {R : StageCutRows74 A D} (F : JunctionFaceFacts74 A D R) (G : JunctionRimFacts74 A D R)
    (e : R.edge.EdgeEnd) where
  point : R.circle.domain
  point_proj : R.circle.proj point = G.rimBase e.1
  rank : Surjective (mfderiv W.model 𝓘(ℝ, ℝ × ℝ)
    (fun z : R.circle.domain => (R.cornerT z, R.slimPieces.residualFn (F.horizontal e) z)) point)
  nbhd : Set R.circle.domain
  nbhd_open : IsOpen nbhd
  fibre_sub : R.circle.proj ⁻¹' {G.rimBase e.1} ⊆ nbhd
  nbhd_buffer : ∀ x ∈ nbhd, (x : W.Carrier) ∈ R.edge.source ∧
    (x : W.Carrier) ∈ R.slimPieces.residualNear (F.horizontal e)
  sign : ∀ x ∈ nbhd,
    ((x : W.Carrier) ∈ R.slimPieces.rowSet (R.slimPieces.residualOwner (F.horizontal e)) ↔
      R.slimPieces.residualFn (F.horizontal e) x ≤ 0) ∧
    ((x : W.Carrier) ∈ R.edge.wholeComponent e.component ↔
      0 ≤ R.slimPieces.residualFn (F.horizontal e) x ∧ R.cornerT x ≤ 0) ∧
    ((x : W.Carrier) ∈ R.circle.region ↔
      0 ≤ R.cornerT x ∧ 0 ≤ R.slimPieces.residualFn (F.horizontal e) x)

/-- **The descended face equation `b_e` at an actual endpoint** (EDP05: `h_F = b_e ∘ f₂`,
`db_e ≠ 0`), valid on the whole sign neighbourhood. -/
structure CornerDescended74 {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A}
    {R : StageCutRows74 A D} {F : JunctionFaceFacts74 A D R} {G : JunctionRimFacts74 A D R}
    {e : R.edge.EdgeEnd} (K : CornerRank74 F G e) where
  descended : R.edge.Base → ℝ
  descended_smooth : ∃ U : TopologicalSpace.Opens R.edge.Base, e.1 ∈ U ∧
    ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ descended U
  descended_regular : mfderiv (𝓡 1) 𝓘(ℝ, ℝ) descended e.1 ≠ 0
  descended_eq : ∀ x ∈ K.nbhd, ∃ hx : (x : W.Carrier) ∈ R.edge.source,
    R.slimPieces.residualFn (F.horizontal e) x = descended (R.edge.proj ⟨x, hx⟩)

/-- **The corner facts of the cut** (the inputs of R0 / R1 at every actual endpoint). -/
structure CornerCutFacts74 {A : SmoothStageGeometry74 W E} {D : StageCutChoice74 A}
    {R : StageCutRows74 A D} (F : JunctionFaceFacts74 A D R) (G : JunctionRimFacts74 A D R) where
  descent : ∀ e, CornerDescent74 F G e
  rank : ∀ e, CornerRank74 F G e
  descended : ∀ e, CornerDescended74 (rank e)

/-- **`H` (draft 74 §4.1): the cut geometry.** The cut-dependent row structures, the FDC04 cover,
the junction face / rim facts and the corner facts. Nothing here is a `JunctionsV2` or a
`LabelledCornerTubes`; those are built from it (J0). -/
structure StageCutGeometry74 (A : SmoothStageGeometry74 W E) (D : StageCutChoice74 A) where
  rows : StageCutRows74 A D
  cover : CutCoverFacts74 A D
  faces : JunctionFaceFacts74 A D rows
  rims : JunctionRimFacts74 A D rows
  corners : CornerCutFacts74 faces rims

end GC.GraphManifold.Assembly.FC39P0
