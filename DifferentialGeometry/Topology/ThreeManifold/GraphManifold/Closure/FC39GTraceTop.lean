import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Corners
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GSafeRows
import DifferentialGeometry.Geometry.Boundary.Manifold.Basic
import DifferentialGeometry.Geometry.Boundary.Model.EuclideanHalfSpace
import DifferentialGeometry.Topology.Manifold.ClosedBall

/-!
# FC39 GROUP G, lane FC39-G-TRACE: finite labels, compact traces, the set-level trace atlas

External draft task 58 §二 F1–F2 (disposition D58-3; sheet `build-logs/resume/sheet-FC39-G-TRACE.md`).
Everything is read from ONE `Rw : FC39RowsV2 W E` (no extra hypothesis). Notation:
`B f = Rw.baseTrace f`, `C₁ = Rw.circle.cbase`, `C₂ = Rw.edge.cbase`.

* circle-bundle topology: `CircleBundle.isOpenMap_proj_GTR` (local trivializations),
  `CircleBundle.isClosed_setOf_fibre_subset_GTR` ("some point of the fibre leaves a closed set" is an
  open condition on the base), `isCompact_fibre_GTR`, `isOpen_tube_GTR`, `fibre_disjoint_GTR`;
* **F1** `FC39RowsV2.isCompact_circleFaceSet_GTR`, `FC39RowsV2.isCompact_baseTrace_GTR`,
  `FC39RowsV2.finite_circleFace_GTR` (the boundary of a compact `𝓡∂ 3` piece has finitely many
  components: `finite_actualComponent_boundary_GTR`, through the charted space of
  `BoundaryManifold`);
* **F2 (set level)** `baseTrace_vertical_eq_GTR` (`B (.vertical C) = rimBase '' C`),
  `baseTrace_vertical_inter_horizontal_GTR` (vertical ∩ horizontal = the registered rim base points),
  `baseTrace_vertical_disjoint_GTR` (VV impossible), `frontier_cbase_eq_iUnion_baseTrace_GTR`
  (`∂C₁ = ⋃ f, B f`; the vertical traces lie in the frontier because a whole edge disk is not its rim:
  `EdgeComponentModels.exists_mem_disk_not_mem_rim_GTR`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

local instance diskChartsTraceTop_GTR : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

/-! ## Actual components -/

/-- An actual component of a closed set is closed. -/
theorem ActualComponent.isClosed_GTR {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsClosed S)
    (C : ActualComponent S) : IsClosed C.1 := by
  obtain ⟨x, hx, hC⟩ := C.2
  rw [hC, connectedComponentIn_eq_image hx]
  exact hS.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_connectedComponent

/-- **The boundary of a compact `𝓡∂ 3` manifold has finitely many actual components** (it is
compact and locally connected, through the charted space of `BoundaryManifold`). -/
theorem finite_actualComponent_boundary_GTR {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M] [CompactSpace M] :
    Finite (ActualComponent ((𝓡∂ 3).boundary M)) := by
  have hB : IsClosed ((𝓡∂ 3).boundary M) :=
    ModelWithCorners.isClosed_boundary (I := 𝓡∂ 3) (M := M) (n := ∞) (by simp)
  have : CompactSpace ((𝓡∂ 3).boundary M) := isCompact_iff_compactSpace.1 hB.isCompact
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) (BoundaryManifold (𝓡∂ 3) M) :=
    BoundaryManifold.chartedSpace (I := 𝓡∂ 3)
  have hlc : LocallyConnectedSpace (BoundaryManifold (𝓡∂ 3) M) :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) _
  have : LocallyConnectedSpace ((𝓡∂ 3).boundary M) := hlc
  have : Finite (ConnectedComponents ((𝓡∂ 3).boundary M)) := finite_of_compact_of_discrete
  refine Finite.of_injective (fun C : ActualComponent ((𝓡∂ 3).boundary M) =>
    ConnectedComponents.mk (⟨C.2.choose, C.2.choose_spec.1⟩ : (𝓡∂ 3).boundary M)) ?_
  intro C C' h
  have hC := C.2.choose_spec.2
  have hC' := C'.2.choose_spec.2
  apply Subtype.ext
  rw [hC, hC', connectedComponentIn_eq_image C.2.choose_spec.1,
    connectedComponentIn_eq_image C'.2.choose_spec.1]
  have h' := ConnectedComponents.coe_eq_coe.1 h
  rw [h']

/-- The model boundary faces of a piece are finitely many. -/
theorem finite_modelBoundaryFace_GTR (P : PieceEmbedding W) : Finite (ModelBoundaryFace P) :=
  finite_actualComponent_boundary_GTR

/-- A model boundary face of a piece is compact. -/
theorem isCompact_modelBoundaryFace_GTR {P : PieceEmbedding W} (F : ModelBoundaryFace P) :
    IsCompact F.1 :=
  (ActualComponent.isClosed_GTR (ModelWithCorners.isClosed_boundary (I := 𝓡∂ 3) (M := P.Piece)
    (n := ∞) (by simp)) F).isCompact

/-! ## Circle-bundle topology -/

namespace CircleBundle

variable (R : CircleBundle W)

/-- **The projection of the circle bundle is an open map** (local trivializations). -/
theorem isOpenMap_proj_GTR : IsOpenMap R.proj := by
  intro U hU
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨x, hxU, rfl⟩
  let N := TopologicalSpace.Opens.comap R.proj (R.neighborhood (R.proj x))
  let T := R.trivialization (R.proj x)
  have hxN : x ∈ N := R.mem_neighborhood (R.proj x)
  let V : Set N := Subtype.val ⁻¹' U
  have hV : IsOpen V := hU.preimage continuous_subtype_val
  have h1 : IsOpen (T '' V) := T.toHomeomorph.isOpenMap V hV
  have h2 : IsOpen (Prod.fst '' (T '' V)) := isOpenMap_fst _ h1
  have h3 : IsOpen ((Subtype.val : R.neighborhood (R.proj x) → R.Base) '' (Prod.fst '' (T '' V))) :=
    (R.neighborhood (R.proj x)).isOpen.isOpenMap_subtype_val _ h2
  refine ⟨_, ?_, h3, ?_⟩
  · rintro _ ⟨_, ⟨_, ⟨y, hyV, rfl⟩, rfl⟩, rfl⟩
    exact ⟨y.1, hyV, (R.projection_trivialization (R.proj x) y).symm⟩
  · exact ⟨_, ⟨_, ⟨⟨x, hxN⟩, hxU, rfl⟩, rfl⟩, R.projection_trivialization (R.proj x) ⟨x, hxN⟩⟩

/-- **F1 (closedness).** For a closed set `S` of `W`, the base points whose whole fibre lies in `S`
form a closed set (its complement is the projection of the open set `Sᶜ`). -/
theorem isClosed_setOf_fibre_subset_GTR {S : Set W.Carrier} (hS : IsClosed S) :
    IsClosed {c : R.Base | R.fibre c ⊆ S} := by
  have heq : {c : R.Base | R.fibre c ⊆ S}ᶜ =
      R.proj '' ((Subtype.val : R.domain → W.Carrier) ⁻¹' Sᶜ) := by
    ext c
    constructor
    · intro hc
      obtain ⟨_, ⟨y, hy, rfl⟩, hyS⟩ := not_subset.1 hc
      exact ⟨y, hyS, hy⟩
    · rintro ⟨y, hyS, rfl⟩ hsub
      exact hyS (hsub ⟨y, rfl, rfl⟩)
  rw [← isOpen_compl_iff, heq]
  exact R.isOpenMap_proj_GTR _ (hS.isOpen_compl.preimage continuous_subtype_val)

/-- A whole fibre is compact. -/
theorem isCompact_fibre_GTR (c : R.Base) : IsCompact (R.fibre c) :=
  R.isCompact_tube_GSAFE isCompact_singleton

/-- The tube over an open base set is open in `W`. -/
theorem isOpen_tube_GTR {V : Set R.Base} (hV : IsOpen V) : IsOpen (R.tube V) :=
  R.domain.isOpen.isOpenMap_subtype_val _ (hV.preimage R.proj.continuous)

/-- Fibres over distinct base points are disjoint. -/
theorem fibre_disjoint_GTR {c c' : R.Base} (h : c ≠ c') : Disjoint (R.fibre c) (R.fibre c') :=
  R.tube_disjoint_GSAFE (disjoint_singleton.2 h)

theorem fibre_subset_tube_GTR {c : R.Base} {V : Set R.Base} (hc : c ∈ V) :
    R.fibre c ⊆ R.tube V :=
  R.tube_mono_GSAFE (singleton_subset_iff.2 hc)

/-- A fibre meeting the circle region lies over `C₁`. -/
theorem mem_cbase_of_mem_fibre_region_GTR {c : R.Base} {x : W.Carrier} (hx : x ∈ R.fibre c)
    (hxr : x ∈ R.region) : c ∈ R.cbase := by
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨y', hy', hyy⟩ := hxr
  have : y' = y := Subtype.ext hyy
  subst this
  rw [mem_preimage, mem_singleton_iff] at hy
  exact hy ▸ hy'

/-- The fibre over a point of `C₁` lies in the circle region. -/
theorem fibre_subset_region_GTR {c : R.Base} (hc : c ∈ R.cbase) : R.fibre c ⊆ R.region :=
  R.tube_mono_GSAFE (singleton_subset_iff.2 hc)

end CircleBundle

/-! ## A whole edge disk is not its rim -/

/-- The centre of the closed disk is not on its rim. -/
theorem zero_notMem_diskRim_GTR : (⟨0, by simp⟩ : ClosedCell 2) ∉ diskRim := by
  intro h
  have h' : (⟨0, by simp⟩ : ClosedCell 2) ∈ (𝓡∂ 2).boundary (ClosedCell 2) := h
  rw [show (𝓡∂ 2).boundary (ClosedCell 2) = {x : ClosedCell 2 | ‖x.val‖ = 1} from
    DifferentialGeometry.Topology.Manifold.closedCell_boundary_eq_sphere 1] at h'
  simp at h'

/-- **The whole edge disk over a point of `C₂` is not its rim** (the component models: the centre
slice of the product parametrization is off the rim, by injectivity). -/
theorem EdgeComponentModels.exists_mem_disk_not_mem_rim_GTR {P : EdgeBundle W}
    (M : EdgeComponentModels P) {c : P.Base} (hc : c ∈ P.cbase) :
    ∃ x ∈ P.disk c, x ∉ P.rim c := by
  have hcC : c ∈ (ActualComponent.of hc : P.EdgeBaseComponent).1 := mem_connectedComponentIn hc
  rcases hs : M.componentEquiv.symm (ActualComponent.of hc) with i | j
  · have hC : M.componentEquiv (.inl i) = ActualComponent.of hc := by
      rw [← hs, Equiv.apply_symm_apply]
    rw [← hC, ← M.intervalBase_range i] at hcC
    obtain ⟨t, rfl⟩ := hcC
    refine ⟨(M.intervalTriv i).map (⟨0, by simp⟩, t), ?_, ?_⟩
    · rw [← M.intervalTriv_disk i t]
      exact ⟨_, rfl⟩
    · rw [← M.intervalTriv_rim i t]
      rintro ⟨w, hw, hweq⟩
      have h := (M.intervalTriv i).injective hweq
      rw [Prod.mk.injEq] at h
      exact zero_notMem_diskRim_GTR (h.1 ▸ hw)
  · have hC : M.componentEquiv (.inr j) = ActualComponent.of hc := by
      rw [← hs, Equiv.apply_symm_apply]
    rw [← hC, ← M.circleBase_range j] at hcC
    obtain ⟨z, rfl⟩ := hcC
    refine ⟨M.circleTriv j (⟨0, by simp⟩, z), ?_, ?_⟩
    · rw [← M.circleTriv_disk j z]
      exact ⟨_, rfl⟩
    · rw [← M.circleTriv_rim j z]
      rintro ⟨w, hw, hweq⟩
      have h := M.circleTriv_injective j hweq
      rw [Prod.mk.injEq] at h
      exact zero_notMem_diskRim_GTR (h.1 ▸ hw)

/-! ## Labels -/

/-- The labels of the circle-base faces as a sum. -/
def CircleFaceLabel.equivSum_GTR (Hor Ver : Type*) : CircleFaceLabel Hor Ver ≃ Hor ⊕ Ver where
  toFun
    | .horizontal F => .inl F
    | .vertical c => .inr c
  invFun
    | .inl F => .horizontal F
    | .inr c => .vertical c
  left_inv f := by cases f <;> rfl
  right_inv s := by cases s <;> rfl

namespace FC39RowsV2

variable (Rw : FC39RowsV2 W E)

/-! ## F1: finite labels, compact faces and traces -/

/-- The residual faces are finitely many. -/
theorem finite_residualFace_GTR : Finite Rw.slim.ResidualFace := by
  have := Rw.finite_slimEnd_GSAFE
  have : ∀ i, Finite (ModelBoundaryFace (Rw.zero.piece i)) := fun i =>
    finite_modelBoundaryFace_GTR _
  have : Finite Rw.cusp.InternalModelFace := by
    unfold CuspCores.InternalModelFace
    infer_instance
  unfold SlimPiecesV2.ResidualFace
  infer_instance

/-- **F1** The labelled faces of the circle base are finitely many. -/
theorem finite_circleFace_GTR : Finite Rw.CircleFace := by
  have := Rw.finite_residualFace_GTR
  have : Finite Rw.edge.EdgeBaseComponent := Finite.of_equiv _ Rw.edgeModels.componentEquiv
  exact Finite.of_equiv _ (CircleFaceLabel.equivSum_GTR _ _).symm

/-- A neighbour face has a compact ambient image. -/
theorem isCompact_neighbourSet_GTR : ∀ F : NeighbourFace Rw.zero Rw.cusp, IsCompact (neighbourSet F)
  | .inl F => (isCompact_modelBoundaryFace_GTR F.2).image (Rw.zero.piece F.1).continuous_map
  | .inr F => (isCompact_modelBoundaryFace_GTR F.2.1).image (Rw.cusp.piece F.1).continuous_map

/-- A residual face is compact. -/
theorem isCompact_residualSet_GTR : ∀ F : Rw.slim.ResidualFace, IsCompact (Rw.slim.residualSet F)
  | .inl F => Rw.isCompact_neighbourSet_GTR F.1
  | .inr e => Rw.slim.isCompact_endSet_GSAFE e.1

/-- An actual base component of `C₂` is compact. -/
theorem isCompact_edgeBaseComponent_GTR (C : Rw.edge.EdgeBaseComponent) : IsCompact C.1 :=
  Rw.edge.cbase_compact.of_isClosed_subset
    (ActualComponent.isClosed_GTR Rw.edge.cbase_compact.isClosed C) C.subset

/-- The whole vertical face of a component is the whole component inside the circle region
(`edge_region`). -/
theorem wholeVertical_eq_GTR (C : Rw.edge.EdgeBaseComponent) :
    Rw.edge.wholeVertical C = Rw.edge.wholeComponent C ∩ Rw.circle.region := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyC, hyl⟩, rfl⟩
    refine ⟨⟨y, ⟨hyC, hyl.le⟩, rfl⟩, ?_⟩
    have hv : (y : W.Carrier) ∈ Rw.edge.vertical := ⟨y, ⟨C.subset hyC, hyl⟩, rfl⟩
    rw [← Rw.junctions.edge_region] at hv
    exact hv.2
  · rintro ⟨⟨y, ⟨hyC, hyl⟩, rfl⟩, hxr⟩
    have hv : (y : W.Carrier) ∈ Rw.edge.vertical := by
      rw [← Rw.junctions.edge_region]
      exact ⟨⟨y, ⟨C.subset hyC, hyl⟩, rfl⟩, hxr⟩
    obtain ⟨y', ⟨-, hyl'⟩, hyy⟩ := hv
    have : y' = y := Subtype.ext hyy
    subst this
    exact ⟨y', ⟨hyC, hyl'⟩, rfl⟩

/-- **F1** Every labelled face of the circle base is compact. -/
theorem isCompact_circleFaceSet_GTR :
    ∀ f : Rw.CircleFace, IsCompact (circleFaceSet Rw.slim Rw.edge f)
  | .horizontal F => Rw.isCompact_residualSet_GTR F
  | .vertical C => by
    change IsCompact (Rw.edge.wholeVertical C)
    rw [Rw.wholeVertical_eq_GTR]
    exact (Rw.edge.proper _ (Rw.isCompact_edgeBaseComponent_GTR C)).inter_right
      Rw.isClosed_region_GSAFE

/-- **F1** Every base trace is compact. -/
theorem isCompact_baseTrace_GTR (f : Rw.CircleFace) : IsCompact (Rw.baseTrace f) :=
  Rw.circle.cbase_compact.inter_right
    (Rw.circle.isClosed_setOf_fibre_subset_GTR (Rw.isCompact_circleFaceSet_GTR f).isClosed)

/-! ## F2 at the set level -/

theorem mem_cbase_of_mem_baseTrace_GTR {f : Rw.CircleFace} {c : Rw.circle.Base}
    (hc : c ∈ Rw.baseTrace f) : c ∈ Rw.circle.cbase :=
  hc.1

/-- **F2** The vertical trace of a component is the rim base image of the component. -/
theorem baseTrace_vertical_eq_GTR (C : Rw.edge.EdgeBaseComponent) :
    Rw.baseTrace (.vertical C) = Rw.junctions.rimBase '' C.1 := by
  ext c
  constructor
  · rintro ⟨-, hsub⟩
    obtain ⟨x, hx⟩ := Rw.circle.fibre_nonempty_GSAFE c
    obtain ⟨y, ⟨hyC, hyl⟩, rfl⟩ := hsub hx
    refine ⟨Rw.edge.proj y, hyC, ?_⟩
    have hyr : (y : W.Carrier) ∈ Rw.edge.rim (Rw.edge.proj y) := ⟨y, ⟨rfl, hyl⟩, rfl⟩
    rw [Rw.junctions.rim_fibre _ (C.subset hyC)] at hyr
    by_contra hne
    exact Set.disjoint_left.1 (Rw.circle.fibre_disjoint_GTR hne) hyr hx
  · rintro ⟨c₂, hc₂, rfl⟩
    have hc₂' : c₂ ∈ Rw.edge.cbase := C.subset hc₂
    refine ⟨?_, ?_⟩
    · obtain ⟨r, hr⟩ := Rw.rim_nonempty_GSAFE hc₂'
      have hr' := hr
      rw [Rw.junctions.rim_fibre _ hc₂'] at hr'
      exact Rw.circle.mem_cbase_of_mem_fibre_region_GTR hr' (Rw.rim_subset_region_GSAFE hc₂' hr)
    · rw [← Rw.junctions.rim_fibre _ hc₂']
      rintro _ ⟨y, ⟨hy, hyl⟩, rfl⟩
      exact ⟨y, ⟨hy ▸ hc₂, hyl⟩, rfl⟩

/-- An endpoint lies in its own component. -/
theorem mem_component_GTR (e : Rw.edge.EdgeEnd) : e.1 ∈ e.component.1 :=
  mem_connectedComponentIn (Rw.edge.frontier_cbase_subset e.2)

/-- The rim base point of an endpoint lies on the vertical trace of its component. -/
theorem rimBase_mem_baseTrace_vertical_GTR (e : Rw.edge.EdgeEnd) :
    Rw.junctions.rimBase e.1 ∈ Rw.baseTrace (.vertical e.component) := by
  rw [Rw.baseTrace_vertical_eq_GTR]
  exact ⟨e.1, Rw.mem_component_GTR e, rfl⟩

/-- The rim base point of an endpoint lies on the trace of its registered horizontal face. -/
theorem rimBase_mem_baseTrace_horizontal_GTR (e : Rw.edge.EdgeEnd) :
    Rw.junctions.rimBase e.1 ∈ Rw.baseTrace (.horizontal (Rw.junctions.horizontal e)) := by
  refine ⟨(Rw.rimBase_mem_baseTrace_vertical_GTR e).1, ?_⟩
  rw [← Rw.junctions.rim_fibre _ (Rw.edge.frontier_cbase_subset e.2)]
  exact (Rw.edge.rim_subset_disk_GSAFE _).trans (Rw.junctions.horizontal_disk e)

/-- **F2 (HV registered)** A vertical and a horizontal trace meet exactly in the registered rim base
points. -/
theorem baseTrace_vertical_inter_horizontal_GTR (C : Rw.edge.EdgeBaseComponent)
    (F : Rw.slim.ResidualFace) :
    Rw.baseTrace (.vertical C) ∩ Rw.baseTrace (.horizontal F) =
      (fun e : Rw.edge.EdgeEnd => Rw.junctions.rimBase e.1) ''
        {e | e.component = C ∧ Rw.junctions.horizontal e = F} := by
  ext c
  constructor
  · rintro ⟨hv, -, hsubF⟩
    rw [Rw.baseTrace_vertical_eq_GTR] at hv
    obtain ⟨c₂, hc₂, rfl⟩ := hv
    have hc₂' : c₂ ∈ Rw.edge.cbase := C.subset hc₂
    obtain ⟨r, hr⟩ := Rw.rim_nonempty_GSAFE hc₂'
    have hrF : r ∈ Rw.slim.residualSet F := by
      have hr' := hr
      rw [Rw.junctions.rim_fibre _ hc₂'] at hr'
      exact hsubF hr'
    have hrP : r ∈ Rw.edge.edgePiece ∩ Rw.slim.residualSet F :=
      ⟨Rw.edge.disk_subset_edgePiece_GSAFE hc₂' (Rw.edge.rim_subset_disk_GSAFE _ hr), hrF⟩
    rw [Rw.junctions.edge_faces F] at hrP
    obtain ⟨e, hrE⟩ := mem_iUnion.1 hrP
    obtain ⟨heF, hre⟩ := mem_iUnion.1 hrE
    have hce : c₂ = e.1 := by
      by_contra hne
      exact Set.disjoint_left.1 (Rw.edge.disk_disjoint hne) (Rw.edge.rim_subset_disk_GSAFE _ hr) hre
    subst hce
    exact ⟨e, ⟨ActualComponent.eq_of_mem (Rw.mem_component_GTR e) hc₂, heF⟩, rfl⟩
  · rintro ⟨e, ⟨rfl, rfl⟩, rfl⟩
    exact ⟨Rw.rimBase_mem_baseTrace_vertical_GTR e, Rw.rimBase_mem_baseTrace_horizontal_GTR e⟩

/-- **F2 (VV impossible)** Distinct components have disjoint vertical traces. -/
theorem baseTrace_vertical_disjoint_GTR {C C' : Rw.edge.EdgeBaseComponent} (h : C ≠ C') :
    Disjoint (Rw.baseTrace (.vertical C)) (Rw.baseTrace (.vertical C')) := by
  refine Set.disjoint_left.2 fun c hc hc' => h ?_
  obtain ⟨x, hx⟩ := Rw.circle.fibre_nonempty_GSAFE c
  obtain ⟨y, ⟨hyC, -⟩, rfl⟩ := hc.2 hx
  obtain ⟨y', ⟨hyC', -⟩, hyy⟩ := hc'.2 hx
  have : y' = y := Subtype.ext hyy
  subst this
  exact ActualComponent.eq_of_mem hyC hyC'

/-! ## F2: `∂C₁ = ⋃ f, B f` -/

/-- A base point of `C₁` whose fibre meets `∂M₂` is not an interior point of `C₁` (the tube over
`int C₁` is open and lies in `M₂`). -/
theorem notMem_interior_cbase_GTR {c : Rw.circle.Base} {x : W.Carrier}
    (hx : x ∈ Rw.circle.fibre c) (hxb : x ∈ Rw.slim.boundaryM2) :
    c ∉ interior Rw.circle.cbase := by
  intro hint
  have hsub : Rw.circle.tube (interior Rw.circle.cbase) ⊆ regionM2 Rw.slim :=
    (Rw.circle.tube_mono_GSAFE interior_subset).trans Rw.region_subset_regionM2_GSAFE
  have hxi : x ∈ interior (regionM2 Rw.slim) :=
    interior_maximal hsub (Rw.circle.isOpen_tube_GTR isOpen_interior)
      (Rw.circle.fibre_subset_tube_GTR hint hx)
  rw [← Rw.junctions.frontier_M2] at hxb
  exact hxb.2 hxi

/-- A base point of `C₁` whose fibre meets `∂M₂` lies in `∂C₁`. -/
theorem mem_frontier_cbase_of_fibre_GTR {c : Rw.circle.Base} (hc : c ∈ Rw.circle.cbase)
    {x : W.Carrier} (hx : x ∈ Rw.circle.fibre c) (hxb : x ∈ Rw.slim.boundaryM2) :
    c ∈ frontier Rw.circle.cbase :=
  ⟨subset_closure hc, Rw.notMem_interior_cbase_GTR hx hxb⟩

/-- **F2** A horizontal trace lies in `∂C₁`. -/
theorem baseTrace_horizontal_subset_frontier_GTR (F : Rw.slim.ResidualFace) :
    Rw.baseTrace (.horizontal F) ⊆ frontier Rw.circle.cbase := by
  rintro c ⟨hc, hsub⟩
  obtain ⟨x, hx⟩ := Rw.circle.fibre_nonempty_GSAFE c
  exact Rw.mem_frontier_cbase_of_fibre_GTR hc hx (mem_iUnion.2 ⟨F, hsub hx⟩)

/-- **F2** A vertical trace lies in `∂C₁`: over an interior point the whole edge disk would be
open-closed in its rim, but a whole disk is not its rim. -/
theorem baseTrace_vertical_subset_frontier_GTR (C : Rw.edge.EdgeBaseComponent) :
    Rw.baseTrace (.vertical C) ⊆ frontier Rw.circle.cbase := by
  intro c hc
  have hcc := hc.1
  rw [Rw.baseTrace_vertical_eq_GTR] at hc
  obtain ⟨c₂, hc₂, rfl⟩ := hc
  have hc₂' : c₂ ∈ Rw.edge.cbase := C.subset hc₂
  refine ⟨subset_closure hcc, fun hint => ?_⟩
  have hVo : IsOpen (Rw.circle.tube (interior Rw.circle.cbase)) :=
    Rw.circle.isOpen_tube_GTR isOpen_interior
  have hrimV : Rw.edge.rim c₂ ⊆ Rw.circle.tube (interior Rw.circle.cbase) := by
    rw [Rw.junctions.rim_fibre _ hc₂']
    exact Rw.circle.fibre_subset_tube_GTR hint
  have hdiskV : Rw.edge.disk c₂ ∩ Rw.circle.tube (interior Rw.circle.cbase) ⊆ Rw.edge.rim c₂ := by
    rintro x ⟨hxd, hxV⟩
    have hxr : x ∈ Rw.circle.region := Rw.circle.tube_mono_GSAFE interior_subset hxV
    have hxv : x ∈ Rw.edge.vertical := by
      rw [← Rw.junctions.edge_region]
      exact ⟨Rw.edge.disk_subset_edgePiece_GSAFE hc₂' hxd, hxr⟩
    obtain ⟨y, ⟨hy, -⟩, rfl⟩ := hxd
    obtain ⟨y', ⟨-, hyl⟩, hyy⟩ := hxv
    have : y' = y := Subtype.ext hyy
    subst this
    exact ⟨y', ⟨hy, hyl⟩, rfl⟩
  have hrimc : IsClosed (Rw.edge.rim c₂) := by
    rw [Rw.junctions.rim_fibre _ hc₂']
    exact (Rw.circle.isCompact_fibre_GTR _).isClosed
  obtain ⟨r, hr⟩ := Rw.rim_nonempty_GSAFE hc₂'
  have hcover : Rw.edge.disk c₂ ⊆ Rw.circle.tube (interior Rw.circle.cbase) ∪ (Rw.edge.rim c₂)ᶜ := by
    intro x _
    by_cases hxr : x ∈ Rw.edge.rim c₂
    · exact Or.inl (hrimV hxr)
    · exact Or.inr hxr
  have hdisj : Rw.edge.disk c₂ ∩ (Rw.circle.tube (interior Rw.circle.cbase) ∩ (Rw.edge.rim c₂)ᶜ) =
      ∅ := by
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
    intro hxd hxV hxr
    exact hxr (hdiskV ⟨hxd, hxV⟩)
  rcases isPreconnected_iff_subset_of_disjoint.1 (Rw.edge.isPreconnected_disk_GSAFE c₂) _ _ hVo
    hrimc.isOpen_compl hcover hdisj with h | h
  · obtain ⟨x, hxd, hxr⟩ := Rw.edgeModels.exists_mem_disk_not_mem_rim_GTR hc₂'
    exact hxr (hdiskV ⟨hxd, h hxd⟩)
  · exact h (Rw.edge.rim_subset_disk_GSAFE _ hr) hr

/-- **F2** Every base trace lies in `∂C₁`. -/
theorem baseTrace_subset_frontier_GTR :
    ∀ f : Rw.CircleFace, Rw.baseTrace f ⊆ frontier Rw.circle.cbase
  | .horizontal F => Rw.baseTrace_horizontal_subset_frontier_GTR F
  | .vertical C => Rw.baseTrace_vertical_subset_frontier_GTR C

/-- A label of a `local_faces` triple at `c` has `c` on its trace. -/
theorem mem_baseTrace_of_localFace_GTR {c : Rw.circle.Base} (hc : c ∈ frontier Rw.circle.cbase)
    {U : Set Rw.circle.Base} (hcU : c ∈ U) {f : Rw.CircleFace} {φ : Rw.circle.Base → ℝ}
    (hφ0 : φ c = 0)
    (hφeq : {c' | c' ∈ U ∧ c' ∈ Rw.circle.cbase ∧ φ c' = 0} =
      {c' | c' ∈ U ∧ c' ∈ Rw.circle.cbase ∧ Rw.circle.fibre c' ⊆ circleFaceSet Rw.slim Rw.edge f}) :
    c ∈ Rw.baseTrace f := by
  have h : c ∈ {c' | c' ∈ U ∧ c' ∈ Rw.circle.cbase ∧ φ c' = 0} :=
    ⟨hcU, Rw.circle.cbase_compact.isClosed.frontier_subset hc, hφ0⟩
  rw [hφeq] at h
  exact ⟨h.2.1, h.2.2⟩

/-- **F2** Every point of `∂C₁` lies on some base trace (`local_faces`). -/
theorem exists_mem_baseTrace_GTR {c : Rw.circle.Base} (hc : c ∈ frontier Rw.circle.cbase) :
    ∃ f, c ∈ Rw.baseTrace f := by
  obtain ⟨U, hcU, L, φ, hL1, -, hφ, -, -⟩ := Rw.junctions.local_faces c hc
  obtain ⟨f, hf⟩ := Finset.card_pos.1 (by omega : 0 < L.card)
  obtain ⟨-, hf0, hfeq⟩ := hφ f hf
  exact ⟨f, Rw.mem_baseTrace_of_localFace_GTR hc hcU hf0 hfeq⟩

/-- **F2** `∂C₁ = ⋃ f, B f`. -/
theorem frontier_cbase_eq_iUnion_baseTrace_GTR :
    frontier Rw.circle.cbase = ⋃ f, Rw.baseTrace f := by
  apply Subset.antisymm
  · intro c hc
    obtain ⟨f, hf⟩ := Rw.exists_mem_baseTrace_GTR hc
    exact mem_iUnion.2 ⟨f, hf⟩
  · exact iUnion_subset Rw.baseTrace_subset_frontier_GTR

end FC39RowsV2

end GC.GraphManifold.Assembly.FC39P0
