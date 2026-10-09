import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0ClosedZero
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Junctions
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SlimCircle
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SingletonLayers

/-!
The X136 singleton row data: actual closed-zero domain on the whole round sphere and honest
empty cusp, slim, edge and circle families. No nonempty handle or port is represented here.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X136

def zeroDomains : ZeroDomains zeroW where
  count := 1
  piece i := zeroClosedPiece.piece
  disjoint i j h := (h (Subsingleton.elim i j)).elim
  ratio i := wholeFunction standardThreeSphere
  near i := ⊤
  near_interior i x hx := ((NoCuts.interiorDiffeomorph standardThreeSphere).symm x).property
  ratio_smooth i := wholeFunction_smooth standardThreeSphere
  ratio_regular i := wholeFunction_regular standardThreeSphere
  zero_subset_near i x hx := trivial
  boundary_eq i := by
    change (wholePiece standardThreeSphere).map '' (𝓡∂ 3).boundary
      (wholePiece standardThreeSphere).Piece = {x | wholeFunction standardThreeSphere x = 0}
    rw [wholePiece_boundary, image_empty]
    apply Eq.symm
    apply eq_empty_of_forall_notMem
    intro x hx
    norm_num [wholeFunction, Function.const] at hx
  range_eq i := by
    rw [zeroClosedPiece_cover]
    ext x
    simp [wholeFunction, Function.const]
  model i := .inr ⟨zeroClosedPiece, rfl⟩

def emptyCusps (Q : ConnectedClosedOrientedManifold.{0} 3) :
    CuspCores (NoCuts.carrier Q) (BoundaryTori.empty (NoCuts.carrier Q)) where
  ports := by rw [closedCarrier_boundary_eq_empty, BoundaryTori.empty_image]
  piece b := b.elim0
  product b := b.elim0
  external_end b := b.elim0
  collar_owned b := b.elim0
  collar_closure_off b := b.elim0
  disjoint b := b.elim0
  cuspFn b := b.elim0
  near b := b.elim0
  near_interior b := b.elim0
  fn_smooth b := b.elim0
  fn_regular b := b.elim0
  internal_eq b := b.elim0
  near_eq b := b.elim0
  internalModelFace b := b.elim0
  internalModelFace_eq b := b.elim0
  externalModelFace b := b.elim0
  externalModelFace_eq b := b.elim0
  modelFace_cases b := b.elim0

def zeroCusps := emptyCusps standardThreeSphere

def zeroSlim : SlimPiecesV2 zeroW zeroDomains zeroCusps where
  count := 0
  piece j := j.elim0
  model j := j.elim0
  disjoint j := j.elim0
  endFace e := e.1.1.elim0
  endFace_eq e := e.1.1.elim0
  endFace_exhausted j := j.elim0
  endKind e := e.1.1.elim0
  endFn e := e.1.1.1.elim0
  endNear e := e.1.1.1.elim0
  endNear_interior e := e.1.1.1.elim0
  endFn_smooth e := e.1.1.1.elim0
  endFn_regular e := e.1.1.1.elim0
  endFn_level e := e.1.1.1.elim0
  endFn_eq e := e.1.1.1.elim0


theorem noWholeFace (Q : ConnectedClosedOrientedManifold.{0} 3)
    (F : ModelBoundaryFace (wholePiece Q)) : False := by
  obtain ⟨x, hx, hcomponent⟩ := F.2
  rw [wholePiece_boundary] at hx
  exact hx.elim

def slimZero : ZeroDomains slimW where
  count := 0
  piece i := i.elim0
  disjoint i := i.elim0
  ratio i := i.elim0
  near i := i.elim0
  near_interior i := i.elim0
  ratio_smooth i := i.elim0
  ratio_regular i := i.elim0
  zero_subset_near i := i.elim0
  boundary_eq i := i.elim0
  range_eq i := i.elim0
  model i := i.elim0

def slimCusps := emptyCusps sphereTwoTimesCircleLift

def slimPieces : SlimPiecesV2 slimW slimZero slimCusps where
  count := 1
  piece := Function.const (Fin 1) slimPiece
  model := Function.const (Fin 1) slimModel
  disjoint j k h := (h (Subsingleton.elim j k)).elim
  endFace e := e.2.elim
  endFace_eq e := e.2.elim
  endFace_exhausted := Fin.cases
    (fun F => (noWholeFace sphereTwoTimesCircleLift F).elim) (fun j => j.elim0)
  endKind e := e.2.elim
  endFn e := e.1.2.elim
  endNear e := e.1.2.elim
  endNear_interior e := e.1.2.elim
  endFn_smooth e := e.1.2.elim
  endFn_regular e := e.1.2.elim
  endFn_level e := e.1.2.elim
  endFn_eq e := e.1.2.elim

def emptyEdges (Q : ConnectedClosedOrientedManifold.{0} 3) : EdgeBundle (NoCuts.carrier Q) where
  Base := PEmpty
  baseCharts := ChartedSpace.empty _ _
  baseSmooth := by
    let emptyBaseCharts : ChartedSpace (EuclideanSpace ℝ (Fin 1)) PEmpty :=
      ChartedSpace.empty _ _
    exact IsManifold.empty ∞
  source := ⊥
  source_interior := by simp
  proj := CircleRegion.emptyProj (NoCuts.carrier Q)
  proj_smooth x := (CircleRegion.false_of_bot (NoCuts.carrier Q) x).elim
  proj_submersion x := (CircleRegion.false_of_bot (NoCuts.carrier Q) x).elim
  height x := (CircleRegion.false_of_bot (NoCuts.carrier Q) x).elim
  height_smooth x := (CircleRegion.false_of_bot (NoCuts.carrier Q) x).elim
  level := 0
  rank_two x := (CircleRegion.false_of_bot (NoCuts.carrier Q) x).elim
  proper K hK := by
    convert isCompact_empty using 1
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact (CircleRegion.false_of_bot (NoCuts.carrier Q) q).elim
    · intro hx
      exact hx.elim
  fibre_disk c := c.elim
  cbase := ∅
  cbase_compact := isCompact_empty
  cbase_domain c := c.elim

def emptyCircles (Q : ConnectedClosedOrientedManifold.{0} 3) :
    CircleBundle (NoCuts.carrier Q) where
  Base := (CircleRegion.empty (NoCuts.carrier Q)).Base
  baseTop := (CircleRegion.empty (NoCuts.carrier Q)).baseTop
  baseCharts := (CircleRegion.empty (NoCuts.carrier Q)).baseCharts
  baseSmooth := (CircleRegion.empty (NoCuts.carrier Q)).baseSmooth
  baseT2 := (CircleRegion.empty (NoCuts.carrier Q)).baseT2
  domain := (CircleRegion.empty (NoCuts.carrier Q)).domain
  domain_interior := (CircleRegion.empty (NoCuts.carrier Q)).domain_interior
  proj := (CircleRegion.empty (NoCuts.carrier Q)).proj
  proj_smooth := (CircleRegion.empty (NoCuts.carrier Q)).proj_smooth
  proj_submersion := (CircleRegion.empty (NoCuts.carrier Q)).proj_submersion
  neighborhood := (CircleRegion.empty (NoCuts.carrier Q)).neighborhood
  mem_neighborhood := (CircleRegion.empty (NoCuts.carrier Q)).mem_neighborhood
  trivialization := (CircleRegion.empty (NoCuts.carrier Q)).trivialization
  projection_trivialization := (CircleRegion.empty (NoCuts.carrier Q)).projection_trivialization
  cbase := ∅
  cbase_compact := isCompact_empty


def zeroEdges := emptyEdges standardThreeSphere

def zeroCircles := emptyCircles standardThreeSphere

def slimEdges := emptyEdges sphereTwoTimesCircleLift

def slimCircles := emptyCircles sphereTwoTimesCircleLift

theorem emptyEdgePiece (Q : ConnectedClosedOrientedManifold.{0} 3) :
    (emptyEdges Q).edgePiece = ∅ := by
  apply eq_empty_of_forall_notMem
  rintro x ⟨q, hq, rfl⟩
  exact (CircleRegion.false_of_bot (NoCuts.carrier Q) q).elim

theorem emptyEdgeVertical (Q : ConnectedClosedOrientedManifold.{0} 3) :
    (emptyEdges Q).vertical = ∅ := by
  apply eq_empty_of_forall_notMem
  rintro x ⟨q, hq, rfl⟩
  exact (CircleRegion.false_of_bot (NoCuts.carrier Q) q).elim

theorem emptyCircleRegion (Q : ConnectedClosedOrientedManifold.{0} 3) :
    (emptyCircles Q).region = ∅ := by
  apply eq_empty_of_forall_notMem
  rintro x ⟨q, hq, rfl⟩
  exact (CircleRegion.false_of_bot (NoCuts.carrier Q) q).elim

instance emptyEdgeComponents (Q : ConnectedClosedOrientedManifold.{0} 3) :
    IsEmpty (emptyEdges Q).EdgeBaseComponent :=
  ⟨fun C => (Classical.choose C.2).elim⟩

instance emptyEdgeEnds (Q : ConnectedClosedOrientedManifold.{0} 3) :
    IsEmpty (emptyEdges Q).EdgeEnd := ⟨fun e => e.1.elim⟩

def emptyEdgeModels (Q : ConnectedClosedOrientedManifold.{0} 3) :
    EdgeComponentModels (emptyEdges Q) where
  intervalCount := 0
  circleCount := 0
  componentEquiv := Equiv.equivOfIsEmpty (Fin 0 ⊕ Fin 0) (emptyEdges Q).EdgeBaseComponent
  intervalBase i := i.elim0
  intervalBase_embedding i := i.elim0
  intervalBase_range i := i.elim0
  circleBase j := j.elim0
  circleBase_embedding j := j.elim0
  circleBase_range j := j.elim0
  endpointEquiv := Equiv.equivOfIsEmpty (Fin 0 × Bool) (emptyEdges Q).EdgeEnd
  endpointEquiv_apply i := i.elim0
  intervalTriv i := i.elim0
  intervalTriv_range i := i.elim0
  intervalTriv_proj i := i.elim0
  intervalTriv_disk i := i.elim0
  intervalTriv_rim i := i.elim0
  circleTriv j := j.elim0
  circleTriv_smooth j := j.elim0
  circleTriv_mfderiv j := j.elim0
  circleTriv_injective j := j.elim0
  circleTriv_range j := j.elim0
  circleTriv_proj j := j.elim0
  circleTriv_disk j := j.elim0
  circleTriv_rim j := j.elim0


def configurationZero : (b : Bool) → ZeroDomains (configurationW b)
  | false => zeroDomains
  | true => slimZero

def configurationCusps (b : Bool) : CuspCores (configurationW b)
    (BoundaryTori.empty (configurationW b)) := emptyCusps (configurationQ b)

def configurationSlim : (b : Bool) → SlimPiecesV2 (configurationW b)
    (configurationZero b) (configurationCusps b)
  | false => zeroSlim
  | true => slimPieces

def configurationEdgeBundle (b : Bool) : EdgeBundle (configurationW b) :=
  emptyEdges (configurationQ b)

def configurationCircleBundle (b : Bool) : CircleBundle (configurationW b) :=
  emptyCircles (configurationQ b)

def configurationIndex : (b : Bool) → (configurationSlim b).RowIndex
  | false => .inl (0 : Fin 1)
  | true => .inr (.inr (0 : Fin 1))

theorem configurationIndex_eq (b : Bool) (a : (configurationSlim b).RowIndex) :
    a = configurationIndex b := by
  cases b
  · rcases a with i | c | j
    · exact congrArg Sum.inl (Subsingleton.elim (α := Fin 1) i 0)
    · exact c.elim0
    · exact j.elim0
  · rcases a with i | c | j
    · exact i.elim0
    · exact c.elim0
    · exact congrArg (fun k : Fin 1 => Sum.inr (Sum.inr k))
        (Subsingleton.elim (α := Fin 1) j (0 : Fin 1))

theorem configurationRowSet (b : Bool) (a : (configurationSlim b).RowIndex) :
    (configurationSlim b).rowSet a = univ := by
  cases b
  · rcases a with i | c | j
    · exact zeroClosedPiece_cover
    · exact c.elim0
    · exact j.elim0
  · rcases a with i | c | j
    · exact i.elim0
    · exact c.elim0
    · exact wholePiece_range sphereTwoTimesCircleLift

theorem configurationPieceIndex (b : Bool)
    (a : (configurationSlim b).RowIndex ⊕ Bool)
    (hne : (allPieces (configurationSlim b) (configurationEdgeBundle b)
      (configurationCircleBundle b) a).Nonempty) : a = .inl (configurationIndex b) := by
  rcases a with a | c
  · exact congrArg Sum.inl (configurationIndex_eq b a)
  · cases c
    · change (emptyCircles (configurationQ b)).region.Nonempty at hne
      rw [emptyCircleRegion] at hne
      rcases hne with ⟨x, hx⟩
      exact hx.elim
    · change (emptyEdges (configurationQ b)).edgePiece.Nonempty at hne
      rw [emptyEdgePiece] at hne
      rcases hne with ⟨x, hx⟩
      exact hx.elim

theorem zeroRegionM1 : regionM1 zeroDomains zeroCusps = ∅ := by
  have hz : (⋃ i, range (zeroDomains.piece i).map) = univ := by
    refine eq_univ_of_univ_subset fun x hx => mem_iUnion.2 ⟨(0 : Fin 1), ?_⟩
    exact zeroClosedPiece_cover.symm ▸ mem_univ x
  unfold regionM1
  rw [hz, univ_union, interior_univ, compl_univ]

theorem slimRegionM1 : regionM1 slimZero slimCusps = univ := by
  unfold regionM1 slimZero slimCusps emptyCusps
  simp only [iUnion_of_empty, empty_union, interior_empty, compl_empty]

theorem slimPieces_union : slimPieces.union = univ := by
  refine eq_univ_of_univ_subset fun x hx => mem_iUnion.2 ⟨(0 : Fin 1), ?_⟩
  exact (wholePiece_range sphereTwoTimesCircleLift).symm ▸ mem_univ x

theorem relativeInteriorUniv (X : Type*) [TopologicalSpace X] :
    relInt (univ : Set X) univ = univ := by
  unfold relInt
  rw [preimage_univ, interior_univ]
  refine eq_univ_of_univ_subset fun x hx => ?_
  exact ⟨⟨x, mem_univ x⟩, mem_univ _, rfl⟩

theorem configurationRegionM2 (b : Bool) : regionM2 (configurationSlim b) = ∅ := by
  cases b
  · change regionM2 zeroSlim = ∅
    unfold regionM2
    rw [zeroRegionM1, empty_sdiff]
  · change regionM2 slimPieces = ∅
    unfold regionM2
    rw [slimRegionM1, slimPieces_union, relativeInteriorUniv, sdiff_self]

theorem configurationRegionM3 (b : Bool) :
    regionM3 (configurationSlim b) (configurationEdgeBundle b) = ∅ := by
  unfold regionM3
  rw [configurationRegionM2, empty_sdiff]

instance configurationEndsEmpty (b : Bool) : IsEmpty (configurationSlim b).End := by
  refine ⟨?_⟩
  intro e
  cases b
  · exact e.1.1.elim0
  · exact e.2

instance configurationNewEndsEmpty (b : Bool) : IsEmpty (configurationSlim b).NewEnd :=
  ⟨fun e => isEmptyElim e.1⟩

instance configurationSharedEmpty (b : Bool) : IsEmpty (ActualSharedFace (configurationSlim b)) :=
  ⟨fun e => isEmptyElim e.1⟩

instance configurationResidualEmpty (b : Bool) :
    IsEmpty (configurationSlim b).ResidualFace := by
  refine ⟨?_⟩
  intro F
  rcases F with F | e
  · rcases F.1 with F | F
    · cases b
      · exact noWholeFace standardThreeSphere F.2
      · exact F.1.elim0
    · exact F.1.elim0
  · exact isEmptyElim e

theorem configurationBoundaryM2 (b : Bool) : (configurationSlim b).boundaryM2 = ∅ := by
  unfold SlimPiecesV2.boundaryM2
  exact iUnion_of_empty _

def configurationJunctions (b : Bool) : JunctionsV2 (configurationW b)
    (BoundaryTori.empty (configurationW b)) (configurationZero b) (configurationCusps b)
    (configurationSlim b) (configurationEdgeBundle b) (configurationCircleBundle b) where
  cover := by
    refine eq_univ_of_univ_subset fun x hx => mem_iUnion.2
      ⟨.inl (configurationIndex b), ?_⟩
    change x ∈ (configurationSlim b).rowSet (configurationIndex b)
    rw [configurationRowSet]
    exact mem_univ x
  interiors_disjoint := by
    intro a a' h
    apply disjoint_left.2
    intro x hx hx'
    have ha := configurationPieceIndex b a ⟨x, interior_subset hx⟩
    have ha' := configurationPieceIndex b a' ⟨x, interior_subset hx'⟩
    exact (h (ha.trans ha'.symm)).elim
  shared_eq e := isEmptyElim e
  zero_cusp_disjoint i c := c.elim0
  horizontal e := e.1.elim
  horizontal_disk e := e.1.elim
  edge_faces F := ((configurationResidualEmpty b).false F).elim
  rimBase c := c.elim
  rimBase_smooth c hc := c.elim
  rim_fibre c := c.elim
  edge_region := by
    change (emptyEdges (configurationQ b)).edgePiece ∩
      (emptyCircles (configurationQ b)).region = (emptyEdges (configurationQ b)).vertical
    rw [emptyEdgePiece, emptyEdgeVertical, empty_inter]
  local_faces c := c.elim
  region_eq := by
    rw [configurationRegionM3]
    exact (emptyCircleRegion (configurationQ b)).symm
  frontier_M2 := by
    rw [configurationRegionM2, configurationBoundaryM2, frontier_empty]
  region_boundary := by
    rw [configurationBoundaryM2, inter_empty, empty_sdiff]
  slim_M2 := by
    rw [configurationRegionM2, inter_empty]
    exact (iUnion_of_empty _).symm
  shared_removed σ := ((configurationSharedEmpty b).false σ).elim

def configurationTubes (b : Bool) : LabelledCornerTubes (configurationJunctions b) where
  base e := e.1.elim
  rimBase_mem e := e.1.elim
  chart e := e.1.elim
  chart_source e := e.1.elim
  chart_center e := e.1.elim
  tube_source e := e.1.elim
  tube_near e := e.1.elim
  height_eq e := e.1.elim
  face_eq e := e.1.elim
  descended e := e.1.elim
  descended_smooth e := e.1.elim
  descended_regular e := e.1.elim
  descended_eq e := e.1.elim
  vertex_side {e} := e.1.elim
  edge_side {e} := e.1.elim
  region_side {e} := e.1.elim

def configurationRows (b : Bool) : FC39RowsV2 (configurationW b)
    (BoundaryTori.empty (configurationW b)) where
  zero := configurationZero b
  cusp := configurationCusps b
  slim := configurationSlim b
  edge := configurationEdgeBundle b
  edgeModels := emptyEdgeModels (configurationQ b)
  circle := configurationCircleBundle b
  junctions := configurationJunctions b
  labelledTubes := configurationTubes b

end GC.GraphManifold.Assembly.FC39P0.X136
