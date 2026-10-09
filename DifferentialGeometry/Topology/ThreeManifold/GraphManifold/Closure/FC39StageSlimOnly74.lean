import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageGeometryH74

/-!
# Draft 74, A0 inhabitants (part 1): slim-only stage families (empty edge and circle stages)

Lane S-JUNCTIONS (suffix `_JN74`). For ANY compact carrier `W`, zero and cusp families and slim
stage there are the empty edge and circle stages (base `PEmpty`, parent `⊥`), and the contracts
`A`, `D`, `H` of `FC39StageGeometryA74.lean` / `FC39StageGeometryH74.lean` reduce to a few
hypotheses: `M₂ = ∅`, no residual face, no shared face and the FDC04 cover. The empty slim stage
gives the empty family (the S³ singleton), a slim stage over a circle with one whole component gives
the closed `S² × S¹` loop. These are the regressions / non-vacuity checks of D74-19; the production
inhabitants come from the row lanes.
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

/-- The empty smooth stage of base dimension `k` (base `PEmpty`, parent `⊥`). -/
def StageProj74.empty (W : CompactCarrier.{u}) (k : ℕ) : StageProj74 W k where
  Base := PEmpty.{u + 1}
  baseCharts := ChartedSpace.empty _ _
  baseSmooth := by
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) PEmpty.{u + 1} := ChartedSpace.empty _ _
    exact IsManifold.empty ∞
  parent := ⊥
  parent_interior := by simp
  proj := CircleRegion.emptyProj W
  proj_smooth x := (CircleRegion.false_of_bot W x).elim
  proj_submersion x := (CircleRegion.false_of_bot W x).elim

/-- The empty slim stage. -/
def SlimStage74.empty (W : CompactCarrier.{u}) : SlimStage74 W where
  toStageProj74 := StageProj74.empty W 1
  C₃ := ∅
  slabImage := ∅
  facePoints := ∅

/-- The empty edge stage. -/
def EdgeStage74.empty (W : CompactCarrier.{u}) : EdgeStage74 W where
  toStageProj74 := StageProj74.empty W 1
  height x := (CircleRegion.false_of_bot W x).elim
  height_smooth x := (CircleRegion.false_of_bot W x).elim
  level := 0

/-- The stage geometry with the given zero and cusp families and slim stage and empty edge /
circle stages. -/
def SmoothStageGeometry74.ofSlim74 (Z : ZeroDomains W) (C : CuspCores W E) (Sl : SlimStage74 W) :
    SmoothStageGeometry74 W E where
  zero := Z
  cusp := C
  slim := Sl
  edge := EdgeStage74.empty W
  circle := StageProj74.empty W 2

/-- The cut choice of a slim-only family: the slim base domains `K₃`, `D₃` and empty edge / circle
bases. -/
def StageCutChoice74.ofSlim74 (Z : ZeroDomains W) (C : CuspCores W E) (Sl : SlimStage74 W)
    (K₃ D₃ : Set Sl.Base) (hK : IsCompact K₃) (hD : IsCompact D₃) (hD₃ : D₃ = K₃ ∩ Sl.C₃)
    (hreq : Sl.slabImage ∪ Sl.facePoints ⊆ interior K₃)
    (hfaces : Disjoint (frontier K₃) Sl.facePoints) :
    StageCutChoice74 (SmoothStageGeometry74.ofSlim74 Z C Sl) where
  K₃ := K₃
  D₃ := D₃
  C₂ := ∅
  C₁ := ∅
  edgeBaseOpen := ⊥
  circleBaseOpen := ⊥
  K₃_compact := hK
  D₃_compact := hD
  D₃_eq := hD₃
  K₃_req := hreq
  K₃_faces := hfaces
  C₂_sub := subset_refl _
  C₁_sub := subset_refl _
  edgeBaseOpen_empty := fun _ => rfl

/-! ## The cut geometry of a slim-only family -/

section SlimOnly

variable (Z : ZeroDomains W) (C : CuspCores W E) (Sl : SlimStage74 W)
  (D : StageCutChoice74 (SmoothStageGeometry74.ofSlim74 Z C Sl))

theorem slimOnly74_edgeSource_isEmpty : IsEmpty D.edgeSource :=
  ⟨fun x => CircleRegion.false_of_bot W
    ⟨x.1, ((SmoothStageGeometry74.ofSlim74 Z C Sl).edge.exists_of_mem_restrictParent x.2).1⟩⟩

theorem slimOnly74_circleSource_isEmpty : IsEmpty D.circleSource :=
  ⟨fun x => CircleRegion.false_of_bot W
    ⟨x.1, ((SmoothStageGeometry74.ofSlim74 Z C Sl).circle.exists_of_mem_restrictParent x.2).1⟩⟩

theorem slimOnly74_edgeSet : D.edgeSet = ∅ :=
  eq_empty_of_forall_notMem fun x ⟨h, _, _⟩ => CircleRegion.false_of_bot W ⟨x, h⟩

theorem slimOnly74_circleRegion : D.circleRegion = ∅ :=
  eq_empty_of_forall_notMem fun x ⟨h, _⟩ => CircleRegion.false_of_bot W ⟨x, h⟩

theorem slimOnly74_M₃ (hM2 : D.M₂ = ∅) : D.M₃ = ∅ := by
  change D.M₂ \ _ = ∅
  rw [hM2, empty_sdiff]

/-- The cut-dependent facts of the empty edge stage. -/
theorem EdgeCutFacts74.slimOnly74 : EdgeCutFacts74 (SmoothStageGeometry74.ofSlim74 Z C Sl) D where
  rank_two x := (slimOnly74_edgeSource_isEmpty Z C Sl D).false x |>.elim
  proper K _ := by
    convert isCompact_empty using 1
    exact eq_empty_of_forall_notMem fun _ ⟨x, _, _⟩ =>
      (slimOnly74_edgeSource_isEmpty Z C Sl D).false x
  fibre_disk c := PEmpty.elim c.1
  cbase_compact := by
    convert isCompact_empty using 1
    exact eq_empty_of_forall_notMem fun c _ => PEmpty.elim c.1
  cbase_domain c _ := PEmpty.elim c.1

/-- The cut-dependent facts of the empty circle stage (`D.M₃ = ∅` gives the saturation). -/
def CircleCutFacts74.slimOnly74 (hM3 : D.M₃ = ∅) :
    CircleCutFacts74 (SmoothStageGeometry74.ofSlim74 Z C Sl) D where
  neighborhood c := PEmpty.elim c.1
  mem_neighborhood c := PEmpty.elim c.1
  trivialization c := PEmpty.elim c.1
  projection_trivialization c := PEmpty.elim c.1
  proper K _ := by
    convert isCompact_empty using 1
    exact eq_empty_of_forall_notMem fun _ ⟨x, _, _⟩ =>
      (slimOnly74_circleSource_isEmpty Z C Sl D).false x
  cbase_compact := by
    convert isCompact_empty using 1
    exact eq_empty_of_forall_notMem fun c _ => PEmpty.elim c.1
  saturation := hM3.trans (slimOnly74_circleRegion Z C Sl D).symm

instance slimOnly74_edgeBaseComponent_isEmpty :
    IsEmpty (edgeBundle74 (SmoothStageGeometry74.ofSlim74 Z C Sl) D
      (EdgeCutFacts74.slimOnly74 Z C Sl D)).EdgeBaseComponent :=
  ⟨fun K => by
    obtain ⟨x, -, -⟩ := K.2
    exact PEmpty.elim x.1⟩

instance slimOnly74_edgeEnd_isEmpty :
    IsEmpty (edgeBundle74 (SmoothStageGeometry74.ofSlim74 Z C Sl) D
      (EdgeCutFacts74.slimOnly74 Z C Sl D)).EdgeEnd :=
  ⟨fun e => PEmpty.elim e.1.1⟩

/-- The empty edge component export. -/
def EdgeComponentModels.slimOnly74 :
    EdgeComponentModels (edgeBundle74 (SmoothStageGeometry74.ofSlim74 Z C Sl) D
      (EdgeCutFacts74.slimOnly74 Z C Sl D)) where
  intervalCount := 0
  circleCount := 0
  componentEquiv := Equiv.equivOfIsEmpty _ _
  intervalBase i := i.elim0
  intervalBase_embedding i := i.elim0
  intervalBase_range i := i.elim0
  circleBase j := j.elim0
  circleBase_embedding j := j.elim0
  circleBase_range j := j.elim0
  endpointEquiv := Equiv.equivOfIsEmpty _ _
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

/-- The cut-dependent rows of a slim-only family. -/
def StageCutRows74.slimOnly74 (S : SlimCutPieces74 (SmoothStageGeometry74.ofSlim74 Z C Sl) D)
    (hM3 : D.M₃ = ∅) : StageCutRows74 (SmoothStageGeometry74.ofSlim74 Z C Sl) D where
  slim := S
  edgeFacts := EdgeCutFacts74.slimOnly74 Z C Sl D
  circleFacts := CircleCutFacts74.slimOnly74 Z C Sl D hM3
  edgeModels := EdgeComponentModels.slimOnly74 Z C Sl D

theorem slimOnly74_vertical (S : SlimCutPieces74 (SmoothStageGeometry74.ofSlim74 Z C Sl) D)
    (hM3 : D.M₃ = ∅) : (StageCutRows74.slimOnly74 Z C Sl D S hM3).edge.vertical = ∅ :=
  eq_empty_of_forall_notMem fun _ ⟨x, _, _⟩ => (slimOnly74_edgeSource_isEmpty Z C Sl D).false x

theorem slimOnly74_horizontalDisks (S : SlimCutPieces74 (SmoothStageGeometry74.ofSlim74 Z C Sl) D)
    (hM3 : D.M₃ = ∅) : (StageCutRows74.slimOnly74 Z C Sl D S hM3).edge.horizontalDisks = ∅ :=
  iUnion_eq_empty.2 fun e => PEmpty.elim e.1.1

/-- **The cut geometry of a slim-only family**: given the slim pieces over the components of `D₃`,
`M₂ = ∅`, no residual face and no shared face, the FDC04 cover, the slim set inside `M₁` and the
zero / cusp separation. -/
def StageCutGeometry74.slimOnly74 (S : SlimCutPieces74 (SmoothStageGeometry74.ofSlim74 Z C Sl) D)
    (hM2 : D.M₂ = ∅)
    (hcover : ((⋃ i, range (Z.piece i).map) ∪ ⋃ b, range (C.piece b).map) ∪ D.slimSet ∪ D.M₂ =
      univ)
    (hsub : D.slimSet ⊆ regionM1 Z C)
    (hZC : ∀ i b, Disjoint (range (Z.piece i).map) (range (C.piece b).map))
    (hRes : IsEmpty S.pieces.ResidualFace) (hSh : IsEmpty (ActualSharedFace S.pieces)) :
    StageCutGeometry74 (SmoothStageGeometry74.ofSlim74 Z C Sl) D where
  rows := StageCutRows74.slimOnly74 Z C Sl D S (slimOnly74_M₃ Z C Sl D hM2)
  cover :=
    { cover := hcover
      slimSet_subset_M₁ := hsub
      edgeSet_subset_M₂ := by
        rw [slimOnly74_edgeSet Z C Sl D]
        exact empty_subset _
      zero_cusp_disjoint := hZC }
  faces :=
    { horizontal := fun e => PEmpty.elim e.1.1
      horizontal_disk := fun e => PEmpty.elim e.1.1
      edge_faces := fun F => (hRes.false F).elim
      frontier_M2 := by
        rw [hM2, frontier_empty]
        exact (iUnion_eq_empty.2 fun F => (hRes.false F).elim).symm
      region_boundary := by
        rw [slimOnly74_M₃ Z C Sl D hM2, empty_inter]
        change ∅ = S.pieces.boundaryM2 \ _
        rw [show S.pieces.boundaryM2 = ∅ from iUnion_eq_empty.2 fun F => (hRes.false F).elim,
          empty_sdiff]
      slim_M2 := by
        rw [hM2, inter_empty]
        exact (iUnion_eq_empty.2 fun e => (hRes.false (Sum.inr e)).elim).symm
      shared_removed := fun σ => (hSh.false σ).elim }
  rims :=
    { rimBase := fun c => PEmpty.elim c.1
      rimBase_smooth := fun c _ => PEmpty.elim c.1
      rim_fibre := fun c _ => PEmpty.elim c.1
      edge_region := by
        rw [slimOnly74_edgeSet Z C Sl D, empty_inter]
        exact (slimOnly74_vertical Z C Sl D S (slimOnly74_M₃ Z C Sl D hM2)).symm
      local_faces := fun c _ => PEmpty.elim c.1 }
  corners :=
    { descent := fun e => PEmpty.elim e.1.1
      rank := fun e => PEmpty.elim e.1.1
      descended := fun e => PEmpty.elim e.1.1 }

end SlimOnly

end GC.GraphManifold.Assembly.FC39P0
