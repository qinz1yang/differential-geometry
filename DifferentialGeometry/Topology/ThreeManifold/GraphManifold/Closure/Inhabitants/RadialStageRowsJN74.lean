import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialStageSlimJN74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageJunctions74

/-!
# Draft 74, G5 (X135 radial `D² × S¹`): the cut-dependent row structures

Lane S-JUNCTIONS2 (suffix `_JN74`). The slim cut pieces (the X135 slim pieces over the one
component `[-1/2, -1/4]` of `D₃`), the identities of the cut sets with the X135 piece sets
(`slimSet = radialSlims.union`, `edgeSet = edgePiece`, `circleRegion = region`, `M₂`, `M₃`), the
restricted edge / circle facts of the whole-base kit and the component models, assembled into
`StageCutRows74 radialStage74 radialCut74`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

local instance carrierCharts_StageRowsJN74 :
    ChartedSpace (EuclideanHalfSpace 3) carrier.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_StageRowsJN74 : IsManifold (𝓡∂ 3) ∞ carrier.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

local instance radialSlimsCountSubsingleton74 : Subsingleton (Fin radialSlims.count) :=
  inferInstanceAs (Subsingleton (Fin 1))

/-- The single component of `D₃ = [-1/2, -1/4]`. -/
def radialK3Comp74 : ActualComponent radialCut74.D₃ :=
  ⟨radialK3_74, e1Equiv74 (-(1 / 2 : ℝ)), ⟨-(1 / 2 : ℝ), ⟨le_refl _, by norm_num⟩, rfl⟩,
    (radialK3_74_connected.connectedComponentIn ⟨-(1 / 2 : ℝ), ⟨le_refl _, by norm_num⟩,
      rfl⟩).symm⟩

theorem radialSlim_piece_range74 (j : Fin radialSlims.count) :
    range (radialSlims.piece j).map = radialSlims.union := by
  have hj : j = ⟨0, by decide⟩ := Subsingleton.elim _ _
  subst hj
  ext x
  constructor
  · intro hx
    exact mem_iUnion.2 ⟨⟨0, by decide⟩, hx⟩
  · intro hx
    obtain ⟨k, hk⟩ := mem_iUnion.1 hx
    have hk' : k = ⟨0, by decide⟩ := Subsingleton.elim _ _
    subst hk'
    exact hk

/-- **The slim cut pieces of the radial solid torus**: the X135 slim band over the component
`[-1/2, -1/4]` of `D₃`. -/
def radialSlimCut74 : SlimCutPieces74 radialStage74 radialCut74 where
  pieces := radialSlims
  componentEquiv :=
    { toFun := fun _ => radialK3Comp74
      invFun := fun _ => ⟨0, by decide⟩
      left_inv := fun j => Subsingleton.elim _ _
      right_inv := fun c => by
        apply Subtype.ext
        obtain ⟨x, hx, hc⟩ := c.2
        change radialK3_74 = c.1
        rw [hc]
        exact (radialK3_74_connected.connectedComponentIn hx).symm }
  piece_range j := by
    rw [radialSlim_piece_range74 j]
    exact radialCut74_slimSet.symm
  shared_eq e F he := radial_shared_eq e F he

theorem radialCut74_edgeSet : radialCut74.edgeSet = radialEdgeBundle.edgePiece :=
  edgeSet_ofBundles74 radialZeros radialCuspCores radialSlimStage74 radialEdgeBundle
    radialCircleBundle ⟨(1 : Circle), mem_univ _⟩ radialK3_74 radialK3_74 radialK3_74_compact
    radialK3_74_compact (inter_univ _).symm (by
      change (∅ : Set (EuclideanSpace ℝ (Fin 1))) ∪ ∅ ⊆ interior radialK3_74
      simp) (disjoint_empty _)

theorem radialCut74_circleRegion : radialCut74.circleRegion = radialCircleBundle.region :=
  circleRegion_ofBundles74 radialZeros radialCuspCores radialSlimStage74 radialEdgeBundle
    radialCircleBundle ⟨(1 : Circle), mem_univ _⟩ radialK3_74 radialK3_74 radialK3_74_compact
    radialK3_74_compact (inter_univ _).symm (by
      change (∅ : Set (EuclideanSpace ℝ (Fin 1))) ∪ ∅ ⊆ interior radialK3_74
      simp) (disjoint_empty _)

theorem radialCut74_M₂ : radialCut74.M₂ = regionM2 radialSlims := by
  change regionM1 radialZeros radialCuspCores \
      relInt (regionM1 radialZeros radialCuspCores) radialCut74.slimSet = _
  rw [radialCut74_slimSet]
  rfl

theorem radialCut74_M₃ : radialCut74.M₃ = radialCircleBundle.region := by
  change radialCut74.M₂ \ relInt radialCut74.M₂ radialCut74.edgeSet = _
  rw [radialCut74_M₂, radialCut74_edgeSet]
  exact radial_M3_circle

theorem radialReq74 :
    radialSlimStage74.slabImage ∪ radialSlimStage74.facePoints ⊆ interior radialK3_74 := by
  change (∅ : Set (EuclideanSpace ℝ (Fin 1))) ∪ ∅ ⊆ interior radialK3_74
  simp

/-- The edge facts of the radial cut (the whole-base kit applied to the X135 edge bundle). -/
theorem radialEdgeFacts74 : EdgeCutFacts74 radialStage74 radialCut74 :=
  edgeCutFacts_ofBundles74 radialZeros radialCuspCores radialSlimStage74 radialEdgeBundle
    radialCircleBundle ⟨(1 : Circle), mem_univ _⟩ radialK3_74 radialK3_74 radialK3_74_compact
    radialK3_74_compact (inter_univ _).symm radialReq74 (disjoint_empty _)

/-- The circle facts of the radial cut (the kit applied to the X135 circle bundle; saturation by
the X135 height identities). -/
def radialCircleFacts74 : CircleCutFacts74 radialStage74 radialCut74 :=
  circleCutFacts_ofBundles74 radialZeros radialCuspCores radialSlimStage74 radialEdgeBundle
    radialCircleBundle ⟨(1 : Circle), mem_univ _⟩ radialK3_74 radialK3_74 radialK3_74_compact
    radialK3_74_compact (inter_univ _).symm radialReq74 (disjoint_empty _)
    (radialCut74_M₃.trans radialCut74_circleRegion.symm)

/-- The component models of the radial cut (X135's models carried over `⊤`). -/
def radialEdgeModels74 :
    EdgeComponentModels (edgeBundle74 radialStage74 radialCut74 radialEdgeFacts74) :=
  edgeModels_ofBundles74 radialZeros radialCuspCores radialSlimStage74 radialEdgeBundle
    radialCircleBundle ⟨(1 : Circle), mem_univ _⟩ radialK3_74 radialK3_74 radialK3_74_compact
    radialK3_74_compact (inter_univ _).symm radialReq74 (disjoint_empty _)
    radialEdgeComponentModels

/-- **The cut-dependent row structures of the radial solid torus.** -/
def radialRows74 : StageCutRows74 radialStage74 radialCut74 where
  slim := radialSlimCut74
  edgeFacts := radialEdgeFacts74
  circleFacts := radialCircleFacts74
  edgeModels := radialEdgeModels74

end GC.GraphManifold.Assembly.FC39P0.X135Radial
