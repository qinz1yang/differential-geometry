import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageTubes74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageRowsLink74

/-!
# Draft 74, package J1: `rows_of_smooth_stage_geometry74`

Lane S-JUNCTIONS (suffix `_JN74`). The shared assembler (D74-15): from the actual stage geometry `A`
(selected zero / cusp core models, the slim, edge and circle stages), the explicit cut choice `D`
and the cut geometry `H` there is a `FC39RowsV2 W E` whose parts are

* `zero = A.zero`, `cusp = A.cusp`,
* `slim = H.rows.slim.pieces`, `edgeModels = H.rows.edgeModels`,
* `edge = edgeBundle74 A D …`, `circle = circleBundle74 A D …` (the ACTUAL restrictions of `A.edge`,
  `A.circle` to the good open bases),
* `junctions = junctions_of_actual_decomposition74 A D H` (J0), `labelledTubes =
  labelledCornerTubes_of_actual_decomposition74 A D H` (J0 via R1),

together with the abstract equality table `StageRowsLink74 A D Rw` (D74-5 on plain data of `W`).
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

/-- **J1, the rows themselves**: the assembled `FC39RowsV2`. -/
def rowsOfStageGeometry74 (A : SmoothStageGeometry74 W E) (D : StageCutChoice74 A)
    (H : StageCutGeometry74 A D) : FC39RowsV2 W E where
  zero := A.zero
  cusp := A.cusp
  slim := H.rows.slimPieces
  edge := H.rows.edge
  edgeModels := H.rows.edgeModels
  circle := H.rows.circle
  junctions := junctions_of_actual_decomposition74 A D H
  labelledTubes := labelledCornerTubes_of_actual_decomposition74 A D H

/-- The identification of the edge base of the assembled rows with `↥D.edgeBaseOpen` (the identity,
since the base IS that subtype). -/
def edgeBaseEquiv74 (A : SmoothStageGeometry74 W E) (D : StageCutChoice74 A)
    (F : EdgeCutFacts74 A D) : (edgeBundle74 A D F).Base ≃ₘ⟮𝓡 1, 𝓡 1⟯ D.edgeBaseOpen :=
  Diffeomorph.refl (𝓡 1) D.edgeBaseOpen ∞

/-- The identification of the circle base of the assembled rows with `↥D.circleBaseOpen`. -/
def circleBaseEquiv74 (A : SmoothStageGeometry74 W E) (D : StageCutChoice74 A)
    (F : CircleCutFacts74 A D) : (circleBundle74 A D F).Base ≃ₘ⟮𝓡 2, 𝓡 2⟯ D.circleBaseOpen :=
  Diffeomorph.refl (𝓡 2) D.circleBaseOpen ∞

theorem edgeBase_cbase_JN74 (A : SmoothStageGeometry74 W E) (D : StageCutChoice74 A)
    (F : EdgeCutFacts74 A D) :
    Subtype.val '' (edgeBaseEquiv74 A D F '' (edgeBundle74 A D F).cbase) = D.C₂ := by
  ext c
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact hz
  · intro hc
    exact ⟨⟨c, D.C₂_sub hc⟩, ⟨⟨c, D.C₂_sub hc⟩, hc, rfl⟩, rfl⟩

theorem circleBase_cbase_JN74 (A : SmoothStageGeometry74 W E) (D : StageCutChoice74 A)
    (F : CircleCutFacts74 A D) :
    Subtype.val '' (circleBaseEquiv74 A D F '' (circleBundle74 A D F).cbase) = D.C₁ := by
  ext c
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact hz
  · intro hc
    exact ⟨⟨c, D.C₁_sub hc⟩, ⟨⟨c, D.C₁_sub hc⟩, hc, rfl⟩, rfl⟩

/-- The assembled rows satisfy the abstract equality table of D74-5. -/
theorem rowsOfStageGeometry74_link (A : SmoothStageGeometry74 W E) (D : StageCutChoice74 A)
    (H : StageCutGeometry74 A D) : StageRowsLink74 A D (rowsOfStageGeometry74 A D H) where
  zeroSlim :=
    { zero_eq := rfl
      cusp_eq := rfl
      slim_union := H.rows.slim.union_eq
      slim_components := ⟨H.rows.slim.componentEquiv, H.rows.slim.piece_range⟩ }
  edge :=
    { edge_source := rfl
      edge_base := ⟨edgeBaseEquiv74 A D H.rows.edgeFacts,
        fun x => ⟨A.edge.restrictParent_le _ x.2, rfl⟩,
        edgeBase_cbase_JN74 A D H.rows.edgeFacts⟩
      edge_height := fun x => ⟨A.edge.restrictParent_le _ x.2, rfl⟩
      edge_level := rfl
      edge_piece := H.rows.edgePiece_eq }
  circle :=
    { circle_domain := rfl
      circle_base := ⟨circleBaseEquiv74 A D H.rows.circleFacts,
        fun x => ⟨A.circle.restrictParent_le _ x.2, rfl⟩,
        circleBase_cbase_JN74 A D H.rows.circleFacts⟩
      circle_region := D.region_circleBundle74 H.rows.circleFacts }
  regions :=
    { regionM1_eq := rfl
      regionM2_eq := H.rows.regionM2_eq
      regionM3_eq := H.rows.regionM3_eq
      region_M3 := region_eq_M₃_JN74 H }

/-- **J1 (`rows_of_smooth_stage_geometry74`)**: the shared rows assembler of draft 74 (D74-15). -/
theorem rows_of_smooth_stage_geometry74 (A : SmoothStageGeometry74 W E) (D : StageCutChoice74 A)
    (H : StageCutGeometry74 A D) : ∃ Rw : FC39RowsV2 W E, StageRowsLink74 A D Rw :=
  ⟨rowsOfStageGeometry74 A D H, rowsOfStageGeometry74_link A D H⟩

end GC.GraphManifold.Assembly.FC39P0
