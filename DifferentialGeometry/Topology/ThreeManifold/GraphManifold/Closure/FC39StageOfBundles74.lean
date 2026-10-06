import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageSlimOnly74

/-!
# Draft 74, A0 / D from existing bundles: the stage geometry and cut choice with `V = ⊤`

Lane S-JUNCTIONS2 (suffix `_JN74`), G5, step 1. For an existing `EdgeBundle P` and `CircleBundle R`
(rows of an older decomposition) the stage geometry whose edge stage is `P`'s map and height
(`EdgeStage74.ofBundle74`), whose circle stage is `R`'s map (`StageProj74.ofCircleBundle74`), with
an arbitrary slim stage, and the cut choice with the whole bases as good open bases
(`edgeBaseOpen = circleBaseOpen = ⊤`, `C₂ = P.cbase`, `C₁ = R.cbase`). The sets of the cut are the
sets of the bundles: `edgeSet = P.edgePiece`, `circleRegion = R.region`, and over `⊤` the restricted
parents are the parents.
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

/-- The edge stage of an existing edge bundle. -/
def EdgeStage74.ofBundle74 (P : EdgeBundle W) : EdgeStage74 W where
  Base := P.Base
  parent := P.source
  parent_interior := P.source_interior
  proj := P.proj
  proj_smooth := P.proj_smooth
  proj_submersion := P.proj_submersion
  height := P.height
  height_smooth := P.height_smooth
  level := P.level

/-- The circle stage of an existing circle bundle. -/
def StageProj74.ofCircleBundle74 (R : CircleBundle W) : StageProj74 W 2 where
  Base := R.Base
  parent := R.domain
  parent_interior := R.domain_interior
  proj := R.proj
  proj_smooth := R.proj_smooth
  proj_submersion := R.proj_submersion

/-- The stage geometry of given zero / cusp / slim data and existing edge and circle bundles. -/
def SmoothStageGeometry74.ofBundles74 (Z : ZeroDomains W) (C : CuspCores W E) (Sl : SlimStage74 W)
    (P : EdgeBundle W) (R : CircleBundle W) : SmoothStageGeometry74 W E where
  zero := Z
  cusp := C
  slim := Sl
  edge := EdgeStage74.ofBundle74 P
  circle := StageProj74.ofCircleBundle74 R

/-- The cut choice with the whole bases as good open bases (`P.cbase` nonempty, so that
`edgeBaseOpen ≠ ⊥` is allowed). -/
def StageCutChoice74.ofBundles74 (Z : ZeroDomains W) (C : CuspCores W E) (Sl : SlimStage74 W)
    (P : EdgeBundle W) (R : CircleBundle W) (hP : P.cbase.Nonempty) (K₃ D₃ : Set Sl.Base)
    (hK : IsCompact K₃) (hD : IsCompact D₃) (hD₃ : D₃ = K₃ ∩ Sl.C₃)
    (hreq : Sl.slabImage ∪ Sl.facePoints ⊆ interior K₃)
    (hfaces : Disjoint (frontier K₃) Sl.facePoints) :
    StageCutChoice74 (SmoothStageGeometry74.ofBundles74 Z C Sl P R) where
  K₃ := K₃
  D₃ := D₃
  C₂ := P.cbase
  C₁ := R.cbase
  edgeBaseOpen := ⊤
  circleBaseOpen := ⊤
  K₃_compact := hK
  D₃_compact := hD
  D₃_eq := hD₃
  K₃_req := hreq
  K₃_faces := hfaces
  C₂_sub := fun _ _ => TopologicalSpace.Opens.mem_top _
  C₁_sub := fun _ _ => TopologicalSpace.Opens.mem_top _
  edgeBaseOpen_empty := fun h => (hP.ne_empty h).elim

section Sets

variable (Z : ZeroDomains W) (C : CuspCores W E) (Sl : SlimStage74 W)
  (P : EdgeBundle W) (R : CircleBundle W) (hP : P.cbase.Nonempty) (K₃ D₃ : Set Sl.Base)
  (hK : IsCompact K₃) (hD : IsCompact D₃) (hD₃ : D₃ = K₃ ∩ Sl.C₃)
  (hreq : Sl.slabImage ∪ Sl.facePoints ⊆ interior K₃)
  (hfaces : Disjoint (frontier K₃) Sl.facePoints)

/-- The edge piece of the cut is the edge piece of the bundle. -/
theorem edgeSet_ofBundles74 :
    (StageCutChoice74.ofBundles74 Z C Sl P R hP K₃ D₃ hK hD hD₃ hreq hfaces).edgeSet =
      P.edgePiece := by
  ext x
  constructor
  · rintro ⟨h, hc, hl⟩
    exact ⟨⟨x, h⟩, ⟨hc, hl⟩, rfl⟩
  · rintro ⟨y, ⟨hc, hl⟩, rfl⟩
    exact ⟨y.2, hc, hl⟩

/-- The circle region of the cut is the region of the bundle. -/
theorem circleRegion_ofBundles74 :
    (StageCutChoice74.ofBundles74 Z C Sl P R hP K₃ D₃ hK hD hD₃ hreq hfaces).circleRegion =
      R.region := by
  ext x
  constructor
  · rintro ⟨h, hc⟩
    exact ⟨⟨x, h⟩, hc, rfl⟩
  · rintro ⟨y, hc, rfl⟩
    exact ⟨y.2, hc⟩

end Sets

end GC.GraphManifold.Assembly.FC39P0
