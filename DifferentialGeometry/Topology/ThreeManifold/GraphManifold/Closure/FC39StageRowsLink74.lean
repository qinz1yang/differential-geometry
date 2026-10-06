import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageGeometryH74

/-!
# Draft 74, D74-5: the abstract link `StageRowsLink74 A D Rw`

Lane S-JUNCTIONS (suffix `_JN74`). The abstract version of the frozen equality table of D74-5
(`ClosedRowsLinkAt74`, §2.1) on plain data of `W`: the rows `Rw` agree with the actual stage
geometry `A` and the cut choice `D`. Sets are subsets of `W.Carrier`; the bases of the rows are
identified with the chosen open base neighbourhoods by smooth equivalences carrying the final maps,
the heights, the levels and the compact bases. Four sub-records (`ZeroSlimLink74`, `EdgeLink74`,
`CircleLink74`, `RegionsLink74`), each with at most six fields.
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

/-- The zero / cusp families are those of `A`; the slim pieces are in bijection with the actual
components of `D₃`, each the WHOLE `f₃`-preimage of its component; their union is `f₃⁻¹(D₃)`. -/
structure ZeroSlimLink74 (A : SmoothStageGeometry74 W E) (D : StageCutChoice74 A)
    (Rw : FC39RowsV2 W E) : Prop where
  zero_eq : Rw.zero = A.zero
  cusp_eq : Rw.cusp = A.cusp
  slim_union : Rw.slim.union = D.slimSet
  slim_components : ∃ e : Fin Rw.slim.count ≃ ActualComponent D.D₃, ∀ j,
    range (Rw.slim.piece j).map =
      {x | ∃ h : x ∈ A.slim.parent, A.slim.proj ⟨x, h⟩ ∈ (e j).1}

/-- The edge bundle is the restriction of `A.edge` to the open good base `D.edgeBaseOpen`: the base
is smoothly identified with `↥D.edgeBaseOpen` through the final edge map `q₁`, the height and the
level are `A`'s, the compact base is `C₂`, the source is `q₁⁻¹(V)` and the edge piece is
`M^edge`. -/
structure EdgeLink74 (A : SmoothStageGeometry74 W E) (D : StageCutChoice74 A)
    (Rw : FC39RowsV2 W E) : Prop where
  edge_source : (Rw.edge.source : Set W.Carrier) = D.edgeSource
  edge_base : ∃ e : Rw.edge.Base ≃ₘ⟮𝓡 1, 𝓡 1⟯ D.edgeBaseOpen,
    (∀ x : Rw.edge.source, ∃ h : (x : W.Carrier) ∈ A.edge.parent,
      ((e (Rw.edge.proj x) : D.edgeBaseOpen) : A.edge.Base) = A.edge.proj ⟨x, h⟩) ∧
    Subtype.val '' (e '' Rw.edge.cbase) = D.C₂
  edge_height : ∀ x : Rw.edge.source, ∃ h : (x : W.Carrier) ∈ A.edge.parent,
    Rw.edge.height x = A.edge.height ⟨x, h⟩
  edge_level : Rw.edge.level = A.edge.level
  edge_piece : Rw.edge.edgePiece = D.edgeSet

/-- The circle bundle is the restriction of `A.circle` to the open good base `D.circleBaseOpen`:
the base is smoothly identified with `↥D.circleBaseOpen` through the final circle map `q₀`, the
compact base is `C₁`, the domain is `q₀⁻¹(V)` and the circle region is `q₀⁻¹(C₁)`. -/
structure CircleLink74 (A : SmoothStageGeometry74 W E) (D : StageCutChoice74 A)
    (Rw : FC39RowsV2 W E) : Prop where
  circle_domain : (Rw.circle.domain : Set W.Carrier) = D.circleSource
  circle_base : ∃ e : Rw.circle.Base ≃ₘ⟮𝓡 2, 𝓡 2⟯ D.circleBaseOpen,
    (∀ x : Rw.circle.domain, ∃ h : (x : W.Carrier) ∈ A.circle.parent,
      ((e (Rw.circle.proj x) : D.circleBaseOpen) : A.circle.Base) = A.circle.proj ⟨x, h⟩) ∧
    Subtype.val '' (e '' Rw.circle.cbase) = D.C₁
  circle_region : Rw.circle.region = D.circleRegion

/-- The relative regions of the rows are the cut's `M₁ / M₂ / M₃` (relative interiors, §5.7), and
the circle region is `M₃` (FDC03 saturation). -/
structure RegionsLink74 (A : SmoothStageGeometry74 W E) (D : StageCutChoice74 A)
    (Rw : FC39RowsV2 W E) : Prop where
  regionM1_eq : regionM1 Rw.zero Rw.cusp = regionM1 A.zero A.cusp
  regionM2_eq : regionM2 Rw.slim = D.M₂
  regionM3_eq : regionM3 Rw.slim Rw.edge = D.M₃
  region_M3 : Rw.circle.region = D.M₃

/-- **The abstract link `StageRowsLink74 A D Rw`** (D74-5 on plain data): the four tables. -/
structure StageRowsLink74 (A : SmoothStageGeometry74 W E) (D : StageCutChoice74 A)
    (Rw : FC39RowsV2 W E) : Prop where
  zeroSlim : ZeroSlimLink74 A D Rw
  edge : EdgeLink74 A D Rw
  circle : CircleLink74 A D Rw
  regions : RegionsLink74 A D Rw

end GC.GraphManifold.Assembly.FC39P0
