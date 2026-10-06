import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RowsLinkOfStageU74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageRows74

/-!
# Plain-data kernel of the closed exits (`ClosedExitsOverU74`) and its tables

Lane S-LANDING (by S-LANDING2, suffix `_LND`), G4. The exits of the closed route
(`ClosedExitsOverU74 D`, lane S-LANDING G2d) are records over a source
`S : ClosedChainEZRowsSource_RGC`, which exists only inside the register-level existence theorems:
no compiled S-level inhabitant can exist before the fixture layer (iii). This file is the
S-free mirror, on PLAIN DATA, of the identification fields the landing lane designed:

* `StageIdentData_LND X Bs`: the plain data of the chain side (the three final maps `f₃, q₁, q₀`
  into one block space `Bs`, the open ambient parent `U₂`, the height and level, the slim base
  sets `C₃`, slab, faces, and the sets of the cut choice);
* `assembleStagesC_LND Zr Cu sl ed ci`: the assembled stage geometry `A` with a given cusp field;
* `StageGeometryKernelU_LND ψ Zr Cu d`: the mirror of `ClosedStageGeometryU74` (three stages over
  `W`, base embeddings `ι`, the identifications `StageIdent_LND74` / `StageIdentU_LND74`, the
  cut `D` of the abstract stage geometry identified with the data, the components equivalence);
* `ExitsKernelU_LND ψ Zr Cu d dom inner outer uv Eset`: the mirror of `ClosedExitsOverU74`: the
  zero table, the stage kernel, the A0 cut geometry `H` (which carries the slim pieces, the edge /
  circle facts and models, the cover, the face, rim and corner facts: the contents of the records
  `ZSP04SmoothExitU74`, `EDP04WholeDiskExitU74`, `FDC03ActualRemainderU74`,
  `EDP05HorizontalExitU74`, `EDP06CircleAgreementU74`) and FDC02's set equality;
* `ExitsKernelU_LND.rows_tables`: the exits kernel feeds the bridges of G2d: the zero, slim, edge
  (open ambient parent) and circle tables of `RowsLinkKernel74` on the J1 rows.

The S-level records project to this kernel in
`Collapse/StaticRegisterV4ChainExitsKernelBridgeU74LND.lean`; the kernel is inhabited on the S³
singleton and the S² × S¹ loop of the abstract assembler in `ExitsKernelU74ApplicationsLND.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open GC.GraphManifold.Assembly
open Manifold
open scoped Manifold ContDiff Topology

universe u v w z

namespace GC.GraphManifold.Assembly.FC39P0

/-- **The plain data of the chain side of the exits**: the final maps `f₃ = slimMap`, `q₁`, `q₀`
into the block space `Bs`, the open ambient parent `U₂`, the height `H = A/s` and the level `4Δ`,
the slim base sets `C₃`, slab image and faces, and the base sets of the cut choice (`K₃`, `D₃`,
`C₂`, `C₁`, the open edge and circle bases). -/
structure StageIdentData_LND (X : Type v) (Bs : Type w) where
  qs : X → Bs
  q1 : X → Bs
  q0 : X → Bs
  U₂ : Set X
  hS : X → ℝ
  lvl : ℝ
  slimC3 : Set Bs
  slab : Set Bs
  faces : Set Bs
  K₃ : Set Bs
  D₃ : Set Bs
  C₂ : Set Bs
  C₁ : Set Bs
  eO : Set Bs
  cO : Set Bs

/-- The assembled stage geometry of the closed route with a given cusp field (`A` of the abstract
assembler). -/
abbrev assembleStagesC_LND {W : CompactCarrier.{u}} (Zr : ZeroDomains W)
    (Cu : CuspCores W (BoundaryTori.empty W)) (sl : SlimStage74 W) (ed : EdgeStage74 W)
    (ci : StageProj74 W 2) : SmoothStageGeometry74 W (BoundaryTori.empty W) where
  zero := Zr
  cusp := Cu
  slim := sl
  edge := ed
  circle := ci

variable {X : Type v} [TopologicalSpace X] {Bs : Type w} [TopologicalSpace Bs]
  {W : CompactCarrier.{u}}

/-- **The mirror of `ClosedStageGeometryU74`** on plain data: three stages over `W` with their
base embeddings into the block space, identified with the chain's final maps (edge on the open
ambient parent `U₂`), the base sets of the stages and of the abstract cut choice identified with
the data, and the equivalence of the actual components of `D₃`. -/
structure StageGeometryKernelU_LND (ψ : X ≃ W.Carrier) (Zr : ZeroDomains W)
    (Cu : CuspCores W (BoundaryTori.empty W)) (d : StageIdentData_LND X Bs) where
  slim : SlimStage74 W
  edge : EdgeStage74 W
  circle : StageProj74 W 2
  ιslim : slim.Base → Bs
  ιedge : edge.Base → Bs
  ιcircle : circle.Base → Bs
  slim_ident : StageIdent_LND74 ψ slim.toStageProj74 d.qs ιslim
  edge_ident : StageIdentU_LND74 ψ edge.toStageProj74 d.q1 ιedge d.U₂
  circle_ident : StageIdent_LND74 ψ circle d.q0 ιcircle
  slim_C₃ : ιslim '' slim.C₃ = d.slimC3
  slim_slab : ιslim '' slim.slabImage = d.slab
  slim_faces : ιslim '' slim.facePoints = d.faces
  edge_height : ∀ x : edge.parent, edge.height x = d.hS (ψ.symm x)
  edge_level : edge.level = d.lvl
  cut : StageCutChoice74 (assembleStagesC_LND Zr Cu slim edge circle)
  cut_K₃ : ιslim '' cut.K₃ = d.K₃
  cut_D₃ : ιslim '' cut.D₃ = d.D₃
  cut_C₂ : ιedge '' cut.C₂ = d.C₂
  cut_C₁ : ιcircle '' cut.C₁ = d.C₁
  cut_edgeOpen : ιedge '' (cut.edgeBaseOpen : Set edge.Base) = d.eO
  cut_circleOpen : ιcircle '' (cut.circleBaseOpen : Set circle.Base) = d.cO
  comp : ActualComponent cut.D₃ ≃ ActualComponent d.D₃
  comp_eq : ∀ c, ιslim '' c.1 = (comp c).1

/-- The stage geometry `A` of the kernel. -/
abbrev StageGeometryKernelU_LND.A {ψ : X ≃ W.Carrier} {Zr : ZeroDomains W}
    {Cu : CuspCores W (BoundaryTori.empty W)} {d : StageIdentData_LND X Bs}
    (P : StageGeometryKernelU_LND ψ Zr Cu d) : SmoothStageGeometry74 W (BoundaryTori.empty W) :=
  assembleStagesC_LND Zr Cu P.slim P.edge P.circle

/-- **The mirror of `ClosedExitsOverU74`** on plain data: the zero table, the stage kernel, the A0
cut geometry `H` of the exits and FDC02's set equality `M^edge = U₂ ∩ q₁⁻¹(C₂) ∩ {H ≤ lvl}`. -/
structure ExitsKernelU_LND {ι : Type z} (ψ : X ≃ W.Carrier) (Zr : ZeroDomains W)
    (Cu : CuspCores W (BoundaryTori.empty W)) (d : StageIdentData_LND X Bs)
    (dom inner outer : ι → Set X) (uv : ι → X → ℝ) (Eset : Set X) where
  zero : ZeroLink_LND74 ψ Zr dom inner outer uv
  stages : StageGeometryKernelU_LND ψ Zr Cu d
  geometry : StageCutGeometry74 stages.A stages.cut
  edgeSet_eq : Eset = d.U₂ ∩ (d.q1 ⁻¹' d.C₂ ∩ {p | d.hS p ≤ d.lvl})

/-- **The exits kernel feeds the bridges of the landing**: the J1 rows of the stage geometry
satisfy the zero, slim, edge (open ambient parent) and circle tables of `RowsLinkKernel74` on the
data (`M₃` the saturated circle region). -/
theorem ExitsKernelU_LND.rows_tables {ι : Type z} {ψ : X ≃ W.Carrier} {Zr : ZeroDomains W}
    {Cu : CuspCores W (BoundaryTori.empty W)} {d : StageIdentData_LND X Bs}
    {dom inner outer : ι → Set X} {uv : ι → X → ℝ} {Eset : Set X}
    (E : ExitsKernelU_LND ψ Zr Cu d dom inner outer uv Eset) (hCV : d.C₂ ⊆ d.eO)
    {M₃ : Set X} (hM3 : M₃ = d.q0 ⁻¹' d.C₁) :
    ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W),
      ZeroLink_LND74 ψ Rw.zero dom inner outer uv ∧
      SlimLink_LND74 ψ Rw.slim (fun c : ActualComponent d.D₃ => d.qs ⁻¹' c.1)
        (d.qs ⁻¹' d.D₃) ∧
      EdgeLinkU_LND74 ψ Rw.edge d.q1 d.hS d.lvl d.eO d.C₂ d.U₂ Eset ∧
      CircleLink_LND74 ψ Rw.circle d.q0 d.cO d.C₁ (d.q0 ⁻¹' d.cO) M₃ := by
  obtain ⟨Rw, L⟩ := rows_of_smooth_stage_geometry74 E.stages.A E.stages.cut E.geometry
  refine ⟨Rw, ?_, ?_, ?_, ?_⟩
  · rw [L.zeroSlim.zero_eq]
    exact E.zero
  · exact slimLink_of_stage_LND74 L.zeroSlim E.stages.slim_ident E.stages.cut_D₃
      E.stages.comp E.stages.comp_eq
  · exact edgeLinkU_of_stage_LND74 L.edge E.stages.edge_ident E.stages.edge_height
      E.stages.cut_edgeOpen E.stages.edge_level E.stages.cut_C₂ hCV E.edgeSet_eq
  · exact circleLink_of_stage_LND74 L.circle E.stages.circle_ident E.stages.cut_circleOpen
      E.stages.cut_C₁ hM3

end GC.GraphManifold.Assembly.FC39P0
