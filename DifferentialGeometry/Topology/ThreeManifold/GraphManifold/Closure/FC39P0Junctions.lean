import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Edges

/-!
# FC39 producer, packet P0 (gate 1): junctions, labelled corner tubes, the revised rows

Task-47 draft §3.1, §5.6, §5.7 (dispositions D6, D8):

* the residual faces `SlimPiecesV2.ResidualFace` (the faces of `∂M₂`: zero / cusp internal model
  faces not shared with a slim end, and the new slim ends), their ambient sets, their defining
  functions (zero `h₁ − .4`, cusp ratio, slim endpoint coordinate), owners and neighbourhoods;
* the labels `CircleFaceLabel` of the faces of the circle base (horizontal = residual face,
  vertical = actual edge base component);
* `JunctionsV2` (§5.6): cover and interiors (K); the two-sided shared-face equality on model faces
  (R); zero / cusp disjointness (K, BCP05 + BCG06, Q10); the labelled horizontal map
  `EdgeEnd → ResidualFace` with whole end disks (R); `P ∩ ∂M₂` face by face (R); the labelled smooth
  `rimBase` (R, not a pointwise existential); `P ∩ R = V_e` (K); the LABELLED local faces of `C₁`
  (R, replacing `CircleBundle.local_faces`); the relative complements of §5.7 as set fields
  (`M₃ = M₂ \ int_{M₂} P = R`, `∂M₂ = ⋃` residual faces, `M₃ ∩ ∂M₂ = ∂M₂ \ int_{∂M₂} H`, `S ∩ M₂` =
  new ends, shared faces removed with their relative inward collar). The old unlabelled `corner`
  is DELETED; its replacement is
* `LabelledCornerTubes` (§3.1): for every actual endpoint `e` the saturated tube `U_e` over a base
  neighbourhood `V_e` of the rim base point, inside the edge source and the face neighbourhood of
  `horizontal e`, a chart `κ_e` with `κ_e¹ ∘ proj = T − 4Δ` and `κ_e² ∘ proj = h_{horizontal e}`
  on the WHOLE tube (no conditional source clause), the descended equation `b_e` with
  `db_e ≠ 0`, and
  the three labelled side equalities (vertex owner ⇔ `Y ≤ 0`; the actual component ⇔ `Y ≥ 0, X ≤ 0`;
  `R` ⇔ `X ≥ 0, Y ≥ 0`);
* `FC39RowsV2` — the raw rows with the edge component export and the labelled tubes.
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

/-! ## Residual faces -/

namespace SlimPiecesV2

variable {Z : ZeroDomains W} {C : CuspCores W E} (S : SlimPiecesV2 W Z C)

/-- The row index of a vertex: a zero domain, a cusp core or a slim piece. -/
abbrev RowIndex : Type :=
  Fin Z.count ⊕ Fin n ⊕ Fin S.count

/-- The image of the row piece of an index. -/
def rowSet : S.RowIndex → Set W.Carrier
  | .inl i => range (Z.piece i).map
  | .inr (.inl b) => range (C.piece b).map
  | .inr (.inr j) => range (S.piece j).map

/-- **The faces of `∂M₂`**: a zero / cusp-internal model face not shared with any slim end, or a
new slim end. -/
def ResidualFace : Type u :=
  {F : NeighbourFace Z C // ∀ e, S.endKind e ≠ some F} ⊕ S.NewEnd

/-- The ambient set of a residual face. -/
def residualSet : S.ResidualFace → Set W.Carrier
  | .inl F => neighbourSet F.1
  | .inr e => S.endSet e.1

/-- The ambient defining function of a residual face: the global zero function `h₁ − .4`, the cusp
ratio, or the slim endpoint coordinate. -/
def residualFn : S.ResidualFace → W.Carrier → ℝ
  | .inl ⟨.inl F, _⟩ => Z.ratio F.1
  | .inl ⟨.inr F, _⟩ => C.cuspFn F.1
  | .inr e => S.endFn e

/-- The neighbourhood on which the defining function of a residual face is a face equation. -/
def residualNear : S.ResidualFace → TopologicalSpace.Opens W.Carrier
  | .inl ⟨.inl F, _⟩ => Z.near F.1
  | .inl ⟨.inr F, _⟩ => C.near F.1
  | .inr e => S.endNear e

/-- The vertex owner of a residual face. -/
def residualOwner : S.ResidualFace → S.RowIndex
  | .inl ⟨.inl F, _⟩ => .inl F.1
  | .inl ⟨.inr F, _⟩ => .inr (.inl F.1)
  | .inr e => .inr (.inr e.1.1.1)

/-- `∂M₂`: the union of the residual faces. -/
def boundaryM2 : Set W.Carrier :=
  ⋃ F, S.residualSet F

end SlimPiecesV2

/-- The labels of the faces of the circle base: a horizontal face (a residual face) or the
vertical face of an actual edge base component. -/
inductive CircleFaceLabel (Hor Ver : Type*)
  | horizontal (F : Hor)
  | vertical (c : Ver)

/-- The ambient set of a labelled circle-base face. -/
def circleFaceSet {Z : ZeroDomains W} {C : CuspCores W E} (S : SlimPiecesV2 W Z C)
    (P : EdgeBundle W) : CircleFaceLabel S.ResidualFace P.EdgeBaseComponent → Set W.Carrier
  | .horizontal F => S.residualSet F
  | .vertical c => P.wholeVertical c

/-- All pieces of the decomposition, indexed by kind. -/
def allPieces {Z : ZeroDomains W} {C : CuspCores W E} (S : SlimPiecesV2 W Z C)
    (P : EdgeBundle W) (R : CircleBundle W) : S.RowIndex ⊕ Bool → Set W.Carrier
  | .inl i => S.rowSet i
  | .inr true => P.edgePiece
  | .inr false => R.region

/-- `M₁ = W \ int_W (Z ∪ C)`. -/
def regionM1 (Z : ZeroDomains W) (C : CuspCores W E) : Set W.Carrier :=
  (interior ((⋃ i, range (Z.piece i).map) ∪ ⋃ b, range (C.piece b).map))ᶜ

/-- `M₂ = M₁ \ int_{M₁} S`. -/
def regionM2 {Z : ZeroDomains W} {C : CuspCores W E} (S : SlimPiecesV2 W Z C) : Set W.Carrier :=
  regionM1 Z C \ relInt (regionM1 Z C) S.union

/-- `M₃ = M₂ \ int_{M₂} P`. -/
def regionM3 {Z : ZeroDomains W} {C : CuspCores W E} (S : SlimPiecesV2 W Z C)
    (P : EdgeBundle W) : Set W.Carrier :=
  regionM2 S \ relInt (regionM2 S) P.edgePiece

/-- The horizontal faces `H_e` of the edge piece: the whole disks over the endpoints. -/
def EdgeBundle.horizontalDisks (P : EdgeBundle W) : Set W.Carrier :=
  ⋃ e : P.EdgeEnd, P.disk e.1

/-- **Junctions (§5.6, §5.7).** `cover`, `interiors_disjoint`, `zero_cusp_disjoint`,
`edge_region` kept (K); `shared_eq` (R: the slim end and the neighbour model face have the same
ambient image — both are actual model boundary components), `horizontal` / `horizontal_disk` (R:
the actual label `EdgeEnd → ResidualFace` and the whole end disk in it), `edge_faces` (R: `P ∩ F` is
the union of the registered end disks, face by face), `rimBase` (R: labelled and smooth on `C₂`),
`local_faces` (R: labelled by the actual faces); NEW (§5.7): the relative-complement identities.
The old `corner` is DELETED (replaced by `LabelledCornerTubes`). -/
structure JunctionsV2 (W : CompactCarrier.{u}) {n : ℕ} (E : BoundaryTori W n) (Z : ZeroDomains W)
    (C : CuspCores W E) (S : SlimPiecesV2 W Z C) (P : EdgeBundle W) (R : CircleBundle W) where
  cover : (⋃ a, allPieces S P R a) = univ
  interiors_disjoint : Pairwise fun a a' =>
    Disjoint (interior (allPieces S P R a)) (interior (allPieces S P R a'))
  shared_eq : ∀ e F, S.endKind e = some F → S.endSet e = neighbourSet F
  zero_cusp_disjoint : ∀ i b, Disjoint (range (Z.piece i).map) (range (C.piece b).map)
  horizontal : P.EdgeEnd → S.ResidualFace
  horizontal_disk : ∀ e, P.disk e.1 ⊆ S.residualSet (horizontal e)
  edge_faces : ∀ F, P.edgePiece ∩ S.residualSet F = ⋃ (e : P.EdgeEnd) (_ : horizontal e = F),
    P.disk e.1
  rimBase : P.Base → R.Base
  rimBase_smooth : ContMDiffOn (𝓡 1) (𝓡 2) ∞ rimBase P.cbase
  rim_fibre : ∀ c ∈ P.cbase, P.rim c = R.fibre (rimBase c)
  edge_region : P.edgePiece ∩ R.region = P.vertical
  local_faces : ∀ c ∈ frontier R.cbase, ∃ U : TopologicalSpace.Opens R.Base, c ∈ U ∧
    ∃ (L : Finset (CircleFaceLabel S.ResidualFace P.EdgeBaseComponent))
      (φ : CircleFaceLabel S.ResidualFace P.EdgeBaseComponent → R.Base → ℝ),
      1 ≤ L.card ∧ L.card ≤ 2 ∧
      (∀ f ∈ L, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (φ f) U ∧ φ f c = 0 ∧
        {c' | c' ∈ U ∧ c' ∈ R.cbase ∧ φ f c' = 0} =
          {c' | c' ∈ U ∧ c' ∈ R.cbase ∧ R.fibre c' ⊆ circleFaceSet S P f}) ∧
      (Surjective fun w : TangentSpace (𝓡 2) c => fun f : L => mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (φ f) c w) ∧
      R.cbase ∩ U = {c' | c' ∈ U ∧ ∀ f ∈ L, φ f c' ≤ 0}
  region_eq : regionM3 S P = R.region
  frontier_M2 : frontier (regionM2 S) = S.boundaryM2
  region_boundary : R.region ∩ S.boundaryM2 =
    S.boundaryM2 \ relInt S.boundaryM2 P.horizontalDisks
  slim_M2 : S.union ∩ regionM2 S = ⋃ e : S.NewEnd, S.endSet e.1
  shared_removed : ∀ σ : ActualSharedFace S, S.endSet σ.1 ⊆ relInt (regionM1 Z C) S.union

/-- **§3.1 The labelled corner tubes** (replacing the dry `Junctions.corner`). For every actual
endpoint `e`: the base neighbourhood `V_e = base e` of the rim base point and the WHOLE saturated
tube `U_e = R.tube V_e`, inside the edge source and inside the face neighbourhood of the label
`horizontal e`; a chart `κ_e` of the circle base centred at the rim base point with
`κ_e¹ ∘ proj = T − 4Δ` and `κ_e² ∘ proj = h_{horizontal e} = b_e ∘ P.proj` on the whole tube
(`db_e ≠ 0`); the three labelled side equalities on the tube, in the coordinates
`X = κ_e¹ ∘ proj`, `Y_e = κ_e² ∘ proj`. -/
structure LabelledCornerTubes {Z : ZeroDomains W} {C : CuspCores W E} {S : SlimPiecesV2 W Z C}
    {P : EdgeBundle W} {R : CircleBundle W} (J : JunctionsV2 W E Z C S P R) where
  base : P.EdgeEnd → TopologicalSpace.Opens R.Base
  rimBase_mem : ∀ e, J.rimBase e.1 ∈ base e
  chart : P.EdgeEnd → PartialDiffeomorph (𝓡 2) 𝓘(ℝ, ℝ × ℝ) R.Base (ℝ × ℝ) ∞
  chart_source : ∀ e, (chart e).source = base e
  chart_center : ∀ e, chart e (J.rimBase e.1) = (0, 0)
  tube_source : ∀ e, R.tube (base e) ⊆ P.source
  tube_near : ∀ e, R.tube (base e) ⊆ S.residualNear (J.horizontal e)
  height_eq : ∀ e (x : R.domain), R.proj x ∈ base e →
    ∃ hx : (x : W.Carrier) ∈ P.source, (chart e (R.proj x)).1 = P.height ⟨x, hx⟩ - P.level
  face_eq : ∀ e (x : R.domain), R.proj x ∈ base e →
    (chart e (R.proj x)).2 = S.residualFn (J.horizontal e) x
  descended : P.EdgeEnd → P.Base → ℝ
  descended_smooth : ∀ e, ∃ U : TopologicalSpace.Opens P.Base, e.1 ∈ U ∧
    ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ (descended e) U
  descended_regular : ∀ e, mfderiv (𝓡 1) 𝓘(ℝ, ℝ) (descended e) e.1 ≠ 0
  descended_eq : ∀ e (x : R.domain), R.proj x ∈ base e →
    ∃ hx : (x : W.Carrier) ∈ P.source,
      S.residualFn (J.horizontal e) x = descended e (P.proj ⟨x, hx⟩)
  vertex_side : ∀ {e} {x : R.domain}, R.proj x ∈ base e →
    ((x : W.Carrier) ∈ S.rowSet (S.residualOwner (J.horizontal e)) ↔
      (chart e (R.proj x)).2 ≤ 0)
  edge_side : ∀ {e} {x : R.domain}, R.proj x ∈ base e →
    ((x : W.Carrier) ∈ P.wholeComponent e.component ↔
      0 ≤ (chart e (R.proj x)).2 ∧ (chart e (R.proj x)).1 ≤ 0)
  region_side : ∀ {e} {x : R.domain}, R.proj x ∈ base e →
    ((x : W.Carrier) ∈ R.region ↔ 0 ≤ (chart e (R.proj x)).1 ∧ 0 ≤ (chart e (R.proj x)).2)

/-- The saturated tube `U_e`. -/
def LabelledCornerTubes.tube {Z : ZeroDomains W} {C : CuspCores W E} {S : SlimPiecesV2 W Z C}
    {P : EdgeBundle W} {R : CircleBundle W} {J : JunctionsV2 W E Z C S P R}
    (T : LabelledCornerTubes J) (e : P.EdgeEnd) : Set W.Carrier :=
  R.tube (T.base e)

/-- **The revised row outputs of one admissible assignment**: the six row structures (§5), the
edge component export (§1) and the labelled corner tubes (§3.1). The global face functions are a
PREPARED output (`FC39Prepared`, open choice 5), not a raw row. -/
structure FC39RowsV2 (W : CompactCarrier.{u}) {n : ℕ} (E : BoundaryTori W n) where
  zero : ZeroDomains W
  cusp : CuspCores W E
  slim : SlimPiecesV2 W zero cusp
  edge : EdgeBundle W
  edgeModels : EdgeComponentModels edge
  circle : CircleBundle W
  junctions : JunctionsV2 W E zero cusp slim edge circle
  labelledTubes : LabelledCornerTubes junctions

end GC.GraphManifold.Assembly.FC39P0
