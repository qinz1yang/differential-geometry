import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificate

/-!
# FC39 producer, packet P0 (gate 1): actual components and the revised row structures

Transcription of the repaired contract (external draft of task 47,
`docs/geometrization/chapter14/out/draft-task47-fc39-contract.md`; lead dispositions D1–D13,
`build-logs/inbox/dispositions-task47-fc39-contract-draft.md`). Nothing of the dry assembly
(`build-logs/scratch/FC39-DRY/FC39Dry.lean`) is installed; every name here is new.

* §1.1 `ActualComponent` (no empty component; open choice 1: the connected-component subtype);
  `relInt` (§5.7, the interior relative to a subspace, mapped back).
* §5.1 `ZeroDomains` with the global `h₁ − .4` (Q7): global smoothness, regularity of every zero,
  `pieceBoundary = {F = 0}`, `range = {F ≤ 0}`, and the closed branch with the auxiliary LFR50
  metric witness inside `ClosedZeroPiece` (Q8).
* §5.4 `EdgeBundle` (dry fields kept) with `edgePiece`, `vertical`, `disk`, `rim`, the endpoints
  `EdgeEnd`, the base components `EdgeBaseComponent` and the whole inverse image `wholeComponent`.
* §5.5 `CircleBundle` (dry fields kept; the unlabelled `local_faces` is replaced by the labelled
  field of `JunctionsV2`).
* §2.1 `ModelBoundaryFace`; §5.2 `CuspCores` with the two model faces (`true = 1` internal,
  `false = 0` external, Q9); `NeighbourFace` (only the internal cusp end); §5.3 `SlimPiecesV2` with
  the actual end type `SlimEnd` (interval models only), the model face of every end and
  `endKind : End → Option NeighbourFace`; `ActualSharedFace`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

local instance diskChartsBase_FC39P0 : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

/-! ## Actual components and relative interiors -/

/-- **§1.1** The actual connected components of a set `S` (an empty component is excluded: every
component is `connectedComponentIn S x` for some `x ∈ S`). -/
def ActualComponent {X : Type*} [TopologicalSpace X] (S : Set X) : Type _ :=
  { C : Set X // ∃ x ∈ S, C = connectedComponentIn S x }

/-- The actual component of `S` through a point of `S`. -/
def ActualComponent.of {X : Type*} [TopologicalSpace X] {S : Set X} {x : X} (hx : x ∈ S) :
    ActualComponent S :=
  ⟨connectedComponentIn S x, x, hx, rfl⟩

/-- Two actual components that meet are equal. -/
theorem ActualComponent.eq_of_mem {X : Type*} [TopologicalSpace X] {S : Set X}
    {C C' : ActualComponent S} {z : X} (hz : z ∈ C.1) (hz' : z ∈ C'.1) : C = C' := by
  obtain ⟨x, -, hx⟩ := C.2
  obtain ⟨x', -, hx'⟩ := C'.2
  apply Subtype.ext
  rw [hx, hx']
  rw [hx] at hz
  rw [hx'] at hz'
  rw [connectedComponentIn_eq hz, connectedComponentIn_eq hz']

/-- Distinct actual components are disjoint. -/
theorem ActualComponent.disjoint_of_ne {X : Type*} [TopologicalSpace X] {S : Set X}
    {C C' : ActualComponent S} (h : C ≠ C') : Disjoint C.1 C'.1 :=
  Set.disjoint_left.2 fun _ hz hz' => h (ActualComponent.eq_of_mem hz hz')

/-- An actual component lies in its set. -/
theorem ActualComponent.subset {X : Type*} [TopologicalSpace X] {S : Set X}
    (C : ActualComponent S) : C.1 ⊆ S := by
  obtain ⟨x, -, hx⟩ := C.2
  rw [hx]
  exact connectedComponentIn_subset S x

/-- **§5.7** The interior of `S` relative to the subspace `A`, mapped back (not `interior S`). -/
def relInt {X : Type*} [TopologicalSpace X] (A S : Set X) : Set X :=
  Subtype.val '' interior ((Subtype.val : A → X) ⁻¹' S)

/-- The model boundary image of an embedded piece. -/
def pieceBoundary {W : CompactCarrier.{u}} (P : PieceEmbedding W) : Set W.Carrier :=
  P.map '' (𝓡∂ 3).boundary P.Piece

/-! ## §5.1 Zero domains -/

/-- **Zero domains (§5.1).** ZSP02 (B:6374–6530) with FC35 (B:6216–6236). Revised against the
dry text: `ratio i` is the GLOBAL shifted function `h₁ − .4` (Q7; on the original boundary buffer it
equals the retained ratio — a provenance fact of `RowsAt`, not a field here), smooth on the whole
carrier, every zero regular and the zero set inside `near i`; `pieceBoundary = {F = 0}` and the
global sublevel `range = {F ≤ 0}` (the dry local forms are corollaries). The model: a zero model, or
the closed branch `ClosedZeroPiece` (explicit `Q`, auxiliary smooth `sec ≥ 0` metric of the LFR50
model, `ident`, `boundary_empty`) with the piece equality (Q8). -/
structure ZeroDomains (W : CompactCarrier.{u}) where
  count : ℕ
  piece : Fin count → PieceEmbedding W
  disjoint : Pairwise fun i j => Disjoint (range (piece i).map) (range (piece j).map)
  ratio : Fin count → W.Carrier → ℝ
  near : Fin count → TopologicalSpace.Opens W.Carrier
  near_interior : ∀ i, (near i : Set W.Carrier) ⊆ W.interior
  ratio_smooth : ∀ i, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (ratio i)
  ratio_regular : ∀ i x, ratio i x = 0 → mfderiv W.model 𝓘(ℝ, ℝ) (ratio i) x ≠ 0
  zero_subset_near : ∀ i, {x | ratio i x = 0} ⊆ near i
  boundary_eq : ∀ i, pieceBoundary (piece i) = {x | ratio i x = 0}
  range_eq : ∀ i, range (piece i).map = {x | ratio i x ≤ 0}
  model : (i : Fin count) → ZeroModel (piece i) ⊕ {C : ClosedZeroPiece W // C.piece = piece i}

/-! ## §5.4 The edge disk bundle -/

/-- **The proper edge disk bundle (§5.4)**: EDP04 (B:6949), EDP05 (B:7040), FDC02 (B:7246); FC37
(B:6260); BCF02. All dry fields are kept (K); the component registry is the separate output
`EdgeComponentModels` (`FC39P0Edges.lean`). -/
structure EdgeBundle (W : CompactCarrier.{u}) where
  Base : Type u
  [baseTop : TopologicalSpace Base]
  [baseCharts : ChartedSpace (EuclideanSpace ℝ (Fin 1)) Base]
  [baseSmooth : IsManifold (𝓡 1) ∞ Base]
  [baseT2 : T2Space Base]
  source : TopologicalSpace.Opens W.Carrier
  source_interior : (source : Set W.Carrier) ⊆ W.interior
  proj : C(source, Base)
  proj_smooth : ContMDiff W.model (𝓡 1) ∞ proj
  proj_submersion : ∀ x, Surjective (mfderiv W.model (𝓡 1) proj x)
  height : source → ℝ
  height_smooth : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ height
  level : ℝ
  rank_two : ∀ x, height x = level → Surjective fun v : TangentSpace W.model (x : W.Carrier) =>
    (mfderiv W.model (𝓡 1) proj x v, mfderiv W.model 𝓘(ℝ, ℝ) height x v)
  proper : ∀ K : Set Base, IsCompact K →
    IsCompact (Subtype.val '' {x : source | proj x ∈ K ∧ height x ≤ level})
  fibre_disk : ∀ c : Base, ∃ φ : ClosedCell 2 → W.Carrier,
    IsSmoothEmbedding (𝓡∂ 2) W.model ∞ φ ∧
      range φ = Subtype.val '' {x : source | proj x = c ∧ height x ≤ level}
  cbase : Set Base
  cbase_compact : IsCompact cbase
  cbase_domain : ∀ c ∈ frontier cbase, ∃ U : TopologicalSpace.Opens Base, c ∈ U ∧
    ∃ φ : Base → ℝ, ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ φ U ∧ φ c = 0 ∧
      mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ c ≠ 0 ∧ cbase ∩ U = {c' | c' ∈ U ∧ 0 ≤ φ c'}

attribute [instance] EdgeBundle.baseTop EdgeBundle.baseCharts EdgeBundle.baseSmooth
  EdgeBundle.baseT2

namespace EdgeBundle

variable {W : CompactCarrier.{u}} (P : EdgeBundle W)

/-- `M^edge = f₂⁻¹(C₂) ∩ {T ≤ 4Δ}` (FDC02). -/
def edgePiece : Set W.Carrier :=
  Subtype.val '' {x : P.source | P.proj x ∈ P.cbase ∧ P.height x ≤ P.level}

/-- The vertical face `V_e = M₂ ∩ ∂X₂` (EF). -/
def vertical : Set W.Carrier :=
  Subtype.val '' {x : P.source | P.proj x ∈ P.cbase ∧ P.height x = P.level}

/-- The whole disk over `c`. -/
def disk (c : P.Base) : Set W.Carrier :=
  Subtype.val '' {x : P.source | P.proj x = c ∧ P.height x ≤ P.level}

/-- The boundary circle of the disk over `c`. -/
def rim (c : P.Base) : Set W.Carrier :=
  Subtype.val '' {x : P.source | P.proj x = c ∧ P.height x = P.level}

/-- The endpoints of the edge base `C₂` (its frontier points). -/
def EdgeEnd : Type u :=
  {c : P.Base // c ∈ frontier P.cbase}

/-- §1.1 the actual components of the closed edge base `C₂`. -/
abbrev EdgeBaseComponent : Type u :=
  ActualComponent P.cbase

/-- §1.1 the actual components of the edge piece. -/
abbrev EdgeActualComponent : Type u :=
  ActualComponent P.edgePiece

/-- **§1.1** The WHOLE inverse image of a base component below the level (not the image of some
local product chart). -/
def wholeComponent (C : P.EdgeBaseComponent) : Set W.Carrier :=
  Subtype.val '' {x : P.source | P.proj x ∈ C.1 ∧ P.height x ≤ P.level}

/-- The vertical face of one base component. -/
def wholeVertical (C : P.EdgeBaseComponent) : Set W.Carrier :=
  Subtype.val '' {x : P.source | P.proj x ∈ C.1 ∧ P.height x = P.level}

theorem frontier_cbase_subset : frontier P.cbase ⊆ P.cbase :=
  P.cbase_compact.isClosed.frontier_subset

/-- The base component of an endpoint. -/
def EdgeEnd.component {P : EdgeBundle W} (e : P.EdgeEnd) : P.EdgeBaseComponent :=
  ActualComponent.of (P.frontier_cbase_subset e.2)

theorem disk_disjoint {c c' : P.Base} (h : c ≠ c') : Disjoint (P.disk c) (P.disk c') := by
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨x, ⟨hx, -⟩, rfl⟩ ⟨y, ⟨hy, -⟩, hxy⟩
  have : y = x := Subtype.ext hxy
  subst this
  exact h (hx.symm.trans hy)

theorem wholeComponent_disjoint {C C' : P.EdgeBaseComponent} (h : C ≠ C') :
    Disjoint (P.wholeComponent C) (P.wholeComponent C') := by
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨x, ⟨hx, -⟩, rfl⟩ ⟨y, ⟨hy, -⟩, hxy⟩
  have : y = x := Subtype.ext hxy
  subst this
  exact h (ActualComponent.eq_of_mem hx hy)

end EdgeBundle

/-! ## §5.5 The circle bundle -/

/-- **The circle bundle (§5.5)**: GAF07 (B:6049), FC38 (B:6287), FDC03 (B:7285); BCF02. All dry
fields are kept (K) except the unlabelled `local_faces`, which is REPLACED by the labelled field
`JunctionsV2.local_faces` (the labels are actual faces of other rows). -/
structure CircleBundle (W : CompactCarrier.{u}) where
  Base : Type u
  [baseTop : TopologicalSpace Base]
  [baseCharts : ChartedSpace (EuclideanSpace ℝ (Fin 2)) Base]
  [baseSmooth : IsManifold (𝓡 2) ∞ Base]
  [baseT2 : T2Space Base]
  domain : TopologicalSpace.Opens W.Carrier
  domain_interior : (domain : Set W.Carrier) ⊆ W.interior
  proj : C(domain, Base)
  proj_smooth : ContMDiff W.model (𝓡 2) ∞ proj
  proj_submersion : ∀ x, Surjective (mfderiv W.model (𝓡 2) proj x)
  neighborhood : Base → TopologicalSpace.Opens Base
  mem_neighborhood : ∀ c, c ∈ neighborhood c
  trivialization : (c : Base) →
    (TopologicalSpace.Opens.comap proj (neighborhood c))
      ≃ₘ⟮W.model, (𝓡 2).prod (𝓡 1)⟯ ((neighborhood c) × Circle)
  projection_trivialization : ∀ c x, ((trivialization c x).1).val = proj x.val
  cbase : Set Base
  cbase_compact : IsCompact cbase

attribute [instance] CircleBundle.baseTop CircleBundle.baseCharts CircleBundle.baseSmooth
  CircleBundle.baseT2

/-- `M₃ = E⁻¹(C₁)` (FDC03). -/
def CircleBundle.region {W : CompactCarrier.{u}} (R : CircleBundle W) : Set W.Carrier :=
  Subtype.val '' (R.proj ⁻¹' R.cbase)

/-- The whole circle fibre over `c`. -/
def CircleBundle.fibre {W : CompactCarrier.{u}} (R : CircleBundle W) (c : R.Base) :
    Set W.Carrier :=
  Subtype.val '' (R.proj ⁻¹' {c})

/-- The full circle preimage of a set of the base (a saturated tube). -/
def CircleBundle.tube {W : CompactCarrier.{u}} (R : CircleBundle W) (V : Set R.Base) :
    Set W.Carrier :=
  Subtype.val '' (R.proj ⁻¹' V)

/-! ## §2.1 Model boundary faces, §5.2 cusp cores -/

/-- **§2.1** The actual connected components of the model boundary of a piece. A closed piece has
none. -/
abbrev ModelBoundaryFace {W : CompactCarrier.{u}} (P : PieceEmbedding W) : Type u :=
  ActualComponent ((𝓡∂ 3).boundary P.Piece)

/-- **Cusp cores (§5.2, separated branch only)**: BCG06–07 (B:9290–9640), BCF01. All dry fields
kept (K), with the end convention `false = 0` external, `true = 1` internal (Q9) and the closure of
the port collar off the internal torus. NEW (G7 typing of the BCG06 product): the internal and the
external model face, their whole boundary parametrizations (the two end slices) and the exhaustion
of the model boundary by these two ends. -/
structure CuspCores (W : CompactCarrier.{u}) {n : ℕ} (E : BoundaryTori W n) where
  ports : W.model.boundary W.Carrier = E.image
  piece : Fin n → PieceEmbedding W
  product : ∀ b, (Torus × Icc (0 : ℝ) 1) ≃ₘ⟮torusModel.prod (𝓡∂ 1), 𝓡∂ 3⟯ (piece b).Piece
  external_end : ∀ b t, (piece b).map (product b (t, iccEnd false)) = E.torusMap b t
  collar_owned : ∀ b, (E.collar b).target ⊆ range (piece b).map
  collar_closure_off : ∀ b, Disjoint (closure (E.collar b).target)
    (range fun t => (piece b).map (product b (t, iccEnd true)))
  disjoint : Pairwise fun b b' => Disjoint (range (piece b).map) (range (piece b').map)
  cuspFn : Fin n → W.Carrier → ℝ
  near : Fin n → TopologicalSpace.Opens W.Carrier
  near_interior : ∀ b, (near b : Set W.Carrier) ⊆ W.interior
  fn_smooth : ∀ b, ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ (cuspFn b) (near b)
  fn_regular : ∀ b, ∀ x ∈ near b, cuspFn b x = 0 → mfderiv W.model 𝓘(ℝ, ℝ) (cuspFn b) x ≠ 0
  internal_eq : ∀ b, (range fun t => (piece b).map (product b (t, iccEnd true))) =
    {x | x ∈ near b ∧ cuspFn b x = 0}
  near_eq : ∀ b, range (piece b).map ∩ near b = {x | x ∈ near b ∧ cuspFn b x ≤ 0}
  internalModelFace : ∀ b, ModelBoundaryFace (piece b)
  internalModelFace_eq : ∀ b, (internalModelFace b).1 = range fun t => product b (t, iccEnd true)
  externalModelFace : ∀ b, ModelBoundaryFace (piece b)
  externalModelFace_eq : ∀ b, (externalModelFace b).1 = range fun t => product b (t, iccEnd false)
  modelFace_cases : ∀ b (F : ModelBoundaryFace (piece b)),
    F = internalModelFace b ∨ F = externalModelFace b

/-- **§2.1** The internal model faces of the cusp cores: ONLY the `true = 1` internal end of each
product (never the external `false = 0` end). -/
def CuspCores.InternalModelFace {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}
    (C : CuspCores W E) : Type u :=
  Σ b : Fin n, {F : ModelBoundaryFace (C.piece b) // F = C.internalModelFace b}

/-- **§2.1** The faces a slim end may be shared with: an actual model boundary component of a zero
domain, or the internal model face of a cusp core. -/
abbrev NeighbourFace {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (Z : ZeroDomains W)
    (C : CuspCores W E) : Type u :=
  (Σ i : Fin Z.count, ModelBoundaryFace (Z.piece i)) ⊕ C.InternalModelFace

/-- The ambient image of a neighbour face. -/
def neighbourSet {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} {Z : ZeroDomains W}
    {C : CuspCores W E} : NeighbourFace Z C → Set W.Carrier
  | .inl F => (Z.piece F.1).map '' F.2.1
  | .inr F => (C.piece F.1).map '' F.2.1.1

/-! ## §5.3 Slim pieces -/

/-- The end slice `b` of a slim model, in the model piece (empty for a model over a circle). -/
def slimModelEnd {W : CompactCarrier.{u}} {P : PieceEmbedding W} :
    SlimModel P → Bool → Set P.Piece
  | .sphereInterval e, b => range fun z => e (z, iccEnd b)
  | .torusInterval e, b => range fun t => e (t, iccEnd b)
  | .overCircle .., _ => ∅

/-- An interval slim model (`sphereInterval` / `torusInterval`); only these have ends. -/
def slimModelIsInterval {W : CompactCarrier.{u}} {P : PieceEmbedding W} : SlimModel P → Prop
  | .sphereInterval _ => True
  | .torusInterval _ => True
  | .overCircle .. => False

/-- The two shapes of a whole face. -/
inductive FaceShape
  | sphere
  | torus

/-- The shape of the ends of an interval slim model (the value on a model over a circle is never
used: such a model has no end). -/
def slimModelEndShape {W : CompactCarrier.{u}} {P : PieceEmbedding W} : SlimModel P → FaceShape
  | .sphereInterval _ => .sphere
  | .torusInterval _ => .torus
  | .overCircle .. => .sphere

/-- **§2.1** The actual ends of a family of slim models: a piece index and a `Bool` end, for
interval models only. -/
def SlimEnd {W : CompactCarrier.{u}} {count : ℕ} {piece : Fin count → PieceEmbedding W}
    (model : ∀ j, SlimModel (piece j)) : Type :=
  {e : Fin count × Bool // slimModelIsInterval (model e.1)}

/-- **Slim pieces (§5.3)**: FC36 (B:6238–6258), ZSP04 (B:6531–6595), ZSP05 (B:6597), BCF01
(B:9642). `count`, `piece`, `model`, `disjoint` kept (K). NEW (transport): the model face of every
actual end and the exhaustion of the model boundary by the ends. REPLACED: `endKind` is defined on
the actual end type and takes values in the neighbour model faces (or `none` = a new end, a face
of `M₂`); the endpoint coordinate and its clauses are defined ONLY on the new ends. -/
structure SlimPiecesV2 (W : CompactCarrier.{u}) {n : ℕ} {E : BoundaryTori W n}
    (Z : ZeroDomains W) (C : CuspCores W E) where
  count : ℕ
  piece : Fin count → PieceEmbedding W
  model : ∀ j, SlimModel (piece j)
  disjoint : Pairwise fun j j' => Disjoint (range (piece j).map) (range (piece j').map)
  endFace : ∀ e : SlimEnd model, ModelBoundaryFace (piece e.1.1)
  endFace_eq : ∀ e, (endFace e).1 = slimModelEnd (model e.1.1) e.1.2
  endFace_exhausted : ∀ j (F : ModelBoundaryFace (piece j)),
    ∃ (b : Bool) (h : slimModelIsInterval (model j)), endFace ⟨(j, b), h⟩ = F
  endKind : SlimEnd model → Option (NeighbourFace Z C)
  endFn : {e : SlimEnd model // endKind e = none} → W.Carrier → ℝ
  endNear : {e : SlimEnd model // endKind e = none} → TopologicalSpace.Opens W.Carrier
  endNear_interior : ∀ e, (endNear e : Set W.Carrier) ⊆ W.interior
  endFn_smooth : ∀ e, ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ (endFn e) (endNear e)
  endFn_regular : ∀ e, ∀ x ∈ endNear e, endFn e x = 0 →
    mfderiv W.model 𝓘(ℝ, ℝ) (endFn e) x ≠ 0
  endFn_level : ∀ e, (piece e.1.1.1).map '' slimModelEnd (model e.1.1.1) e.1.1.2 =
    {x | x ∈ endNear e ∧ endFn e x = 0}
  endFn_eq : ∀ e, range (piece e.1.1.1).map ∩ endNear e =
    {x | x ∈ endNear e ∧ endFn e x ≤ 0}

namespace SlimPiecesV2

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} {Z : ZeroDomains W}
  {C : CuspCores W E} (S : SlimPiecesV2 W Z C)

/-- The actual ends of the slim pieces. -/
abbrev End : Type :=
  SlimEnd S.model

/-- The new (unshared) ends: faces of `M₂`. -/
abbrev NewEnd : Type :=
  {e : S.End // S.endKind e = none}

/-- The ambient image of an end (the whole end slice). -/
def endSet (e : S.End) : Set W.Carrier :=
  (S.piece e.1.1).map '' slimModelEnd (S.model e.1.1) e.1.2

/-- The shape of an end. -/
def endShape (e : S.End) : FaceShape :=
  slimModelEndShape (S.model e.1.1)

/-- The union of the slim pieces. -/
def union : Set W.Carrier :=
  ⋃ j, range (S.piece j).map

end SlimPiecesV2

/-- **§2.1** The actual shared faces: the ends registered as shared with a neighbour model face.
-/
def ActualSharedFace {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} {Z : ZeroDomains W}
    {C : CuspCores W E} (S : SlimPiecesV2 W Z C) : Type :=
  { e : S.End // (S.endKind e).isSome }

end GC.GraphManifold.Assembly.FC39P0
