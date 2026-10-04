import DifferentialGeometry.Geometry.Comparison.RadialHessianLowerBound
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyPieces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySeams
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.SolidTorus
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MobiusRefibration
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardDiscardedModels
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Defs
import DifferentialGeometry.Topology.Handle.Manifold
import DifferentialGeometry.Topology.Manifold.CornerRounding.RoundedMin

/-!
# Chapter-14 assembly certificate: vertices, edges, the circle region and face kinds

The parts of the FC39 decomposition certificate (`AssemblyCertificate.lean`), moved VERBATIM from the
frozen interface file V2 (`build-logs/scratch/ASM-FIX/AssemblyInterfacesV2.lean`, the helpers of
lines 67–92 and §1 lines 109–318; change log
`docs/geometrization/chapter14/design-fc39-fc42-assembly-v2-changes-20261004.md`). Two deviations,
both forced by the lane rules: the four local instances on `ClosedCell 2` and `ClosedCell 3` carry
the suffix `_ASMCERT` (their bodies are unchanged), and the four `sorry` statements about
`standardRimRounding` (V2 lines 94–107) are not moved — they are library facts of lane ASM-L1 and no
certificate field needs them. One field is restated, for the `explicitVarsOfIff` linter (a structure
projection cannot make `self` implicit): V2's
`rounding_agree : ∀ b, b ∉ ⋃ k, cornerChart k '' rimBox 1 → (rounding b ≤ 0 ↔ b ∈ cornerBase)` is
the equivalent set equality `{b | rounding b ≤ 0} \ U = cornerBase \ U` with `U` that union
(`CircleRegion.rounding_le_zero_iff` in `AssemblyCertificate.lean` recovers the pointwise form).

Contents: the endpoints `iccEnd`, the rim `diskRim`, the boxes `rimBox`, the ONE standard rim rounding
`standardRimRounding` (review item 2, D3); the vertex models `ZeroModel`, `ClosedZeroPiece`,
`SlimFibre`, `SlimModel` (with `overCircle … hclosed`, review item 7, D5), `Vertex` with `image`,
`piece`, `boundaryImage`; the edges `EdgeHandle`, `EdgeCirclePiece` (with `boundary_submersion`,
review item 1, D2); the two-stratum `CircleRegion` with genuine corner charts and the controlled
common rounding (review items 3 and 10, D4/D14); and `FaceKind`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance ballCharts_ASMCERT : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmooth_ASMCERT : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

local instance diskCharts_ASMCERT : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmooth_ASMCERT : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

/-- The two endpoints of the unit interval. -/
def iccEnd (b : Bool) : Icc (0 : ℝ) 1 :=
  if b then ⟨1, zero_le_one, le_rfl⟩ else ⟨0, le_rfl, zero_le_one⟩

/-- The boundary circle of the closed disk. -/
def diskRim : Set (ClosedCell 2) := {x | (𝓡∂ 2).IsBoundaryPoint x}

/-- The open square `(-r, r)²` of the rim and corner charts. -/
def rimBox (r : ℝ) : Set (ℝ × ℝ) := {v | |v.1| < r ∧ |v.2| < r}

/-! ## The ONE standard rim rounding function (V2, review item 2, D3)

The V1 structure `RimRounding` (any smooth `ψ` with regular zero level and the right signs outside
the unit box) is REMOVED: a positive island inside the box satisfies it and adds a torus boundary
component to the rounded union. V2 fixes one function, the tree's regularized minimum
(`CornerRounding/RoundedMin.lean:28`) of the two coordinates at width `1/4`. Its band
`{0 ≤ x, 0 ≤ y, x + y < 3/4}` (`CornerRounding/Regular.lean:202–226`) lies in the open unit box. -/

/-- The fixed width of the standard rim rounding. -/
def rimRoundingWidth : ℝ := 1 / 4

/-- The standard rim rounding `ψ_std (x, y) = roundedMin (1/4) x y`. The ball–handle side is
`{ψ_std ≤ 0}` (the concave union `{y ≤ 0} ∪ {x ≤ 0}` outside the unit box), the circle-region side
is `{ψ_std ≥ 0}` (the quadrant `{x ≥ 0, y ≥ 0}` outside the unit box): the SAME arc. -/
def standardRimRounding (v : ℝ × ℝ) : ℝ :=
  DifferentialGeometry.Topology.Manifold.CornerRounding.roundedMin rimRoundingWidth v.1 v.2

/-! ## §1 FC39: the decomposition certificate (draft (a)) -/

/-- The smooth zero models (ZSP02 / LFR54 list). Unchanged from V1. -/
inductive ZeroModel {W : CompactCarrier.{u}} (P : PieceEmbedding W) : Type u
  | ball (e : P.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3)
  | solidTorus
      (e : solidTorusCarrier.{u}.Carrier ≃ₘ⟮solidTorusCarrier.{u}.model, 𝓡∂ 3⟯ P.Piece)
  | twistedIBundle
      (e : mobiusBundleCarrier.{u}.Carrier ≃ₘ⟮mobiusBundleCarrier.{u}.model, 𝓡∂ 3⟯ P.Piece)
  /-- Punctured `RP³`: an actual embedding into the fixed `projectiveThreeSpaceLift` whose image
  is the complement of an open oriented ball chart (the model of `ConnectedSumFixedFold.lean:22–34`). -/
  | puncturedRP3
      (c : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold)
      (f : P.Piece → projectiveThreeSpaceLift.{u}.Carrier)
      (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
      (hrange : range f = {x | x ∉ c.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1})

/-- A closed zero piece. Unchanged from V1. -/
structure ClosedZeroPiece (W : CompactCarrier.{u}) where
  piece : PieceEmbedding W
  boundary_empty : (𝓡∂ 3).boundary piece.Piece = ∅
  Q : ConnectedClosedOrientedManifold.{u} 3
  metric : SmoothRiemannianMetric (𝓡 3) Q.Carrier
  nonneg : DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow metric 0
  ident : piece.Piece ≃ₘ⟮𝓡∂ 3, 𝓡 3⟯ Q.Carrier

/-- The fibre of a slim piece over a circle, at the base point `1`. Unchanged from V1. -/
inductive SlimFibre {W : CompactCarrier.{u}} (P : PieceEmbedding W) (p : P.Piece → Circle) :
    Type u
  | sphere (f : ClosureSphere.{u} → P.Piece) (hf : IsSmoothEmbedding (𝓡 2) (𝓡∂ 3) ∞ f)
      (hr : range f = p ⁻¹' {1})
  | torus (f : Torus → P.Piece) (hf : IsSmoothEmbedding torusModel (𝓡∂ 3) ∞ f)
      (hr : range f = p ⁻¹' {1})

/-- Slim models. V2 (review item 7, D5): `overCircle` takes `hclosed : ∂P = ∅`. Without it a
closed `S²`- or `T²`-product over the circle minus a small ball avoiding the base fibre satisfies
the constructor (submersion, actual closed fibre at `1`), so FC42 could not conclude that the piece
exhausts `W`. With `hclosed`, compactness and the submersion make `P` a closed fibre bundle, and
its image is open and closed in `W`. -/
inductive SlimModel {W : CompactCarrier.{u}} (P : PieceEmbedding W) : Type u
  | sphereInterval
      (e : (ClosureSphere.{u} × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece)
  | torusInterval (e : (Torus × Icc (0 : ℝ) 1) ≃ₘ⟮torusModel.prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece)
  | overCircle (p : P.Piece → Circle) (hp : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ p)
      (hsub : ∀ q, Surjective (mfderiv (𝓡∂ 3) (𝓡 1) p q)) (fibre : SlimFibre P p)
      (hclosed : (𝓡∂ 3).boundary P.Piece = ∅)

/-- The vertices of the assembly. Unchanged from V1. -/
inductive Vertex (W : CompactCarrier.{u}) : Type (u + 1)
  | zero (P : PieceEmbedding W) (m : ZeroModel P)
  | closedZero (C : ClosedZeroPiece W)
  | slim (P : PieceEmbedding W) (m : SlimModel P)
  | cuspCore (P : PieceEmbedding W)
      (e : (Torus × Icc (0 : ℝ) 1) ≃ₘ⟮torusModel.prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece)

/-- The actual image of a vertex in `W`. Unchanged from V1. -/
def Vertex.image {W : CompactCarrier.{u}} : Vertex W → Set W.Carrier
  | .zero P _ => range P.map
  | .closedZero C => range C.piece.map
  | .slim P _ => range P.map
  | .cuspCore P _ => range P.map

/-- V2 (review item 3, D4): the piece of a vertex. -/
def Vertex.piece {W : CompactCarrier.{u}} : Vertex W → PieceEmbedding W
  | .zero P _ => P
  | .closedZero C => C.piece
  | .slim P _ => P
  | .cuspCore P _ => P

/-- V2 (review item 3, D4): the image of the MODEL boundary of a vertex (the set that the
certificate's faces partition exhaustively). -/
def Vertex.boundaryImage {W : CompactCarrier.{u}} (v : Vertex W) : Set W.Carrier :=
  v.piece.map '' (𝓡∂ 3).boundary v.piece.Piece

/-- A product disk handle over a closed interval, with its REAL corners. Unchanged from V1. -/
structure EdgeHandle (W : CompactCarrier.{u}) where
  map : ClosedCell 2 × Icc (0 : ℝ) 1 → W.Carrier
  smooth : ContMDiff ((𝓡∂ 2).prod (𝓡∂ 1)) W.model ∞ map
  mfderiv_bijective : ∀ p, Bijective (mfderiv ((𝓡∂ 2).prod (𝓡∂ 1)) W.model map p)
  injective : Injective map
  interior : range map ⊆ W.interior

/-- The horizontal end disk of a handle at the endpoint `b`. -/
def EdgeHandle.endDisk {W : CompactCarrier.{u}} (H : EdgeHandle W) (b : Bool) : Set W.Carrier :=
  range fun x : ClosedCell 2 => H.map (x, iccEnd b)

/-- The vertical face of a handle. -/
def EdgeHandle.vertical {W : CompactCarrier.{u}} (H : EdgeHandle W) : Set W.Carrier :=
  H.map '' (diskRim ×ˢ univ)

/-- An edge component over a circle: a GENUINE smooth `D²`-bundle (no corners), its projection and
one actual fibre disk. V2 (review item 1, D2): field `boundary_submersion` — the projection
restricted to `∂P` is a submersion, stated chart-free: through every boundary point runs a smooth
curve inside `∂P` along which `proj` has nonzero derivative. V1 had only the submersion on `P`
and one disk fibre; `(D² × S¹) \ int B³` with the small ball avoiding the base fibre satisfies those
fields, embeds in an oriented `W`, and has an extra `S²` boundary component (`proj|S²` has
critical points, so `boundary_submersion` fails for it). The boundary-preserving Ehresmann lemma
that this field feeds is `exists_circleLiftFlow_of_boundary_submersion` (§3). -/
structure EdgeCirclePiece (W : CompactCarrier.{u}) where
  piece : PieceEmbedding W
  proj : piece.Piece → Circle
  proj_smooth : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ proj
  proj_submersion : ∀ q, Surjective (mfderiv (𝓡∂ 3) (𝓡 1) proj q)
  boundary_submersion : ∀ q, (𝓡∂ 3).IsBoundaryPoint q → ∃ γ : ℝ → piece.Piece,
    ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ 3) ∞ γ ∧ γ 0 = q ∧ (∀ t, (𝓡∂ 3).IsBoundaryPoint (γ t)) ∧
      mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (proj ∘ γ) 0 ≠ 0
  fibre : ClosedCell 2 → piece.Piece
  fibre_embedding : IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 3) ∞ fibre
  fibre_range : range fibre = proj ⁻¹' {1}
  interior : range piece.map ⊆ W.interior

/-- The two-stratum circle region with corners and the COMMON rounding data (FDC03, FDC04 ¶3,
B:7402–7419). V2 (review items 3 and 10, D4/D14) adds, as fields:
* `defining_independent`: the two active defining functions at a corner are linearly independent
  (the pair of differentials is onto `ℝ × ℝ`);
* genuine corner charts `cornerChart k` on `(-2, 2)²` in which the two active defining functions
  are `-(λₖ x)` and `-(λₖ y)` and every other one is negative; every corner of the base is the
  centre of one chart; the charts have pairwise disjoint targets (the V1 field
  `rectangle_disjoint` and the V1 field `rectangle` are replaced: the rectangle is now the image of
  the unit box);
* the controlled common rounding: on each chart target, `rounding = -(λₖ ψ_std)` with the ONE
  standard function `standardRimRounding`; outside the unit-box images, `rounding ≤ 0` is the
  cornered base (V1 `rounding_agree`). A positive island is impossible: the rounded base is fixed
  everywhere. -/
structure CircleRegion (W : CompactCarrier.{u}) where
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
  mem_neighborhood : ∀ b, b ∈ neighborhood b
  trivialization : (b : Base) →
    (TopologicalSpace.Opens.comap proj (neighborhood b))
      ≃ₘ⟮W.model, (𝓡 2).prod (𝓡 1)⟯ ((neighborhood b) × Circle)
  projection_trivialization : ∀ b x, ((trivialization b x).1).val = proj x.val
  definingCount : ℕ
  defining : Fin definingCount → Base → ℝ
  defining_smooth : ∀ l, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (defining l)
  defining_regular : ∀ l b, defining l b = 0 → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (defining l) b ≠ 0
  depth_le_two : ∀ b, (Finset.univ.filter fun l => defining l b = 0).card ≤ 2
  -- V2 (review item 3, D4): linear independence of the two active defining functions
  defining_independent : ∀ b l l', l ≠ l' → defining l b = 0 → defining l' b = 0 →
    Surjective fun w : TangentSpace (𝓡 2) b =>
      (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (defining l) b w, mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (defining l') b w)
  cornerBase : Set Base
  cornerBase_eq : cornerBase = {b | ∀ l, defining l b ≤ 0}
  cornerBase_compact : IsCompact cornerBase
  -- V2 (review item 3, D4): genuine corner charts
  cornerCount : ℕ
  cornerChart : Fin cornerCount → PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (ℝ × ℝ) Base ∞
  cornerChart_source : ∀ k, (cornerChart k).source = rimBox 2
  cornerChart_disjoint : Pairwise fun k k' =>
    Disjoint (cornerChart k).target (cornerChart k').target
  cornerFirst : Fin cornerCount → Fin definingCount
  cornerSecond : Fin cornerCount → Fin definingCount
  corner_ne : ∀ k, cornerFirst k ≠ cornerSecond k
  cornerScale : Fin cornerCount → ℝ
  cornerScale_pos : ∀ k, 0 < cornerScale k
  chart_first : ∀ k v, v ∈ rimBox 2 →
    defining (cornerFirst k) (cornerChart k v) = -(cornerScale k * v.1)
  chart_second : ∀ k v, v ∈ rimBox 2 →
    defining (cornerSecond k) (cornerChart k v) = -(cornerScale k * v.2)
  chart_other : ∀ k l v, l ≠ cornerFirst k → l ≠ cornerSecond k → v ∈ rimBox 2 →
    defining l (cornerChart k v) < 0
  corner_center : ∀ b l l', l ≠ l' → defining l b = 0 → defining l' b = 0 →
    ∃ k, b = cornerChart k (0, 0)
  -- the common rounding (V2, review items 2/3/10, D3/D4/D14: controlled, standard in every chart)
  rounding : Base → ℝ
  rounding_smooth : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ rounding
  rounding_regular : ∀ b, rounding b = 0 → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) rounding b ≠ 0
  rounding_chart : ∀ k v, v ∈ rimBox 2 →
    rounding (cornerChart k v) = -(cornerScale k * standardRimRounding v)
  rounding_agree : {b | rounding b ≤ 0} \ (⋃ k, cornerChart k '' rimBox 1) =
    cornerBase \ ⋃ k, cornerChart k '' rimBox 1
  rounded_compact : IsCompact {b | rounding b ≤ 0}

attribute [instance] CircleRegion.baseTop CircleRegion.baseCharts CircleRegion.baseSmooth
  CircleRegion.baseT2

/-- The cornered circle region `R = proj⁻¹(C₁)` as a subset of `W`. -/
def CircleRegion.region {W : CompactCarrier.{u}} (R : CircleRegion W) : Set W.Carrier :=
  Subtype.val '' (R.proj ⁻¹' R.cornerBase)

/-- The rounded circle region `R' = proj⁻¹{rounding ≤ 0}`. -/
def CircleRegion.rounded {W : CompactCarrier.{u}} (R : CircleRegion W) : Set W.Carrier :=
  Subtype.val '' (R.proj ⁻¹' {b | R.rounding b ≤ 0})

/-- V2: the corner rectangle `k` (the image of the unit box; V1 had a free `Opens` field). -/
def CircleRegion.rectangle {W : CompactCarrier.{u}} (R : CircleRegion W) (k : Fin R.cornerCount) :
    Set R.Base :=
  R.cornerChart k '' rimBox 1

/-- V2 (review item 3, D4): the support of the rounding at corner `k`, in `W`. -/
def CircleRegion.roundingSupport {W : CompactCarrier.{u}} (R : CircleRegion W)
    (k : Fin R.cornerCount) : Set W.Carrier :=
  Subtype.val '' (R.proj ⁻¹' (R.cornerChart k).target)

/-- V2 (review item 3, D4): what a vertex face is. A face of kind `external i`, `torusSeam c b` or
`sphereSeam c b` is that whole torus / sphere; a `partitioned` face is cut into handle end disks
and circle-region faces (arcs and loops). -/
inductive FaceKind (n torusSeams sphereSeams : ℕ) : Type
  | external (i : Fin n)
  | torusSeam (c : Fin torusSeams) (b : Bool)
  | sphereSeam (c : Fin sphereSeams) (b : Bool)
  | partitioned

end GC.GraphManifold.Assembly
