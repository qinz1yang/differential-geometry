import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainExports74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRowsLinkU74

/-!
# D74-4 on the closed source, revised exits: `ClosedGeometricExportsU74 S B`

Lane S-LANDING (`_LND74`), G2d. Named revision of `ClosedGeometricExportsU74` (review by O-CL0): the
edge stage is identified with `q₁` on the OPEN AMBIENT PARENT `U₂` (`StageIdentU_LND74`, parent
`= ψ(U₂)`), not on the whole preimage, and FDC02's set equality is
`M^edge = U₂ ∩ q₁⁻¹(C₂) ∩ {A/s ≤ 4Δ}`. `ZSP02SmoothExit74`, `ClosedBlock74`, `assembleStages74`
are those of `ClosedGeometricExportsU74`; the stage geometry and the exits over it are restated.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **`ClosedStageGeometryU74 S B choice zero`**: the stage geometry of the closed route on `W`
(the BASES output carried by `M.ψ`) and the abstract cut choice `cut` identified with `choice`. -/
structure ClosedStageGeometryU74 {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    {S : ClosedChainEZRowsSource_RGC K R M δ εr Λz} {B : ClosedBases74 S}
    (choice : ClosedCutChoice74 S B) (zero : ZSP02SmoothExit74 S) where
  slim : SlimStage74 W
  edge : EdgeStage74 W
  circle : StageProj74 W 2
  ιslim : slim.Base → ClosedBlock74 S
  ιedge : edge.Base → ClosedBlock74 S
  ιcircle : circle.Base → ClosedBlock74 S
  slim_ident : StageIdent_LND74 M.ψ.toEquiv slim.toStageProj74 S.chain.slimMap_ZSP35 ιslim
  edge_ident : StageIdentU_LND74 M.ψ.toEquiv edge.toStageProj74
    (S.chain.toGaf02ChainE.cutQ_R74 1) ιedge
    (gafStageDomain5_BAS S.F.family.toLocalChartPacketsC14.toLocalChartPackets 1)
  circle_ident : StageIdent_LND74 M.ψ.toEquiv circle (S.chain.toGaf02ChainE.cutQ_R74 0) ιcircle
  slim_C₃ : ιslim '' slim.C₃ = S.chain.slimC3_ZSP35
  slim_slab : ιslim '' slim.slabImage = S.chain.toChain.slimSlabImage_ZSP35
  slim_faces : ιslim '' slim.facePoints = S.chain.slimFacePoints_ZSP35
  edge_height : ∀ x : edge.parent,
    edge.height x = S.toE_RGC.toRowsSource_RGC.height (M.ψ.symm x)
  edge_level : edge.level = R.edgeLevel_R74
  cut : StageCutChoice74 (assembleStages74 M zero.rows slim edge circle)
  cut_K₃ : ιslim '' cut.K₃ = choice.K₃.carrier
  cut_D₃ : ιslim '' cut.D₃ = choice.D₃.carrier
  cut_C₂ : ιedge '' cut.C₂ = choice.C₂
  cut_C₁ : ιcircle '' cut.C₁ = choice.C₁
  cut_edgeOpen : ιedge '' (cut.edgeBaseOpen : Set _) = choice.edgeBaseOpen
  cut_circleOpen : ιcircle '' (cut.circleBaseOpen : Set _) = choice.circleBaseOpen
  comp : ActualComponent cut.D₃ ≃ ActualComponent choice.D₃.carrier
  comp_eq : ∀ c, ιslim '' c.1 = (comp c).1

/-- The stage geometry `A` of the closed route. -/
abbrev ClosedStageGeometryU74.A {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    {S : ClosedChainEZRowsSource_RGC K R M δ εr Λz} {B : ClosedBases74 S}
    {choice : ClosedCutChoice74 S B} {zero : ZSP02SmoothExit74 S}
    (P : ClosedStageGeometryU74 choice zero) : SmoothStageGeometry74 W (BoundaryTori.empty W) :=
  assembleStages74 M zero.rows P.slim P.edge P.circle

/-- **`ZSP04SmoothExitU74`** (ZSP04 / ZSP05 smooth slim row): the slim pieces over the actual
components of `D₃`, each the WHOLE `f₃`-preimage of its component, with the shared ends. -/
structure ZSP04SmoothExitU74 {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    {S : ClosedChainEZRowsSource_RGC K R M δ εr Λz} {B : ClosedBases74 S}
    {choice : ClosedCutChoice74 S B} {zero : ZSP02SmoothExit74 S}
    (P : ClosedStageGeometryU74 choice zero) where
  pieces : SlimCutPieces74 P.A P.cut

/-- **`EDP04WholeDiskExitU74`** (EDP04 / EDP05 (A) / FDC02): the cut-dependent fields of the edge
bundle over `↥cut.edgeBaseOpen` (whole smooth disks, rank two, proper, compact base), the edge
component export (E3 / E4c), and FDC02's set equality
`M^edge = U₂ ∩ q₁⁻¹(C₂) ∩ {A/s ≤ 4Δ}` for the actual `M^edge = M₂ ∩ X₂`. -/
structure EDP04WholeDiskExitU74 {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    {S : ClosedChainEZRowsSource_RGC K R M δ εr Λz} {B : ClosedBases74 S}
    {choice : ClosedCutChoice74 S B} {zero : ZSP02SmoothExit74 S}
    (P : ClosedStageGeometryU74 choice zero) where
  facts : EdgeCutFacts74 P.A P.cut
  models : EdgeComponentModels (edgeBundle74 P.A P.cut facts)
  edgeSet_eq : choice.edgeSet =
    gafStageDomain5_BAS S.F.family.toLocalChartPacketsC14.toLocalChartPackets 1 ∩
      (S.chain.toGaf02ChainE.cutQ_R74 1 ⁻¹' choice.C₂ ∩
        {p | S.toE_RGC.toRowsSource_RGC.height p ≤ R.edgeLevel_R74})

/-- **`FDC03ActualRemainderU74`** (FDC03 / GAF07 circle bundle, FDC04 cover): the circle bundle
facts over `↥cut.circleBaseOpen` (local trivializations, whole-circle properness, compact base,
saturation `M₃ = q₀⁻¹(C₁)`) and FDC04's point-set cover of the actual pieces. -/
structure FDC03ActualRemainderU74 {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    {S : ClosedChainEZRowsSource_RGC K R M δ εr Λz} {B : ClosedBases74 S}
    {choice : ClosedCutChoice74 S B} {zero : ZSP02SmoothExit74 S}
    (P : ClosedStageGeometryU74 choice zero) where
  facts : CircleCutFacts74 P.A P.cut
  cover : CutCoverFacts74 P.A P.cut

/-- The cut-dependent row structures of the exits. -/
def ClosedStageGeometryU74.rows {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    {S : ClosedChainEZRowsSource_RGC K R M δ εr Λz} {B : ClosedBases74 S}
    {choice : ClosedCutChoice74 S B} {zero : ZSP02SmoothExit74 S}
    (P : ClosedStageGeometryU74 choice zero) (slim : ZSP04SmoothExitU74 P)
    (edge : EDP04WholeDiskExitU74 P) (final : FDC03ActualRemainderU74 P) :
    StageCutRows74 P.A P.cut where
  slim := slim.pieces
  edgeFacts := edge.facts
  circleFacts := final.facts
  edgeModels := edge.models

/-- **`EDP05HorizontalExitU74`** (EDP05 horizontal exit, ZSP05, FDC03 LastFaces): the face facts of
the junctions on the actual rows. -/
structure EDP05HorizontalExitU74 {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    {S : ClosedChainEZRowsSource_RGC K R M δ εr Λz} {B : ClosedBases74 S}
    {choice : ClosedCutChoice74 S B} {zero : ZSP02SmoothExit74 S}
    (P : ClosedStageGeometryU74 choice zero) (slim : ZSP04SmoothExitU74 P)
    (edge : EDP04WholeDiskExitU74 P) (final : FDC03ActualRemainderU74 P) where
  facts : JunctionFaceFacts74 P.A P.cut (P.rows slim edge final)

/-- **`EDP06CircleAgreementU74`** (EDP06 whole rim agreement, FDC03 corners, R1's inputs): the rim
facts and the corner facts at every actual endpoint. -/
structure EDP06CircleAgreementU74 {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    {S : ClosedChainEZRowsSource_RGC K R M δ εr Λz} {B : ClosedBases74 S}
    {choice : ClosedCutChoice74 S B} {zero : ZSP02SmoothExit74 S}
    (P : ClosedStageGeometryU74 choice zero) (slim : ZSP04SmoothExitU74 P)
    (edge : EDP04WholeDiskExitU74 P) (final : FDC03ActualRemainderU74 P)
    (faces : EDP05HorizontalExitU74 P slim edge final) where
  facts : JunctionRimFacts74 P.A P.cut (P.rows slim edge final)
  corners : CornerCutFacts74 faces.facts facts

/-- **`FDC03FinalExit74`-free assembly**: the cut geometry `H` of the exits. -/
def ClosedStageGeometryU74.geometry {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    {S : ClosedChainEZRowsSource_RGC K R M δ εr Λz} {B : ClosedBases74 S}
    {choice : ClosedCutChoice74 S B} {zero : ZSP02SmoothExit74 S}
    (P : ClosedStageGeometryU74 choice zero) (slim : ZSP04SmoothExitU74 P)
    (edge : EDP04WholeDiskExitU74 P) (final : FDC03ActualRemainderU74 P)
    (faces : EDP05HorizontalExitU74 P slim edge final)
    (rims : EDP06CircleAgreementU74 P slim edge final faces) :
    StageCutGeometry74 P.A P.cut where
  rows := P.rows slim edge final
  cover := final.cover
  faces := faces.facts
  rims := rims.facts
  corners := rims.corners

/-- **`ClosedGeometricExportsU74 S B`** (D74-4): the cut choice and the exits of the rows
ZSP02, ZSP04, EDP04, FDC03, EDP05, EDP06 on the SAME `(S, B)`. NOT an unconditional `(S) (B)`
statement: it is the interface the row producers fill, item by item. -/
structure ClosedGeometricExportsU74 {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S) where
  choice : ClosedCutChoice74 S B
  zero : ZSP02SmoothExit74 S
  stages : ClosedStageGeometryU74 choice zero
  slim : ZSP04SmoothExitU74 stages
  edge : EDP04WholeDiskExitU74 stages
  final : FDC03ActualRemainderU74 stages
  faces : EDP05HorizontalExitU74 stages slim edge final
  rims : EDP06CircleAgreementU74 stages slim edge final faces

end DifferentialGeometry.Geometry.Collapse
