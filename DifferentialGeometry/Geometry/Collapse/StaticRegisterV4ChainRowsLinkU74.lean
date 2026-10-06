import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRowsLink74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RowsLinkOfStageU74

/-!
# D74-5 on the closed source, revised edge row: `ClosedRowsLinkAtU74` (open ambient parent)

Lane S-LANDING (`_LND74`), G2d. Named revision of `ClosedRowsLinkAt74` (review by O-CL0): the edge
source is the open ambient parent restriction `U₂ ∩ q₁⁻¹(V)` (draft 74 §1.3, `U₂` the threshold-5
domain `gafStageDomain5_BAS … 1`), not the whole preimage `q₁⁻¹(V)`:

* `ClosedCutChoice74.edgeSourceU D := U₂ ∩ D.edgeSource` (= `U₂ ∩ q₁⁻¹(D.edgeBaseOpen)`);
* `ClosedRowsLinkAtU74 S B D Rw`: the zero, slim, circle and regions tables of
  `ClosedRowsLinkAt74` and the edge table `EdgeLinkU_LND74` over `U₂`;
* `ClosedRowsLinkU74 S B Rw := ∃ D, ClosedRowsLinkAtU74 S B D Rw`.
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

/-- **The open ambient parent restriction `U₂ ∩ q₁⁻¹(V)`** of the cut choice (draft 74 §1.3). -/
def ClosedCutChoice74.edgeSourceU {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    {S : ClosedChainEZRowsSource_RGC K R M δ εr Λz} {B : ClosedBases74 S}
    (D : ClosedCutChoice74 S B) : Set M.X :=
  gafStageDomain5_BAS S.F.family.toLocalChartPacketsC14.toLocalChartPackets 1 ∩ D.edgeSource

/-- **`ClosedRowsLinkAtU74 S B D Rw`** (D74-5, revised edge row). -/
structure ClosedRowsLinkAtU74 {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
    (D : ClosedCutChoice74 S B) (Rw : FC39RowsV2 W (BoundaryTori.empty W)) : Prop where
  zero : ZeroLink_LND74 M.ψ.toEquiv Rw.zero S.zeroDom74 S.zeroInner74 S.zeroOuter74 S.zeroUV74
  slim : SlimLink_LND74 M.ψ.toEquiv Rw.slim
    (fun c : ActualComponent D.D₃.carrier => S.chain.slimMap_ZSP35 ⁻¹' c.1) D.slimSet
  edge : EdgeLinkU_LND74 M.ψ.toEquiv Rw.edge (S.chain.toGaf02ChainE.cutQ_R74 1)
    S.toE_RGC.toRowsSource_RGC.height R.edgeLevel_R74 D.edgeBaseOpen D.C₂
    (gafStageDomain5_BAS S.F.family.toLocalChartPacketsC14.toLocalChartPackets 1) D.edgeSet
  circle : CircleLink_LND74 M.ψ.toEquiv Rw.circle (S.chain.toGaf02ChainE.cutQ_R74 0)
    D.circleBaseOpen D.C₁ D.circleSource D.M₃
  regions : RegionsLink_LND74 M.ψ.toEquiv Rw S.chain.toGaf02ChainE.cutM1_R74 D.M₂ D.M₃

/-- **`ClosedRowsLinkU74 S B Rw`**: the revised link at SOME legal cut choice. -/
def ClosedRowsLinkU74 {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
    (Rw : FC39RowsV2 W (BoundaryTori.empty W)) : Prop :=
  ∃ D : ClosedCutChoice74 S B, ClosedRowsLinkAtU74 S B D Rw

end DifferentialGeometry.Geometry.Collapse
