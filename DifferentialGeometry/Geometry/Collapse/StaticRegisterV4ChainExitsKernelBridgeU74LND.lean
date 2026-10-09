import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRowsOfExportsU74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.ExitsKernelU74LND

/-!
# The closed exits project to the plain-data kernel

Lane S-LANDING (by S-LANDING2, suffix `_LND`), G4. `ClosedExitsOverU74 D` (G2d) is a record over
a source `S : ClosedChainEZRowsSource_RGC`; `ExitsKernelU_LND` (`Closure/ExitsKernelU74LND`) is its
S-free mirror on plain data, inhabited on the S³ singleton and the S² × S¹ loop
(`Closure/ExitsKernelU74ApplicationsLND`). This file proves that the records of the closed route
ARE instances of the kernel, field for field:

* `ClosedCutChoice74.stageIdentData_LND D`: the plain data of the chain side at the cut choice
  `D` (the final maps `f₃, q₁, q₀`, the open ambient parent `U₂ = gafStageDomain5_BAS … 1`, the
  rows' height `A/s`, the level `4Δ`, the slim base sets and the base sets of `D`);
* `ClosedStageGeometryU74.toKernel_LND P : StageGeometryKernelU_LND …`;
* `ClosedExitsOverU74.toKernel_LND O : ExitsKernelU_LND …` (zero table `S.zeroDom74 …`, the
  A0 cut geometry `P.geometry …`, FDC02's set equality `D.edgeSet = U₂ ∩ q₁⁻¹(C₂) ∩ {H ≤ 4Δ}`);
* `ClosedExitsOverU74.rows_tables_LND`: the kernel consumer on the exits of the closed route
  (zero, slim, edge on `U₂`, circle tables of the J1 rows), through the projection.
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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Bridge

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
  {S : ClosedChainEZRowsSource_RGC K R M δ εr Λz} {B : ClosedBases74 S}

/-- **The plain data of the chain side of the exits at the cut choice `D`**. -/
def ClosedCutChoice74.stageIdentData_LND (D : ClosedCutChoice74 S B) :
    StageIdentData_LND M.X (ClosedBlock74 S) where
  qs := S.chain.slimMap_ZSP35
  q1 := S.chain.toGaf02ChainE.cutQ_R74 1
  q0 := S.chain.toGaf02ChainE.cutQ_R74 0
  U₂ := gafStageDomain5_BAS S.F.family.toLocalChartPacketsC14.toLocalChartPackets 1
  hS := S.toE_RGC.toRowsSource_RGC.height
  lvl := R.edgeLevel_R74
  slimC3 := S.chain.slimC3_ZSP35
  slab := S.chain.toChain.slimSlabImage_ZSP35
  faces := S.chain.slimFacePoints_ZSP35
  K₃ := D.K₃.carrier
  D₃ := D.D₃.carrier
  C₂ := D.C₂
  C₁ := D.C₁
  eO := D.edgeBaseOpen
  cO := D.circleBaseOpen

/-- **`ClosedStageGeometryU74` is an instance of the stage kernel.** -/
def ClosedStageGeometryU74.toKernel_LND {D : ClosedCutChoice74 S B} {zero : ZSP02SmoothExit74 S}
    (P : ClosedStageGeometryU74 D zero) :
    StageGeometryKernelU_LND M.ψ.toEquiv zero.rows M.cusp_R74 D.stageIdentData_LND where
  slim := P.slim
  edge := P.edge
  circle := P.circle
  ιslim := P.ιslim
  ιedge := P.ιedge
  ιcircle := P.ιcircle
  slim_ident := P.slim_ident
  edge_ident := P.edge_ident
  circle_ident := P.circle_ident
  slim_C₃ := P.slim_C₃
  slim_slab := P.slim_slab
  slim_faces := P.slim_faces
  edge_height := P.edge_height
  edge_level := P.edge_level
  cut := P.cut
  cut_K₃ := P.cut_K₃
  cut_D₃ := P.cut_D₃
  cut_C₂ := P.cut_C₂
  cut_C₁ := P.cut_C₁
  cut_edgeOpen := P.cut_edgeOpen
  cut_circleOpen := P.cut_circleOpen
  comp := P.comp
  comp_eq := P.comp_eq

/-- **`ClosedExitsOverU74` is an instance of the exits kernel**: the zero table of the source, the
stage kernel, the A0 cut geometry assembled from the exit records, FDC02's set equality. -/
def ClosedExitsOverU74.toKernel_LND {D : ClosedCutChoice74 S B} (O : ClosedExitsOverU74 D) :
    ExitsKernelU_LND M.ψ.toEquiv O.zero.rows M.cusp_R74 D.stageIdentData_LND S.zeroDom74
      S.zeroInner74 S.zeroOuter74 S.zeroUV74 D.edgeSet where
  zero := O.zero.link
  stages := O.stages.toKernel_LND
  geometry := O.stages.geometry O.slim O.edge O.final O.faces O.rims
  edgeSet_eq := O.edge.edgeSet_eq

/-- **Kernel consumer on the exits of the closed route**: the J1 rows of the stage geometry satisfy
the zero, slim, edge (on `U₂`) and circle tables of `RowsLinkKernel74` on the chain's data
(`hCV`: `C₂ ⊆ edgeBaseOpen`; `hM3`: the saturation `M₃ = q₀⁻¹(C₁)` of FDC03). -/
theorem ClosedExitsOverU74.rows_tables_LND {D : ClosedCutChoice74 S B}
    (O : ClosedExitsOverU74 D) (hCV : D.C₂ ⊆ D.edgeBaseOpen)
    (hM3 : D.M₃ = S.chain.toGaf02ChainE.cutQ_R74 0 ⁻¹' D.C₁) :
    ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W),
      ZeroLink_LND74 M.ψ.toEquiv Rw.zero S.zeroDom74 S.zeroInner74 S.zeroOuter74 S.zeroUV74 ∧
      SlimLink_LND74 M.ψ.toEquiv Rw.slim
        (fun c : ActualComponent D.D₃.carrier => S.chain.slimMap_ZSP35 ⁻¹' c.1)
        (S.chain.slimMap_ZSP35 ⁻¹' D.D₃.carrier) ∧
      EdgeLinkU_LND74 M.ψ.toEquiv Rw.edge (S.chain.toGaf02ChainE.cutQ_R74 1)
        S.toE_RGC.toRowsSource_RGC.height R.edgeLevel_R74 D.edgeBaseOpen D.C₂
        (gafStageDomain5_BAS S.F.family.toLocalChartPacketsC14.toLocalChartPackets 1)
        D.edgeSet ∧
      CircleLink_LND74 M.ψ.toEquiv Rw.circle (S.chain.toGaf02ChainE.cutQ_R74 0)
        D.circleBaseOpen D.C₁ (S.chain.toGaf02ChainE.cutQ_R74 0 ⁻¹' D.circleBaseOpen) D.M₃ :=
  O.toKernel_LND.rows_tables hCV hM3

end Bridge

end DifferentialGeometry.Geometry.Collapse
