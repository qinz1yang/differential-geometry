import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainExportsU74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainExitsOfRows74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageRows74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GFinalClosed

/-!
# D74-4 heads on the closed source, revised (open ambient parent, given cut choice)

Lane S-LANDING (`_LND74`), G2d. Named revision of the closed landing heads (review by O-CL0):

* the exits are `ClosedGeometricExportsU74` (edge stage on `U₂`) and the link is
  `ClosedRowsLinkAtU74` / `ClosedRowsLinkU74` (edge source `U₂ ∩ q₁⁻¹(V)`):
  **`closed_rows_of_geometric_exports_atU74`**, **`closed_rows_of_chain_outputsU74`** (assembler
  `J1 = rows_of_smooth_stage_geometry74` plugged in; `…_of_assembler` take it as `hJ1`);
* the development-stage record `Hrows` is stated at a GIVEN cut choice `D`
  (`RemainingActualRowExitsU74 S B D`): quantifying over all `D` was unsatisfiable (a legal `D`
  with `edgeBaseOpen = W₂` breaks `EdgeCutFacts74.fibre_disk` off `B₂`); the head
  **`closed_geometric_exports_of_rowsU74 S B D Htail Hrows`** works at the explicit `D`, as does
  **`closed_rows_of_rowsU74`**.
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

/-- **Revised D74-4 head, assembler as an explicit argument**: from the exits `G` of the SAME
`(S, B)`, rows linked (revised edge row) to the actual objects of the chain at `G.choice`. -/
theorem closed_rows_of_geometric_exports_atU74_of_assembler {K : ℕ}
    {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (hJ1 : ∀ (A : SmoothStageGeometry74 W (BoundaryTori.empty W)) (D : StageCutChoice74 A),
      StageCutGeometry74 A D →
      ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W), StageRowsLink74 A D Rw)
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
    (G : ClosedGeometricExportsU74 S B) :
    ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W), ClosedRowsLinkAtU74 S B G.choice Rw := by
  obtain ⟨Rw, L⟩ := hJ1 G.stages.A G.stages.cut
    (G.stages.geometry G.slim G.edge G.final G.faces G.rims)
  have hz : ZeroLink_LND74 M.ψ.toEquiv Rw.zero S.zeroDom74 S.zeroInner74 S.zeroOuter74
      S.zeroUV74 := by
    rw [L.zeroSlim.zero_eq]
    exact G.zero.link
  have hslim := slimLink_of_stage_LND74 L.zeroSlim G.stages.slim_ident G.stages.cut_D₃
    G.stages.comp G.stages.comp_eq
  have hedge := edgeLinkU_of_stage_LND74 L.edge G.stages.edge_ident G.stages.edge_height
    G.stages.cut_edgeOpen G.stages.edge_level G.stages.cut_C₂ G.choice.edgeBaseOpen_sub
    G.edge.edgeSet_eq
  have hSset := slimSetW_of_stage_LND74 (D := G.stages.cut) G.stages.slim_ident G.stages.cut_D₃
  have hEset := (edgeSetWU_of_stage_LND74 (D := G.stages.cut) G.stages.edge_ident
    G.stages.edge_height G.stages.edge_level G.stages.cut_C₂).trans
    (congrArg _ G.edge.edgeSet_eq.symm)
  have hzσ : ∃ σ : Fin G.stages.A.zero.count ≃ S.ZeroIdx74, ∀ i,
      range (G.stages.A.zero.piece i).map = M.ψ '' S.zeroDom74 (σ i) := by
    obtain ⟨σ, hσ⟩ := G.zero.link
    exact ⟨σ, fun i => (hσ i).1⟩
  have hreg := regionsLink_of_stage_LND74 (M₁c := S.chain.toGaf02ChainE.cutM1_R74) M.ψ L.regions
    hzσ hSset hEset rfl G.choice.M₂_eq G.choice.M₃_eq
  have hM3 : G.choice.M₃ = S.chain.toGaf02ChainE.cutQ_R74 0 ⁻¹' G.choice.C₁ := by
    have h1 : M.ψ '' G.choice.M₃ = M.ψ '' (S.chain.toGaf02ChainE.cutQ_R74 0 ⁻¹' G.choice.C₁) := by
      have hD3 : G.stages.cut.M₃ = M.ψ '' G.choice.M₃ :=
        L.regions.regionM3_eq.symm.trans hreg.2.2
      have hcr : G.stages.cut.circleRegion =
          M.ψ '' (S.chain.toGaf02ChainE.cutQ_R74 0 ⁻¹' G.choice.C₁) := by
        rw [← G.stages.cut_C₁]
        exact stageSet_LND74 G.stages.circle_ident G.stages.cut.C₁
      rw [← hD3, G.final.facts.saturation, hcr]
    exact M.ψ.toEquiv.injective.image_injective h1
  exact ⟨Rw, ⟨hz, hslim, hedge,
    circleLink_of_stage_LND74 L.circle G.stages.circle_ident G.stages.cut_circleOpen
      G.stages.cut_C₁ hM3, hreg⟩⟩

/-- **Revised head, `∃ D` version**, assembler as an explicit argument. -/
theorem closed_rows_of_chain_outputsU74_of_assembler {K : ℕ}
    {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (hJ1 : ∀ (A : SmoothStageGeometry74 W (BoundaryTori.empty W)) (D : StageCutChoice74 A),
      StageCutGeometry74 A D →
      ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W), StageRowsLink74 A D Rw)
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
    (G : ClosedGeometricExportsU74 S B) :
    ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W), ClosedRowsLinkU74 S B Rw := by
  obtain ⟨Rw, L⟩ := closed_rows_of_geometric_exports_atU74_of_assembler hJ1 S B G
  exact ⟨Rw, G.choice, L⟩

/-- **Revised head with `J1` plugged in** (`closed_rows_of_geometric_exports_at74`, edge on
`U₂`). -/
theorem closed_rows_of_geometric_exports_atU74 {K : ℕ}
    {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
    (G : ClosedGeometricExportsU74 S B) :
    ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W), ClosedRowsLinkAtU74 S B G.choice Rw :=
  closed_rows_of_geometric_exports_atU74_of_assembler
    (fun A D H => rows_of_smooth_stage_geometry74 A D H) S B G

/-- **Revised head with `J1` plugged in**, `∃ D` version (`closed_rows_of_chain_outputs74`). -/
theorem closed_rows_of_chain_outputsU74 {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
    (G : ClosedGeometricExportsU74 S B) :
    ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W), ClosedRowsLinkU74 S B Rw :=
  closed_rows_of_chain_outputsU74_of_assembler
    (fun A D H => rows_of_smooth_stage_geometry74 A D H) S B G

/-- **Consumer: the revised exits feed GROUP G** (`exists_strongCertificate_of_rows_GFIN`). -/
theorem closed_strongCertificate_of_exportsU74 {K : ℕ}
    {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
    (G : ClosedGeometricExportsU74 S B) :
    Nonempty (StrongCertificate W (BoundaryTori.empty W)) := by
  obtain ⟨Rw, -⟩ := closed_rows_of_geometric_exports_atU74 S B G
  exact exists_strongCertificate_of_rows_GFIN Rw

/-- The revised exits over a given cut choice. -/
structure ClosedExitsOverU74 {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    {S : ClosedChainEZRowsSource_RGC K R M δ εr Λz} {B : ClosedBases74 S}
    (choice : ClosedCutChoice74 S B) where
  zero : ZSP02SmoothExit74 S
  stages : ClosedStageGeometryU74 choice zero
  slim : ZSP04SmoothExitU74 stages
  edge : EDP04WholeDiskExitU74 stages
  final : FDC03ActualRemainderU74 stages
  faces : EDP05HorizontalExitU74 stages slim edge final
  rims : EDP06CircleAgreementU74 stages slim edge final faces

/-- The revised exits over a choice, bundled with the choice. -/
def ClosedExitsOverU74.toExports {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    {S : ClosedChainEZRowsSource_RGC K R M δ εr Λz} {B : ClosedBases74 S}
    {choice : ClosedCutChoice74 S B} (O : ClosedExitsOverU74 choice) :
    ClosedGeometricExportsU74 S B :=
  ⟨choice, O.zero, O.stages, O.slim, O.edge, O.final, O.faces, O.rims⟩

/-- **`Hrows` at a GIVEN cut choice `D`** (D74-18 revised): given the FDC04 facts at `D`, the
revised exits over `D` exist. Removed item by item as the producers land. -/
structure RemainingActualRowExitsU74 {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
    (D : ClosedCutChoice74 S B) : Prop where
  exits : ClosedFdcFacts74 D → Nonempty (ClosedExitsOverU74 D)

/-- **Revised `closed_geometric_exports_of_rows74` at the explicit cut choice `D`**. -/
theorem closed_geometric_exports_of_rowsU74 {K : ℕ}
    {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
    (D : ClosedCutChoice74 S B) (Htail : ClosedFdcFacts74 D)
    (Hrows : RemainingActualRowExitsU74 S B D) :
    ∃ G : ClosedGeometricExportsU74 S B, G.choice = D := by
  obtain ⟨O⟩ := Hrows.exits Htail
  exact ⟨O.toExports, rfl⟩

/-- **The closed route at the explicit choice `D`** from the revised development-stage records,
with `J1` plugged in. -/
theorem closed_rows_of_rowsU74 {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
    (D : ClosedCutChoice74 S B) (Htail : ClosedFdcFacts74 D)
    (Hrows : RemainingActualRowExitsU74 S B D) :
    ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W), ClosedRowsLinkU74 S B Rw := by
  obtain ⟨G, -⟩ := closed_geometric_exports_of_rowsU74 S B D Htail Hrows
  exact closed_rows_of_chain_outputsU74 S B G

end DifferentialGeometry.Geometry.Collapse
