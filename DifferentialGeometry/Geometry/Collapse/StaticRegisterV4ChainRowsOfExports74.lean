import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainExports74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GFinalClosed

/-!
# D74-4 heads on the closed source: rows from the geometric exports

Lane S-LANDING (`_LND74`), G2 (heads). Draft 74 §1.5: with the abstract assembler `J1`
(`rows_of_smooth_stage_geometry74`, lane S-JUNCTIONS) as the EXPLICIT theorem argument `hJ1`:

* **`closed_rows_of_geometric_exports_at74_of_assembler hJ1 S B G`**: rows `Rw : FC39RowsV2 W
  (BoundaryTori.empty W)` with `ClosedRowsLinkAt74 S B G.choice Rw`, the link kept at the SAME cut
  choice `G.choice`;
* **`closed_rows_of_chain_outputs74_of_assembler hJ1 S B G`**: the `∃ D` version `ClosedRowsLink`.

The proof assembles `A, D, H` from the exits (`ClosedStageGeometry74.A / cut / geometry`), applies
`hJ1`, and derives the five tables of `ClosedRowsLinkAt74` from `StageRowsLink74` through the
identification of the stages with the chain (`RowsLinkOfStage74`). The theorem argument `hJ1` is
EXACTLY the type of `rows_of_smooth_stage_geometry74` at `E = BoundaryTori.empty W`; once that
theorem is delivered the heads are obtained by `hJ1 := rows_of_smooth_stage_geometry74`.
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

/-- **D74-4 head, assembler as an explicit argument**: from the exits `G` of the SAME `(S, B)`,
rows linked to the actual objects of the chain at the SAME cut choice `G.choice`. -/
theorem closed_rows_of_geometric_exports_at74_of_assembler {K : ℕ}
    {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (hJ1 : ∀ (A : SmoothStageGeometry74 W (BoundaryTori.empty W)) (D : StageCutChoice74 A),
      StageCutGeometry74 A D →
      ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W), StageRowsLink74 A D Rw)
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
    (G : ClosedGeometricExports74 S B) :
    ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W), ClosedRowsLinkAt74 S B G.choice Rw := by
  obtain ⟨Rw, L⟩ := hJ1 G.stages.A G.stages.cut
    (G.stages.geometry G.slim G.edge G.final G.faces G.rims)
  have hz : ZeroLink_LND74 M.ψ.toEquiv Rw.zero S.zeroDom74 S.zeroInner74 S.zeroOuter74
      S.zeroUV74 := by
    rw [L.zeroSlim.zero_eq]
    exact G.zero.link
  have hslim := slimLink_of_stage_LND74 L.zeroSlim G.stages.slim_ident G.stages.cut_D₃
    G.stages.comp G.stages.comp_eq
  have hedge := edgeLink_of_stage_LND74 L.edge G.stages.edge_ident G.stages.edge_height
    G.stages.cut_edgeOpen G.stages.edge_level G.stages.cut_C₂ G.choice.edgeBaseOpen_sub
    G.edge.edgeSet_eq
  have hSset := slimSetW_of_stage_LND74 (D := G.stages.cut) G.stages.slim_ident G.stages.cut_D₃
  have hEset := (edgeSetW_of_stage_LND74 (D := G.stages.cut) G.stages.edge_ident
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

/-- **D74-4 head, the `∃ D` version** (`closed_rows_of_chain_outputs74` with the assembler as an
explicit argument): rows linked to the actual objects of the chain at SOME legal cut choice. -/
theorem closed_rows_of_chain_outputs74_of_assembler {K : ℕ}
    {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (hJ1 : ∀ (A : SmoothStageGeometry74 W (BoundaryTori.empty W)) (D : StageCutChoice74 A),
      StageCutGeometry74 A D →
      ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W), StageRowsLink74 A D Rw)
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
    (G : ClosedGeometricExports74 S B) :
    ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W), ClosedRowsLink S B Rw := by
  obtain ⟨Rw, L⟩ := closed_rows_of_geometric_exports_at74_of_assembler hJ1 S B G
  exact ⟨Rw, L.link⟩

/-- **Consumer: the exits feed GROUP G.** The rows of the closed head go to
`exists_strongCertificate_of_rows_GFIN`: a strong certificate on `W` with the empty port family. -/
theorem closed_strongCertificate_of_exports74_of_assembler {K : ℕ}
    {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (hJ1 : ∀ (A : SmoothStageGeometry74 W (BoundaryTori.empty W)) (D : StageCutChoice74 A),
      StageCutGeometry74 A D →
      ∃ Rw : FC39RowsV2 W (BoundaryTori.empty W), StageRowsLink74 A D Rw)
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
    (G : ClosedGeometricExports74 S B) :
    Nonempty (StrongCertificate W (BoundaryTori.empty W)) := by
  obtain ⟨Rw, -⟩ := closed_rows_of_geometric_exports_at74_of_assembler hJ1 S B G
  exact exists_strongCertificate_of_rows_GFIN Rw

end DifferentialGeometry.Geometry.Collapse
