import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainExitsAtOCL

/-!
# Consumer of O-CL1 G3: the produced stage record at `D_R` has good open bases

Lane O-CL1 (`_OCL`), G3 consumer. The cut of the produced stage geometry
`P = S.closedStagesAt_OCL B hT hεr A zero` (G3a) is read back through the record's
identification fields:

* every point of `P.cut.edgeBaseOpen` carries EDP04's WHOLE smooth disk
  `{q₁ = ι c, A/s ≤ 4Δ}` with boundary circle the whole rim (O-CL0 G1 `goodCut_edge_disk_OCL`
  through `P.cut_edgeOpen`);
* every point of `P.cut.circleBaseOpen` carries GAF07's WHOLE smooth circle `q₀⁻¹(ι c)`
  (`goodCut_circle_fibre_OCL` through `P.cut_circleOpen`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open DifferentialGeometry.Topology
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

/-- **The produced stage record's edge base is good**: EDP04's whole smooth disk over every
point of `P.cut.edgeBaseOpen`, in the rows' height `A/s` and level `4Δ`. -/
theorem stagesAt_edge_disk_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (B : ClosedBases74 S)
    (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
    (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C) (hεr : εr < 1 / 2)
    (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)
    (c : (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeBaseOpen) :
    ∃ φ : ClosedCell 2 → M.X, IsSmoothEmbedding (𝓡∂ 2) 𝓘(ℝ, E3) ∞ φ ∧
      range φ = {x | S.chain.toGaf02ChainE.cutQ_R74 1 x =
          (S.closedStagesAt_OCL B hT hεr A zero).ιedge c.1 ∧
        S.toE_RGC.toRowsSource_RGC.height x ≤ R.edgeLevel_R74} := by
  have hc : (S.closedStagesAt_OCL B hT hεr A zero).ιedge c.1 ∈
      (S.goodCut_OCL B hT hεr).edgeBaseOpen := by
    rw [← (S.closedStagesAt_OCL B hT hεr A zero).cut_edgeOpen]
    exact mem_image_of_mem _ c.2
  obtain ⟨φ, hφ, hr, -⟩ := S.goodCut_edge_disk_OCL B hT hNb hcw hεr hc
  exact ⟨φ, hφ, hr⟩

/-- **The produced stage record's circle base is good**: GAF07's whole smooth circle over every
point of `P.cut.circleBaseOpen`. -/
theorem stagesAt_circle_fibre_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (B : ClosedBases74 S)
    (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
    (hεr : εr < 1 / 2) (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)
    (c : (S.closedStagesAt_OCL B hT hεr A zero).cut.circleBaseOpen) :
    ∃ f : Circle → M.X, IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, E3) ∞ f ∧
      range f = S.chain.toGaf02ChainE.cutQ_R74 0 ⁻¹'
        {(S.closedStagesAt_OCL B hT hεr A zero).ιcircle c.1} := by
  have hc : (S.closedStagesAt_OCL B hT hεr A zero).ιcircle c.1 ∈
      (S.goodCut_OCL B hT hεr).circleBaseOpen := by
    rw [← (S.closedStagesAt_OCL B hT hεr A zero).cut_circleOpen]
    exact mem_image_of_mem _ c.2
  exact S.goodCut_circle_fibre_OCL B hT hεr hc

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
