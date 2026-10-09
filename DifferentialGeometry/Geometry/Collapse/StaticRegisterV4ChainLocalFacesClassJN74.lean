import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainLocalFacesVertJN74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageLocalFacesClassJN74

/-!
# Draft 74, `local_faces` at `D_R`: the classification of the frontier points of `C₁`

Lane S-JUNCTIONS (by S-JUNCTIONS4), G25 consumer (suffix `_JN74`). `frontier_classification_JN74`
on the actual rows of `closedStagesAt_OCL` with `edge_region`
(`cut_edgeSet_inter_M₃_eq_vertical_JN74`) and `edgeSet ⊆ M₂` (`cover_at_OCL`) produced.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open DifferentialGeometry.Topology.Manifold
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

section At

variable (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
  (hεr : εr < 1 / 2)

/-- **The classification of the frontier points of `C₁` on the actual rows at `D_R`.** -/
theorem frontier_classification_at_JN74 (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)
    (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (Rw : StageCutRows74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (F : JunctionFaceFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut Rw)
    (rimBase : Rw.edge.Base → Rw.circle.Base)
    (hrim : ∀ c ∈ Rw.edge.cbase, Rw.edge.rim c = Rw.circle.fibre (rimBase c))
    {c : Rw.circle.Base} (hc : c ∈ frontier Rw.circle.cbase) :
    (∃ c' ∈ Rw.edge.cbase, c' ∉ frontier Rw.edge.cbase ∧ c = rimBase c') ∨
      (∃ e : Rw.edge.EdgeEnd, c = rimBase e.1) ∨
      ∃ (x₀ : W.Carrier) (Fl : Rw.slimPieces.ResidualFace), x₀ ∈ Rw.circle.fibre c ∧
        x₀ ∈ Rw.slimPieces.residualSet Fl ∧
        ∀ x ∈ Rw.circle.fibre c, x ∉ (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeSet :=
  Rw.frontier_classification_JN74 F rimBase hrim
    (S.cut_edgeSet_inter_M₃_eq_vertical_JN74 B hT hεr A zero hNb hcw Rw.edgeFacts)
    (S.cover_at_OCL B hT hεr A zero (S.goodCut_edgeSet_eq_OCL B hT hεr hNb hcw)).edgeSet_subset_M₂
    hc

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
