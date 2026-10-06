import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRowsAtOCL

/-!
# Consumer of O-CL1 G4: the regions of the produced stage geometry at `D_R`

Lane O-CL1 (`_OCL`), G4 consumer. On `P = S.closedStagesAt_OCL B hT hεr A zero`, the carried cut's
slim set is a COMPACT subset of `W` and the produced cover reads `W = ψ(Z) ∪ slimSet ∪ M₂` with the
carried slim set and `M₂` (non-vacuous: `slimSet` and `M₂` are the `M.ψ`-images of the actual
regions of `D_R`, G4a), the input format of FDC04 / the assembler `J1`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

/-- **The produced stage geometry's regions at `D_R`**: the carried slim set is compact and
`W = ψ(Z) ∪ slimSet ∪ M₂` for the carried cut. -/
theorem stagesAt_regions_OCL (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (B : ClosedBases74 S)
    (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
    (hεr : εr < 1 / 2) (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S) :
    IsCompact (S.closedStagesAt_OCL B hT hεr A zero).cut.slimSet ∧
      M.ψ '' S.chain.zeroUnion_ZSP35 ∪ (S.closedStagesAt_OCL B hT hεr A zero).cut.slimSet ∪
        (S.closedStagesAt_OCL B hT hεr A zero).cut.M₂ = univ := by
  have hF := S.goodCut_facts_OCL B hT hεr
  rw [S.slimSet_at_OCL B hT hεr A zero, S.M₂_at_OCL B hT hεr A zero]
  refine ⟨hF.2.1.image M.ψ.continuous, ?_⟩
  rw [← image_union, ← image_union, hF.2.2.1]
  exact image_univ_of_surjective M.ψ.toEquiv.surjective

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
