import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainFaceRemovalJN74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageSharedRemovedJN74

/-!
# Draft 74, field g7 `shared_removed` at `D_R`

Lane S-JUNCTIONS (by S-JUNCTIONS4), G28 consumer (suffix `_JN74`). `shared_removed_JN74` on the rows
of the carried stage geometry with `hKR` produced (`zeroFace_slim_relInt_at_JN74`, G24): every
shared end of the slim pieces of ANY rows over `closedStagesAt_OCL` lies in the relative interior of
the slim set in `M₁`.
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

/-- **g7 `shared_removed` on the actual rows at `D_R`.** -/
theorem shared_removed_at_JN74 (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)
    (Rw : StageCutRows74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut) :
    ∀ σ : ActualSharedFace Rw.slimPieces, Rw.slimPieces.endSet σ.1 ⊆
      relInt (regionM1 (S.closedStagesAt_OCL B hT hεr A zero).A.zero
        (S.closedStagesAt_OCL B hT hεr A zero).A.cusp)
        (S.closedStagesAt_OCL B hT hεr A zero).cut.slimSet :=
  shared_removed_JN74 Rw (S.zeroFace_slim_relInt_at_JN74 B hT hεr A zero)

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
