import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSlimEndCoordOCL
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainCornerDescentJN74

/-!
# Draft 74, G3 consumer: the slim face function is constant on the `q₀`-fibres of the circle domain

Lane C14-REG-CHAIN (by S-REG-CHAIN6), G3 consumer (suffix `_OCL`). `slimEnd_circleFibreConst_OCL` is
the exact shape of the input `hconstH` of `cornerDescent_ofFibreConst_JN74` for a SLIM label
`F.horizontal e = .inr en` (HANDOVER ADDENDUM 2 of S-JUNCTIONS3): on the rows `Rw` built from
`slimExitAt2_OCL`, the residual face function `residualFn (.inr en)` takes equal values at two
points `x, y` of the circle domain of its neighbourhood with the same circle projection `q₀`.
The proof transports `q₀ = E` (`circle_ident.proj_eq`, `gafStageQ_zero_starProjection_BAS`) as in
`cornerT_fibreConst_at_JN74` and applies `slimEnd_fibreConst_OCL`.
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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

section At

variable (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
  (hεr : εr < 1 / 2) (A : SmoothStageBases74 S) (hK : 5 ≤ K)
  (edge : EDP04WholeDiskExitU74 (S.stagesAtZ_OCL B hT hεr A))
  (final : FDC03ActualRemainderU74 (S.stagesAtZ_OCL B hT hεr A))

/-- **The slim face function is constant on the `q₀`-fibres** (the input `hconstH` of
`cornerDescent_ofFibreConst_JN74` for a slim label): on the rows of the gate with the exit
`slimExitAt2_OCL`, for every new slim end `en`, two points `x, y` of the circle domain inside the
neighbourhood of `en` with the same circle projection have the same residual face function. -/
theorem slimEnd_circleFibreConst_OCL
    (en : ((S.stagesAtZ_OCL B hT hεr A).rows
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
        (S.slimExitAt2_OCL B hT hεr A hK)) edge final).slimPieces.NewEnd)
    (x y : ((S.stagesAtZ_OCL B hT hεr A).rows
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
        (S.slimExitAt2_OCL B hT hεr A hK)) edge final).circle.domain)
    (hx : (x : W.Carrier) ∈ (((S.stagesAtZ_OCL B hT hεr A).rows
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
        (S.slimExitAt2_OCL B hT hεr A hK)) edge final).slimPieces.residualNear (.inr en) :
          Set W.Carrier))
    (hy : (y : W.Carrier) ∈ (((S.stagesAtZ_OCL B hT hεr A).rows
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
        (S.slimExitAt2_OCL B hT hεr A hK)) edge final).slimPieces.residualNear (.inr en) :
          Set W.Carrier))
    (hxy : ((S.stagesAtZ_OCL B hT hεr A).rows
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
        (S.slimExitAt2_OCL B hT hεr A hK)) edge final).circle.proj y =
      ((S.stagesAtZ_OCL B hT hεr A).rows
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
        (S.slimExitAt2_OCL B hT hεr A hK)) edge final).circle.proj x) :
    ((S.stagesAtZ_OCL B hT hεr A).rows
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
        (S.slimExitAt2_OCL B hT hεr A hK)) edge final).slimPieces.residualFn (.inr en) x.1 =
    ((S.stagesAtZ_OCL B hT hεr A).rows
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
        (S.slimExitAt2_OCL B hT hεr A hK)) edge final).slimPieces.residualFn (.inr en) y.1 := by
  have hπ0 := gafStageQ_zero_starProjection_BAS
    S.F.family.toLocalChartPacketsC14.toLocalChartPackets
  have hxp : (x : W.Carrier) ∈ (S.stagesAtZ_OCL B hT hεr A).A.circle.parent :=
    (S.stagesAtZ_OCL B hT hεr A).A.circle.restrictParent_le _ x.2
  have hyp : (y : W.Carrier) ∈ (S.stagesAtZ_OCL B hT hεr A).A.circle.parent :=
    (S.stagesAtZ_OCL B hT hεr A).A.circle.restrictParent_le _ y.2
  have hqx := (S.stagesAtZ_OCL B hT hεr A).circle_ident.proj_eq ⟨x, hxp⟩
  have hqy := (S.stagesAtZ_OCL B hT hεr A).circle_ident.proj_eq ⟨y, hyp⟩
  have hq : S.chain.toGaf02ChainE.cutQ_R74 0 (M.ψ.symm y) =
      S.chain.toGaf02ChainE.cutQ_R74 0 (M.ψ.symm x) :=
    hqy.symm.trans ((congrArg (fun v : (S.stagesAtZ_OCL B hT hεr A).cut.circleBaseOpen =>
      (S.stagesAtZ_OCL B hT hεr A).ιcircle v.1) hxy).trans hqx)
  have hE : S.chain.toChain.E (M.ψ.symm x) = S.chain.toChain.E (M.ψ.symm y) := by
    have h : (gafStageQ S.F.family.toLocalChartPacketsC14.toLocalChartFamily
        S.F.family.toLocalChartPacketsC14.zero 0).starProjection
          (S.chain.toChain.E (M.ψ.symm y)) =
      (gafStageQ S.F.family.toLocalChartPacketsC14.toLocalChartFamily
        S.F.family.toLocalChartPacketsC14.zero 0).starProjection
          (S.chain.toChain.E (M.ψ.symm x)) := hq
    rw [hπ0, hπ0] at h
    exact h.symm
  exact S.slimEnd_fibreConst_OCL B hT hεr A hK en hx hy hE

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
