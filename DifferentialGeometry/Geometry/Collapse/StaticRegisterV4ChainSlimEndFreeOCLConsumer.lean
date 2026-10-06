import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSlimEndFreeOCL
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainCornerDescentJN74

/-!
# Draft 74, G4 consumer: the slim face function of `slimExitAt3_OCL` is constant on `q₀`-fibres

Lane C14-REG-CHAIN (by S-REG-CHAIN6), G4 consumer (suffix `_OCL`). G3's
`slimEnd_circleFibreConst_OCL` for the rows built from the exit `slimExitAt3_OCL` (the exit of G4,
with the end classification): `slimEnd3_circleFibreConst_OCL` is the input `hconstH` of
`cornerDescent_ofFibreConst_JN74` for a SLIM label `F.horizontal e = .inr en`. The proof is G3's:
`q₀ = E` as in `cornerT_fibreConst_at_JN74`, then `slimEnd3_fibreConst_OCL`.
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
`slimExitAt3_OCL`, for every new slim end `en`, two points `x, y` of the circle domain inside the
neighbourhood of `en` with the same circle projection have the same residual face function. -/
theorem slimEnd3_circleFibreConst_OCL
    (en : ((S.stagesAtZ_OCL B hT hεr A).rows
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
        (S.slimExitAt3_OCL B hT hεr A hK)) edge final).slimPieces.NewEnd)
    (x y : ((S.stagesAtZ_OCL B hT hεr A).rows
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
        (S.slimExitAt3_OCL B hT hεr A hK)) edge final).circle.domain)
    (hx : (x : W.Carrier) ∈ (((S.stagesAtZ_OCL B hT hεr A).rows
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
        (S.slimExitAt3_OCL B hT hεr A hK)) edge final).slimPieces.residualNear (.inr en) :
          Set W.Carrier))
    (hy : (y : W.Carrier) ∈ (((S.stagesAtZ_OCL B hT hεr A).rows
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
        (S.slimExitAt3_OCL B hT hεr A hK)) edge final).slimPieces.residualNear (.inr en) :
          Set W.Carrier))
    (hxy : ((S.stagesAtZ_OCL B hT hεr A).rows
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
        (S.slimExitAt3_OCL B hT hεr A hK)) edge final).circle.proj y =
      ((S.stagesAtZ_OCL B hT hεr A).rows
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
        (S.slimExitAt3_OCL B hT hεr A hK)) edge final).circle.proj x) :
    ((S.stagesAtZ_OCL B hT hεr A).rows
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
        (S.slimExitAt3_OCL B hT hεr A hK)) edge final).slimPieces.residualFn (.inr en) x.1 =
    ((S.stagesAtZ_OCL B hT hεr A).rows
      (S.zsp04ExitAt_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
        (S.slimExitAt3_OCL B hT hεr A hK)) edge final).slimPieces.residualFn (.inr en) y.1 := by
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
  exact S.slimEnd3_fibreConst_OCL B hT hεr A hK en hx hy hE

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
