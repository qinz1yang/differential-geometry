import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSmoothBases
import DifferentialGeometry.Geometry.Fibration.ActualStageChainSmoothBasesFibres

/-!
# D74-2 row 6 on the closed source: final = native fibres over the parent domains

Lane C14-REG-CHAIN (by C14-REG-CHAINc), G18 (closed consumer): for the closed rows' source `S`
and its smooth stage bases `A = S.smoothBases74`, the rows' final stage map `q_st` (the source's
`stageMap st`) has, inside FC33's open parent domain `U_st`, exactly the native fibres
(`closed_fibre_domain5_R74`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **Final = native fibres on the closed source**, inside the open parent domains. -/
theorem closed_fibre_domain5_R74 {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (st : Fin 3)
    {w₀ : BlockSpace (fun _ : CGPTag S.F.family.toLocalChartPacketsC14.toLocalChartFamily
      S.F.family.toLocalChartPacketsC14.zero => ℝ²)}
    (hw₀ : w₀ ∈ S.chain.toChain.markedBase_BAS st) :
    {p | p ∈ gafStageDomain5_BAS S.F.family.toLocalChartPacketsC14.toLocalChartPackets st ∧
        S.toE_RGC.toRowsSource_RGC.stageMap st p = S.chain.toChain.Θ_BAS st w₀} =
      {p | p ∈ gafStageDomain5_BAS S.F.family.toLocalChartPacketsC14.toLocalChartPackets st ∧
        S.chain.toChain.stageMap_BAS st p = w₀} :=
  S.smoothBases74.fibre_domain5_R74 st hw₀

end DifferentialGeometry.Geometry.Collapse
