import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainCircleStage74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageGeometryA74

/-!
# Draft 74 §4.1 / G31: the closed-route circle stage `StageProj74 W 2` (the record the rows
# assembler reads)

Lane C14-REG-CHAIN (by S-REG-CHAIN2), G31 (record layer): the pieces of
`StaticRegisterV4ChainCircleStage74` as the `StageProj74 W 2` of the abstract rows assembler
(lane S-JUNCTIONS, `Closure/FC39StageGeometryA74`): `Base = W₁` (model `𝓡 2`), open parent
`M.ψ(U₁) ⊆ int W`, final map `q₀ ∘ M.ψ⁻¹` (smooth, submersion). Separate file, as for the edge.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

/-- **The closed-route circle stage** `q₀ : M.ψ(U₁) → W₁` of the rows assembler. -/
def circleStage74 (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (A : SmoothStageBases74 S) :
    StageProj74 W 2 where
  Base := ↥(S.chain.toChain.finalBase_BAS 0)
  baseCharts := A.circleChartedSpace
  baseSmooth := A.circle_isManifold.1
  parent := S.circleParent_R74
  parent_interior := S.circleParent_interior_R74
  proj := S.circleProj_R74 A
  proj_smooth := S.circleProj_smooth_R74 A
  proj_submersion := S.circleProj_submersion_R74 A

/-- The record's parent is the circle parent. -/
theorem circleStage74_parent (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (A : SmoothStageBases74 S) : (S.circleStage74 A).parent = S.circleParent_R74 :=
  rfl

/-- The record's final map is `q₀ ∘ M.ψ⁻¹`. -/
theorem circleStage74_proj_val (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (A : SmoothStageBases74 S) (x : S.circleParent_R74) :
    (show ↥(S.chain.toChain.finalBase_BAS 0) from (S.circleStage74 A).proj x).1 =
      S.stageProjW_R74 0 x.1 :=
  rfl

end ClosedChainEZRowsSource_RGC

/-- **Consumer: the register yields the closed-route circle stage** (as
`register_yields_edgeStage_R74`): for every register, tail member and base point a source `S` with
`E : StageProj74 (Wseq m) 2`, `E.parent = S.circleParent_R74`. -/
theorem register_yields_circleStage_R74 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{0})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      ClosedStrategyRefinesV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)) ∧
      T.Nb = maxNb_V4C ∧ T.cw = maxCw_V4C ∧
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T, ∃ εr δ Λz : ℝ, ∀ m, R.later.tail ≤ m →
        ∃ M : ClosedModel (Wseq m) (gseq m), Nonempty M.X ∧ ∀ x₀ : M.X,
          ∃ S : ClosedChainEZRowsSource_RGC K R M δ εr Λz, S.chain.x₀ = x₀ ∧
            ∃ E : StageProj74 (Wseq m) 2, E.parent = S.circleParent_R74 := by
  obtain ⟨T, hTU, -, hNb, hcw, hR⟩ := exists_closedChainEZRowsSource_RGC K hK A hA Wseq gseq hf hg
  refine ⟨T, hTU, hNb, hcw, fun R => ?_⟩
  obtain ⟨εr, δ, Λz, ht⟩ := hR R
  refine ⟨εr, δ, Λz, fun m hm => ?_⟩
  obtain ⟨M, hne, hS⟩ := ht m hm
  refine ⟨M, hne, fun x₀ => ?_⟩
  obtain ⟨S, hS0⟩ := hS x₀
  exact ⟨S, hS0, S.circleStage74 S.smoothBases74, rfl⟩

end DifferentialGeometry.Geometry.Collapse
