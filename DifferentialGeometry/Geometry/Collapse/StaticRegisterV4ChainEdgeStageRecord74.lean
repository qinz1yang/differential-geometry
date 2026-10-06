import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainEdgeStage74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageGeometryA74

/-!
# Draft 74 §4.1 / G30: the closed-route `EdgeStage74 W` (the data the rows assembler reads)

Lane C14-REG-CHAIN (by S-REG-CHAIN2), G30 (record layer). The pieces of
`StaticRegisterV4ChainEdgeStage74` packaged as the `EdgeStage74 W` of the abstract rows assembler
(lane S-JUNCTIONS, `Closure/FC39StageGeometryA74`): `Base = W₂` (model `𝓡 1`), open parent
`M.ψ(U₂) ⊆ int W`, final map `q₁ ∘ M.ψ⁻¹` (smooth, submersion), height `A/s ∘ M.ψ⁻¹`, level `4Δ`.
Separate from the stage file so that it depends on the (not yet accepted) assembler module only
here. The assembler restricts this stage to the chosen good open base
`D.edgeBaseOpen = edgeBaseOpens_R74` with `cbase = C₂`; its cut-dependent facts
(`EdgeCutFacts74`: `fibre_disk` = EDP04, `rank_two`, `proper`, `cbase_compact`, `cbase_domain`)
are the EDP04 / EDP05 / FDC02 exits.
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

/-- **The closed-route edge stage** `q₁ : M.ψ(U₂) → W₂` of the rows assembler. -/
def edgeStage74 (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (A : SmoothStageBases74 S) :
    EdgeStage74 W where
  Base := ↥(S.chain.toChain.finalBase_BAS 1)
  baseCharts := A.edgeChartedSpace1
  baseSmooth := A.edge_isManifold1.1
  parent := S.edgeParent_R74
  parent_interior := S.edgeParent_interior_R74
  proj := S.edgeProj_R74 A
  proj_smooth := S.edgeProj_smooth_R74 A
  proj_submersion := S.edgeProj_submersion_R74 A
  height := S.edgeHeightP_R74
  height_smooth := S.edgeHeightP_smooth_R74
  level := R.edgeLevel_R74

/-- The record's data are the stage's. -/
theorem edgeStage74_parent (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (A : SmoothStageBases74 S) : (S.edgeStage74 A).parent = S.edgeParent_R74 :=
  rfl

theorem edgeStage74_level (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (A : SmoothStageBases74 S) : (S.edgeStage74 A).level = 4 * R.later.excl.Δ :=
  rfl

/-- The record's final map is `q₁ ∘ M.ψ⁻¹`. -/
theorem edgeStage74_proj_val (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (A : SmoothStageBases74 S) (x : S.edgeParent_R74) :
    (show ↥(S.chain.toChain.finalBase_BAS 1) from (S.edgeStage74 A).proj x).1 =
      S.stageProjW_R74 1 x.1 :=
  rfl

/-- The record's height is `H_S ∘ M.ψ⁻¹` (`H_S = A/s`). -/
theorem edgeStage74_height (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (A : SmoothStageBases74 S) (x : S.edgeParent_R74) :
    (S.edgeStage74 A).height x = S.edgeHeightW_R74 x.1 :=
  rfl

end ClosedChainEZRowsSource_RGC

/-- **Consumer: the register yields the closed-route edge stage** (at the strategy of
`register_yields_chainEJAZ_RGC`, as `register_yields_smoothBases_R74`): every register has on
every tail member, for every base point, a source `S` with that base point whose edge stage record
is `S.edgeStage74 S.smoothBases74`: open parent `M.ψ(U₂)`, final map `q₁ ∘ M.ψ⁻¹` onto the smooth
`𝓡 1`-manifold `W₂`, the level `4Δ`. -/
theorem register_yields_edgeStage_R74 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
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
            ∃ E : EdgeStage74 (Wseq m), E.parent = S.edgeParent_R74 ∧
              E.level = 4 * R.later.excl.Δ := by
  obtain ⟨T, hTU, -, hNb, hcw, hR⟩ := exists_closedChainEZRowsSource_RGC K hK A hA Wseq gseq hf hg
  refine ⟨T, hTU, hNb, hcw, fun R => ?_⟩
  obtain ⟨εr, δ, Λz, ht⟩ := hR R
  refine ⟨εr, δ, Λz, fun m hm => ?_⟩
  obtain ⟨M, hne, hS⟩ := ht m hm
  refine ⟨M, hne, fun x₀ => ?_⟩
  obtain ⟨S, hS0⟩ := hS x₀
  exact ⟨S, hS0, S.edgeStage74 S.smoothBases74, rfl, rfl⟩

end DifferentialGeometry.Geometry.Collapse
