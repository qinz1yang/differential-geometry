import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRowsB
import DifferentialGeometry.Geometry.Fibration.ActualStageChainSmoothBases

/-!
# D74-2 on the closed source: `SmoothStageBases74 S` and the adapter applied to `B_R`

Lane C14-REG-CHAIN (by C14-REG-CHAINc), G11 (closed binding). Draft 74 §1.2:

* `SmoothStageBases74 S := SmoothStageBasesOn74 S.chain.toChain` — the smooth stage bases of
  the closed rows' source (seven-row contract, kernel `Fibration/ActualStageChainSmoothBases`);
* `Gaf02Bases.toSmoothStageBases74 (B : ClosedBases74 S) : SmoothStageBases74 S` is the kernel
  adapter (deterministic); `ClosedChainEZRowsSource_RGC.smoothBases74 S` its value at `S.bases74`;
* `SmoothStageBasesOn74.stageMap_ident_R74`: the rows source's `stageMap j` (= `q_j = π_j ∘ E`,
  the FINAL projection D74-5 points at) is `Θ_j ∘ f_j` — the native `stageMap_BAS` enters only
  through the later map;
* consumer `register_yields_smoothBases_R74`: at the strategy of `register_yields_chainEJAZ_RGC`
  every register, tail member and base point has a source whose smooth stage bases (from its own
  `B_R`) have open parent domains, the same-chain identification, and `W₁, W₂, W₃` smooth
  manifolds of dimensions `2, 1, 1` with immersed inclusions.
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

/-- **D74-2: the smooth stage bases of the closed rows' source.** -/
abbrev SmoothStageBases74 {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) : Type :=
  SmoothStageBasesOn74 S.chain.toChain

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

/-- The smooth stage bases of the source: the D74-2 adapter at the source's own `B_R`. -/
def smoothBases74 (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) : SmoothStageBases74 S :=
  S.bases74.toSmoothStageBases74

end ClosedChainEZRowsSource_RGC

namespace SmoothStageBasesOn74

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
  {S : ClosedChainEZRowsSource_RGC K R M δ εr Λz}

/-- The rows source's FINAL stage map `q_j = π_j ∘ E` is `Θ_j ∘ f_j` (D74-5: the native map only
through the later map). -/
theorem stageMap_ident_R74 (A : SmoothStageBases74 S) (j : Fin 3) (p : M.X) :
    S.toE_RGC.toRowsSource_RGC.stageMap j p =
      S.chain.toChain.Θ_BAS j (S.chain.toChain.stageMap_BAS j p) :=
  A.later.final_factor j p

end SmoothStageBasesOn74

/-- **Consumer: the register yields the smooth stage bases on its own source** (D74-2): at the
strategy of `register_yields_chainEJAZ_RGC`, every register has on every tail member, for every
base point, a source with that base point whose smooth stage bases (the adapter at `S.bases74`)
have open threshold-5 parent domains, the same-chain identification `q_j = Θ_j ∘ f_j`, and
`W₁` a smooth surface with immersed inclusion (model `ℝ²`). -/
theorem register_yields_smoothBases_R74 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      ClosedStrategyRefinesV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)) ∧
      PartialClosedThresholdValidityV4Rows K A Wseq gseq (earlyDataSharedV4 K) T ∧
      T.Nb = maxNb_V4C ∧ T.cw = maxCw_V4C ∧
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T, ∃ εr δ Λz : ℝ, ∀ m, R.later.tail ≤ m →
        ∃ M : ClosedModel (Wseq m) (gseq m), Nonempty M.X ∧ ∀ x₀ : M.X,
          ∃ S : ClosedChainEZRowsSource_RGC K R M δ εr Λz, S.chain.x₀ = x₀ ∧
            ∃ Ab : SmoothStageBases74 S, Ab = S.smoothBases74 ∧
              (∀ j, IsOpen (gafStageDomain5_BAS
                S.F.family.toLocalChartPacketsC14.toLocalChartPackets j)) ∧
              (∀ j p, S.toE_RGC.toRowsSource_RGC.stageMap j p =
                S.chain.toChain.Θ_BAS j (S.chain.toChain.stageMap_BAS j p)) ∧
              (let _ := Ab.circleChartedSpace
               IsManifold 𝓘(ℝ, ℝ²) ∞ (S.chain.toChain.finalBase_BAS 0)) := by
  obtain ⟨T, hTU, hv, hNb, hcw, hR⟩ := exists_closedChainEZRowsSource_RGC K hK A hA Wseq gseq hf hg
  refine ⟨T, hTU, hv, hNb, hcw, fun R => ?_⟩
  obtain ⟨εr, δ, Λz, ht⟩ := hR R
  refine ⟨εr, δ, Λz, fun m hm => ?_⟩
  obtain ⟨M, hne, hS⟩ := ht m hm
  refine ⟨M, hne, fun x₀ => ?_⟩
  obtain ⟨S, hS0⟩ := hS x₀
  exact ⟨S, hS0, S.smoothBases74, rfl, S.smoothBases74.proj.domain_open,
    S.smoothBases74.stageMap_ident_R74, S.smoothBases74.circle_isManifold.1⟩

end DifferentialGeometry.Geometry.Collapse
