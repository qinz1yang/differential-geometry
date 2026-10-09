import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRowsB
import DifferentialGeometry.Geometry.Fibration.ActualStageChainBasesManifold

/-!
# The manifold-level threshold-5 submersions on the closed rows' source, on the final family

Lane S-BASES-KER, group G10 (closed binding). `ClosedBases74 S = Gaf02Bases S.chain.toChain
S.chain.rough` carries `π_jE : U_j → W_j` as a smooth submersion into the manifold `W_j`
(`Gaf02Bases.final_submersion_manifold_circle/edge/slim_BAS`, models `ℝ², ℝ, ℝ`).

* `ClosedChainEZRowsSource_RGC.final_submersion_manifold_BAS`: the three statements at the
  source's own `bases74`;
* `eventually_final_submersion_manifold_rowsSourceZ_BAS`: consumer on the final closed family at
  register V4's strategy, tail form `∀ᶠ`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

/-- **The manifold-level threshold-5 submersions of the rows source** (at its own `bases74`),
all three stages. -/
theorem final_submersion_manifold_BAS (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) :
    (∀ (y₀ : ↥(S.chain.toChain.finalBase_BAS 0)) (p : M.X)
      (hp : p ∈ gafStageDomain5_BAS S.F.family.toLocalChartPacketsC14.toLocalChartPackets 0),
      type_of% (S.bases74.final_submersion_manifold_circle_BAS y₀ hp)) ∧
    (∀ (y₀ : ↥(S.chain.toChain.finalBase_BAS 1)) (p : M.X)
      (hp : p ∈ gafStageDomain5_BAS S.F.family.toLocalChartPacketsC14.toLocalChartPackets 1),
      type_of% (S.bases74.final_submersion_manifold_edge_BAS y₀ hp)) ∧
    (∀ (y₀ : ↥(S.chain.toChain.finalBase_BAS 2)) (p : M.X)
      (hp : p ∈ gafStageDomain5_BAS S.F.family.toLocalChartPacketsC14.toLocalChartPackets 2),
      type_of% (S.bases74.final_submersion_manifold_slim_BAS y₀ hp)) :=
  ⟨fun y₀ _ hp => S.bases74.final_submersion_manifold_circle_BAS y₀ hp,
    fun y₀ _ hp => S.bases74.final_submersion_manifold_edge_BAS y₀ hp,
    fun y₀ _ hp => S.bases74.final_submersion_manifold_slim_BAS y₀ hp⟩

end ClosedChainEZRowsSource_RGC

/-- **Consumer: the manifold-level threshold-5 submersions on the final family** (register V4's
strategy, tail form `∀ᶠ`): for every register, on every tail member (a nonempty model), for every
base point, a rows source with that base point whose threshold-5 maps `π_jE : U_j → W_j` are
smooth submersions into the manifolds `W_j`. -/
theorem eventually_final_submersion_manifold_rowsSourceZ_BAS (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      ClosedStrategyRefinesV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)) ∧
      PartialClosedThresholdValidityV4Rows K A Wseq gseq (earlyDataSharedV4 K) T ∧
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T, ∃ εr δ Λz : ℝ, ∀ᶠ m in atTop,
        ∃ M : ClosedModel (Wseq m) (gseq m), Nonempty M.X ∧ ∀ x₀ : M.X,
          ∃ S : ClosedChainEZRowsSource_RGC K R M δ εr Λz, S.chain.x₀ = x₀ ∧
            type_of% S.final_submersion_manifold_BAS := by
  have key := exists_closedChainEZRowsSource_RGC K hK A hA Wseq gseq hf hg
  refine key.imp fun T hT => ⟨hT.1, hT.2.1, fun R => ?_⟩
  exact (hT.2.2.2.2 R).imp fun εr h => h.imp fun δ h => h.imp fun Λz ht =>
    eventually_atTop.mpr ⟨R.later.tail, fun m hm => (ht m hm).imp fun M hM =>
      ⟨hM.1, fun x₀ => (hM.2 x₀).imp fun S hS => ⟨hS, S.final_submersion_manifold_BAS⟩⟩⟩

end DifferentialGeometry.Geometry.Collapse
