import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRowsB
import DifferentialGeometry.Geometry.Fibration.ActualStageChainFc33Row

/-!
# The FC33 row on the closed rows' source, on the final family

Lane S-BASES-KER, group G11 (closed binding). The rows' source `S : ClosedChainEZRowsSource_RGC`
of the final closed family `C14Z` carries a chain with (JA) (`S.chain : Gaf02ChainEJA …`,
`c₃ < c_adjust`) and the bases object `S.bases74 : Gaf02Bases S.chain.toChain S.chain.rough`;
`Gaf02Bases.fc33_row_BAS` at that pair is FC33's row.

* `ClosedChainEZRowsSource_RGC.fc33_row_BAS`: the row at the source's own `bases74`;
* `eventually_fc33_row_rowsSourceZ_BAS`: consumer on the final closed family at register V4's
  strategy, tail form `∀ᶠ`: every register, every tail member (a nonempty model), every base
  point has a rows source with that base point on which FC33's row holds.
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

/-- **FC33's row on the rows source** (at its own `bases74` and the chain's `c₃ < c_adjust`). -/
theorem fc33_row_BAS (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) :
    type_of% (S.bases74.fc33_row_BAS S.chain.c_lt_adj) :=
  S.bases74.fc33_row_BAS S.chain.c_lt_adj

end ClosedChainEZRowsSource_RGC

/-- **Consumer: FC33's row on the final family** (register V4's strategy, tail form `∀ᶠ`): for
every register, on every tail member (a nonempty model), for every base point, a rows source with
that base point on which the FC33 row holds. -/
theorem eventually_fc33_row_rowsSourceZ_BAS (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
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
            type_of% S.fc33_row_BAS := by
  have key := exists_closedChainEZRowsSource_RGC K hK A hA Wseq gseq hf hg
  refine key.imp fun T hT => ⟨hT.1, hT.2.1, fun R => ?_⟩
  exact (hT.2.2.2.2 R).imp fun εr h => h.imp fun δ h => h.imp fun Λz ht =>
    eventually_atTop.mpr ⟨R.later.tail, fun m hm => (ht m hm).imp fun M hM =>
      ⟨hM.1, fun x₀ => (hM.2 x₀).imp fun S hS => ⟨hS, S.fc33_row_BAS⟩⟩⟩

end DifferentialGeometry.Geometry.Collapse
