import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRowsB
import DifferentialGeometry.Geometry.Fibration.ActualStageChainBasesKernel

/-!
# The kernel identification on the closed rows' source, on the final family

Lane S-BASES-KER, group G9 (closed binding). `ClosedBases74 S = Gaf02Bases S.chain.toChain
S.chain.rough` carries the kernel identification `Gaf02Bases.ker_final_eq_BAS`
(`Fibration/ActualStageChainBasesKernel`): on the restricted carrier `D_st = B⁶_st ∩ f_st⁻¹(V_st⁰)`
the kernels of `D(π_st E)` and of `D f_st` coincide, in particular on FC33's `U_st ⊆ D_st`.

* `ClosedChainEZRowsSource_RGC.ker_final_BAS`: the statement at the source's own `bases74`;
* `eventually_ker_final_rowsSourceZ_BAS`: consumer on the final closed family `C14Z` at register
  V4's strategy: for every register, every tail member (`∀ᶠ m`, a nonempty model), every base
  point, a rows source with that base point on which the identification holds at every
  carrier point and `U_st ⊆ D_st`.
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

/-- **The kernel identification on the rows source** (at its own `bases74`): on `D_st`,
`ker D(π_st E)(p) = ker D f_st(p)`. -/
theorem ker_final_BAS (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (st : Fin 3) (p : M.X)
    (hp : p ∈ S.chain.toChain.carrier_BAS st) :
    type_of% (S.bases74.ker_final_eq_BAS st hp) :=
  S.bases74.ker_final_eq_BAS st hp

end ClosedChainEZRowsSource_RGC

/-- **Consumer: the kernel identification on the final family** (register V4's strategy, tail
form `∀ᶠ`): for every register, on every tail member (a nonempty model), for every base point, a
rows source with that base point on which the kernels of `D(π_st E)` and `D f_st` agree at every
point of the carrier `D_st`, and FC33's `U_st ⊆ D_st`. -/
theorem eventually_ker_final_rowsSourceZ_BAS (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
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
            (∀ st, gafStageDomain5_BAS S.F.family.toLocalChartPacketsC14.toLocalChartPackets st ⊆
              S.chain.toChain.carrier_BAS st) ∧
            ∀ (st : Fin 3) (p : M.X) (hp : p ∈ S.chain.toChain.carrier_BAS st),
              type_of% (S.ker_final_BAS st p hp) := by
  have key := exists_closedChainEZRowsSource_RGC K hK A hA Wseq gseq hf hg
  refine key.imp fun T hT => ⟨hT.1, hT.2.1, fun R => ?_⟩
  exact (hT.2.2.2.2 R).imp fun εr h => h.imp fun δ h => h.imp fun Λz ht =>
    eventually_atTop.mpr ⟨R.later.tail, fun m hm => (ht m hm).imp fun M hM =>
      ⟨hM.1, fun x₀ => (hM.2 x₀).imp fun S hS =>
        ⟨hS, fun st => S.chain.toChain.domain5_subset_carrier_BAS st,
          fun st p hp => S.ker_final_BAS st p hp⟩⟩⟩

end DifferentialGeometry.Geometry.Collapse
