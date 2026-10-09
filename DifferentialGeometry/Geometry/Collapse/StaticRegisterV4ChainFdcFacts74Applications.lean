import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainFdcFacts74

/-!
# Consumers of `Htail = ClosedFdcMemberFacts74 S B` produced by the register

Lane S-REG-NUM (`_RNUM`), G2. The records `N` and `Htail` of `register_yields_fdcFacts_RNUM` feed
the cut-choice producer and the FDC04 facts at the SAME cut choice:

* `closedCutChoice_with_fdcFacts_RNUM`: from `N` and `Htail`, a cut choice (the output of
  `exists_closedCutChoice74` with all its properties) AND the FDC04 facts at it;
* `closedFdcFacts_M₂_compact_RNUM`: the compact remainder `M₂ = M^edge ∪ M₃` from the facts;
* `exists_closedChainEZRowsSource_fdcFacts_RNUM` (nonempty production path): on every member
  `m ≥ n` of every register's tail, for every base point, a source `S` with `N` and, on its own
  bases object, a cut choice with the FDC04 facts at it.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **Consumer 1**: `N` gives the cut choice (with its producer properties), `Htail` the FDC04 facts
at it. -/
theorem closedCutChoice_with_fdcFacts_RNUM {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    {S : ClosedChainEZRowsSource_RGC K R M δ εr Λz} (B : ClosedBases74 S)
    (N : ClosedRowsNumericsAt74 S) (H : ClosedFdcMemberFacts74 S B) :
    ∃ D : ClosedCutChoice74 S B,
      D.slimSet = (interior S.chain.zeroUnion_ZSP35)ᶜ ∩
        S.chain.slimMap_ZSP35 ⁻¹' D.K₃.carrier ∧
      IsCompact D.slimSet ∧ S.chain.zeroUnion_ZSP35 ∪ D.slimSet ∪ D.M₂ = univ ∧
      ClosedFdcFacts74 D := by
  obtain ⟨D, h1, h2, h3, -⟩ := exists_closedCutChoice74 S B N.eps_lt N.qe_le N.gamma_nonneg
    N.gamma_le
  exact ⟨D, h1, h2, h3, H.facts D⟩

/-- **Consumer 2**: the remainder `M₂` of a cut choice with the FDC04 facts is compact. -/
theorem closedFdcFacts_M₂_compact_RNUM {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    {S : ClosedChainEZRowsSource_RGC K R M δ εr Λz} {B : ClosedBases74 S}
    {D : ClosedCutChoice74 S B} (H : ClosedFdcFacts74 D) : IsCompact D.M₂ := by
  rw [H.M₂_eq]
  exact H.edge_compact.union H.remainder_compact

/-- **Consumer 3 (nonempty production path)**: on every member `m ≥ n` of every register's tail,
for every base point, a source `S` with `N` and, on its own bases object, a cut choice with the
FDC04 facts at it (compact edge piece and remainder, the four-piece cover, disjoint interiors). -/
theorem exists_closedChainEZRowsSource_fdcFacts_RNUM (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      ClosedStrategyRefinesV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)) ∧
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T, ∃ εr δ Λz : ℝ, ∃ n : ℕ, ∀ m, n ≤ m →
        ∃ M : ClosedModel (Wseq m) (gseq m), Nonempty M.X ∧ ∀ x₀ : M.X,
          ∃ S : ClosedChainEZRowsSource_RGC K R M δ εr Λz, S.chain.x₀ = x₀ ∧
            ∃ D : ClosedCutChoice74 S S.bases74, ClosedFdcFacts74 D := by
  obtain ⟨T, hTU, -, -, h⟩ := register_yields_fdcFacts_RNUM K hK A hA Wseq gseq hf hg
  refine ⟨T, hTU, fun R => ?_⟩
  obtain ⟨εr, δ, Λz, -, -, n, hn⟩ := h R
  refine ⟨εr, δ, Λz, n, fun m hm => ?_⟩
  obtain ⟨M, hne, hx⟩ := hn m hm
  refine ⟨M, hne, fun x₀ => ?_⟩
  obtain ⟨S, hS, ⟨N⟩, hH⟩ := hx x₀
  obtain ⟨D, -, -, -, hD⟩ := closedCutChoice_with_fdcFacts_RNUM S.bases74 N (hH S.bases74)
  exact ⟨S, hS, D, hD⟩

end DifferentialGeometry.Geometry.Collapse
