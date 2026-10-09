import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainNumerics74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRowsE

/-!
# Consumers of `N = ClosedRowsNumericsAt74 S`

Lane S-REG-NUM (`_RNUM`), G1. The record `N` produced by `register_yields_numerics_RNUM` feeds the
two calls it was designed for, with no further numeric hypothesis:

* `edge_height_of_numerics_RNUM`: EDP-E's height tolerance `h_* < 1/1000` of `edge_height_RGC`
  (its premises `hT`, `hNb`, `hcw` are fields of `N`);
* `closedCutChoice_of_numerics_RNUM`: a cut choice on `(S, B)` (the premises `ε_r < 1/2`,
  `σ_c ≤ 1/2`, `0 ≤ γ ≤ 3/4` of `exists_closedCutChoice74` are fields of `N`);
* `exists_closedChainEZRowsSource_numerics_RNUM`: on every closed standing sequence, a strategy and
  on every tail member and base point a source with `N` AND a cut choice on its own bases object.
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

/-- **Consumer 1** (`edge_height_RGC`'s premises are the fields `strategy_below`, `nb_eq`,
`cw_eq` of `N`): the height tolerance of EDP-E's (EH) is below `1/1000` at every edge centre. -/
theorem edge_height_of_numerics_RNUM {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    {S : ClosedChainEZRowsSource_RGC K R M δ εr Λz} (N : ClosedRowsNumericsAt74 S) {j : M.X}
    (hj : j ∈ S.toE_RGC.F.family.edge.centres) : R.heightTol_RGC < 1 / 1000 :=
  (ClosedChainERowsSource_RGC.edge_height_RGC N.strategy_below N.nb_eq N.cw_eq S.toE_RGC hj).1

/-- **Consumer 2** (`exists_closedCutChoice74`'s numeric premises are fields of `N`): a cut choice
on `(S, B)`. -/
theorem closedCutChoice_of_numerics_RNUM {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    {S : ClosedChainEZRowsSource_RGC K R M δ εr Λz} (B : ClosedBases74 S)
    (N : ClosedRowsNumericsAt74 S) : Nonempty (ClosedCutChoice74 S B) := by
  obtain ⟨D, -⟩ := exists_closedCutChoice74 S B N.eps_lt N.qe_le N.gamma_nonneg N.gamma_le
  exact ⟨D⟩

/-- **Consumer 3 (nonempty production path)**: on every closed standing sequence, a strategy `T`
and on every tail member and base point a source `S` carrying `N` and, on its own bases object, a
cut choice produced from `N` alone. -/
theorem exists_closedChainEZRowsSource_numerics_RNUM (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      ClosedStrategyRefinesV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)) ∧
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T, ∃ εr δ Λz : ℝ, ∀ m, R.later.tail ≤ m →
        ∃ M : ClosedModel (Wseq m) (gseq m), Nonempty M.X ∧ ∀ x₀ : M.X,
          ∃ S : ClosedChainEZRowsSource_RGC K R M δ εr Λz, S.chain.x₀ = x₀ ∧
            Nonempty (ClosedRowsNumericsAt74 S) ∧ Nonempty (ClosedCutChoice74 S S.bases74) := by
  obtain ⟨T, hTU, -, -, h⟩ := register_yields_numerics_RNUM K hK A hA Wseq gseq hf hg
  refine ⟨T, hTU, fun R => ?_⟩
  obtain ⟨εr, δ, Λz, -, -, hm⟩ := h R
  refine ⟨εr, δ, Λz, fun m hmt => ?_⟩
  obtain ⟨M, hne, hx⟩ := hm m hmt
  refine ⟨M, hne, fun x₀ => ?_⟩
  obtain ⟨S, hS, ⟨N⟩⟩ := hx x₀
  exact ⟨S, hS, ⟨N⟩, closedCutChoice_of_numerics_RNUM S.bases74 N⟩

end DifferentialGeometry.Geometry.Collapse
