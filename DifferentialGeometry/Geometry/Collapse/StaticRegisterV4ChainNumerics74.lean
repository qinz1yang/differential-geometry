import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainExitsOfRows74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainCutChoiceRegister74

/-!
# D74-18: the record `N = ClosedRowsNumericsAt74 S` is produced by the register, clause by clause

Lane S-REG-NUM (`_RNUM`), G1. Draft 74 §6.2–6.3 / D74-18: `S` does not carry the numerics and
strategy equalities of the actual calls (`edge_height_RGC` takes `hT`, `hNb`, `hcw`
explicitly; the cut-choice producer takes `ε_r < 1/2`, `σ_c ≤ 1/2`, `0 ≤ γ ≤ 3/4`; ZSP02 / FDC
take `e ≤ 1/1000`). They are NOT projections of `S`, but every one of them is a register or
strategy value read BEFORE the member (D74-18's order: one early choice → one strategy → `R` →
the same FAMZ parameters → the current member), so no number is claimed after the fact and no
quantifier is changed.

## Audit table: clause → choice node → supplier

* `eps_lt : εr < 1/2`. Node: FAMZ's own `ε_r` (register V4: `ε_r < min(1/4, ε₀)`, the producer's
  OUTPUT before the family; `εr` is a parameter of `S`, never shrunk afterwards). Supplier:
  `exists_closed_realization_C14Z_RGC` (clause `hεr14`), re-exported by
  `register_yields_cutChoice_R74`.
* `qe_le : q_e ≤ 1/2`. Node: PR14 slot `qe_lt`, `q_e < θ_e²/10⁸` with `θ_e < 1/100` (a field of
  every register). Supplier: `ClosedLaterV4.qe_le_half_R74`.
* `gamma_nonneg`, `gamma_le : 0 ≤ γ ≤ 3/4`. Node: PR11 slot `γ_lt` below the Gram cap
  (`withGram_V4C`: `γ < 1/100`). Supplier: `ClosedRegisterV4.gram_request_of_below_V4C`, from
  `ClosedStrategyBelowV4.complete_caps_V4C`.
* `e_le : e₀ ≤ 1/1000`. Node: PR14–PR17 slot `e₀_lt : e₀ < min(1/1000, errorsUp)` (the (ZB)
  tolerance of ZSP02, `C14Requests.e_le`). Supplier: `ClosedLaterV4.e₀_lt`.
* `strategy_below`. Node: the strategy `T` refines `closedStrategyCompleteV4C` (the realization's
  `T`). Supplier: `ClosedStrategyRefinesV4.below_VAL6`.
* `nb_eq`, `cw_eq`. Node: PR10 slots `N_b`, `c_w` are the maxima `maxNb_V4C`, `maxCw_V4C` already
  in the complete strategy. Supplier: `ClosedStrategyRefinesV4.Nb_eq`, `cw_eq`, re-exported by
  `register_yields_cutChoice_R74`.

No clause is out of order: the only quantity not fixed before `S` is `εr`, and it is a PARAMETER of
`S` fixed by FAMZ before the family and the chain.

* `closedRowsNumerics_of_register_RNUM`: for EVERY source `S` whose parameter `εr < 1/2` at a
  register of a strategy below `closedStrategyCompleteV4C` with the two PR10 equalities, the record
  `N` (strengthening: the record is needed for every source, not for one).
* **`register_yields_numerics_RNUM`**: the register theorem: one strategy `T`, and on every member
  of every register's tail, for every base point, a source `S` with `N` (same strategy, same
  `ε_r`, same member as `register_yields_cutChoice_R74`).
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

/-- **`N` at a register** (D74-18): for every source `S` with parameter `ε_r < 1/2`, at a register
of a strategy below the complete one with the two PR10 equalities, the numerics and strategy
equalities of the actual calls hold; each clause is read from the register (module header table). -/
theorem closedRowsNumerics_of_register_RNUM {K : ℕ}
    {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
    (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C) (hεr : εr < 1 / 2)
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) : ClosedRowsNumericsAt74 S := by
  obtain ⟨-, -, hgram, -⟩ := hT.complete_caps_V4C
  obtain ⟨hγ0, hγ1, -⟩ := R.gram_request_of_below_V4C hgram
  exact ⟨hεr, R.later.qe_le_half_R74, hγ0.le, by linarith,
    (R.later.e₀_lt.trans_le (min_le_left _ _)).le, hT, hNb, hcw⟩

/-- **The register yields `N` on every member** (D74-18's order, same strategy / `ε_r` / member as
`register_yields_cutChoice_R74`): one strategy `T` refining the complete strategy with the PR10
equalities and, at every register, FAMZ's `ε_r < 1/4`, `δ`, `Λz`; on every tail member, for every
base point, a source `S` with that base point carrying `N`. -/
theorem register_yields_numerics_RNUM (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      ClosedStrategyRefinesV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)) ∧
      T.Nb = maxNb_V4C ∧ T.cw = maxCw_V4C ∧
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T, ∃ εr δ Λz : ℝ, 0 < εr ∧ εr < 1 / 4 ∧
        ∀ m, R.later.tail ≤ m → ∃ M : ClosedModel (Wseq m) (gseq m), Nonempty M.X ∧
          ∀ x₀ : M.X, ∃ S : ClosedChainEZRowsSource_RGC K R M δ εr Λz, S.chain.x₀ = x₀ ∧
            Nonempty (ClosedRowsNumericsAt74 S) := by
  obtain ⟨T, hTU, hNb, hcw, h⟩ := register_yields_cutChoice_R74 K hK A hA Wseq gseq hf hg
  refine ⟨T, hTU, hNb, hcw, fun R => ?_⟩
  obtain ⟨εr, δ, Λz, hεr0, hεr14, hm⟩ := h R
  refine ⟨εr, δ, Λz, hεr0, hεr14, fun m hmt => ?_⟩
  obtain ⟨M, hne, hx⟩ := hm m hmt
  refine ⟨M, hne, fun x₀ => ?_⟩
  obtain ⟨S, hS, -⟩ := hx x₀
  exact ⟨S, hS, ⟨closedRowsNumerics_of_register_RNUM hTU.below_VAL6 hNb hcw (by linarith) S⟩⟩

end DifferentialGeometry.Geometry.Collapse
