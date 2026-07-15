# StepBApproxIso.lean — B-Falpha (`lbl399`) `C⁰` core + `C^∞` upgrade

## Status: `lbl399` `C⁰` core COMPLETE; `C^∞` two-parameter upgrade COMPLETE

**Verification PASSED** for the focused file checks.  The new `C^∞` endpoint is
`comp_cInf_id_on`.

## Delivered (`lbl399`, `C⁰` core)
- `comp_tendsto_id_on` — two-parameter composition converges to the identity, **order-0
  (uniform on compacts)**. From `B_k → B∞` and `A_ℓ → A∞` in `C^∞`-on-compacts (the
  `isometry_seq_diffeo_on`/B-trans outputs) and the limit identity `A∞ (B∞ x) = x`, the
  family `A_ℓ ∘ B_k → id` uniformly on each compact `K ⊆ U` (with `B∞ '' K ⊆ V`) as
  `k, ℓ → ∞` independently: `∀ ε>0, ∃ N, ∀ k,ℓ ≥ N, ∀ x∈K, dist (A_ℓ (B_k x)) x < ε`.
  Proof: corral the moving point `B_k x` into the fixed compact `cthickening δ₀ (B∞''K)
  ⊆ V` (`exists_cthickening_subset_open`), Heine–Cantor uniform continuity of `A∞` there,
  and uniform convergence of `A_ℓ`; triangle split `A_ℓ(B_k x) − A∞(B_k x)` +
  `A∞(B_k x) − A∞(B∞ x)`. Inverse identity consumed conditionally on `B∞ x ∈ V` (`hKV`),
  matching `isometry_seq_diffeo_on`.

For the book's `F_{kℓ,β}^α = J̄_ℓ^{αβ} ∘ J_k^{βα}`: `B := J^{βα}`, `A := J̄^{αβ}`, the
limit cocycle `A∞ ∘ B∞ = id` is `exists_transitionLimit_on`'s output.

## Delivered (`lbl399`, `C^∞` upgrade)

- `comp_cInf_id_on` — two-parameter `C^∞` convergence to the identity.  For every
  compact `K ⊆ U`, finite order `p`, and `ε > 0`, there is one threshold `N` such
  that for all `k,l ≥ N`, all `r ≤ p`, and all `x ∈ K`,
  `mapDerivNorm r (A_l ∘ B_k) id x ≤ ε`.
- Proof route: use `MapConvergenceComp.lean`'s same-index
  `MapCInfConvOnCompacts.comp`, then prove the two-parameter tail by
  contradiction.  A bad tail would choose `k_N,l_N ≥ N`; the reindexing lemmas
  turn `A_{l_N}` and `B_{k_N}` back into valid convergent sequences, contradicting
  same-index composition convergence.

## Remaining Frontier

`lbl404` is still not attempted here.  The composition-convergence analysis
needed by `lbl399` is now available, but the pullback/source-domain layer still
needs its own product and domain bookkeeping for the metric pullback expression.
