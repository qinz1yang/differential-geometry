# NablaTraceGen — notes

## 2026-07-12 — short-time branch alignment

- The five merge-compatibility failures now use the public opaque-fiber APIs:
  `Tensor0SSpace.add_apply`, `smul_apply`, and `domDomCongr_apply`, with explicit
  fiber-level `change` steps around section products and slot reindexing.
- Focused verification passed without `sorry`; the local compatibility repair is
  complete (100%) and has no remaining blocker.
- This is consumer compatibility only: it does not add mathematical content to the
  short-time existence theorem. The headline short-time theorem remains complete
  (100%); its current branch-alignment integration is about 95% pending the rerun of
  the large downstream targets.

Rank-`s` metric-trace fields and their algebra/`∇`-commutation (generalisations of `Trace04` /
`NablaTrace02`): `freezeTailField`, `metricTraceFirstTwoField`, `metricTraceFirstTwoField_eq_sum`,
`_add`/`_smul`/`_zero`/`_domDomCongr_gen`/`_product`, `nablaRealizes_metricTraceFirstTwo`.

## 2026-06-14 — component-eval transparency sweep (item 4): 9 → 8 blocks

**Block removed (component-eval, was STALE):** `metricTraceFirstTwoField_eq_sum` — the pointwise coordinate
formula. Its proof is a pure pointwise `rw`-chain (`metricTraceFirstTwoField_apply`,
`metricTraceFirstTwo0STensor_apply`, `metricTraceFirstTwo0SAt_eq_sum_basis`) with **no**
`letI tensor0SBundle_topology`, **no** `DFunLike.ext`, **no** `ContMDiffAt`. The `respectTransparency false`
was unnecessary — the `_apply`/`_eq_sum_basis` lemmas match without it. Focused-check **green**.

**Blocks kept (bundle-section, load-bearing) — 8:** the `…Field` smooth-section defs (`freezeTailField`,
`metricTraceFirstTwoField`) and the field-level algebra identities `_add`, `_smul`, `_zero`,
`_domDomCongr_gen`, `_product`, plus `nablaRealizes_metricTraceFirstTwo`. Empirically removing the 5 algebra
hacks gave **`synthInstanceFailed` at the `Tensor0SField` statement-level type-class binders** (e.g. 651/676/842)
+ `rewrite failed` once `tensor0SBundle_topology` is no longer pinned. This is exactly the file's own NOTE
(near `metricTraceFirstTwoField_zero`): the bundle topology / `Zero`/`Add` instance is only pinned once a
concrete-rank function fixes it. These belong to the bundle/model-topology workstream, not component-eval.

**Triage signal (finer than per-file):** within one file, component-eval and bundle-section blocks coexist.
Discriminate **per theorem by proof shape** — a pointwise `rw`-chain through `_apply`/`_eq_sum`/component
lemmas (no `letI …bundle_topology`, no `DFunLike.ext`/section ext, no `ContMDiffAt`) is component-eval and the
hack is often stale; a statement binding smooth `…Field`/sections whose proof needs `letI tensor0SBundle_topology`
+ `DFunLike.ext` is bundle-section (`synthInstanceFailed` at the field binders) → keep. See
`Tensor/RSTensor/ComponentEvalApiPlan.md`.
