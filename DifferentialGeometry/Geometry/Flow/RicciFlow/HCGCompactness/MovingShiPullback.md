# MovingShiPullback

P1.3 of the HCG g_∞ assembly (MSM135 Thm 3.10 ⇐ 3.9): the **Shi-bound pullback transfer**
`MovingShiBoundOn g → MovingShiBoundOn (Φ^* g)` for a non-endo diffeomorphism `Φ : M ≃ₘ N`.

## Status (2026-06-30): DONE end-to-end (focus-checked clean)

Lemmas, in order:
- `covDerivOfField_apply_eq_iterCov` — evaluated form of `covDerivOfField_eq_iterCov`:
  `covDerivOfField gRef A0 m x slots = iterCov gRef 2 A0 m x (slots ∘ acEquiv m)`.
- `ricCovTower_pullback` — `ricCovTower (Φ^*g)(Φ^*g) s x slots = ricCovTower g g s (Φx)(dΦ slots)`.
- `ricCovTower_normSq0S_pullback` — `normSq0S (Φ^*g) x (ricCovTower..) = normSq0S g (Φx)(ricCovTower..)`.
- `movingShiBoundOn_pullback` — the endpoint: transfers `MovingShiBoundOn` from `gSeq` on `U⊆N` to
  `i t ↦ Φ^*(gSeq i t)` on `V⊆M` with `Φ '' V ⊆ U`.

Depends on the Ricci-naturality chain proven in `MetricCovDerivPullback.lean`
(`covDerivOfField_pullback`, `ricciTensor_pullback`, `ricciSection_pullback`,
`metricRm04StdAt_eq_inner_riemannOp`, `ricciSection_eq_ricciTensor`) — see that note for how the
apparent "Ricci-naturality-at-M≃N wall" dissolved (trace route via `metricRm04Std_pullback`).

## Lessons / gotchas

- **`domDomCongr_apply` is `rfl` but `rw` won't match it** (coercion); `rfl` closes by defeq. So
  `covDerivOfField_apply_eq_iterCov` is `rw [covDerivOfField_eq_iterCov]; rfl`, NOT a chain of
  `rw [MultilinearSection.domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply]` (those
  `rw`s fail "did not find pattern" even though NablaTraceGen uses them on a *bare* goal — the
  difference is rw-at-hypothesis / surrounding application context).
- **Route B beats Route A** for the norm transfer: do it at the `ricCovTower` (iterCov) level with
  `normSq0S_pullback_eval_of_orthonormal` (needs ONLY an orthonormal basis, `exists_gOrthonormalBasis`),
  NOT at the `covDerivOfField` level (which would need `normSq0S_iterCov_domDomCongr` +
  `MetricInverseInBasis_gen`). Pushing the `acEquiv` reindex into `ricCovTower_pullback` (a tensor-eval
  lemma) is cleaner than into the norm.
- The `(slots ∘ (acEquiv s).symm) ∘ acEquiv s = slots` reindex closes by
  `funext i; simp [Function.comp, Equiv.symm_apply_apply]`.
- New file (downstream of both `RicBound` and `MetricCovDerivPullback`) because `RicBound` (has
  `ricCovTower`/`MovingShiBoundOn`) does not import `MetricCovDerivPullback`, and the latter is upstream.
- Build note: a full `lake build` hit pre-existing corrupt upstream oleans (`invalid header`,
  Windows `exited with code 3221225477`), unrelated to this file; the focused `lake env lean` is clean.

## Remaining (P1.4, not here)

Feed `movingShiBoundOn_pullback` into the `SolWindowData`/`winGInfOfData` builder for the conv field
(`FlowLimitUpgrade.lean`). That is pullback bookkeeping; the analytic content (Shi transfer) is done.
