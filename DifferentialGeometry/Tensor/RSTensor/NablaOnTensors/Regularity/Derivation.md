# Mixed-tensor derivation verification frontier

## Resolved (2026-07-10)

The `nablaRSFun_eval_moving_raw` performance wall is closed.  The reusable
producer `TensorLieDeriv.modelAt_mcovRS` now projects
`mcovariantDeriv_tensorRSWithin` through the fixed-chart mixed-tensor
trivialization using `tensorRSModelAt_trivializationAt_symm`.

`nablaRSFun_eval_moving_raw` consumes that producer through
`tensorRSModelInChart_apply_modelSlots_center`; it no longer constructs and
normalizes a raw Hom-bundle trivialization equality inside the theorem.
Focused source verification passed within the normal heartbeat budget.  The
next consumer-side action is the rank-zero scalar connection-Laplacian bridge.

The consumer proof now also restricts its final normalization to the named
model alias and the two set simplifications needed after `modelAt_mcovRS`;
focused verification still passes.  No whole-Hom equality or broad simp search
remains in that bridge.

The model-projection producer and this derivation theorem are now checked.
This removes a tooling/API gate but does not itself advance a Hamilton
compactness endpoint: whole HCG machinery remains about 45%, and the
compactness endpoint theorems remain 0%.

## Historical blocker (2026-07-09)

An intermediate repair imported `Tensor.Mixed.Bundle` directly while the
failure was being isolated.  The file did not use declarations from that
module, and the import introduced a second generic Hom-bundle instance path;
it was removed after the model-projection repair, with focused verification
still passing.

That import repair removes all unknown mixed-bundle declarations, but current
source verification still fails in `nablaRSFun_eval_moving_raw`.  The exact
frontier is a deterministic `whnf` heartbeat timeout in the Hom-bundle model
identity.  The smallest isolated producer attempted was `nablaRS_model_eq`:
it had no beta, moving-frame, or evaluation arguments, yet its command itself
still reached the default heartbeat ceiling.  The later unknown
`nablaRSFun_eval_moving_raw` error was only a cascade from this failure.

Failed genuinely different routes:

1. A theorem-local heartbeat budget of 800000 still timed out in the original
   `hleft_model` block.
2. Extracting the entire fiber/model evaluation block as
   `nablaRS_model_eval` still timed out in that helper; this attempt was
   reverted.
3. Extracting only the no-evaluation equality `nablaRS_model_eq` still times
   out at `whnf`; this final failed extraction was also reverted.

The failed budget change and both helper extractions were reverted.  The
producer-level repair below subsequently closed the source check and restored
the `Derivation` object file.

## Repair identified

The missing cheaper producer was `TensorLieDeriv.modelAt_mcovRS` in
`RawDefs/MCovariant.lean`.  It reuses the fixed-chart model round-trip theorem
instead of unfolding the Hom implementation.  The producer was checked
independently before being consumed here.

## Project position

- mixed model-projection producer: 100% checked;
- `nablaRSFun_eval_moving_raw`: source proof and focused verification complete;
- rank-zero smooth-field embedding infrastructure: 100% checked;
- scalar connection-Laplacian bridge: theorem completion 0%, with dedicated
  rank-zero machinery roughly 35%;
- Perelman no-local-collapsing and `ham3_noncollapse`: theorem completion 0%;
- whole HCG compactness machinery remains roughly 45%, with endpoint theorems
  still 0%.
