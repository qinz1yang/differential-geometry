# CGTInjectivity

## P1b local-curvature producer

- `intrInj_ge_cgt_on` keeps the established CGT injectivity-radius conclusion
  and all scale, local-diffeomorphism, and positivity assumptions of
  `intrInj_ge_cgt`, but assumes the curvature bound only at
  `intrinsicFramedExp g hEnorm p z` for `‖z‖ < 3 * R / 4`.
- This is exactly the curvature input consumed by `CGT.intrFiber_count_core`.
  The long flat-loop and collision arguments are shared through private
  `flatLoop_ge_cgt_on` and `collision_ge_cgt_on` producers.
- The existing public `flatLoop_ge_cgt`, `collision_ge_cgt`, and
  `intrInj_ge_cgt` declarations retain their global `Rm04GlobalBound`
  interfaces and now specialize the local producers. Existing P0 consumers do
  not need to change.

## Verification

- Static source and diff review completed. Focused verification passed without
  warnings, and the named module refresh completed successfully (4061/4061).
- No proof-route failure remains in this module. A downstream axiom audit is
  tracked separately from the source verification.

## Program status

- P1b E1 endpoint remains 0% until the frozen downstream endpoint is checked.
- Dedicated P1b machinery is about 92%. The whole P0–P9 infrastructure remains
  at the authoritative 15–25%; this producer does not itself close a
  Morgan–Tian endpoint.
