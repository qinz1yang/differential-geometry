# Fixed-slice reduced-volume floor

`SliceVolumeLow.lean` is the narrow consumer of the fixed-slice splice bound.
It does not produce a minimizing ray and does not state the late-time endpoint.

## Result

- `redVolume_slice_low` takes exactly the concrete minimizing-ray and
  low-reduced-length data consumed by `redLen_slice_bound`.
- The slice theorem supplies one measurable target set, a fixed positive
  Riemannian-volume floor at time `a0`, and a terminal-time-independent
  reduced-length bound.
- The proof bounds the remaining reduced-density normalization uniformly using
  `T - a0 < omega - a0`, then applies `redVolume_set_low`.

## Verification

Source is written without `sorry`, `admit`, or a new axiom. The first focused
verification hit a deterministic heartbeat timeout in a broad `convert`/`ring`
step for the metric time. Replacing that step by the separate scalar equality
`T - (T - a0) = a0` and a targeted rewrite made the second focused verification
pass without warnings. The named module artifact was refreshed successfully;
its replayed warnings came only from unrelated upstream modules.

## Scope and progress

The checked theorem is only the conditional fixed-slice reduced-volume consumer. The
all-point spacetime weak barrier, `exists_redLen_le`, `redVolume_late_low`, and
`smooth_nlc` remain 0% as theorem endpoints. Subject to focused verification,
the dedicated late-time-floor machinery is roughly 55--60% complete; reused
generic infrastructure remains tracked separately.
