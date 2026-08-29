# RedLengthFence

## Role

This module proves Perelman's half-dimension reduced-length fence on a complete
bounded-curvature backward slab.

## Checked endpoint

`exists_redLen_le` states that for every positive interior backward time there
is an endpoint `y` with

```text
redLength S T x y tau <= finrank Real E / 2.
```

The proof first obtains a smaller-time seed from a minimizing ray. It applies
continuity of `redMinVal` and the generic right-upper-support fencing lemma. If
the minimum crossed above half the dimension, `exists_redWeak_sup` supplies a
genuine spacetime support. At the support endpoint the spatial slice has a
local minimum, so the metric-compatible Laplacian is nonnegative; the weak
barrier inequality then forces a strictly negative right derivative, exactly
the contradiction required by the fence.

No compactness assumption, support wrapper, desired differential inequality,
new axiom, `sorry`, or `admit` is introduced.

## Verification and position

Focused verification is warning-free green, and the named module artifact is
refreshed. `exists_redLen_le` and its dedicated fencing assembly are 100%.
It is consumed by `LateVolumeLow.redVolume_late_low`.
