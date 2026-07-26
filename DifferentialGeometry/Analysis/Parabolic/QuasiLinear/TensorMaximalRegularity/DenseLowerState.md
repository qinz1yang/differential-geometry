# DenseLowerState

## 2026-07-19

This file is focused-check green, warning-free, and its named `.olean` has
been refreshed.  `dense_lowerCore` proves that a dense ambient core stays
dense after restriction to a positive closed ball measured by a continuous
lower-order map.

The boundary case is handled by first moving the target point radially into
the strict lower ball and only then applying ambient density.  Thus the proof
does not rely on the false unrestricted claim that intersecting an arbitrary
dense set with a closed set preserves density.

Endpoint accounting: this is verified dense-core machinery only.  Neither
exact analytic endpoint theorem is yet proved.
