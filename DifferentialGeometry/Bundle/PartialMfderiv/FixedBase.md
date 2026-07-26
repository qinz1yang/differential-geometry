# FixedBase

2026-06-17 HCG/P4 bridge note: added
`extDerivFun_comp_diffeomorph`, the scalar directional-derivative chain rule
through a diffeomorphism.  This is the reusable leading-term producer needed
for the all-orders `metricCovDeriv` pullback induction.

Verification passed for this file.

## Joint-smooth constructor

`fixedBaseOnRegSmooth` removes both separate spatial-differentiability
hypotheses from `fixedBaseOnRegLocal`. It works first on the open regular-time
set, where joint `C²` regularity controls both spatial slices and the actual
time partial, then transports the resulting ordinary derivative back to the
requested time carrier. The uniform time-derivative identity identifies the
supplied derivative with that partial on the open spatial domain.

Focused verification passed.
