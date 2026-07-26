# Retag

## 2026-07-10

`SmoothCcTensor g r s` stores no metric-dependent data: its section and
compact-support witness are independent of the phantom metric parameter.  The
new `SmoothCcTensor.retagEquiv` is therefore the canonical real-linear
equivalence between two metric tags, and `retag_toSection` records its scalar
consumer normal form.

Focused verification passed without warnings.  No metric comparison,
regularity, compactness, or convergence assumption is used.
