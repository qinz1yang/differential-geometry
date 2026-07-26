# MetricDerivNormFlat

## 2026-07-10

This module is the composition layer between ordinary open-subtype locality
and diffeomorphism pullback naturality.  It keeps
`MetricDerivNormRestrict.lean` at its original weak `NormedSpace` interface and
opens a separate `InnerProductSpace` context before constructing the model with
corners, matching the assumptions of `MetricCovDerivPullback.lean` without an
instance-order mismatch.

`metricDerivNorm_flat` identifies the pointwise derivative norm of three
metrics flatly restricted from `U` to an ambient open `V ≤ U` with the original
derivative norm at the inclusion point.  The proof realizes `V` as the nested
open subset of `U`, constructs the identity diffeomorphism between the flat and
nested carriers, identifies the three restricted metrics as pullbacks, and
then composes `metricDerivNorm_pullback` with
`metricDerivNorm_restrictOpen`.

Focused source verification passed without warnings and without a raised
heartbeat budget.  The explicitly named module refresh also passed after the
upstream `Derivation` artifact was restored.  No new `sorry` was introduced.

Project position: this pointwise D6 restriction bridge is complete and is now
consumed by `tailFlatSup_lt`.  That compact-supremum producer in turn feeds the
checked `tailAmbientConv`, so ambient convergence and `tailLimitComplete` use
the same shrunk direct-limit metric.  The final D6 theorem remains unstated and
unproved (0%); dedicated D6 wiring is about 30%, and whole Step-D machinery is
about 97%.

## 2026-07-19

`restrictSubset_pull` now exports the metric-level identity already used
internally by `metricDerivNorm_flat`: flat restriction from an ambient open
`U` to `V ≤ U` is the pullback of ordinary restriction to the corresponding
nested open subtype.  This is the lowest reusable bridge needed to transport
finite-head covariant metric bounds in the concrete Step-D provenance proof;
the higher proof can combine it with the existing pullback and open-restriction
norm theorems without duplicating the flat-carrier construction.

Focused source verification and the explicitly named exact module refresh both
passed without local warnings.

Project accounting after the downstream closure: this helper is complete
(100%), `HasCanonBounds` is proved (100%), and the concrete Step-D provenance
lane plus conditional metric-compactness endpoint are 100% checked.  The
selected conditional Chapter-4 route is complete; the separately named
textbook B1 theorem and unconditional Theorem 3.9 remain 0%.  Whole-HCG
machinery remains approximately 60%, and the unconditional solution/Hamilton
endpoints remain theorem-level 0%.
