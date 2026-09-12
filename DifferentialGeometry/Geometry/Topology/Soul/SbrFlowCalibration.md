# SbrFlowCalibration.lean

Verified 2026-09-08 in the dev checkout. Actual normalized right velocity implies exact level increments by the right chain rule and Dini comparisons for F and minus F. Submaximum data derive nonvanishing; uniqueness now derives equal levels from the equation and common initial point.

Empty focused output: 19.8s. Lint-clean named build: 24.2s.
Fresh external public axiom audit: 17.8s; all 3 explicit public declarations use only standard axioms (or none).
Evidence: E:/lean-tools/soul-audits-20260907/SbrFlowCalibration-result3.json and its three logs.
The source-preparation record below is historical; its pending-check status is superseded by this verification. Actual claims and integration state remain in the shared status and wrapper records.

## Source-preparation record

2026-09-08 parent continuation. Claim
`42eabad3-d630-4655-821c-89b2496f6132` retained. SOURCE-WRITTEN / UNVERIFIED.

The book census identified lem:sbr-flow-calibration as a separate result:
the existing Euler producer returns calibrated curves, but the book also
derives calibration for an arbitrary normalized ascent curve. The source
here uses the actual right-tangent chain rule, positive homogeneity of the
intrinsic directional derivative, and gradient calibration to show that
the real right derivative of F along the curve is one. Applying the
existing Dini affine comparison to F and -F proves the exact increment,
including the endpoint by continuity.

The nonzero-gradient version is reusable directly with produced curves.
The book version derives nonvanishing from an attained larger value and
the explicit condition F(eta(t))<m before the endpoint. Local Lipschitz
continuity of the curve is unnecessary for this Dini proof; continuity
and its actual normalized right derivative suffice.

The final uniqueness theorem derives equality of function levels from
the equation and common initial point. It does not assume calibration or
equal-level compatibility. It reuses the existing SbrFlowUniqueness
comparison theorem; no flow, derivative, or support producer is replaced
by a new assumption. These three public results still require focused,
named-build and public axiom verification.
