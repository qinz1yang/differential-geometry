# SbrExponentialSecants.lean

Verified 2026-09-08 in the dev checkout. The actual fiber exponential is locally Lipschitz from the model norm to the ambient metric. Along any positive-time filter, converging model initial vectors yield the actual intrinsic directional derivative; tangent/model values are compared through an explicit fixed model vector.

Empty focused output: 17.4s. Lint-clean named build: 22.2s.
Fresh external public axiom audit: 17s; all 2 explicit public declarations use only standard axioms (or none).
Evidence: E:/lean-tools/soul-audits-20260907/SbrExponentialSecants-result4.json and its three logs.
The source-preparation record below is historical; its pending-check status is superseded by this verification. Actual claims and integration state remain in the shared status and wrapper records.

## Source-preparation record

2026-09-08 parent source work, claim
`f12e4f9c-d544-4095-a9b8-d1e4fbc8b1e1`. SOURCE-ONLY; no compiler evidence.

This is a supplementary sequential geometric comparison. The now-verified
SbrMetricVelocity uses a stronger pointwise support inequality and a
squared-norm squeeze, so its actual Euler-limit velocity criterion does
not depend on this source-only leaf. The first theorem here gives a local
Lipschitz bound for the actual
fiber exponential from the existing model norm to the actual ambient metric.
It is not a sharp Riemannian norm statement. The second theorem allows any
filter of positive times tending to zero and model vectors tending to v;
the corresponding F-secants tend to the actual intrinsic derivative in v.

The proof combines the uniform chart distance bound in SbrRightTangent with
native smoothness of the fiber exponential and Mathlib's C1 local Lipschitz
theorem. This transfers the small vector error h*(w-v) to an o(h) metric
error. No interpolation of the sampled times or assumed curve derivative
is needed. Compactness and existence of convergent tangent subsequences
are separate subsequent steps.
