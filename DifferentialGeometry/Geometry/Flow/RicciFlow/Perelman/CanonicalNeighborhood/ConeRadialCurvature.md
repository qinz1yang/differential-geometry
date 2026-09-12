# ConeRadialCurvature

Owner: Chapter25 task01a07c8d-49fa-7373-9948-022395d0119a.
Claim11fea36e-5657-4c32-bb91-3c1f7a67f20d, 2026-09-08.

Derives zero
curvature on a local concurrent field from the native torsion-free connection
and neighborhood congruence. Instantiate this with the radial dilation field
produced by ConeKoszul, then use multilinearity to get the radial unit field.
The public curvature is the native `metricRm04At`, with the standard argument
order. No connection identity is assumed in the cone specialization.

Focused15.3s EMPTY, named build18.9s and fresh external audit passed; all6 public
theorems are standard-only. Source is in31a49361c and the unique root import is
registered; receipt E:/lean-tools/chapter25-cone-20260908/completion.json.
Claim release is recorded in WORKING_STATUS.md. The actual realization from
`ConeChart`, traced kernel variation and terminal Ricci-flow exclusion remain
open. No skeleton hole is closed by these helpers.

Continuation route: the native `(1,3)` identity is also proved before tracing,
and `metricRicci_concurrent_eq_zero` gives the Ricci kernel. This leaves a
possible direct Ricci-tensor route to the terminal contradiction: differentiate
the local Ricci kernel twice, use `nabla_X partial_r = r^-1 X` on angular
vectors, and trace to obtain a strictly positive Laplacian at a nonflat point.
The Ricci evolution's reaction vanishes on the radial kernel; a left time
derivative of a nonnegative function vanishing at time zero cannot be positive.
The existing KernelSecondDerivative identities handle the fixed-space
algebra, but parallel-frame realization or intrinsic covariant product rules
and the actual terminal evolution still need proofs. This is a route, not a
new hypothesis package or a claimed endpoint.
