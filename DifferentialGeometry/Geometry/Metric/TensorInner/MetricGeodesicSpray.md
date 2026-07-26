# MetricGeodesicSpray

## 2026-07-15

The coordinate metric spray is now a total, proof-independent definition.  It
uses `Ring.inverse` of Mathlib's canonical Gram operator and the existing
`MetricKoszul.koszulCovCLM`; coercivity is used only by
`raisedKoszulOp_eq`/`metricSpray_eq` to recover the geometric Lax--Milgram
formula.

The convergence proof is split into inverse-Gram, Koszul--Riesz, raised-operator,
and diagonal-phase bricks.  This avoids a monolithic elaboration and leaves no
new radius, velocity, or stage-containment assumption.  Focused verification
passed.  This generic spray layer is complete; it is infrastructure for, not a
proof of, `StepB1RawInput`.

## 2026-07-16

The existing `raisedOp_smooth` theorem is now public.  This is the canonical
smoothness companion to `raisedKoszulOp_conv`: downstream component consumers
need both convergence and smoothness of the full raised Koszul bilinear
operator, while `metricSpray_contDiffOn` exposes only its diagonal phase-space
evaluation.  No statement or assumption changed, and focused verification
passed.
