# SbrAscentExponentialDerivative.lean

Verified 2026-09-08 in the dev checkout. The book normal-chart right limit yields the native right manifold derivative, with unnecessary completeness and bundle hypotheses removed from that converse. Actual normalized ascents have sharp metric speed, minimizing exponential secants and the literal normalChartAt scaled limit.

Empty focused output: 20.6s. Lint-clean named build: 23s.
Fresh external public axiom audit: 17.3s; all 4 explicit public declarations use only standard axioms (or none).
Evidence: E:/lean-tools/soul-audits-20260907/SbrAscentExponentialDerivative-result3.json and its three logs.
The source-preparation record below is historical; its pending-check status is superseded by this verification. Actual claims and integration state remain in the shared status and wrapper records.

## Source-preparation record

2026-09-08 parent source work. Claim
`b004aba8-a502-4a0d-b419-f34a35d72a69` retained. SOURCE-WRITTEN / UNVERIFIED.
Chapter23 owns the current 17:36--18:10 compiler window; no Lean, Lake,
REPL, artifact refresh or public audit is run for this leaf in that window.

Book-interface audit after the compact-superlevel retraction closed:
the native producer exposes `HasMFDerivWithinAt` for actual time orbits,
whereas the book defines the right tangent by scaled local exponential
inverses. This leaf proves the concrete bridge for normalized ascent
curves; it does not replace the curve, derivative, metric or gradient by
an abstract interface premise.

First compare an arbitrary actual right-velocity curve with the intrinsic
geodesic of that velocity, using the already checked first-order distance
agreement theorem in SbrRightTangent. The native geodesic distance bound
then gives eventual upper metric speed equal to its metric length.

Next apply this to the normalized gradient. Its metric length is the
inverse gradient length. SbrFlowCalibration supplies exact level increments,
and the checked SbrMetricVelocity producer constructs actual minimizing
exponential displacements with the required scaled-vector limit.

Finally use the positive `expDiffeoRadius`, the exact minimizing length,
and right continuity. These displacements eventually lie in the actual
normal exponential domain; `expDiffeo_eq_intr` and the normal exponential
left inverse identify them with `normalChartAt`. The resulting limit is
the book's exponential-inverse right tangent. Time is based at zero for
the same local convention as the existing right-tangent API; arbitrary
times are handled by the affine time translation used by the flow APIs.

The converse bridge also takes the book's actual normal-chart secant limit
and right continuity and produces `HasMFDerivWithinAt`, by differentiating
the normal-chart coordinate curve and composing with the actual smooth
inverse chart. Thus native calibration and uniqueness apply to the book's
right-tangent formulation as well as to the constructed curves.

Four public declarations are intended. They require the standard focused,
linted named-build and external public dependency audit before counting as
verified. SbrFlowCalibration is itself still unverified. New Markdown notes
remain ignored as requested; no force-add is authorized or needed.
