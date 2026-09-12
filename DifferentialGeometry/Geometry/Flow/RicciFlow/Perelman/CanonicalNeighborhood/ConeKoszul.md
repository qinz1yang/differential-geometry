# ConeKoszul

Chapter25 proof continuation, 2026-09-08. Owner: task
01a07c8d-49fa-7373-9948-022395d0119a; claim
f45c183e-2159-4ff6-8d11-45a6be3ef2e3.

Scope: derive the radial Levi-Civita derivative from the actual local metric
`dr^2 + r^2 h`, using the native `MetricKoszul.const_flat_eq_nhds` theorem.
No new connection, curvature hierarchy, or Chapter25 assumption is introduced.
The bilinear form is defined on model coordinates; its use as a metric is
restricted by an actual smooth metric and a neighborhood equality. The radius
must be nonzero for the radial-connection conclusion.

Focused18.2s EMPTY, named build23.5s and fresh external audit passed; all9 public
theorems and3 data definitions are standard-only. Source is in31a49361c;
receipt E:/lean-tools/chapter25-cone-20260908/completion.json. Claim release is
recorded in WORKING_STATUS.md.
ConeRadialCurvature now proves the model radial-curvature identity. The actual
ConeChart realization, positive Laplacian and terminal-flow contradiction
remain open; these helpers do not close `cone_terminal_exclusion`.

Compiler lessons: use explicit local normed instances for the one- and
two-covector spaces, as in native MetricKoszul. Use `ContinuousLinearMap.ext`
on maps from products. Avoid `change` between `cov coneEulerField` and
`cov (radius • radialField)`: it unfolded the large connection and timed out
even at600k heartbeats. Prove the field equality by `rfl`, then rewrite it
under the connection. This passes at the default heartbeat limit.
