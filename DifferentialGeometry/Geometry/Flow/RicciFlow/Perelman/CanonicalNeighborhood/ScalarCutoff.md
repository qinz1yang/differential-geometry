# Scalar cutoff entropy estimates

Owner: Chapter25 task01a07c8d-49fa-7373-9948-022395d0119a.
Claim: 8c5ff5d8-d45c-4949-9791-6ce902b5c969 (shared three-file batch).
2026-09-08 20:09 UTC: VERIFIED, five public theorems. Upstream integration is deferred
at the user's request; this file proves Chapter25's own single-slice cutoff argument.

Use native FlowMetricBall.IsScalarControlled. Adapt the checked dyadic scale
selection and cutoff/positive-approximation proof to scalar upper control alone.
The scalar bound must persist under smaller concentric balls even when scalar
curvature is negative. No backward time window or Ricci lower bound is assumed.
Existing Noncollapsing leaves are read-only; arithmetic/private proof steps may
be adapted here without changing their exported APIs.

Final focused check: 43.3s EMPTY. Named build: 36s, lint-clean. Fresh joint
external audit: 28.4s, all five declarations standard axioms only. The one initial
parser error was docstring placement before `omit`; the corrected file has no
warnings. Shared receipt `E:/lean-tools/chapter25-audit-20260908/noncollapse-completion.json`
retains current source/artifact hashes and exact log paths. Root import is unique;
the batch claim is released after registration. Constant: 400*2^(n+1)+1-(n/2)*log(4*pi)-n.
