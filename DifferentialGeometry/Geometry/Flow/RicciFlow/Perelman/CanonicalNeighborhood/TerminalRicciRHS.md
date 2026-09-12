# Actual terminal Ricci evolution RHS

Verified 2026-09-09: focused3 EMPTY (32.07s), named1 clean (44.62s/11421),
fresh audit1 (30.82s), both public declarations standard-only.
Receipts: E:/lean-tools/chapter25-terminal-local-20260909/.
The checked TerminalRicciHessian
producer supplies actual covariant Hessian continuity. All remaining
inverse-metric, Ricci and Riemann terms use the original carrier continuity
from IsSolutionOn. No terminal regular-time or flow-completeness assumption
may be inserted. The terminal left derivative now consumes this actual
continuity producer through RicciTerminalDerivative.

Infer the inverse-metric continuity composition before checking its target;
checking it directly against the desired lambda exhausted the default
heartbeat limit. Then normalize Function.comp_def, not comp_apply: here the
composite occurs as a function argument rather than an applied expression.
