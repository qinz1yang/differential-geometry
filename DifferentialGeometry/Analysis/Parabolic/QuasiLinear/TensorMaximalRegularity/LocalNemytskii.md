# LocalNemytskii

## 2026-07-19

This file is focused-check green, warning-free, and its named `.olean` has
been refreshed.  It supplies the measurable state-set lift `aeSetLift`, the
local linear-growth integrability lemma `memLp_on`, and `nemytskiiOn` for a
nonlinearity defined only on a state subtype.

The construction is genuine local machinery: outside the almost-everywhere
state set it uses the supplied zero member only to choose a total measurable
representative.  It does not assume a global extension or add a PDE
hypothesis.

Endpoint accounting: this producer is verified, but both
`ricci_flow_unif_existence` and `ricci_flow_forward_unique` remain 0% until
their exact declarations are proved and checked.
