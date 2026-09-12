# Finite terminal jet identification

Development: the native metric application identifies actual terminal jets
from finite uniform Cauchy control in a fixed chart. It uses no terminal Shi
input and no endpoint regular-time hypothesis. The covariant-to-coordinate
estimates remain separate; do not count this conditional identification as
the terminal Ricci RHS producer.

Claim and verification status are in WORKING_STATUS.md and the phase plan.

Verified 2026-09-09: focused attempt3 EMPTY (17.74s), named build1 passed
(22.55s), fresh four-public axiom audit2 standard-only (16.96s).
Receipts: E:/lean-tools/chapter25-terminal-local-20260909/.
Namespace for audits is DifferentialGeometry.PDE.RicciFlow, distinct from
the module path DifferentialGeometry.Geometry.Flow.RicciFlow.
For filter expressions, ascribe Eventually or Tendsto before using .mono or
.comp. Continuous/Tendsto composition may need Function.comp_def to normalize.
