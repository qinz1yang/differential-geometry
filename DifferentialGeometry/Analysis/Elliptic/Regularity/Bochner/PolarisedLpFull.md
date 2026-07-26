# PolarisedLpFull

## 2026-07-17 import refresh repair

An upstream refresh exposed an ambiguous unqualified `gradFun_sub`: both the
Bochner-local compatibility lemma and the canonical connection-layer theorem
were open.  The consumer now names
`DifferentialGeometry.Integral.Connection.gradFun_sub` explicitly; no theorem
statement or mathematical content changed.  Focused verification passed.
