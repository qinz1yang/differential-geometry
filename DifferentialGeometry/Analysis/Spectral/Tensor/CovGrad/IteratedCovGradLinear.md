# IteratedCovGradLinear

## 2026-07-15 scalar homogeneity

`iteratedCovGrad_smul` records real scalar homogeneity of every iterated
covariant gradient.  It is the scalar companion to the existing add/neg/sub
API and is proved by the same rank-changing induction through
`iteratedCovGrad_succ` and `covGrad_smul`.

Focused verification passes.  The check retains one pre-existing
`unusedSectionVars` warning on `covGrad_neg`; the new theorem adds no warning.

This is a completed reusable algebraic producer (**100%**), not an A2 operator.
It unblocks bundling `scalarLapDiffCc` as a genuine linear map; that completed
`H^(m+2) ->L H^m` operator remains theorem-level **0%** until its dense-core
extension and core-compatibility proofs are verified.
