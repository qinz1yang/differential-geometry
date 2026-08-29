# Raw L-length minimizers

## Role

`lCost` is defined in `Minimizer.lean` directly as the infimum of raw
`lLength` over square-root reparameterizations of global regularized `C¹`
curves with the prescribed endpoints.  This fixes the admissible category
without adding a new foundational path object or a temporary predicate.

`lCost_eq_reg` identifies this raw cost with `lRegCostC1` at nonnegative
backward time by applying `lLength_sqrt` to every competitor.

`exists_lMinimizer` applies `exists_lRegMinOn` on
`[0, sqrt tau]`.  It returns an endpoint-honest `IsLRegCurveOn`, realizes the
raw cost through `sqrtReparam`, and proves the raw L-length comparison against
every global regularized `C¹` fixed-endpoint competitor.  The theorem is
identified with the canonical maximal solution and therefore also returns the
closed-interval equality with `lRegCurve`, membership
`(Z,tau) ∈ lExpPosDom S T x`, and the genuine endpoint equation
`lExp S T x Z tau = y`.  The theorem is
restricted to positive `tau`; it does not assert a broader AC or piecewise-C1
competitor category than the direct method established.

## Verification and progress

Focused verification and the targeted module refresh pass without warnings or
placeholders.  The public endpoints depend only on the standard logical
quotient/choice axioms.  The theorem contains no supplied minimizer, Euler
equation, or regularity conclusion.

The compact global-regularized-C1 endpoint `exists_lMinimizer` is 100%.
`redVolume_anti` remains 0%; the next global frontier is the minimizing/cut-
domain geometry needed for reduced length.  Broader AC or piecewise-C1
competitor categories are not claimed by this theorem.
