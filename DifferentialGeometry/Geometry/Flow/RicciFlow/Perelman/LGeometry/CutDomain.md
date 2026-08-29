# Minimizing L-exponential domain

## Result

`IsLMinVec` says that `(Z,tau)` lies in the positive L-exponential domain and
that the raw L-length of its canonical L-exp ray realizes `lCost` to its own
endpoint.  `lMinDomain` is the corresponding joint subset of initial tangents
and positive backward times.

`exists_lMinVec` consumes the compact direct-method endpoint and proves that
every endpoint in its stated competitor category is reached by some
`Z` in `lMinDomain`.  The proof uses the exported equality between the attained
curve and `lRegCurve`, `lLength_sqrt`, and `lRegAction_congr`; it does not add a
supplied minimizer or assume a cut-domain decomposition.

`lMinDomain_down` proves that minimizing membership survives every decrease to
a still-positive backward time.  It restricts the regularized ray, transfers
whole-interval minimality to the prefix with `lReg_prefix_min`, identifies the
closed-prefix action with `lRegCostC1_eq_on`, and converts back to raw L-cost.
Consequently `lMinFiber_ord` proves that the minimizing times for each fixed
initial tangent form an order-connected subset of `Real`.

## Verification and frontier

Focused verification and targeted module refresh pass without warnings or
placeholders.  The public `exists_lMinVec` endpoint's axiom audit reports only
`propext`, classical choice, and quotient soundness; the new
`lMinDomain_down` and `lMinFiber_ord` endpoints have the same audit.  No new
foundational class, inverse-branch structure, or reference-tree import is
used.

The minimizing-domain definition, compact nonemptiness/surjectivity brick, and
backward-time star-shaped/order-connected fiber structure are verified.
`IsLMinVec` deliberately includes equality at a possible cut time, so this
inclusive `lMinDomain` is not generally expected to be open.  The next honest
producer is strict pre-cut uniqueness / a cut alternative, from which a
separate open injectivity domain can be defined and related to the cut
boundary.  Introducing an `interior` wrapper would not prove that mathematics.
The cut-image measure-zero theorem remains a separate global frontier.
`redVolume_anti` remains 0%, P2 remains below 1%, and the whole Poincare program
remains approximately 3--5%.

The first half of that next stage is now complete in `CutStrict.lean`:
`lMinVec_unique_lt` proves uniqueness at every strictly earlier time along a
ray that remains minimizing later.  What remains is the nonconjugacy-before-
cut theorem and the limiting cut alternative; those are not consequences of
order-connectedness alone.
