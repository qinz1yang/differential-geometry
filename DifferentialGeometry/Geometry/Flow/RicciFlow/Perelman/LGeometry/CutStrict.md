# CutStrict

## Result

`lMinVec_unique_lt` proves strict pre-cut uniqueness: if `Z` minimizes through
`tau`, `0 < sigma < tau`, and a minimizing `W` reaches the same point at
`sigma`, then `W = Z`.

`lMinVec_nconj_lt` proves the companion strict pre-cut nonconjugacy result.  A
ray that minimizes through `tau` cannot be L-conjugate at any strictly earlier
parameter.  Positivity of the earlier parameter is inferred from conjugacy, so
the public statement does not carry a redundant `0 < sigma` hypothesis.

The proof is native to `DifferentialGeometry`.  It splices the two minimizing
regularized curves, transports the branchwise action while ignoring the single
node, applies finite chart-H1 minimizer regularity to obtain C1 matching at the
node, and propagates the matched phase state back to zero by regularized ODE
uniqueness.

For nonconjugacy, `lIndex_neg_conj` constructs two globally smooth directions
that match at the conjugate node and have negative total branch index.
`lIndex_sum_nonneg` realizes the same pair by a genuinely moving-node
variation and contradicts that negativity using fixed-endpoint minimality.
The moving node is essential: fixing it would erase the positive Green cross
term.

## Verification

Focused verification passed without warnings.  The axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.  The source contains no
placeholder proof.

## Frontier

This closes both strict pre-cut uniqueness and strict pre-cut nonconjugacy.  It does not prove
openness of `lMinDomain`: membership is intentionally inclusive at cut time.
The classical cut alternative at the first non-minimizing time remains a
separate frontier requiring a native limiting/compactness statement for
minimizing initial tangents and the conjugate-point alternative.

Project accounting: `lMinVec_unique_lt` and `lMinVec_nconj_lt` are complete
(100%); their dedicated strict-splice and moving-node index machinery is
complete (100%).  The broader cut-alternative
theorem is not yet stated or proved (0%); the existing dedicated minimizing,
splice, ODE-uniqueness, and conjugate infrastructure is substantial but is not
counted as completion of that theorem.
