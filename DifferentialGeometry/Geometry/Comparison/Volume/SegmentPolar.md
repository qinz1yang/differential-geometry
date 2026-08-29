# Segment-polar base API

`transDens_eq_rigid` now has its canonical home in
`SegmentPolarEquality.lean`.  Its complete public statement, docstring,
attribute wrapper, and proof were moved verbatim across that abstraction
boundary.  This base module no longer imports `JacobiRiccati` solely for the
equality theorem and is now 2883 source lines, below the 3000-line limit.

`segBall_vol_le_int` is now the public canonical bridge from segment-ball volume to the
integral of exponential-Jacobian density; its statement and proof are unchanged.
Likewise, `gBall_model_int` is the public canonical evaluation of the model-density
integral over a metric tangent ball; only its visibility and name changed.

After the split, this base module passed warning-free focused verification and
its named refresh.  The new equality module also passed both gates.  The
equality theorem's canonical status is recorded in `SegmentPolarEquality.md`;
its direct axiom audit remains pending.

Progress: P1a endpoints remain 6/8 (75%), dedicated machinery is about 96%,
and the strict Euclidean final endpoint remains unverified (0%).
