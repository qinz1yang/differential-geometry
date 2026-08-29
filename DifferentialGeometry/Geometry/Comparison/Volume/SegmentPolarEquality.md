# Segment-polar equality propagation

`transDens_eq_rigid` is the canonical radial equality producer in this module.
It was moved verbatim, including its public statement, docstring, attribute
wrapper, and proof, from `SegmentPolar.lean` so that the base polar module stays
within the repository size limit.  The declaration still imports the base
segment-polar API and the Riccati equality characterization directly; no
mathematical assumption, proof step, or public name changed.

The proof propagates endpoint equality by trapping the antitone density/model
ratio between its pole and endpoint limits.  Differentiating the resulting
ratio and mean-curvature identities reaches `mean_riccati_eq_iff`, yielding
radial Ricci saturation and scalar shape.

The new module passed warning-free focused verification and its named refresh,
so the moved declaration is verified at its canonical import boundary.  No
admitted proof was introduced; direct axiom audit remains pending.

Progress: the theorem statement and proof are unchanged and source-complete;
verification of the new module boundary is green.  P1a endpoints remain 6/8
(75%), dedicated machinery is about 96%, and the strict Euclidean final endpoint
remains unverified (0%).
