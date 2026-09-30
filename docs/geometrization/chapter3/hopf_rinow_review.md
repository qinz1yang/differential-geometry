# Independent follow-on review: Hopf–Rinow and packing-to-limit assembly

The complete proofs in Topology/MetricSpace/HopfRinow.lean,
Topology/MetricSpace/FiniteNets.lean, and
Geometry/Metric/Approximation/LengthLimitExtraction.lean were independently
read. Their exact statements were compared with blueprint master207A.tex,
MC01's finite-distance Hopf–Rinow theorem and proof plan (754–781), MC02's
net/packing statements (785–831), and MC13's eventual-net and finite-prefix
arguments (1330–1466). No mathematical defect or contract mismatch was found.

This supersedes the interim statement in final_metric_review.md that generic
metric Hopf–Rinow was still in progress. The reviewed implementation now proves
the properness and exact-segment conclusions, under completeness, local
compactness, and the explicitly stated near-short-curve length property.

## Hopf–Rinow: assumptions and the compact-radius argument

The curve input quantifies over every pair of points and every positive
accuracy, with continuous unit-interval curves, exact endpoints, and actual
eVariationOn length less than distance plus accuracy. It assumes neither
compact balls nor geodesics. The ambient MetricSpace has finite real distances;
all balls use those same distances. No restricted ball is itself assumed to be
a length space. Completeness and local compactness are both retained.

The radial-trimming lemma is the key independent producer. If
d(y,p) ≤ r+δ, r,δ ≥ 0 and η>0, it produces z in the closed r-ball with
d(y,z)<δ+η. If y is already in the ball, z=y works. Otherwise the radial
distance along a near-short curve meets r by the intermediate value theorem.
The two-piece variation bound gives

    r + d(z,y) < d(p,y) + η ≤ r + δ + η.

This proves the required distance estimate without assuming that the curve
has controlled speed, attains the distance, or stays inside a prescribed ball.
The zero-radius and coincident-point cases are covered without division by a
distance or by the radius.

For compact-ball enlargement, local compactness gives a compact closed
δ-thickening of the existing compact ball, with δ>0. Trimming with radius
increment δ/3 and error δ/3 puts every point of the larger ball within
distance <2δ/3 of the old ball. Thus the larger closed ball is a closed subset
of the compact thickening. No equality between a thickened ball and a larger
metric ball, and no preexisting ProperSpace instance, is used.

For a fixed center, the set S of positive compact-ball radii is nonempty by
local compactness. In the bounded case its real supremum s is positive and
finite. At each ε>0, the supremum property supplies r in S with
s−ε/4<r≤s. Trimming from the closed s-ball to the closed r-ball with error
ε/4 and then using an ε/2-net in that compact ball gives covering error

    < (s−r) + ε/4 + ε/2 < ε.

Hence the supremum ball is totally bounded. It is closed in the complete
ambient space, so it is complete and compact. Enlargement then yields a radius
strictly above s in S, contradicting the upper-bound property. Therefore S is
unbounded, and every closed ball is a closed subset of a larger compact ball.
This includes requested radii ≤0. The proof is valid for the empty space:
the ProperSpace field is a universal assertion about centers, so no basepoint
is improperly selected.

The approximate-midpoint variant uses the already proved completeness-only
MC22 to produce the required curves. The exact-segment theorem then uses the
new properness instance and the proved near-short-curve → midpoint → segment
chain. Its conclusion includes coincident endpoints and specifies all pairwise
segment distances. It asserts no uniqueness or extension of arbitrary local
geodesics. General arclength reparameterization is bypassed, not postulated.

## Finite nets: cardinality and exceptional cases

- The separated-net bound selects one actual nearby center per point of a
  finite separated set. Shared centers would force distance ≤2ε<ρ, so the
  map is injective and the exact cardinal bound follows. Both sets may be
  empty. The theorem is about finite sets, not cardinal arithmetic for an
  unspecified infinite set. It also works in pseudometric spaces.
- The packing converse assumes every finite ρ-separated subset has cardinal
  at most N, with ρ>0. It selects a largest attainable cardinality in 0,…,N;
  the empty set makes this selection valid even when N=0. An uncovered point
  would be at distance ≥ρ from every chosen center, could be inserted, and
  would contradict maximality. Thus the resulting net has cardinal at most N,
  centers inside the given set, and strict covering distances <ρ. When N=0
  the hypotheses force that set to be empty; no nonempty center is fabricated.
- Compact-set nets have internal centers and actual coverage witnesses. The
  finite-prefix adapter requires properness of every source and chooses
  internal nets in the omitted closed balls. Its bound N plus the sum of their
  cardinalities is valid; it need not be the minimal possible bound. I=0 gives
  an empty sum and needs no prefix case. The whole construction occurs after
  fixing R and ε, so N and I may depend on both; no uniform threshold over
  infinitely many scales is introduced.

These are the exact cardinality-preserving ingredients needed by the
downstream theorem. The main pointed extraction never invokes the proper-source
prefix adapter and therefore does not acquire a hidden source-properness premise.

## The actual packing-to-geodesic-limit application

The producer input is exactly

    ∀ R>0, ∀ η>0, ∃ N I, ∀ n≥I,
      every finite η-separated subset of the closed source R-ball has card ≤N.

For each fixed radius, accuracy, and late index, the packing converse supplies
an internal net with the same N and I. Its strict error bound implies the
non-strict bound required by pointed precompactness. There is one extracted
metric limit, basepoint, and strictly increasing subsequence for all scales.
The limit is proper and complete; source completeness and properness are not
assumed. The small target universe is justified by the previously reviewed
countable-label construction.

The geodesic variant additionally requires the actual near-short-curve property
for every source space. It supplies that property at the indices φ(n) of the
same subsequence, then applies the already proved midpoint-transfer and proper
segment construction to the same target metric. It does not choose a second
limit or silently assert that a closed source ball is geodesic. Its remaining
geometric inputs are the displayed packing and curve hypotheses; it supplies
no curvature-to-packing proof, dimension bound, or Alexandrov comparison.

## Evidence and source scope

The existing source records revision58, revision59, revision61, and revision68
were reused for unchanged contracts. The independent review read the new
hopf_rinow.md source comparison: its author reopened BBI Definition 2.5.21,
Proposition 2.5.22 and its proof, and Theorem 2.5.23, printed 49–50/PDF 64–65,
with adjacent qualifications and retained errata pages 2–4. This review did
not separately reopen those PDF pages or retrieve remote errata. The finite-net
reference remains BBI Definition 1.6.1 and Exercise 1.6.4/Theorem 1.6.5,
printed 13–14/PDF 28–29. Existing source hashes are retained in the leaf notes.

The actual Mathlib helpers were inspected: Pseudo/Lemmas.lean:88–99 derives a
positive compact closed ball from local compactness; Thickening.lean:432–438
constructs a compact closed thickening from a compact neighborhood. Neither
uses properness, so there is no circular invocation of the conclusion.

A combined targeted build of the three reviewed modules passed (1,988 jobs,
including cached dependencies), on Lean 4.35.0-rc3 and Mathlib
c55e6e786f49471c72fbddbec5415808896aec1e. Independent successful stdin checks
inspected all eleven public theorem axiom closures and three principal fully
elaborated signatures. Each closure contained exactly propext, Classical.choice,
and Quot.sound. No reviewed Lean source was edited.

| Reviewed file | SHA-256 |
| --- | --- |
| HopfRinow.lean | a37945aee58222bcafb106892e9f5cc2601f75480b19e44c0ef4c3efcdc8f5ea |
| FiniteNets.lean | 87486a8c7bbfce157936a23a1f3935303d22ea9f555b1df67ebd170f4854dd7d |
| LengthLimitExtraction.lean | 17eb29f001222dbf274e2613373881b6276c1ee9cf1c683e02d1cb19c631e82a |

The completed generic metric argument does not certify compatibility with the
migrating PC manifold APIs. Those inherited metric/length/scaling adapters and
the Chapter 4 geometric packing/comparison producers remain separate boundaries.
