# Pointed metric precompactness from eventual finite nets

The completed development consists of:

- `DifferentialGeometry/Topology/MetricSpace/DistanceMatrixLimit.lean`;
- `DifferentialGeometry/Topology/MetricSpace/CountableNetLabels.lean`;
- `DifferentialGeometry/Geometry/Metric/Approximation/PointedPrecompactness.lean`.

It formalizes MC13's eventual finite-net extraction theorem, including
the finite-set enumeration, distance-matrix, completion, properness, and
actual-map arguments. The natural net hypothesis feeds the labeled core
through a proved adapter; labeled nets are not an additional assumption
of the final theorem.

## The full MC13 theorem

`GC.MetricGeometry.exists_pointedGHConverges_of_eventual_finite_nets`
assumes a sequence of pointed metric spaces `(X n, p n)` and exactly
this quantifier order: for every `R > 0` and `η > 0`, there exist natural
numbers `N` and `I` such that every `n ≥ I` admits a finite set `S` of
at most `N` points, all in the closed radius-`R` source ball, with every
point of that ball within distance at most `η` of some point of `S`.

It constructs a metric space `Y`, a basepoint `q`, and a strictly
increasing subsequence `φ`, such that `Y` is proper and
`PointedGHConverges (fun n => p (φ n)) q` holds. This latter conclusion
includes completeness of `Y`. The limiting carrier is small because
the construction uses the completion of a countable label set; source
carriers may lie in an arbitrary fixed universe.

`exists_pointedGHConverges_of_uniform_finite_nets` supplies the all-index
variant by taking `I = 0`. Neither variant needs the original sources
to be complete or proper. Thus the blueprint's proper-source statement
is an immediate specialization. The separate converse finite-prefix
absorption statement for proper sources is not asserted by these proofs.

The enumeration adapter is documented in `countable_net_labels.md`.
It uses dummy basepoints before each level's own threshold and padded
finite enumerations afterward; its basepoint identity is retained in
the final convergence statement.

## Exact labeled-net theorem

`GC.MetricGeometry.exists_pointedGHConverges_of_countable_nets` assumes:

1. A countable label type `L` with a distinguished label `o`.
2. A sequence of metric spaces `X n`, with points `x n a` for every
   source index `n` and label `a`. The source basepoint is `x n o`.
3. For each label `a`, one finite real bound `C a` satisfying
   `dist (x n a) (x n o) ≤ C a` for every `n`. The bound may depend on
   the label; it need not be uniform over all labels.
4. Finite sets of labels `F m` such that, for each natural number `m`,
   eventually in `n`, every point of the closed source ball of radius
   `m+1` is within distance at most `1/(m+1)` of `x n a` for some
   `a ∈ F m`. The eventual threshold may depend on `m`.

It proves the existence of one strictly increasing subsequence `φ` and
one pseudometric on `L`. With that pseudometric, the canonical completion
`UniformSpace.Completion L` is a proper metric space, and the actual
pointed spaces `(X (φ n), x (φ n) o)` converge to the completed space
pointed at the image of `o` in the project's `PointedGHConverges`
convention. This includes a complete limit and, for every fixed radius
and admissible error, actual closed-ball approximation maps eventually
in the selected subsequence.

No source space is assumed complete, proper, compact, or a length
space. The chosen labels are not assumed dense in any source. No
dimension, curvature, smoothness, topology, or fibration conclusion is
asserted.

## What the proof actually constructs

`Metric.exists_pseudometric_subseq_tendsto_dist` is a reusable
countable-distance-matrix theorem. Given a countable label family and a
uniform finite bound for each pair of labels, it takes a convergent
subsequence in the countable product of the corresponding compact real
intervals. Symmetry, zero diagonal, and the triangle inequality pass to
the limit and produce an actual `PseudoMetricSpace L`.

`Metric.exists_completion_subseq_tendsto_dist` passes to Mathlib's
canonical completion, with its genuine metric and dense label map.
The completion of a pseudometric space already identifies labels at
zero distance; injectivity of the label map is neither assumed nor
asserted. All pairwise distances converge along the same subsequence.

Three other generic results handle the net argument:

- Eventual coverage by a fixed finite label set passes to the limit.
  A finite pigeonhole argument provides a frequently chosen center;
  the non-strict distance bound passes to the limit at that center.
- A finite union of closed balls that covers all dense labels lying
  in an open ball covers every point of that open ball.
- In a complete metric space, finite ambient nets at every positive
  scale in every ball about one basepoint imply properness. The centers
  need not lie in the ball. Mathlib total boundedness uses ambient
  centers, so no artificial intrinsic metric on a ball is introduced.

For the final approximation at radius `R` and error `ε`, choose a single
level `m` with `R < m+1` and `1/(m+1) < ε/4`. Adjoin `o` to its finite
label set. Eventually all pairwise matrix errors on this finite set
are smaller than `η = 1/(m+1)`, and the source net is available. The
proved `PointedBallApprox.ofPairedNets` constructor then gives the actual
map, exact basepoint identity, pairwise distortion, and target coverage.
Its source-domain estimate keeps coverage witnesses inside the required
closed source ball even when labels repeat or merge in the limit.

The proof uses radii `m+1` and accuracies `1/(m+1)`, instead of the
blueprint's `m` and `2^(-m)`. This is an explicitly proved cofinal choice
of radii and accuracies, not a change to the theorem's convergence
quantifiers. The extracted subsequence and completed limit remain fixed
before any final requested radius or error is selected.

## Sources and reuse

- Blueprint `GEOMETRIZATION_BLUEPRINT/master207A.tex:1332`, theorem
  `thm:metric-eventual-compactness`, and its displayed proof.
- BBI, *A Course in Metric Geometry* (AMS, 2001), Theorem 7.4.15,
  printed page 264 / PDF page 279: full distance-matrix and completion
  proof reopened. Theorem 8.1.10 and its outline, printed pages
  274–275 / PDF pages 289–290, also reopened. The broader eventual-net
  arbitrary-source version is the blueprint's adaptation, not a
  verbatim stronger theorem attributed to BBI.
- Archive: `BuragoBuragoIvanovBook.pdf`, SHA-256
  `4efaa168dcc83e7e9f5663d14824f9543104beab21642ca3830a5dd1c684c971`;
  recomputed during this implementation and unchanged.
- `reference_checks_revision61.md` was reread, including its recorded
  2024-07-06 author errata review and the finite-prefix/source-properness
  qualifications. That unchanged source/errata check is reused; no
  fresh exhaustive errata review is claimed.
- Existing `Topology/MetricSpace/DistanceConvergence.lean` and
  `Analysis/Calculus/Compactness/DiagonalSubsequence.lean` were inspected.
  The former is a convergence criterion in an already-given proper
  target; the latter contains a natural-indexed scalar diagonal
  specialization. The new reusable theorem directly uses Mathlib's
  compact countable-product subsequence theorem, handles arbitrary
  countable labels and varying source carriers, and constructs the
  limiting pseudometric. Standard completion and finite-filter lemmas
  are reused rather than reimplemented.

## Verification

Lean `4.35.0-rc3`, Mathlib commit
`c55e6e786f49471c72fbddbec5415808896aec1e`:

- The distance-matrix module built successfully (1,566 jobs including
  cached dependencies), without warnings.
- The completed pointed-precompactness module built successfully (1,578 jobs
  including cached dependencies), without warnings.
- Separate stdin imports audited all five public generic theorems and
  all three pointed-precompactness theorems. Every axiom closure is exactly `propext`,
  `Classical.choice`, and `Quot.sound`; no admission is used.
- The declarations and the proof's quantifier order were manually
  checked against the blueprint, including exceptional prefixes,
  repeated labels, ambient finite nets, and one limit for all radii.
- A direct application of the full eventual-net theorem to a constant
  singleton sequence compiled, using a one-point net and threshold zero.
- The final elaborated signature was printed and checked: its only
  source-space instance requirement is `MetricSpace`, and its input
  quantifiers and inside-center conditions are exactly those above.

These are scoped pure-metric builds, not a migration or rebuild of the
Poincare library. Neither source file imports the admitted skeleton.
