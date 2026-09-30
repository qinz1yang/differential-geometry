# Lifting bounded configurations: AC34 and the selection step of AC37

File: `DifferentialGeometry/Geometry/Metric/Approximation/FiniteConfiguration.lean`.

## Exact mathematical statements

`GC.MetricGeometry.PointedBallApprox.exists_lift_configuration` takes an
actual `PointedBallApprox p q (M+2) epsilon`, with `M >= 1`,
`epsilon < 1/4`, and a labeled target configuration `y a` satisfying
`dist (y a) q <= M`. Positivity of epsilon is already a field of the
approximation. It produces points `z a` in the actual source closed ball,
represented by its subtype, with:

- `dist (f(z a)) (y a) < epsilon`;
- `dist (z a) p < dist (y a) q + 2*epsilon < M+2`;
- `abs (dist (z a) (z b) - dist (y a) (y b)) < 3*epsilon`.

The label type need not be finite. The only additional requirement for
an arbitrary label type is the same single bound `M` for every label.
For the blueprint's finite configuration, take its displayed maximum.
Neither labels nor target points are assumed distinct. The empty label
type is allowed. The bound `M >= 1` follows the blueprint convention;
the first proof does not need that lower bound once the approximation
and common bound are supplied.

`PointedBallApprox.exists_injective_lift_configuration` has the same
conclusions and additionally makes the lift function injective, provided
`3*epsilon < dist (y a) (y b)` for every distinct pair of labels.
The blueprint's minimum-distance condition implies exactly this premise.
This formulation avoids a spurious minimum over an empty pair family
when there are zero or one labels. Injectivity into the subtype implies
injectivity of the underlying source points.

`PointedGHConverges.exists_subsequence_lift_configuration` starts from the
already specified pointed convergence to `Y,q`; it constructs no second
limit. Supply a bounded target configuration, a sequence of strictly
positive errors less than `1/4` tending to zero, and predicates `P j n`
such that, for every `j`, `P j n` holds for all sufficiently large source
indices `n`. It returns:

- a strictly increasing source-index sequence `phi`;
- `P j (phi j)` for every `j`;
- actual source points `z j a` in the closed `(M+2)`-ball in
  `X (phi j)`, with the strict radial and `3*epsilon j` distance bounds;
- convergence of every source pair distance to the corresponding target
  pair distance.

There is no common eventual threshold required for all errors or all
predicate rows. The proof selects a source index satisfying both the
prescribed row and the required approximation. A predicate depending only
on the source index is passed as `fun _ n => P n`. The output remains on
the original target metric and the exact selected source metrics.

## Proof and assumptions

The first theorem reuses the existing approximation's `inverseLift`.
Its coverage theorem gives image error less than epsilon. The exact
basepoint and distortion imply the radial bound, and
`inverseLift_distortion` gives the three-error estimate. The injectivity
claim follows by contradiction if two lift points coincide.

The sequence theorem uses Mathlib's
`Filter.extraction_forall_of_eventually` on the conjunction of each
predicate row and the eventual approximation requirement. Every selected
approximation has the fixed radius `M+2`; only its error changes. The
pairwise distance convergence follows by squeezing its error between
zero and `3*epsilon j`.

No continuity of the approximation maps, geodesic assumption, source
properness, source completeness, dimension bound, or curvature premise
is used. The project pointed-convergence object includes completeness
of the target, but this selection argument uses only its eventual
approximation part. All balls and estimates use ambient metric
distances, with no assertion about intrinsic ball metrics.

## Blueprint and source correspondence

Read the statement and full proof of AC34 at
`docs/geometrization/blueprint/master207A.tex`, lines 3809--3841,
label `lem:alexandrov-finite-lifting`, and the complete existing
`GEOMETRIZATION_BLUEPRINT/reference_checks_revision69.md` record. The
blueprint copy has SHA-256
`277359ee147d25184d4b38b20a91ee44a394fd6ea316cfc368fab74e06bef79b`.

AC34 is the blueprint's elementary adapter, not a verbatim imported BBI
statement. The existing revision69 checks of BBI Proposition 10.7.1
(printed page 376 / PDF page 391) explain its role in transferring
comparison to a metric limit. Those unchanged source checks and errata
comparisons are reused; this module needs no additional geometric source
theorem and claims no fresh reading of the archived BBI PDF.

The sequential theorem formalizes the increasing-index selection and
six-distance convergence step described in AC37 and its revision69
record. It does not supply source comparison inequalities, comparison
angle continuity, or target curvature comparison. Those are separate
consumers and producers.

## Verification

The new leaf built on Lean 4.35.0-rc3 and mathlib commit
`c55e6e786f49471c72fbddbec5415808896aec1e`, with 1381 Lake jobs and no
warnings. All three public declarations' printed axiom closures contain
only `propext`, `Classical.choice`, and `Quot.sound`. There are no
admissions or added mathematical axioms. The repository-wide scoped gate
and downstream integration are recorded separately by the parent task.

Lean applications also checked the empty label type for the injective
theorem and two repeated target labels for the general theorem. They
compiled successfully through `lake env lean --stdin`; these are
interface corner checks, not extra library declarations.
