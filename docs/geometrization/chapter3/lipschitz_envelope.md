# Positive Lipschitz envelopes: Chapter 3, MC19 / MG02

The implementation is
`DifferentialGeometry/Topology/MetricSpace/LipschitzEnvelope.lean`.
It uses only Mathlib imports. It does not import the Poincare foundation,
manifolds, curvature, flows, or the admitted geometrization skeleton.

## Exact statements and their relation to the blueprint

`Metric.exists_lipschitzWith_between_iff` says: for a pseudometric space `X`,
a nonnegative real Lipschitz constant `K`, and arbitrary functions
`lower upper : X → ℝ`, there exists a `K`-Lipschitz real function `r`
satisfying `lower ≤ r ≤ upper` if and only if

\[
\forall p,q\in X,\qquad
\operatorname{lower}(p)-K\,d(p,q)\leq\operatorname{upper}(q).
\]

The orders on functions are pointwise. `K : ℝ≥0` is Mathlib's standard
constant type for `LipschitzWith`. No compactness, completeness, continuity
of the bounding functions, or nonemptiness of `X` is assumed.

`Metric.exists_pos_lipschitzWith_between_iff` adds the hypothesis that
`lower` is everywhere strictly positive and adds the conclusion that
`r` is everywhere strictly positive. This is the blueprint's positive
envelope, with a real-valued function plus its positivity proof encoding
the positive codomain. It also permits `K = 0`; the blueprint and KL state
the positive-constant case. Positivity of `upper` need not be an extra
hypothesis: whenever compatibility holds, taking `p = q` implies
`0 < lower q ≤ upper q`. Pseudometric spaces are another harmless
generalization proved by the same triangle-inequality argument.

The proof takes the real supremum
\[
r(q)=\sup_p\bigl(\operatorname{lower}(p)-K\,d(p,q)\bigr).
\]
For every given `q`, the term `p = q` makes the set nonempty and
compatibility bounds it above by `upper q`. These facts are supplied
explicitly to the conditional supremum lemmas. The empty-space case
requires no artificial global nonemptiness assumption: all those
pointwise obligations are vacuous.

This proves neither a smooth envelope nor a geometric volume scale.
The smoothing and scale-comparison requirements of KL Corollary 6.5
remain separate.

## Sources and reuse check

- Blueprint: `GEOMETRIZATION_BLUEPRINT/master207A.tex`, section
  `sec:metric-envelope`, lines 844–892, MC19 / MG02.
- Archived source: Kleiner–Lott, *Locally collapsed 3-manifolds* (2014),
  `KleinerLottAsterisqueLocalCollapse.pdf`, Lemma 6.1, printed page 41,
  PDF page 36; displayed equations (6.2)–(6.3). The source page was
  reopened during this implementation. Source SHA-256:
  `7a860b4dd95b35fe33b06bf040100ec243d72c80528d927f4763391aaf79cb6e`.
- Existing checked records `reference_checks_revision56.md` and
  `reference_checks_revision58.md` were reread. They explicitly verify
  the non-strict inequalities against the rendered page and distinguish
  Lemma 6.1 from the corrected smoothing corollary. PDF text extraction
  alone misreads some non-strict inequalities. The unchanged author
  correction check (2015-05-15 sheet) is reused; no fresh complete errata
  audit is claimed.
- Target Mathlib: commit
  `c55e6e786f49471c72fbddbec5415808896aec1e`, Lean `v4.35.0-rc3`.
  The target library was searched for Lipschitz envelopes and functions
  between two bounds. `LipschitzOnWith.extend_real` in
  `Mathlib/Topology/MetricSpace/Lipschitz.lean` was inspected. It extends
  a given Lipschitz function from a subset and does not directly state
  the compatible lower/upper-bound result. The new proof reuses
  `LipschitzWith.of_le_add_mul`, `LipschitzWith.le_add_mul`, `le_csSup`,
  and `csSup_le`; it does not introduce another Lipschitz definition.
- Both proposed public names were searched in Mathlib and
  DifferentialGeometry without finding a collision.

## Verification

On Lean `v4.35.0-rc3` and the target Mathlib commit above:

- `lake build DifferentialGeometry.Topology.MetricSpace.LipschitzEnvelope`
  passed (1,279 jobs, including cached dependencies), with no warnings.
- An independent stdin Lean invocation imported the built module and
  printed the axioms of both public theorems. Each uses exactly
  `propext`, `Classical.choice`, and `Quot.sound`; neither uses `sorryAx`.
- The same invocation checked an empty-space application at `K = 0`
  and a positive-envelope application on the real line at `K = 0`.
- The archived PDF's SHA-256 was recomputed and matches the existing
  source record above.
- The mathematical signatures were reread against the blueprint.
  The declared generalizations are nonnegative constants, pseudometrics,
  and dropping the redundant upper-positivity hypothesis. All are proved;
  no smoothing or scale comparison is added.

The build is a narrow verification of this leaf on the selected migration
target, not a build or migration of the whole Poincare library. Source
contains no `sorry`, axioms, comments, or docstrings.
