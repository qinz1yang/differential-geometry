# Binding BBI's strict-supremum pointed convergence convention

This leaf supplies the literal open-ball, strict-supremum convention in BBI Definition 8.1.1 and proves its equivalence with the project's closed-ball convergence when the target is complete. It distinguishes the printed definition from the following complete-limit convention and preserves every positive error parameter, including errors larger than the radius.

## Fresh source inspection

The archived AMS 2001 Burago–Burago–Ivanov A Course in Metric Geometry was reopened read-only and rehashed:

    BooksPapers/BuragoBuragoIvanovBook.pdf
    4efaa168dcc83e7e9f5663d14824f9543104beab21642ca3830a5dd1c684c971

The following complete relevant pages were freshly read, with the stated visual checks:

- Definition 1.3.1, printed page 7/PDF page 22: \(B_r(p)\) means the open ball; closed balls have the overline notation. Extracted and visually inspected.
- Definition 7.1.4, printed page 249/PDF page 264: distortion of an arbitrary map is the supremum of its absolute pairwise distance errors. Extracted and visually inspected. Continuity is not required.
- Section 7.3.1's opening convention, printed page 252/PDF page 267: an \(r\)-neighborhood is the set at distance strictly less than \(r\), equivalently the union of the open radius-\(r\) balls. Extracted and read.
- Definition 8.1.1, printed page 272/PDF page 287: all \(R>0\) and all \(\varepsilon>0\), a threshold with \(n>n_0\), a map from the open source ball, exact basepoint, strict supremum distortion, and open \(\varepsilon\)-neighborhood coverage of the open \((R-\varepsilon)\)-ball. Extracted and visually inspected.
- The following discussion on printed page 273/PDF page 288: the separate standing restriction to complete limit spaces, and the warning that closed-ball convergence needs a length qualification. Extracted and visually inspected.

The retained July 6, 2024 BBI author correction sheet was also reopened, rehashed, and its complete page 9 was extracted and visually inspected:

    GEOMETRIZATION_BLUEPRINT/references/bbi-errata-2024-07-06.pdf
    68338c7a8b37b8637efbad8af5f547f6cf789675df020fbc6aa04d4babdde42e

Page 9 requires the uniform diameter assumption in Exercise 8.1.2(1) and changes the two occurrences of \(\varepsilon_n\) to \(\varepsilon\) on printed page 273. It gives no alteration of Definition 8.1.1's three tests. This is a check of that dated retained sheet, not a claim that the current remote sheet was fetched. The earlier complete correction review and convention comparison in reference_checks_revision59.md and reference_checks_revision60.md were reused.

The PDF skill was used for the reading and visual checks. A temporary Python environment and rendered pages were confined to /tmp/gc_bbi_source_435rc3; no repository dependency or archive file was changed. This development does not create or modify a PDF deliverable.

## Supremum distortion is actual supremum distortion

At DifferentialGeometry/Geometry/Metric/Approximation/BBIApproximation.lean:13,

    Metric.mapEDistortion

is the extended nonnegative supremum
\[
\operatorname{dis}_{\infty}(f)
 =\sup_{x,x'}\operatorname{ofReal}
    \left|d(f(x),f(x'))-d(x,x')\right|
 \quad\in[0,\infty].
\]

Using an extended value is essential for arbitrary maps on open balls: an unbounded set of errors cannot be assigned a spurious real supremum value. At every finite positive bound used by BBI, this is exactly the source's supremum-distortion condition.

The three public lemmas at lines 16, 20 and 25 prove that each pairwise error is bounded by the supremum, a uniform non-strict real error bound bounds the supremum, and a strict supremum bound implies every pairwise strict bound. The converse from pairwise strict bounds at the same error is deliberately not asserted: errors can approach a bound without attaining it.

## The exact finite-radius BBI data

At line 37,

    GC.MetricGeometry.PointedBBIApprox

contains \(R>0\), \(\varepsilon>0\), and a map
\[
f:B_X(p,R)\to Y
\]
with these three properties:

1. \(f(p)=q\) exactly.
2. \(\operatorname{dis}_{\infty}(f)<\operatorname{ofReal}(\varepsilon)\).
3. For every \(y\) with \(d_Y(y,q)<R-\varepsilon\), there exists \(x\in B_X(p,R)\) with \(d_Y(y,f(x))<\varepsilon\).

The third field is exactly the witnessed union-of-open-balls meaning of the source's open neighborhood. It does not require a nearest point, compact image, continuity, or attainment of an infimum. All distances in the open source ball are the ambient restricted metric.

There is no requirement \(\varepsilon<R\) in this BBI structure. If \(\varepsilon\ge R\), the target coverage ball is empty; the positive-radius domain, exact basepoint and strict distortion requirements still apply. BBI Definition 8.1.1 quantifies over these parameters too. The existing PointedOpenBallApprox and PointedBallApprox types have the additional \(\varepsilon<R\) requirement and are not renamed as this source definition.

## Fixed-parameter adapters with explicit slack

The following are actual compiling maps between the data types:

- PointedBBIApprox.pairwise_distortion, line 49, obtains the pairwise strict error from the actual supremum bound.
- PointedBBIApprox.toOpenBall, line 54, gives the existing pairwise-open approximation at the same \(R,\varepsilon\), provided \(\varepsilon<R\).
- PointedOpenBallApprox.toBBIApprox, line 73, converts an existing pairwise-open approximation of error \(\varepsilon\) into BBI data of error \(\eta\) for any strict enlargement \(\varepsilon<\eta\), on the same open radius-\(R\) ball. Indeed the supremum is at most \(\varepsilon<\eta\); the smaller target ball and larger covering error follow directly.
- PointedBBIApprox.toClosedBall, line 63, gives a closed-ball approximation of radius \(s\) and error \(2\varepsilon\) when \(2\varepsilon<s<R\), by applying the existing open-to-closed restriction proof.
- PointedBallApprox.toBBIApprox, line 93, takes closed-ball data of radius \(R\) and error \(\varepsilon\), with \(2\varepsilon<s<R\), and produces BBI data of radius \(s\) and error \(3\varepsilon\). The existing closed-to-open adapter first gives pairwise error \(2\varepsilon\); strict enlargement to \(3\varepsilon\) supplies the genuine strict supremum bound.

These adapters retain the actual function where the domains agree and explicitly restrict it when the domains change. No fixed-error equivalence between pairwise strict and supremum strict is claimed. No map is required to work at every radius or accuracy simultaneously.

## Raw BBI convergence and the complete-limit convention

At line 101,

    GC.MetricGeometry.BBIPointedGHConverges

states
\[
\forall R>0\ \forall\varepsilon>0,\quad
\text{for every sufficiently large }n,\
\operatorname{Nonempty}
  \bigl(\operatorname{PointedBBIApprox}(p_n,q,R,\varepsilon)\bigr).
\]

It does not include completeness of the target: that follows the literal Definition 8.1.1. The source introduces its complete-limit restriction separately on the next printed page.

The theorem bbiPointedGHConverges_iff_strict_threshold, line 133, proves that the filter-based eventual quantifier is equivalent to the source's literal form
\[
\forall R>0\ \forall\varepsilon>0\
\exists N\in\mathbb N\
\forall n>N,\quad
\operatorname{Nonempty}
  \bigl(\operatorname{PointedBBIApprox}(p_n,q,R,\varepsilon)\bigr).
\]
The natural-number indexing origin changes only a finite prefix.

PointedGHConverges.bbi, line 105, proves that project convergence supplies all these BBI tests. For arbitrary \(R,\varepsilon>0\), choose
\[
\delta=\min\{\varepsilon/2,R/2\}>0.
\]
The existing project-to-open convergence theorem supplies pairwise-open data at radius \(R\), error \(\delta<R\); the strict enlargement \(\delta<\varepsilon\) supplies BBI data. This proves even the tests with \(\varepsilon\ge R\).

PointedGHConverges.of_bbi, line 116, takes raw BBI convergence and a complete target. For \(0<\varepsilon<R\), its BBI tests yield the existing pairwise-open tests at that same error, and the existing all-radii open-to-closed convergence theorem supplies project convergence.

Consequently the exact equivalence at line 124 is

    GC.MetricGeometry.pointedGHConverges_iff_completeSpace_and_bbi

\[
\operatorname{PointedGHConverges}(p_n,q)
\quad\Longleftrightarrow\quad
\operatorname{CompleteSpace}(Y)\ \land\
\operatorname{BBIPointedGHConverges}(p_n,q).
\]

This is a full convergence equivalence with the source's complete-limit convention, with the completeness distinction explicit. It neither claims that raw BBI convergence forces completeness nor adds source properness, compactness, or length assumptions.

## Verification

The actual pinned Mathlib ENNReal supremum and ofReal APIs were used; no new supremum axiom or finite-distortion assumption was introduced.

Ran:

    lake build DifferentialGeometry.Geometry.Metric.Approximation.BBIApproximation

The scoped build passed with 1,250 Lake jobs, new leaf 917 ms, without warnings. This is not a full DifferentialGeometry root build.

Toolchain: Lean 4.35.0-rc3, compiler commit 470d5ce1400764999581fd26d5d72b00d990b0f4, arm64-apple-darwin24.6.0. Mathlib commit c55e6e786f49471c72fbddbec5415808896aec1e.

Lean stdin checked the new scalar definition, the raw convergence definition, all adapter definitions and all public theorems. No axiom closure contains an admission or a custom axiom; the proof closures are contained in:

    propext, Classical.choice, Quot.sound

The successful smoke check explicitly tested \(R=1,\varepsilon=2\) on the constant real-line sequence, ruled out zero-error BBI data through its actual positive-error field, and consumed raw BBI convergence with a complete target to obtain PointedGHConverges.

Source SHA256:

    c812d3b6d9c406e9cea17ea8ebf7c10032100ba7d14e252a1db5c8c614112bd5

The Lean source contains no comments, docstrings, admissions, or custom axioms. Existing approximation/convergence leaves were imported and left unchanged.
