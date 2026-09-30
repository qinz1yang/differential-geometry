# Polynomial covering bounds imply Hausdorff dimension bounds

This development proves AC39 using Mathlib's actual Hausdorff measure and Hausdorff dimension. It supplies the measure-theoretic consumer needed by AC40; it does not produce the geometric covering bounds assumed by AC38 or assume a dimension bound for a pointed limit.

## Source and contract checks

The source statement and its proof were read in `docs/geometrization/blueprint/master207A.tex`, lines 4109–4160. The file's SHA256 is:

    277359ee147d25184d4b38b20a91ee44a394fd6ea316cfc368fab74e06bef79b

The unchanged source reading recorded in `GEOMETRIZATION_BLUEPRINT/reference_checks_revision70.md` was reused after reading that record. It concerns Burago–Burago–Ivanov, *A Course in Metric Geometry*, AMS 2001:

- Definition 1.7.7 and Proposition 1.7.8, printed pages 19–20/PDF pages 34–35: diameter covers, Hausdorff measure and countable subadditivity.
- Theorem 1.7.16, Definition 1.7.17 and Proposition 1.7.19, printed pages 22–23/PDF pages 37–38: the critical exponent and countable unions.

Archived book SHA256:

    4efaa168dcc83e7e9f5663d14824f9543104beab21642ca3830a5dd1c684c971

The source record's check of the retained July 6, 2024 author correction sheet was reused. Its SHA256 is:

    68338c7a8b37b8637efbad8af5f547f6cf789675df020fbc6aa04d4babdde42e

This is reuse of the dated, previously inspected record, not a fresh check of a moving remote errata file. The record identifies an exponent-direction issue in the printed proof as a project observation; it is not represented here as an author-issued correction. The Lean proof directly uses the positive exponent \(s-n\).

The pinned Mathlib definitions and the proofs of the used APIs were inspected in `Mathlib/MeasureTheory/Measure/Hausdorff.lean` and `Mathlib/Topology/MetricSpace/HausdorffDimension.lean`. In particular, the development uses the actual gauge \((\operatorname{ediam} U)^s\), the finite-cover liminf bound, `dimH_le`, isometric invariance, and countable-union formulas. There is no replacement definition of Hausdorff measure or dimension. The measure is the unnormalized diameter-power convention; multiplying it by a positive finite dimensional normalization factor does not change the vanishing statements proved here.

## Exact principal statement

The file is `DifferentialGeometry/Topology/MetricSpace/PolynomialCovering.lean`. At line 9,

    MeasureTheory.Measure.hausdorffMeasure_zero_of_polynomial_nets

has the following meaning. Let \(A\subseteq X\), where \(X\) is any metric space equipped with its Borel measurable structure. Let \(n,C,s\) be real numbers with \(n\ge0\), \(C>0\), and \(s>n\). Assume that, for every real \(0<\delta\le1\), there is a finite set \(F\subseteq X\) such that:

1. Every member of \(F\) belongs to \(A\).
2. \(|F|\le C\delta^{-n}\), as an inequality of real numbers.
3. For every \(x\in A\), some \(y\in F\) satisfies \(d_X(x,y)\le\delta\).

Then Mathlib's measure `hausdorffMeasure s A`, also written \(\mu_H[s](A)\), equals zero.

The single constant \(C\) works at all the stated scales. The centers can change with \(\delta\), and the hypotheses do not select coherent nets. All distances are the ambient metric, so this theorem applies directly to a closed ball as a subset of its target metric space. The set \(A\) need not be measurable, compact, closed, bounded by an independently supplied bound, or nonempty. No completeness or properness is assumed. The real exponent \(n\) is not restricted to an integer and may be zero.

At line 82,

    dimH_le_of_polynomial_nets

takes exactly the same hypotheses on \(A,n,C\) and the finite nets, with no \(s\), and concludes
\[
\dim_H A\le \operatorname{ofReal}(n).
\]
The right side is the nonnegative real \(n\) embedded in the extended nonnegative reals, which is Mathlib's codomain for Hausdorff dimension. This theorem requires no measurable-space instance: its proof installs the canonical Borel structure locally, as permitted by Mathlib's definition of `dimH`.

## Actual proof

Set \(\delta_k=(k+1)^{-1}\) and choose one of the supplied finite nets \(F_k\) for each \(k\). For each center \(y\in F_k\), use the covering set
\[
U_{k,y}=A\cap\overline B_X(y,\delta_k).
\]
The triangle inequality bounds every diameter by \(2\delta_k\), and the net hypothesis proves that these sets cover \(A\). Since \(s>n\ge0\), real-power monotonicity gives
\[
\begin{aligned}
\sum_{y\in F_k}(\operatorname{ediam}U_{k,y})^s
&\le |F_k|(2\delta_k)^s\\
&\le C\,2^s\delta_k^{s-n}\longrightarrow0.
\end{aligned}
\]
The formal sums and inequalities are in the extended nonnegative reals; the proof explicitly converts the finite real cardinality and power estimates. Both the maximal diameter and the sum tend to zero. Mathlib's `hausdorffMeasure_le_liminf_sum` then gives zero Hausdorff measure. For dimension, every nonnegative exponent larger than \(n\) has zero measure and therefore cannot have infinite measure; `dimH_le` yields the bound. The proof does not replace the measure by a covering-number surrogate.

The empty net and empty covering family are allowed. With \(n=0\), the final exponent is \(s>0\), so the same limit argument applies. The first selected scale is exactly \(\delta_0=1\), which the non-strict upper scale bound permits. No evaluation at \(\delta=0\) or claim about the critical measure \(\mu_H[n](A)\) is used.

## Whole spaces, restricted metrics, and countable unions

The remaining public declarations are:

| Line | Declaration | Exact additional use |
| --- | --- | --- |
| 101 | `MeasureTheory.Measure.hausdorffMeasure_univ_zero_of_polynomial_nets` | The whole-space form: finite nets in \(X\), without a redundant center-membership condition. |
| 112 | `MeasureTheory.Measure.hausdorffMeasure_zero_of_subtype_polynomial_nets` | Nets are finite sets of the subtype \(A\), with its inherited metric; the conclusion is the ambient measure of \(A\). |
| 123 | `MeasureTheory.Measure.hausdorffMeasure_iUnion_zero_of_polynomial_nets` | A countable family \(A_i\) has a common real exponent \(n\), but each member may have its own positive constant \(C_i\); the ambient measure of the union is zero for every \(s>n\). |
| 136 | `MeasureTheory.Measure.hausdorffMeasure_iUnion_zero_of_subtype_zero` | For every countable family \(A_i\) and every \(s\ge0\), zero \(s\)-measure of each entire subtype \(A_i\) implies zero ambient \(s\)-measure of their union. No polynomial-net hypothesis is imposed on this adapter. |
| 149 | `dimH_univ_le_of_polynomial_nets` | The corresponding whole-space dimension bound. |
| 159 | `dimH_le_of_subtype_polynomial_nets` | Polynomial nets in the inherited subtype metric bound the ambient dimension of \(A\). |
| 169 | `dimH_iUnion_le_of_polynomial_nets` | The countable-union dimension bound, with independent positive \(C_i\). |

The subtype map into \(X\) is an actual isometry. Its image of the whole subtype is exactly \(A\), so Mathlib's Hausdorff-measure and dimension invariance apply. The nonnegative exponent condition in isometric measure invariance is explicitly supplied. Countable subadditivity for null sets does not require those sets to be measurable. Empty members and an empty indexing type are permitted. The generic restricted-metric union theorem closes the separate clause of AC39 even when a member's measure vanishing was obtained by a different argument.

## Verification and boundary

Ran the scoped build:

    lake build DifferentialGeometry.Topology.MetricSpace.PolynomialCovering

The final build passed without warnings: 2,622 Lake jobs, with this leaf rebuilt in 1.5 seconds. This is not a full project build. Toolchain: Lean 4.35.0-rc3, compiler commit `470d5ce1400764999581fd26d5d72b00d990b0f4`; Mathlib commit `c55e6e786f49471c72fbddbec5415808896aec1e`.

`#print axioms` was run on all nine public declarations. Each closure is exactly:

    propext, Classical.choice, Quot.sound

Lean stdin additionally instantiated the polynomial theorem with the empty subset at \(n=0,C=1,s=1\), the dimension theorem with the singleton \(\{0\}\subset\mathbb R\) at \(n=0,C=1\), and the generic countable union theorem with actual restricted-metric measure hypotheses. A separate agent independently read the proof, rebuilt the leaf, and checked all nine axiom closures; it reported no mathematical defect.

The Lean source has no admissions, custom axioms, comments or docstrings. SHA256:

    ec8be7807bbc24806d7b48272ad1ba5f0bd515fc8a8ba43bee2a220bfa1f2775

Only this leaf and its notes were authored for this task. AC38's geometric and pointed-limit net production and AC40's application to the actual limit are separate consumers/producers; these theorems neither assume those results nor certify their premises automatically.
