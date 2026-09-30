# Global approximation bounds and pointed-to-compact convergence

This development proves the forward Gromov–Hausdorff estimate in MC05 and the bounded-diameter pointed-to-compact convergence implication MC11. It proves neither the remaining converse of MC05 nor all of its global inverse-map estimates.

## Source and correction record

Freshly read the full MC05 statement and proof at docs/geometrization/blueprint/master207A.tex:959–986, and the MC11 statement, proof and uniform-diameter warning at lines 1209–1231. These occur in the source with SHA256:

    277359ee147d25184d4b38b20a91ee44a394fd6ea316cfc368fab74e06bef79b

Reused the unchanged source checks in the surrounding worktree's GEOMETRIZATION_BLUEPRINT/reference_checks_revision58.md and reference_checks_revision59.md. The first records reading BBI Definition 7.3.27, Corollary 7.3.28 and its estimates, Remark 7.3.29, and Theorem 7.3.30 with proof, printed pages 258–259/PDF pages 273–274. Corollary 7.3.28 is the approximation estimate cited by MC05; Theorem 7.3.30 gives neighboring separation/isometry context, not an additional unproved adapter.

The second check records the July 6, 2024 BBI author erratum on page 9 for Exercise 8.1.2(1), printed page 272/PDF page 287: a uniform source diameter bound is required. It also records the fixed-error correction in the following discussion on printed page 273/PDF page 288. The present theorem explicitly retains one bound uniform in every source index. The archived AMS 2001 BBI book hash is:

    4efaa168dcc83e7e9f5663d14824f9543104beab21642ca3830a5dd1c684c971

The retained July 6, 2024 correction-sheet hash is:

    68338c7a8b37b8637efbad8af5f547f6cf789675df020fbc6aa04d4babdde42e

The archived book and remote errata were not reopened this turn. Those are reused source checks for unchanged contracts, not a new assertion about the current online correction sheet. The reference archive is unchanged.

Freshly read the full actual Mathlib theorem and proof ghDist_le_of_approx_subsets, Mathlib/Topology/MetricSpace/GromovHausdorff.lean:538–619. It permits non-strict covering and distortion estimates without continuity of its comparison map. Its proof introduces an arbitrary positive gluing slack and removes it at the end; this permits a zero final error parameter. The source was inspected at Mathlib commit:

    c55e6e786f49471c72fbddbec5415808896aec1e

The file hash is:

    ce374a2cf004786a7beefbfe911108cf11f44e39e7a4cc48f88a2714b933273d

The PointedBallApprox structure and PointedGHConverges definition were also read directly. This implementation uses their actual closed-ball, strict-error, exact-basepoint contracts. It does not identify them with BBI's fixed-parameter open-ball convention.

## MC05's forward estimate

At DifferentialGeometry/Geometry/Metric/Approximation/CompactComparison.lean:11,

    GromovHausdorff.ghDist_le_of_map

takes nonempty compact metric spaces \(X,Y\), a real number \(\varepsilon\), and an arbitrary function \(f:X\to Y\). Its two hypotheses are:

\[
\forall x,x'\in X,\quad
\left|d_Y(f(x),f(x'))-d_X(x,x')\right|\le\varepsilon,
\]
\[
\forall y\in Y\ \exists x\in X,\quad d_Y(y,f(x))\le\varepsilon.
\]

It proves \(d_{GH}(X,Y)\le 3\varepsilon/2\). No continuity of \(f\) is assumed.

An explicit \(\varepsilon>0\) hypothesis is unnecessary for this forward estimate. Both spaces are nonempty, so the distortion hypothesis at \(x=x'\) forces \(\varepsilon\ge0\). In particular, \(\varepsilon=0\) is allowed and makes \(f\) an onto distance-preserving map. This is a valid extension of the blueprint's positive-error forward statement, proved by the same existing gluing estimate rather than treated as an extra assumption.

The proof applies Mathlib's estimate to the subset \(s=X\), source-cover error zero, distortion error \(\varepsilon\), and target-cover error \(\varepsilon\). Its bound becomes
\[
0+\frac{\varepsilon}{2}+\varepsilon
  =\frac{3\varepsilon}{2}.
\]

## Consuming an actual pointed approximation

At CompactComparison.lean:30,

    GC.MetricGeometry.PointedBallApprox.ghDist_le_of_global

takes an existing approximation \(f:\overline B_X(p,R)\to Y\) with error \(\varepsilon\), between nonempty compact metric spaces, and the explicit additional bounds
\[
\forall x\in X,\ d_X(x,p)\le R,
\qquad
\forall y\in Y,\ d_Y(y,q)\le R-\varepsilon.
\]

It proves \(d_{GH}(X,Y)\le3\varepsilon/2\) by applying the preceding global-map theorem to the function on all of \(X\) obtained by inserting each \(x\) into the closed-ball subtype.

The two displayed hypotheses do the work needed to pass from local pointed data to a global compact comparison: the source ball contains every source point, and the target ball for which coverage is promised contains every target point. The existing strict distortion and coverage bounds imply the non-strict bounds used above. All subtype distances remain the original ambient distances. PointedBallApprox itself still requires \(0<\varepsilon<R\); this consumer does not change that definition.

## MC11: one uniform diameter bound

At CompactComparison.lean:44,

    GC.MetricGeometry.PointedGHConverges.tendsto_ghDist_of_uniform_diam

takes nonempty compact metric spaces \(X_i,Y\), basepoints \(p_i\in X_i\), \(q\in Y\), and:

- PointedGHConverges \(p_i\) \(q\), meaning \(Y\) is complete and, for every pair \(0<\eta<R\), all sufficiently large indices admit the actual PointedBallApprox \(p_i\) \(q\) \(R\) \(\eta\);
- one real number \(D\) for which \(\operatorname{diam}X_i\le D\) for every \(i\).

It proves convergence along the original sequence:
\[
d_{GH}(X_i,Y)\longrightarrow0.
\]

Compactness of every source and of the target is an explicit hypothesis. Completeness of the target is also already included in PointedGHConverges; no separate completeness assumption or new limiting space is introduced. The conclusion is convergence to this supplied \(Y\), with its supplied metric.

For a desired tolerance \(\varepsilon>0\), the proof sets
\[
R=\max\{D,\operatorname{diam}Y\}+\varepsilon+1
\]
and uses the eventual pointed approximation with error \(\eta=\varepsilon/2\). Compactness makes the real diameters bound all the relevant pairwise distances, so every source point has radius at most \(R\) and every target point has radius at most \(R-\eta\). The preceding consumer gives
\[
d_{GH}(X_i,Y)\le\frac32\,\frac{\varepsilon}{2}
  =\frac34\varepsilon<\varepsilon
\]
for every sufficiently large \(i\).

No \(D>0\) assumption is introduced. The source diameter hypotheses already imply \(D\ge0\), and the proof includes \(D=0\). The uniformity in \(i\) is essential and remains explicit; compactness of each source separately is not substituted for it. The blueprint's escaping-point counterexample is not needed by this proof and is not implemented here.

## Verification

Ran:

    lake build DifferentialGeometry.Geometry.Metric.Approximation.CompactComparison

The scoped build passed with 2,165 Lake jobs; the new leaf built in 1.2 seconds. This is not a full DifferentialGeometry root build.

The toolchain is Lean 4.35.0-rc3, compiler commit 470d5ce1400764999581fd26d5d72b00d990b0f4, arm64-apple-darwin24.6.0. The Mathlib commit is given above.

Lean stdin checked all three public theorems' axiom closures. Each contains exactly:

    propext, Classical.choice, Quot.sound

The same successful check used the global-map theorem with \(\varepsilon=0\) and an arbitrary isometry equivalence between nonempty compact spaces, obtaining \(d_{GH}(X,Y)\le0\). It also used the convergence theorem on the constant sequence of one-point spaces with \(D=0\). These checks create no Lean module outside DifferentialGeometry.

CompactComparison.lean SHA256:

    29ff361b29509659a86dd9c3787f4954586fc52b5b173eb26fe00dc055c5d681

PointedConvergence.lean as consumed by this check had SHA256:

    5db64a4e6f759d31efed85046fa990d555f8b379aba5cee255773a17e9c7d79f

All three statements have complete proofs. The source contains no comments, docstrings, admissions, or custom axioms. It imports the shared PointedConvergence development and the existing Mathlib Gromov–Hausdorff source; no foundational compactness or quotient theory is rebuilt.

MC05's global inverse-map estimates and the converse from a GH bound to an approximating map remain outside this leaf. Its proved forward estimate is sufficient for the fully proved MC11 implication.
