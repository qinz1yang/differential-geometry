# Compact convergence of closed balls in a proper length limit

This leaf proves MC15 through actual target metric segments, then supplies compiling consumers from approximate midpoints and from arbitrarily short continuous curves. The source spaces are assumed proper but are never assumed to be length spaces or geodesic spaces.

## Source and reuse record

Freshly read the full MC15 statement, radial-trimming proof and counterexample at docs/geometrization/blueprint/master207A.tex:1706–1736. The source hash is:

    277359ee147d25184d4b38b20a91ee44a394fd6ea316cfc368fab74e06bef79b

Reused the unchanged source checks in GEOMETRIZATION_BLUEPRINT/reference_checks_revision58.md and reference_checks_revision68.md in the surrounding worktree. These record BBI's pointed Definitions/Exercises 8.1.1–8.1.5, printed pages 272–273/PDF pages 287–288, and Theorem 2.4.16 with the midpoint/geodesic qualifications, printed pages 42–43/PDF pages 57–58. Revision 68 explicitly records the MC23 radial-geodesic dependency used by MC15.

The archived AMS 2001 BBI book hash is:

    4efaa168dcc83e7e9f5663d14824f9543104beab21642ca3830a5dd1c684c971

The retained July 6, 2024 author correction-sheet hash is:

    68338c7a8b37b8637efbad8af5f547f6cf789675df020fbc6aa04d4babdde42e

The revision 68 check records the finite-distance qualification and the corrected local-compactness preamble near the midpoint theorem, along with the Chapter 8 uniform-diameter and fixed-error corrections. The book and remote correction sheet were not freshly reopened in this implementation. These are reused documented checks, and the archive remains unchanged.

Freshly read the actual local segment producer Metric.exists_metric_segment_of_approximate_midpoints at DifferentialGeometry/Topology/MetricSpace/GeodesicMidpoint.lean:216 and the actual curve producer Metric.approximate_midpoints_of_arbitrarily_short_curves at DifferentialGeometry/Topology/MetricSpace/CurveMidpoint.lean:47. The latter file's full elementary proof was read. The shared CompactComparison theorem used here was separately source-checked and compiled; see compact_comparison.md.

No abstract “length space” predicate is silently substituted for these interfaces. The length corollary below uses explicit continuous curves and Mathlib's actual extended variation as their length.

## Radial trimming

At DifferentialGeometry/Geometry/Metric/Approximation/ClosedBallConvergence.lean:12,

    Metric.exists_radial_trimming_of_metric_segments

assumes that any two target points \(a,b\) admit a continuous map \(f:[0,1]\to Y\), with the correct endpoints, such that
\[
d(f(s),f(t))=d(a,b)|s-t|
\qquad (s,t\in[0,1]).
\]
Given \(q,y\in Y\), \(r\ge0\), \(\delta\ge0\), and
\[
d(y,q)\le r+\delta,
\]
it produces \(z\in Y\) with
\[
d(z,q)\le r,\qquad d(y,z)\le\delta.
\]

If \(y\) already lies in the ball, take \(z=y\). Otherwise \(d(q,y)>r\ge0\), so the proof evaluates the segment from \(q\) to \(y\) at \(r/d(q,y)\). The exact segment identity gives radius \(r\) and movement \(d(q,y)-r\le\delta\). The proof handles \(r=0\), \(\delta=0\), and coincident endpoints without division by zero. This radial lemma itself needs no properness.

At line 45, BallCarrier.compactSpace adapts the existing compactness of a closed ball in a proper metric space to the project's definition
\[
\operatorname{BallCarrier}(p,R)=\{x:d(x,p)\le R\}.
\]
This is the same closed subset and the same restricted ambient metric; no intrinsic path metric is introduced.

## Quantitative comparison of the closed balls

At line 50,

    GC.MetricGeometry.PointedBallApprox.ghDist_closedBall_le_of_metric_segments

takes proper metric spaces \(X,Y\), the target segment hypothesis above, and an actual PointedBallApprox from \(p\) to \(q\) of radius \(R\) and error \(\varepsilon\). In particular \(0<\varepsilon<R\), its source is the whole closed \(R\)-ball, its basepoint equality is exact, pairwise distortion is strictly less than \(\varepsilon\), and it covers the target closed \((R-\varepsilon)\)-ball with strict error \(\varepsilon\).

It proves
\[
d_{GH}\bigl(\overline B_X(p,R),\overline B_Y(q,R)\bigr)
\le\frac92\varepsilon.
\]

The leaf keeps explicit Nonempty instances for the two ball types in this estimate. Their nonemptiness follows from \(R>0\); the convergence theorem constructs these instances directly from \(p\) and \(q\). They are not an extra geometric assumption.

For each source point \(x\), radial distortion bounds the radius of its image by \(R+\varepsilon\). The proof trims this image into the target closed \(R\)-ball, moving it at most \(\varepsilon\), and calls the resulting map \(F\). Triangle inequalities show that \(F\) has distortion at most \(3\varepsilon\).

For each target point \(y\) in the closed \(R\)-ball, trim \(y\) inward to radius at most \(R-\varepsilon\), moving at most \(\varepsilon\). The original approximation covers that new point, with a witness already in its closed \(R\)-ball domain. The witness's image is moved at most another \(\varepsilon\) by the first trimming. Hence \(F\) covers all of the target ball within \(3\varepsilon\). Applying the proved global-map estimate gives \(3(3\varepsilon)/2\).

This is a checked improvement of the blueprint's \(15\varepsilon/2\) estimate. The blueprint starts with a map on a larger ball and then has to control whether coverage preimages survive restriction. Here PointedGHConverges supplies a map directly on the requested radius \(R\), whose witnesses already lie in the desired source ball. Thus inward movement by \(\varepsilon\) suffices. The qualitative MC15 conclusion is unchanged.

The trimmed map need not be continuous, and no continuous radial projection is asserted.

## Three convergence interfaces

At line 97,

    GC.MetricGeometry.PointedGHConverges.tendsto_ghDist_closedBall_of_metric_segments

takes a sequence of proper pointed metric spaces \((X_n,p_n)\), a proper target \((Y,q)\), actual PointedGHConverges to that target, the segment hypothesis, and a fixed \(R>0\). It proves convergence on the original sequence:
\[
d_{GH}\bigl(\overline B_{X_n}(p_n,R),\overline B_Y(q,R)\bigr)
\longrightarrow0.
\]

For any tolerance \(\eta>0\), it chooses
\[
\varepsilon=\min\{\eta/10,R/2\}.
\]
The convergence hypothesis supplies radius-\(R\) approximations with that positive error for every sufficiently late index. The preceding bound is strictly below \(\eta\). Properness supplies compactness of both balls. Their inherited distances are the original ambient distances.

At line 127,

    GC.MetricGeometry.PointedGHConverges.tendsto_ghDist_closedBall_of_approximate_midpoints

has the same source, target and convergence assumptions, and replaces target segments by:
\[
\forall a,b\in Y\ \forall\eta>0\ \exists z\in Y:
\quad
d(a,z),d(b,z)\le d(a,b)/2+\eta.
\]
It applies the already proved MC23 segment producer and then the preceding theorem. This is an actual assembly proof, with the same target metric throughout.

At line 141,

    GC.MetricGeometry.PointedGHConverges.tendsto_ghDist_closedBall_of_arbitrarily_short_curves

replaces that midpoint premise by the following explicit length witnesses:
\[
\forall a,b\in Y\ \forall\eta>0\ \exists c:[0,1]\to Y,
\]
where \(c\) is continuous, \(c(0)=a\), \(c(1)=b\), and
\[
\operatorname{eVariationOn}(c,[0,1])
 <\operatorname{ofReal}\bigl(d(a,b)+\eta\bigr).
\]
The variation is Mathlib's extended-nonnegative-real curve length, and the endpoints are exact. The existing CurveMidpoint theorem supplies approximate midpoints from these witnesses, so the conclusion follows from the preceding corollary. This is the fully explicit proper-length-target route.

None of the three convergence statements assumes that a source ball is a length space, imposes a uniform bound on the diameters of whole source spaces, or compares their intrinsic path metrics. The target segment/length qualification is retained: the blueprint's two-point counterexample prevents removing it. The convergence theorems state \(R>0\); a separate zero-radius convergence theorem is not included.

## Verification

Ran the final scoped build:

    lake build DifferentialGeometry.Geometry.Metric.Approximation.ClosedBallConvergence

It passed with 2,176 Lake jobs and the new leaf built in 1.3 seconds, without warnings. This was not a full DifferentialGeometry root build.

The toolchain is Lean 4.35.0-rc3, compiler commit 470d5ce1400764999581fd26d5d72b00d990b0f4, arm64-apple-darwin24.6.0. Mathlib is pinned to c55e6e786f49471c72fbddbec5415808896aec1e.

Lean stdin checked all five public theorems and the ball compactness instance. Every axiom closure is exactly:

    propext, Classical.choice, Quot.sound

The same successful check instantiated the approximate-midpoint convergence consumer on a constant singleton sequence at \(R=1\), and instantiated radial trimming at \(r=\delta=0\) with coincident endpoints.

ClosedBallConvergence.lean SHA256:

    8bbef7b92e18ae1202310d5391825fd7f66780ba5d9490155734bd0038b75e48

The consumed GeodesicMidpoint.lean hash was:

    f4c50dc2ac90c6de96ad63da613ae01c39bd389aa2099913d1ee3b53f1d5f16d

The consumed CurveMidpoint.lean hash was:

    06eff33283a4f9fd79d121904dc77bcb1ecd144bb39c62531646df3376d87f1d

The new source has no comments, docstrings, admissions, or custom axioms. Its proofs use existing compactness, midpoint, segment, pointed approximation, and compact GH APIs without changing their mathematical carriers.
