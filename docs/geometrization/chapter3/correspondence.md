# Sharp correspondences and global approximate inverses

This leaf proves the sharp correspondence formula in MC04, including attainment for compact spaces, and the global inverse/converse clauses of MC05. The forward MC05 estimate was already proved in CompactComparison.lean. All results use Mathlib's existing ghDist and GHSpace.

## Reuse and source audit

Freshly read the correspondence definition, theorem, proof decomposition and MC05 at docs/geometrization/blueprint/master207A.tex:915–986. The source hash is:

    277359ee147d25184d4b38b20a91ee44a394fd6ea316cfc368fab74e06bef79b

Reused the unchanged primary-source reading in GEOMETRIZATION_BLUEPRINT/reference_checks_revision58.md and correction record reference_checks_revision59.md in the surrounding worktree. The source passages are BBI's definitions of correspondence/distortion, Theorem 7.3.25 and the adjacent Exercise 7.3.26, printed pages 256–258/PDF pages 271–273, followed by Corollary 7.3.28, Remark 7.3.29 and Theorem 7.3.30, printed pages 258–259/PDF pages 273–274.

The archived AMS 2001 book hash is:

    4efaa168dcc83e7e9f5663d14824f9543104beab21642ca3830a5dd1c684c971

The retained July 6, 2024 BBI erratum hash is:

    68338c7a8b37b8637efbad8af5f547f6cf789675df020fbc6aa04d4babdde42e

No fresh book or remote erratum reading is claimed. These are reused recorded checks for the same contracts; BooksPapers remains unchanged.

A search of the pinned Mathlib metric/Gromov–Hausdorff files found no theorem already giving the relation-based correspondence formula. The existing approximate-subset estimate gives the weaker global-map constant \(3\varepsilon/2\); it does not by itself give the sharp half-distortion estimate for an arbitrary relation. A relation is not assumed to be the graph of a function.

The following actual Mathlib source was freshly inspected at commit c55e6e786f49471c72fbddbec5415808896aec1e:

- Metric/Gluing.lean:69–191: the definition of glueDist, exact cross-distance for paired points, both cross-triangle arguments, and glueMetricApprox. It accepts an arbitrary nonempty index type and two maps; it does not require their pairing relation to be closed, functional, or continuous.
- Metric/GromovHausdorffRealized.lean:479–512: OptimalGHCoupling, its two isometric injections and compactness.
- Metric/GromovHausdorff.lean:238–373: the complete proof that the optimal coupling's Hausdorff distance equals the existing ghDist.
- Metric/HausdorffDistance.lean:611–614 and 724–748: compact attainment of point-to-set distance and the Hausdorff covering inequalities, including their boundedness/nonemptiness qualifications.

The paths in this list abbreviate Mathlib/Topology/MetricSpace. Source hashes are:

    Gluing.lean:
    8346d54a08917b348ee8bfba83d6b8cb27246f3f1b46dfa5d7925cbc45dd9abb
    GromovHausdorffRealized.lean:
    da32e66a9fec2b67ae7865f7f9e95bc98861ec2bcae78577543a81da416f516f
    GromovHausdorff.lean:
    ce374a2cf004786a7beefbfe911108cf11f44e39e7a4cc48f88a2714b933273d
    HausdorffDistance.lean:
    9bdca849e0d34aee7a027af90d5d0fc5ba04b9a0742ed2c882ed577904fe41f9

The full internal construction of every imported metric theorem was not re-proved. The new theorems apply those actual existing declarations and their complete axiom closures were checked.

## Actual distortion of a relation

At DifferentialGeometry/Geometry/Metric/Approximation/Correspondence.lean:12,

    GromovHausdorff.correspondenceDistortion

is defined for a relation \(r:X\to Y\to\mathrm{Prop}\) between compact metric spaces by the actual real supremum
\[
\operatorname{dis}(r)=
\sup\left\{
\left|d_X(x,x')-d_Y(y,y')\right|:
r(x,y),\ r(x',y')
\right\}.
\]

The compact-space assumptions are explicit in this definition's Lean type. A private proof bounds its set of errors by \(\operatorname{diam}X+\operatorname{diam}Y\). The definition permits arbitrary relations, but the correspondence theorems require both projections to be onto and the spaces to be nonempty. In those applications the error set contains zero, so no empty-supremum convention enters the formula.

The public lemmas dist_error_le_correspondenceDistortion at line 31 and correspondenceDistortion_le at line 37 prove the two needed supremum directions. The first requires compact spaces and actual pairs in the relation; it needs no separate nonempty-space hypotheses. The second requires nonempty \(X\), a partner for every \(x\), and an upper bound on every pairwise error; it does not require that every \(y\) have a partner.

No new definition of Gromov–Hausdorff distance or isometry-class space is introduced.

## The sharp upper bound

At line 49,

    GromovHausdorff.ghDist_le_half_of_correspondence

takes nonempty compact metric spaces \(X,Y\), a relation \(r\), and the three explicit premises
\[
\forall x\in X\ \exists y\in Y,\ r(x,y),
\qquad
\forall y\in Y\ \exists x\in X,\ r(x,y),
\]
\[
\forall (x,y),(x',y')\in r,\quad
|d_X(x,x')-d_Y(y,y')|\le D.
\]
It proves \(d_{GH}(X,Y)\le D/2\).

There is no closedness or continuity assumption on \(r\), no requirement that it be single-valued, and no explicit \(D>0\) assumption. The nonempty relation and diagonal error force \(D\ge0\).

For an arbitrary \(\delta>0\), the proof uses the full relation as the index type for Mathlib's approximate gluing. Its coordinate projections map into \(X\) and \(Y\). With gluing length \(D/2+\delta>0\), the supplied distortion bound is at most twice that length. The two original metrics embed isometrically into the resulting metric on the disjoint union. Every point has a relation partner exactly that cross-distance away, so the Hausdorff distance is at most \(D/2+\delta\). Removing \(\delta\) gives the exact half bound, also when \(D=0\).

## Optimal relation and half-infimum formula

At line 86,

    GromovHausdorff.exists_correspondence_distortion_le_twice_ghDist

produces a relation whose two projections are onto and whose every pairwise error is at most \(2d_{GH}(X,Y)\).

It uses Mathlib's optimal coupling and defines the relation by
\[
r(x,y)\quad\Longleftrightarrow\quad
d\bigl(\iota_X(x),\iota_Y(y)\bigr)\le d_{GH}(X,Y).
\]
The two images are nonempty compact sets. Compact nearest-point attainment and the exact optimal Hausdorff distance supply both onto projections at this non-strict threshold. Triangle inequalities and the isometry identities give the distortion bound. This includes \(d_{GH}=0\); it does not rely on an unjustified strict witness at the optimum.

The following public consequences are genuine applications of the two directions:

- ghDist_le_half_iff_exists_correspondence, line 125: for any real \(D\), \(d_{GH}(X,Y)\le D/2\) if and only if an onto-pair relation exists with every pairwise error at most \(D\).
- exists_correspondence_distortion_eq_twice_ghDist, line 139: there is such a relation with actual supremum distortion exactly \(2d_{GH}(X,Y)\).
- ghDist_eq_half_sInf_correspondenceDistortion, line 149:
  \[
  d_{GH}(X,Y)
    =\frac12\inf_{\substack{r\subseteq X\times Y\\
                           r\text{ projects onto }X,Y}}
          \operatorname{dis}(r).
  \]

The last statement uses the set of real distortion values of actual onto relations. The proof establishes that this set is nonempty, that \(2d_{GH}\) is a lower bound, and that \(2d_{GH}\) belongs to the set. Thus both the real infimum and its attainment are justified. The existing MetricSpace GHSpace instance continues to supply the metric axioms on isometry classes.

## MC05's converse map

At line 168,

    GromovHausdorff.exists_map_of_ghDist_lt

takes nonempty compact metric spaces and \(d_{GH}(X,Y)<a\). It produces a function \(f:X\to Y\) with
\[
\forall x,x',\
|d_Y(f(x),f(x'))-d_X(x,x')|\le2a,
\]
\[
\forall y\in Y\ \exists x\in X,\quad d_Y(y,f(x))\le2a.
\]

The proof chooses one partner for each \(x\) in the optimal relation. To cover an arbitrary \(y\), choose its relation partner \(x\); comparing the two relation pairs \((x,y)\) and \((x,f(x))\) gives the desired distance estimate. No continuity of this chosen map is asserted. The assumption automatically forces \(a>0\).

## MC05's global inverse estimates

At line 192,

    Metric.exists_approximate_inverse_of_map

takes arbitrary metric spaces \(X,Y\), a function \(f:X\to Y\), and the same non-strict distortion and coverage bounds \(\varepsilon\) as the forward global-map estimate. It produces \(g:Y\to X\) with
\[
d_Y(f(g(y)),y)\le\varepsilon,\qquad
d_X(g(f(x)),x)\le2\varepsilon,
\]
\[
|d_X(g(y),g(y'))-d_Y(y,y')|\le3\varepsilon.
\]

It chooses the supplied coverage witness for each \(y\). The first estimate is that witness's property; the second uses the distortion of \(f\) on \(g(f(x)),x\); the third inserts \(f(g(y))\) and \(f(g(y'))\) into the triangle inequalities and uses the same distortion bound.

This inverse theorem requires neither compactness, completeness, source/target nonemptiness as separate assumptions, nor continuity. It does not explicitly require \(\varepsilon>0\), so exact inverses at \(\varepsilon=0\) are included. If both spaces are empty, the function and estimate conclusions are correctly vacuous; the theorem does not assume a choice of an element of an empty space.

Together with ghDist_le_of_map in CompactComparison.lean, these two results prove all three substantive clauses of MC05.

## Verification

Ran the final scoped build:

    lake build DifferentialGeometry.Geometry.Metric.Approximation.Correspondence

It passed with 2,166 Lake jobs, new leaf 1.3 seconds, without warnings. This was not a full DifferentialGeometry root build.

Toolchain: Lean 4.35.0-rc3, compiler commit 470d5ce1400764999581fd26d5d72b00d990b0f4, arm64-apple-darwin24.6.0. The Mathlib pin is recorded above.

Lean stdin checked the distortion definition and all nine public theorems. Every axiom closure is exactly:

    propext, Classical.choice, Quot.sound

The successful smoke checks supplied the equality correspondence with \(D=0\) on an arbitrary nonempty compact metric space, applied the inverse theorem to the identity of the real line at \(\varepsilon=0\), and instantiated optimal-distortion attainment on a singleton pair where the distortion is zero.

Source SHA256:

    8f1450a47a48753193b41148789e2b5d9a30128de05b40868a1ce308db5a5820

The source has no comments, docstrings, admissions, or custom axioms. This leaf proves the sharp correspondence and global inverse/converse steps; it does not alter any geometric producer or formalize a new GH foundation.
