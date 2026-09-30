# Compact Gromov–Hausdorff extraction from uniform finite nets

This development proves the compact metric extraction statement MC12 of blueprint 207 by adapting the existing Mathlib Gromov compactness theorem. It does not prove the pointed eventual-net extraction theorem MC13 or produce geometric packing bounds.

## Source record

Freshly read the complete MC12 statement and distance-matrix proof at docs/geometrization/blueprint/master207A.tex:1264–1309. The source hash is:

    277359ee147d25184d4b38b20a91ee44a394fd6ea316cfc368fab74e06bef79b

Reused the unchanged primary-source comparison in GEOMETRIZATION_BLUEPRINT/reference_checks_revision61.md, in the surrounding worktree. That record identifies Burago–Burago–Ivanov, A Course in Metric Geometry, AMS 2001: Definition 7.4.13 on printed page 263/PDF page 278, Theorem 7.4.15 and its proof on printed page 264/PDF page 279, and the finite-net definitions and moving-center issue on printed pages 13–14/PDF pages 28–29. The archived book hash recorded there is:

    4efaa168dcc83e7e9f5663d14824f9543104beab21642ca3830a5dd1c684c971

The same record checked the retained July 6, 2024 BBI correction sheet, hash:

    68338c7a8b37b8637efbad8af5f547f6cf789675df020fbc6aa04d4babdde42e

It records the finite-subset limit correction on printed page 263, the factor-two correction when moving centers into a subset, and no correction to the selected Theorem 7.4.15. This implementation does not move external centers into a space: every supplied center already lies inside its own space, and transport is by an isometry. The book and remote errata were not freshly reopened this turn; these are explicitly reused checks, not a claim that a moving online erratum has been reverified. BooksPapers remains unchanged.

Freshly inspected the actual target Mathlib source at commit:

    c55e6e786f49471c72fbddbec5415808896aec1e

In Mathlib/Topology/MetricSpace/GromovHausdorff.lean, the relevant declarations are GHSpace.Rep at line 97, GHSpace.toGHSpace_rep at line 134, toGHSpace_eq_toGHSpace_iff_isometryEquiv at line 142, ghDist at line 176, totallyBounded at line 735, and the CompleteSpace GHSpace instance beginning at line 938. The full total-boundedness proof and the representative/isometry interfaces were read, along with the completeness implementation's construction and conclusion. File hash:

    ce374a2cf004786a7beefbfe911108cf11f44e39e7a4cc48f88a2714b933273d

The proof also applies the existing general IsCompact.tendsto_subseq theorem in Mathlib/Topology/Sequences.lean:298. No new Gromov–Hausdorff distance, quotient, completion, or compactness foundation is introduced.

## Exact mathematical contract

Both public theorems take a sequence \((X_i)_{i\in\mathbb N}\) of nonempty compact metric spaces. The types may live in any one Lean universe, and may vary with \(i\). They take a real number \(D\) and these two hypotheses:

1. For every \(i\), the diameter of the whole space \(X_i\) is at most \(D\).
2. For every real \(\varepsilon>0\), there exists one natural number \(N\) such that, for every \(i\), there is a finite set \(S\subseteq X_i\) with \(|S|\le N\) and
   \[
   \forall x\in X_i\ \exists y\in S:\quad d_{X_i}(x,y)\le\varepsilon.
   \]

The finite sets are Finset (X i), so their centers are in the actual metric space \(X_i\). The coverage bound is non-strict. The order of quantifiers is exactly
\[
\forall\varepsilon>0\ \exists N\ \forall i\ \exists S.
\]
In particular, the bound \(N\) is uniform in the entire sequence at a fixed scale. Neither a prechosen modulus nor a monotone modulus is an extra hypothesis. No completeness assumption needs to be separately supplied, because each \(X_i\) is already assumed compact.

The diameter is Mathlib's real-valued Metric.diam of the entire space. Its possible behavior on unbounded sets causes no weakening here, because compactness ensures boundedness. No explicit \(D>0\) is imposed; the zero-diameter case is included. Since \(D\) is a real number, its finiteness is built into its type.

## Public declarations and proof

At DifferentialGeometry/Topology/MetricSpace/GromovHausdorffCompactness.lean:17,

    GromovHausdorff.totallyBounded_range_toGHSpace_of_uniform_finite_nets

proves that the set of isometry classes \(\{[X_i]:i\in\mathbb N\}\) is totally bounded in Mathlib's metric space GHSpace.

The proof chooses \(r_n=1/(n+1)\), applies the supplied net hypothesis at \(r_n/2\), and chooses the resulting cardinal bound \(K(n)\). It does not require that the user supply this choice as additional data.

For each \(i\), a private helper produces an actual isometry equivalence
\[
X_i\cong \operatorname{Rep}([X_i]).
\]
It transports the diameter bound and each chosen net to that representative. An isometric image of a finite set has no larger cardinality. Since
\[
d(x,y)\le r_n/2<r_n,
\]
the transported set supplies the open radius-\(r_n\) ball cover required by Mathlib's GromovHausdorff.totallyBounded. This half-scale step is essential: it does not silently replace a non-strict net bound by a strict bound at the same scale.

At DifferentialGeometry/Topology/MetricSpace/GromovHausdorffCompactness.lean:55,

    GromovHausdorff.exists_subsequence_ghDist_tendsto_zero_of_uniform_finite_nets

proves that there exist a strictly increasing map \(\varphi:\mathbb N\to\mathbb N\) and \(p\in\mathrm{GHSpace}\) such that
\[
d_{GH}(X_{\varphi(j)},p.\mathrm{Rep})\longrightarrow 0.
\]

The output \(p.\mathrm{Rep}\) is an actual metric-space type, with existing Nonempty, CompactSpace, and MetricSpace instances. It is a concrete choice of the \(X_\infty\) required by MC12, rather than merely a statement that a formal quotient has a limit. GHSpace.Rep lives in the lowest type universe; the isometry interfaces allow the input spaces to live in a larger universe.

This second theorem is a genuine downstream use of the first. Completeness of GHSpace makes the closure of its totally bounded range compact. Sequential compactness yields \(p\), a strictly increasing \(\varphi\), and convergence of the isometry classes to \(p\). The definition of ghDist and the proved identity \([p.\mathrm{Rep}]=p\) give exactly the displayed metric convergence.

No length-space hypothesis, curvature hypothesis, connectedness, boundary condition, marked point, uniqueness of the limiting representative, or convergence rate is asserted or needed. No strict subsequence quantifier was dropped, and the finite-net requirement applies at every positive scale.

## Verification actually performed

Ran the scoped build in the isolated GC_CHAPTER3_435_RC3 checkout:

    lake build DifferentialGeometry.Topology.MetricSpace.GromovHausdorffCompactness

It passed: 2,160 Lake jobs, with the new leaf built in 1.2 seconds. This is a targeted dependency build, not a full DifferentialGeometry root build.

Toolchain: Lean 4.35.0-rc3, compiler commit 470d5ce1400764999581fd26d5d72b00d990b0f4, arm64-apple-darwin24.6.0. The Mathlib pin is given above.

Lean stdin checks inspected both public theorems' axiom closures. Each is exactly:

    propext, Classical.choice, Quot.sound

The final stdin smoke check also instantiated the subsequence theorem on the constant sequence of one-point spaces with \(D=0\), and on an arbitrary sequence satisfying the hypotheses with \(D=0\). This exercises the nonempty, zero-diameter corner without imposing \(D>0\). No test file or Lean module was placed outside DifferentialGeometry.

Source SHA256 at verification:

    3cb92746dad3e670a6d9e6f3313568f7ba2ea170c3653c7f3927526e9a3353cc

The Lean source contains no comments, docstrings, admissions, or custom axioms. Its two public theorems depend only on Mathlib and the proved helper. The module stays in its natural Topology/MetricSpace home and uses Mathlib's existing GromovHausdorff namespace. Root aggregate registration is left to the coordinating task.

The result closes MC12's compact extraction interface. It does not claim the additional basepoint control, eventual bounds, simultaneous ball compatibility, length closure, or geometric producer needed by subsequent blueprint nodes.
