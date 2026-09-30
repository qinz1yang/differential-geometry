# Countable labels from eventual ball nets

This leaf proves the labeling step in MC13's eventual-net construction. Its output is designed to feed the separately proved countable-label compactness theorem. It makes no completeness, properness, compactness, or length-space assumption on the source spaces.

## Source scope

Freshly read the eventual-net theorem and its whole constructive proof at docs/geometrization/blueprint/master207A.tex:1330–1446, especially the fixed-label and exceptional-prefix construction at lines 1350–1366. The blueprint hash is:

    277359ee147d25184d4b38b20a91ee44a394fd6ea316cfc368fab74e06bef79b

Reused the unchanged underlying source review in the surrounding worktree's GEOMETRIZATION_BLUEPRINT/reference_checks_revision61.md. That record checked BBI Theorem 7.4.15, printed page 264/PDF page 279, and Theorem 8.1.10 and its pointed outline, printed pages 274–275/PDF pages 289–290. It explicitly distinguishes the blueprint's arbitrary-source eventual-net extension from the proper-space statement in BBI.

The archived BBI book hash recorded there is:

    4efaa168dcc83e7e9f5663d14824f9543104beab21642ca3830a5dd1c684c971

The retained July 6, 2024 author erratum has hash:

    68338c7a8b37b8637efbad8af5f547f6cf789675df020fbc6aa04d4babdde42e

The source review records the finite-net and moving-center qualifications and no correction to the selected compactness statements. No book page or remote erratum was freshly reopened in this implementation; this is reuse of documented checks for an unchanged elementary labeling construction. The archive is unchanged.

The implementation uses the existing Mathlib Finset.equivFin at Mathlib/Data/Fintype/EquivFin.lean:320, at Mathlib commit c55e6e786f49471c72fbddbec5415808896aec1e. This identifies an actual finite set with the finite ordinal having the same cardinality. No enumeration theorem or metric foundation is postulated.

## Exact hypothesis

At DifferentialGeometry/Topology/MetricSpace/CountableNetLabels.lean:41,

    Metric.exists_countable_ball_net_labels_of_eventual_nets

takes a sequence of arbitrary metric spaces \(X_n\), points \(p_n\in X_n\), and precisely the following hypothesis:
\[
\forall R>0\ \forall\eta>0\ \exists N,I\in\mathbb N\
\forall n\ge I\ \exists S\subseteq X_n
\]
such that \(S\) is finite, \(|S|\le N\), all its centers satisfy \(d_n(y,p_n)\le R\), and
\[
\forall z\in X_n,\quad
d_n(z,p_n)\le R\ \Longrightarrow\
\exists y\in S,\ d_n(z,y)\le\eta.
\]

The cardinality bound and starting index are chosen before the source index. Each may depend on both the radius and the accuracy. The finite sets are actual Finset (X n), with their inside-ball condition explicit. Coverage is non-strict, includes the boundary of the source ball, and is asserted only after the chosen starting index.

No uniform bound on all the starting indices is assumed. Basepoints supply source nonemptiness; it is not a separate hidden condition.

## Exact output

The theorem returns a function \(N:\mathbb N\to\mathbb N\) and uses the particular countable label type
\[
L=\{\mathrm{none}\}\ \sqcup\
\coprod_{m\in\mathbb N}\mathrm{Fin}(N(m)+1).
\]
Here none is the distinguished base label. Countability follows from the existing instances for a countable disjoint union of finite types and for Option; no countability hypothesis is added to the input.

It returns point maps \(x_n:L\to X_n\), a real-valued bound \(C:L\to\mathbb R\), and finite label sets \(F_m\subseteq L\), with these four proved conclusions:

1. \(x_n(\mathrm{none})=p_n\) for every \(n\).
2. \(d_n(x_n(a),x_n(\mathrm{none}))\le C(a)\) for every \(n\) and every label \(a\).
3. \(\mathrm{none}\in F_m\) for every \(m\).
4. For each \(m\), all sufficiently large \(n\) satisfy
   \[
   d_n(z,x_n(\mathrm{none}))\le m+1
   \ \Longrightarrow\
   \exists a\in F_m,\quad
   d_n(z,x_n(a))\le\frac1{m+1}
   \]
   for every \(z\in X_n\).

The theorem uses ordinary existential conclusions and conjunctions. It does not introduce a new structure that merely packages a theorem conclusion.

The output is exactly the hypothesis shape required by the countable-label extraction theorem: fixed labels, a distinguished exact basepoint, uniform bounds for each label, and finite increasingly accurate nets of expanding source balls. It does not by itself claim that the labels are dense in any source space.

## Construction, padding, and scales

The proof applies the input hypothesis at radius \(m+1\) and accuracy \(1/(m+1)\), choosing \(N(m)\), a threshold \(I(m)\), and finite sets after that threshold. For earlier indices it selects the empty finite set. Thus no net property is inferred on an exceptional prefix.

A private padded enumeration maps Fin \((N(m)+1)\) into \(X_n\). Its first \(|S|\) entries enumerate the actual selected set using Finset.equivFin; all unused entries are the basepoint \(p_n\). Two private lemmas prove that every enumerated point either belongs to \(S\) or equals \(p_n\), and that every point of \(S\) is hit when \(|S|\le N(m)\).

This construction is valid when \(S\) is empty or \(N(m)=0\). It never selects an element of an empty set. On a bad prefix every label in that block is simply the basepoint. A genuine net of a nonempty positive-radius ball cannot be empty, but the implementation does not need an extra \(N(m)>0\) assumption or a separate proof of that fact.

The bound used in the proof is
\[
C(\mathrm{none})=0,\qquad C(m,a)=m+1.
\]
These bounds hold for every source index, including exceptional prefixes. The finite set \(F_m\) consists of the base label and all labels in the \(m\)-th block. After \(I(m)\), every required covering center in \(S\) is represented by a label in that block.

The blueprint's written construction uses integer radii and errors \(2^{-m}\). This implementation instead uses radii \(m+1\) and errors \(1/(m+1)\). The change is deliberate: both radii tend to infinity and errors tend to zero, and the downstream compactness proof is written and checked for precisely the latter scales. No numerical rate or fixed-index equality with the blueprint's dyadic labels is asserted. The input supplies all positive radii and errors, so this specialization adds no assumption.

## Verification and integration boundary

Ran:

    lake build DifferentialGeometry.Topology.MetricSpace.CountableNetLabels

The scoped build passed with 1,249 Lake jobs, new leaf 924 ms, without warnings. The toolchain is Lean 4.35.0-rc3, compiler commit 470d5ce1400764999581fd26d5d72b00d990b0f4, arm64-apple-darwin24.6.0.

A Lean stdin check inspected the elaborated public statement and axiom closure. The closure is exactly:

    propext, Classical.choice, Quot.sound

The final stdin check supplied singleton-space nets with starting index \(I=5\) at every requested scale and extracted the exact basepoint and all-index label radius bounds. This confirms that the public interface accepts a nonempty exceptional prefix; it does not require the source to supply nets before that index.

Source SHA256:

    09261a99db474f2d83eae761476e6a934ff9b1b6b4cb8ba9e7a4aec145245ae7

No comments, docstrings, admissions, custom axioms, source-geometry assumptions, or new theorem-packaging structure occur in the Lean source. Only this leaf and its notes were authored for this labeling subtask. The subsequent pseudometric limit, completion, properness, pointed maps, and final MC13 assembly belong to PointedPrecompactness.lean and are verified separately.
