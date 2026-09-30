# Mathematical reading of the topology and finite-regularity skeleton {#topology-finite-regularity}

This report translates the actual Lean source at commit `ea0fae60ee01ef8c8d9b57a51794c6538f679c5d`. It covers all 32 authored declarations in the five files listed below. It is a reading of what the code says, including its weaker conclusions and omitted data; it does not replace those statements by the stronger blueprint assertions.

There are **five admitted theorems** in this part: three topology producers, one finite-order compactness theorem, and one finite-regularity pullback theorem. Seven further theorem bodies contain actual proofs: three elementary collar facts independent of these admissions, two corollaries of the admitted pullback theorem, and two assemblies of admitted topology producers. The remaining 20 authored declarations define mathematical objects or construct data. Anonymous instances and compiler-generated structure projections are not separate authored declarations in these counts.

The five source files are:

| Short name in this report | Actual source |
|---|---|
| Presentation | [GraphManifold/Presentation.lean](/Users/bennettchow/Documents/Codex/Geometrization/Worktrees/wtgc1/GC_BASELINE_EXPORT/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Presentation.lean) |
| Refinement | [GraphManifold/Refinement.lean](/Users/bennettchow/Documents/Codex/Geometrization/Worktrees/wtgc1/GC_BASELINE_EXPORT/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Refinement.lean) |
| TorusDecomposition | [TorusCut/Decomposition.lean](/Users/bennettchow/Documents/Codex/Geometrization/Worktrees/wtgc1/GC_BASELINE_EXPORT/DifferentialGeometry/Topology/ThreeManifold/TorusCut/Decomposition.lean) |
| Pullback | [Metric/Pullback/FiniteRegularity.lean](/Users/bennettchow/Documents/Codex/Geometrization/Worktrees/wtgc1/GC_BASELINE_EXPORT/DifferentialGeometry/Geometry/Metric/Pullback/FiniteRegularity.lean) |
| Compactness | [Calculus/Compactness/FiniteOrder.lean](/Users/bennettchow/Documents/Codex/Geometrization/Worktrees/wtgc1/GC_BASELINE_EXPORT/DifferentialGeometry/Analysis/Calculus/Compactness/FiniteOrder.lean) |

## T0. The mathematical types used throughout {#t0}

The carrier of a compact piece is an **actual compact, Hausdorff, second-countable, oriented smooth 3-manifold**, possibly with boundary. It is not a homeomorphism type, a fundamental group, or a model name. Its chart model is either all of Euclidean 3-space or a Euclidean half-space. A half-space chart model permits a manifold whose boundary happens to be empty. The carrier type by itself need not be connected or nonempty.

`CompactCarrier.Components` adds a finite decomposition into actual subsets of that carrier. More precisely, it supplies a positive integer \(n>0\), open-and-closed subsets \(C_i\), \(0\leq i<n\), which are pairwise disjoint and cover the carrier, with each \(C_i\) connected **and nonempty**. Each \(\operatorname{int}(C_i)=C_i\cap\operatorname{int}(C)\) is also required to be connected and nonempty. In Lean, `ConnectedSpace` includes nonemptiness. Thus this component record cannot describe an empty carrier or an empty component list. Individual torus-index lists below may nevertheless be empty.

These inherited definitions are in [Carrier.lean:32](/Users/bennettchow/Documents/Codex/Geometrization/Worktrees/wtgc1/GC_BASELINE_EXPORT/DifferentialGeometry/Topology/ThreeManifold/Geometrization/Carrier.lean:32) and [Carrier.lean:56](/Users/bennettchow/Documents/Codex/Geometrization/Worktrees/wtgc1/GC_BASELINE_EXPORT/DifferentialGeometry/Topology/ThreeManifold/Geometrization/Carrier.lean:56).

An `InteriorGeometry` on \(C_i\) means a smooth Riemannian metric on **the whole actual interior** \(C_i\cap\operatorname{int}(C)\), complete in its own Riemannian distance, together with local isometric charts for one specified member of the eight fixed Thurston models. If the model is hyperbolic, its total volume is finite. For the other seven models, finite volume is **not** required. This is the existing endpoint convention. It permits, for example, complete infinite-volume flat product interiors. It does not mean merely “there is some locally homogeneous metric on some abstract manifold related to this component.” See [Atlas.lean:56](/Users/bennettchow/Documents/Codex/Geometrization/Worktrees/wtgc1/GC_BASELINE_EXPORT/DifferentialGeometry/Geometry/Thurston/Atlas.lean:56).

For a connected closed oriented smooth 3-manifold \(M\), a `PrimeDecomposition M` supplies a nonempty finite list of actual connected closed oriented manifolds \(P_i\), each prime, and an orientation-preserving smooth diffeomorphism

\[
       P_1\#\cdots\#P_m\;\longrightarrow\;M.
\]

Here prime means that every smooth connected-sum decomposition has a summand diffeomorphic to \(S^3\). Primeness is formulated without an orientation requirement on that summand-identifying diffeomorphism. In particular, \(S^3\) is allowed as a recorded prime identity, and \(S^2\times S^1\) is not excluded. The record does not itself supply an embedded sphere system or cap balls in \(M\). See [Prime.lean:11](/Users/bennettchow/Documents/Codex/Geometrization/Worktrees/wtgc1/GC_BASELINE_EXPORT/DifferentialGeometry/Topology/ThreeManifold/Geometrization/Prime.lean:11).

A `GeometricDecomposition P` consists of actual compact cut components, paired torus boundaries, their smooth oriented reconstruction to \(P\), injection of each reconstructed torus into \(\pi_1(P)\), and an `InteriorGeometry` for each cut component. The type can be formed for any connected closed \(P\); it does not itself assume that \(P\) is prime. A `GeometrizationCertificate M` additionally requires its chosen factors \(P_i\) to be prime. The proposition `Geometrizes M` means that such a certificate exists. See [Statement.lean:11](/Users/bennettchow/Documents/Codex/Geometrization/Worktrees/wtgc1/GC_BASELINE_EXPORT/DifferentialGeometry/Topology/ThreeManifold/Geometrization/Statement.lean:11).

## T1. Surfaces and ordinary circle bundles {#t1}

**Declarations:** `SurfaceModel` (Presentation:10), `SurfaceModel.Space` (:13), `SurfaceModel.model` (:22), `CompactSurface` (:28), and `CircleFibration` (:43). All five define data; none asserts an existence theorem.

`SurfaceModel` has two choices: the plane and the closed half-plane. The `Space` and `model` declarations associate their usual smooth manifold models to those choices. `CompactSurface` is a compact, connected, nonempty, Hausdorff, second-countable smooth surface with one of these models. **There is no assumption that the surface is orientable.** The half-plane choice does not require nonempty boundary.

For an open subset \(U\subset C\), a `CircleFibration C U` supplies:

1. A compact surface \(B\) as just defined.
2. A continuous, smooth, surjective map \(\pi:U\to B\).
3. For every \(b\in B\), an open neighborhood \(V_b\ni b\) and an actual smooth diffeomorphism
   \[
        \tau_b:\pi^{-1}(V_b)\longrightarrow V_b\times S^1
   \]
   whose first coordinate is exactly \(\pi\).

The domain in item 3 is the inverse image **inside the actual subset \(U\)**. This is an ordinary smooth circle bundle with local product trivializations. Every fiber is a smooth circle. The record does not require principal \(S^1\)-bundle transition functions, a global circle action, a chosen fiber orientation, or an orientable base. Arbitrary smooth fiberwise changes of circle coordinates are allowed. It also has no exceptional fibers or orbifold base. Thus it represents the regular circle-bundle blocks of the raw graph presentation, not a definition of every Seifert fibration.

In the later `RawGraphPresentation`, \(U\) is one of the compact clopen connected cut components. The generic definition of `CircleFibration C U` itself does not separately assume that \(U\) is compact or connected.

## T2. Actual labelled boundary tori and their elementary properties {#t2}

**Declaration:** `BoundaryTori C n` (Presentation:55), a definition of data.

For each label \(i\in\{0,\ldots,n-1\}\), the record supplies a smooth collar diffeomorphism from \(T^2\times[0,1)\) onto an open subset of \(C\). Technically the object is a partial diffeomorphism defined on ambient \(T^2\times[0,\infty)\), with designated source exactly \(T^2\times[0,1)\). Only its restriction to the source carries the asserted inverse and regularity properties. The zero slice lies in the intrinsic boundary of \(C\). The target open sets of distinct collars are disjoint.

This record **does not by itself say that these tori exhaust the boundary**, or that they are incompressible. Boundary exhaustion is a separate field of `RawGraphPresentation`. The number \(n\) may be zero.

The following seven declarations make the convention precise:

| Declaration and location | Exact mathematical content | Status |
|---|---|---|
| `BoundaryTori.torusMap`, Presentation:64 | \(j_i(t)=\operatorname{collar}_i(t,0)\). | Definition |
| `BoundaryTori.image`, :67 | The union \(\bigcup_i j_i(T^2)\). | Definition |
| `BoundaryTori.zero_mem_source`, :70 | Every \((t,0)\) is in the designated collar source because \(0<1\). This helper is private. | Proved, independent of admissions |
| `BoundaryTori.torusMap_smooth`, :77 | Each \(j_i:T^2\to C\) is smooth. | Proved, independent of admissions |
| `BoundaryTori.boundaryMap`, :82 | The same \(j_i\), now packaged as a continuous map for use with \(\pi_1\). | Definition using the proved smoothness |
| `BoundaryTori.torusMap_isEmbedding`, :86 | Each \(j_i\) is a topological embedding. The proof uses collar injectivity and compactness of the torus into the Hausdorff carrier. | Proved, independent of admissions |
| `BoundaryTori.incompressible`, :93 | For every label \(i\) and **every** basepoint \(x\in T^2\), the map \(\pi_1(T^2,x)\to\pi_1(C,j_i(x))\) induced by this actual \(j_i\) is injective. | Definition, not an asserted theorem |

There is no implicit distinction here between “injects into a block” and “injects into an ambient manifold”: the target is exactly the carrier \(C\) passed to this record. At \(n=0\), the last predicate is vacuously true, as expected for an empty torus family.

## T3. Paired torus ports and the quotient they actually define {#t3}

**Declarations:** `TorusPairing` (Presentation:98), `TorusPairing.QuotientSpace` (:118), and `TorusPairing.quotientMap` (:124). These define data, not new existence theorems.

For a compact carrier \(C\), `TorusPairing C` supplies finitely many pairs \((L_i,R_i)\) of closed subsets of \(C\). Each is parametrized by \(T^2\). All the subsets are disjoint, including \(L_i\cap R_i=\varnothing\), and there is a homeomorphism \(a_i:L_i\to R_i\). In the selected parametrizations, \(a_i\) is represented by an actual smooth torus diffeomorphism \(m_i:T^2\to T^2\):

\[
       a_i(\ell_i(t))=r_i(m_i(t)).
\]

Both parametrizations are the zero slices of supplied smooth half-collars, each with source \(T^2\times[0,1)\). The left and matched-right collar derivatives induce opposite orientations from the orientation on \(C\). Precisely, pull back the ambient three-dimensional tangent orientation by the two collar derivatives at \((t,0)\); one equals the negative of the other. This is the code's boundary-orientation reversal condition. It is not an additional assertion that \(m_i\) has a particular degree with respect to an independently chosen torus orientation.

The generic pairing record does not itself contain boundary exhaustion. In `RawGraphPresentation`, boundary exhaustion forces every paired port to lie in the actual boundary. It permits \(L_i\) and \(R_i\) to belong to the same connected component of \(C\), although the subsets themselves must be distinct and disjoint. Thus loop edges are permitted.

`QuotientSpace` is the literal quotient that identifies \(x\in L_i\) with \(a_i(x)\in R_i\), and identifies no other distinct points. It is not a guessed assembled manifold. Disjointness of all ports makes these pairwise identifications an equivalence relation. The inherited compact Hausdorff quotient theorem supplies its Hausdorff topology. `quotientMap` is the actual continuous quotient map \(q:C\to C/{\sim}\).

The inherited gluing relation and its assumptions are in [BoundaryGluing.lean:154](/Users/bennettchow/Documents/Codex/Geometrization/Worktrees/wtgc1/GC_BASELINE_EXPORT/DifferentialGeometry/Topology/Attachment/BoundaryGluing.lean:154). The exact orientation condition is in [SmoothTorusReconstruction.lean:13](/Users/bennettchow/Documents/Codex/Geometrization/Worktrees/wtgc1/GC_BASELINE_EXPORT/DifferentialGeometry/Topology/ThreeManifold/Geometrization/SmoothTorusReconstruction.lean:13).

## T4. What a raw graph presentation contains {#t4}

**Declaration:** `RawGraphPresentation W` (Presentation:129). This is a definition of data, not a theorem that a given \(W\) has such data.

It says that the actual compact oriented smooth carrier \(W\) is obtained by gluing finitely many actual regular circle-bundle blocks along actual paired torus boundaries, with all the following witnesses.

| Lean field(s) | Mathematical data or requirement |
|---|---|
| `cutCarrier`, `components` | A compact smooth oriented cut carrier \(C\), with a positive finite clopen decomposition \(C=\coprod_i C_i\) as in T0. |
| `fibration` | An ordinary circle-bundle structure on each entire compact component \(C_i\), as in T1. |
| `pairing` | Paired internal ports and their smooth matching maps and half-collars, as in T3. Write \(q:C\to Q=C/{\sim}\). |
| `externalCount`, `external`, `cutExternal` | A chosen finite label set for external boundary tori, and disjoint smooth half-collars on both \(W\) and \(C\), with those same labels. |
| `external_exhausted` | The actual boundary of \(W\) equals the union of its external zero-slice tori. |
| `cut_boundary_exhausted` | The actual boundary of \(C\) equals the union of all paired internal ports and all cut external zero-slice tori. |
| `external_disjoint` | The paired internal ports are disjoint from the cut external zero-slice tori. |
| `reconstruction` | An actual homeomorphism \(h:Q\to W\). |
| `quotient_smooth` | The map \(F=h\circ q:C\to W\) is smooth, including in the manifold-with-boundary sense at each boundary point. |
| `quotient_oriented` | At every \(x\in C\), \(dF_x\) is represented by a linear isomorphism carrying the chosen tangent orientation of \(C\) to that of \(W\). Thus the half-side maps have nonsingular orientation-preserving derivatives. |
| `interiorImage`, `interiorDiffeomorph`, `interior_map` | An open subset \(V\subset W\) and a smooth diffeomorphism \(C^\circ\to V\), whose underlying map is exactly \(F\vert_{C^\circ}\). The interior here removes **all** boundary of \(C\), paired and external. |
| `seam`, `seam_source`, `seam_zero` | For each pair, a smooth two-sided seam chart \(s_i:T^2\times(-1,1)\to W\), onto an open set, with \(s_i(t,0)=F(\ell_i(t))\). |
| `seam_positive` | For \(0\leq u<1\), \(s_i(t,u)=F(\text{rightCollar}_i(m_i(t),u))\). |
| `seam_negative` | For \(-1<u\leq0\), \(s_i(t,u)=F(\text{leftCollar}_i(t,-u))\). |
| `seam_interior`, `seam_disjoint` | Each seam chart has image in \(W^\circ\), and these images are pairwise disjoint. |
| `marked_collar` | On **every point of** \(T^2\times[0,1)\), reconstruction of the cut external collar is exactly the corresponding external collar of \(W\). This is equality of parametrized collar maps, not just equality of homology classes. |
| `external_seam_disjoint` | Every external collar image in \(W\) is disjoint from every internal seam image. |
| `leftPiece`, `rightPiece`, `left_owned`, `right_owned` | Each paired port is assigned to an actual connected cut component, and its subset is contained in that component. The assignments may be equal for the two sides of one pair. |
| `externalPiece`, `external_owned` | Each external zero-slice torus is assigned to its actual connected cut component. |

This definition has **no incompressibility hypothesis**. Its auxiliary seams may be compressible; they need not be the final essential tori. It supplies no irreducibility of a block and no geometric metric. It supplies no circle-fiber compatibility between opposite sides of an arbitrary torus pairing; all smooth orientation-compatible torus matchings are allowed. The number of paired or external tori can be zero. The blocks cannot form an empty list.

The external labels and collar parametrizations are genuinely retained **inside the supplied presentation**. But `RawGraphPresentation W` chooses them as part of its own data. A theorem merely concluding `Nonempty (RawGraphPresentation W)` does not by that fact preserve an independently prescribed set of external labels or parametrizations. A separate producer must state any such comparison.

The code uses regular bundles, even when a later Seifert description has exceptional fibers. To obtain a raw presentation from that later description, one must actually remove exceptional-fiber neighborhoods and use regular bundle pieces; an exceptional solid-torus carrier may itself be given a different ordinary bundle structure over a disk. That conversion is not a theorem in these five files.

## T5. A torus decomposition before geometry or incompressibility {#t5}

**Declaration:** `componentCarrier` (TorusDecomposition:10), a definition.

Given the data \(C=\coprod_i C_i\) of T0 and an index \(i\), this is the actual subset \(C_i\), equipped with its inherited smooth chart model and the restriction of \(C\)'s orientation. Compactness comes from \(C_i\) being closed in compact \(C\). No replacement by an abstract diffeomorphic manifold occurs.

**Declaration:** `TorusDecomposition M` (TorusDecomposition:17), a definition of data.

Here \(M\) is an actual connected, nonempty, closed, oriented smooth 3-manifold, **not assumed prime**. A torus decomposition supplies a compact oriented cut carrier with its positive finite components, pairs of torus ports exhausting its entire boundary, a smooth oriented assembly of their literal quotient, and an orientation-preserving diffeomorphism from the assembled quotient to \(M\). Every left and right port is assigned to its actual component. The inherited assembly includes the smooth quotient map, its orientation-preserving nonsingular derivatives, an interior diffeomorphism, matching half-collars, and two-sided seam charts with the exact positive/negative identities described in T4.

Unlike T4, all boundary ports in this record are paired: the reconstructed \(M\) is closed. Unlike `RawGraphPresentation`, this definition asks for no circle fibrations on the pieces. Crucially, **it also asks for neither incompressibility nor geometric metrics**. Those are subsequent premises. There may be zero tori, and there may be loop edges.

**Declaration:** `TorusDecomposition.component` (TorusDecomposition:30), a definition, is just the component carrier above for this particular decomposition.

**Declaration:** `TorusDecomposition.toGeometricDecomposition` (TorusDecomposition:34), an actual data assembly without an admission.

If this same torus decomposition is supplied with (i) injection of every reconstructed seam \(T^2\to M\) on \(\pi_1\), at every torus basepoint, and (ii) a complete model geometry on each actual cut interior, then it becomes a `GeometricDecomposition M` by retaining every carrier, pairing, reconstruction map, and piece assignment unchanged. This construction adds the supplied evidence; it proves no new geometry or incompressibility. It is valid without assuming \(M\) prime, because that assumption belongs to the surrounding prime-decomposition certificate.

## T6. The first admitted topology producer: closed graph carriers admit graph prime factors {#t6}

**Lean:** `GC.GraphManifold.exists_prime_decomposition_of_rawGraphPresentation`, [Refinement:23](/Users/bennettchow/Documents/Codex/Geometrization/Worktrees/wtgc1/GC_BASELINE_EXPORT/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Refinement.lean:23).

**Status: admitted with `sorry`.**

For **every** connected closed oriented smooth 3-manifold \(M\), and **every supplied** raw graph presentation of the actual \(M\), there exists a `PrimeDecomposition M` such that **each of its chosen factors** also has a raw graph presentation.

In symbols, with “graph” meaning existence of the full data in T4:

\[
\begin{gathered}
 \forall M\;\forall G\in\operatorname{RawGraphPresentation}(M),\\
 \exists\,(P_1,\ldots,P_m,\Phi),\quad
 m\geq1,\quad P_i\text{ prime and graph},\\
 \Phi:\#_iP_i\cong_+M.
\end{gathered}
\]

`NoCuts.carrier M` in the Lean signature means \(M\) itself regarded as a compact carrier with no boundary; it is not an extra topological assumption.

This is a **closed consequence** of the blueprint's relative graph-prime construction. The conclusion preserves the actual selected factor identities: it asserts graph presentations on precisely the \(P_i\) in its reconstruction. But it gives no relation between the original raw seams and the factor seams, no embedded sphere system in \(M\), no punctured factors or cap-ball assignments, and no relative boundary data. The theorem does not accept a preselected prime decomposition which it must use.

It does not assume irreducibility of \(M\), nonempty torus cuts, incompressibility of raw seams, or uniqueness of prime decomposition. It permits \(S^3\) identity factors and \(S^2\times S^1\) factors under the definition in T0.

## T7. The second admitted topology producer: a prime graph carrier admits the endpoint geometry {#t7}

**Lean:** `GC.GraphManifold.exists_geometric_decomposition_of_prime_rawGraphPresentation`, [Refinement:31](/Users/bennettchow/Documents/Codex/Geometrization/Worktrees/wtgc1/GC_BASELINE_EXPORT/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Refinement.lean:31).

**Status: admitted with `sorry`.**

For every connected closed oriented smooth 3-manifold \(P\), if \(P\) is prime and an actual raw graph presentation of \(P\) is supplied, then \(P\) has a `GeometricDecomposition` as defined in T0 and T5, including essential torus cuts and complete metrics on all the actual cut interiors.

The final torus family and geometric models are chosen by the conclusion. No statement identifies them with the raw auxiliary torus family. Their actual reconstructed inclusions into \(P\) must be injective on \(\pi_1\). The code imposes no minimality, canonical JSJ property, nonparallel condition, prescribed fiber slope, or prohibition on extra product cuts. A torus bundle that could support an uncut Sol metric may therefore instead be represented by retained essential product cuts with complete flat or Seifert-type interiors.

The output's model field may be any of the eight models. This theorem does **not** additionally assert that hyperbolic pieces cannot occur in its chosen output, even though a sharper graph-manifold classification would provide such a statement. Whatever model is chosen must have its actual model atlas and complete metric; a model tag alone is insufficient. Only hyperbolic outputs have the additional finite-volume requirement.

It also does not say that the complete metrics are restrictions of a metric on \(P\), agree across a torus, or retain a prescribed boundary metric. Completeness is required on the whole cut interior, and no complete restriction is claimed after sphere puncturing.

## T8. The actual closed graph assembly {#t8}

**Lean:** `GC.GraphManifold.geometrizes_of_rawGraphPresentation`, [Refinement:37](/Users/bennettchow/Documents/Codex/Geometrization/Worktrees/wtgc1/GC_BASELINE_EXPORT/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Refinement.lean:37).

**Status: actual proof, depending on the two admissions T6 and T7.**

Given a raw graph presentation of a connected closed oriented smooth \(M\), the proof obtains the selected prime decomposition from T6, obtains geometric decomposition data on each of those same factors from T7, and puts them into `GeometrizationCertificate M`. It uses choice to select the finitely indexed witnesses from existence statements. It does not prove the two producers.

This is a real, compiling connection between supplier and consumer: the graph presentation returned for \(P_i\) is applied to that exact \(P_i\), using the primality proof of that same factor. It does not substitute merely an isomorphic fundamental group or an unmarked list of prime types.

## T9. Hyperbolic-or-graph pieces and the mixed admitted topology producer {#t9}

**Declarations:** `isHyperbolicInteriorGeometry` (Refinement:11) and `HyperbolicOrGraph` (:17), both definitions.

`isHyperbolicInteriorGeometry g` means that the `InteriorGeometry` \(g\) of T0 has its model field equal to the fixed hyperbolic model. The rest of the mathematical force lies in the already supplied `InteriorGeometry`: completeness, an actual hyperbolic model atlas, and finite volume.

For an actual cut component \(C_i\subset C\), `HyperbolicOrGraph C components i` is data of **one of** the following kinds:

1. A complete finite-volume hyperbolic structure on the actual whole interior \(C_i\cap C^\circ\).
2. A full raw graph presentation of the actual compact carrier \(C_i\).

No metric is required in the graph alternative. The alternatives are constructors of a data type, not a theorem that every component has one of these forms. No relation to an ambient Ricci-flow metric is imposed by this particular type; those metric relations belong to the separate collapse/flow input layer.

**Lean:** `GC.GraphManifold.exists_prime_geometric_decomposition_of_hyperbolicOrGraph`, [Refinement:46](/Users/bennettchow/Documents/Codex/Geometrization/Worktrees/wtgc1/GC_BASELINE_EXPORT/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Refinement.lean:46).

**Status: admitted with `sorry`.**

For every connected closed oriented smooth 3-manifold \(M\), every supplied actual torus decomposition \(D\) of \(M\), and every choice of hyperbolic-or-graph data for each of its actual cut components, assume additionally that **each of the input seam maps into this actual \(M\)** induces an injection on fundamental groups, at every basepoint. Then there exists a prime decomposition of \(M\), together with a geometric decomposition of each of its selected prime factors.

The incompressibility assumption concerns the actual reconstructed seam \(T^2\to M\). Injection into just a hyperbolic model or a single cut piece is not a substitute. The theorem does not assume \(M\) already prime or irreducible, and does not assume that every raw internal graph seam is incompressible. It permits zero ambient seams, no hyperbolic components, and self-pairings between ports of one component.

The conclusion is a new existentially chosen prime decomposition and new geometric cut data. It contains **no comparison identifying the final seams with the input seams, no requirement to retain the supplied hyperbolic metric, and no requirement to preserve the input graph labels or external collars in those final data**. The new output nevertheless reconstructs the same actual \(M\) by the maps required in T0. These omissions make this an endpoint consequence of the fuller relative blueprint, not an implementation of all the relative data in AT13–AT18.

In particular, this admitted theorem has **not** been proved in Lean by combining T6 and T7. Those are statements for closed graph carriers; an argument for graph carriers with boundary, their relative prime/cap construction, and the hyperbolic reattachment is still inside this single mixed admission.

## T10. The actual mixed endpoint assembly {#t10}

**Lean:** `GC.GraphManifold.geometrizes_of_hyperbolicOrGraph`, [Refinement:54](/Users/bennettchow/Documents/Codex/Geometrization/Worktrees/wtgc1/GC_BASELINE_EXPORT/DifferentialGeometry/Topology/ThreeManifold/GraphManifold/Refinement.lean:54).

**Status: actual proof, depending on the admission T9.**

Under exactly the hypotheses of T9, \(M\) geometrizes in the existing certificate sense. The proof takes the prime decomposition and per-factor geometric decompositions supplied by T9 and packages them into the certificate. No further topological input is used in this packaging. It is a short conditional assembly, not a proof of relative graph refinement.

The two graph routes in these files are therefore:

\[
\begin{aligned}
  &\text{raw closed graph presentation}\\
  &\quad\xrightarrow{\text{T6, admitted}}\text{graph prime factors}\\
  &\quad\xrightarrow{\text{T7, admitted}}\text{factor geometries}\\
  &\quad\xrightarrow{\text{T8, proved assembly}}\text{certificate}.
\end{aligned}
\]

and separately

\[
\begin{aligned}
  &\text{actual mixed torus decomposition}\\
  &\qquad{}+\text{ ambient injection}\\
  &\quad\xrightarrow{\text{T9, admitted}}\text{prime factors + geometries}\\
  &\quad\xrightarrow{\text{T10, proved assembly}}\text{certificate}.
\end{aligned}
\]

## FR1. Finite-order compactness: the exact admitted local statement {#fr1}

**Lean:** `DifferentialGeometry.CheegerGromovCompactness.exists_bilinear_form_limit_subsequence_of_bounded_derivatives`, [Compactness:11](/Users/bennettchow/Documents/Codex/Geometrization/Worktrees/wtgc1/GC_BASELINE_EXPORT/DifferentialGeometry/Analysis/Calculus/Compactness/FiniteOrder.lean:11).

**Status: admitted with `sorry`.**

Let \(E\) be a finite-dimensional complete real normed vector space, \(U\subset E\) an open set, and \(K\geq1\) an integer. Let \(g_i(x)\) be continuous bilinear forms on \(E\), with \(g_i\) defined as a function on all of \(E\) and of class \(C^K\) on \(U\). Symmetry and metric inequalities below are required only on \(U\).

Assume:

1. For **each** integer \(0\leq q\leq K\) and **each** compact set \(S\subset U\), there is a real number \(C_{q,S}\) such that, for all sufficiently large \(i\),
   \[
        \sup_{x\in S}\|D^q g_i(x)\|\leq C_{q,S}.
   \]
   Both \(C_{q,S}\) and the starting index may depend on \(q,S\). There is no single global derivative bound on \(U\), and finitely many early sequence terms need not satisfy a chosen bound.
2. There are two **fixed** real constants \(a,b\), with \(a>0\), such that for **every** index \(i\), every \(x\in U\), and every \(v,w\in E\),
   \[
     g_i(x)(v,w)=g_i(x)(w,v),\qquad
     a\|v\|^2\leq g_i(x)(v,v)\leq b\|v\|^2.
   \]
   The same \(a,b\) apply on all of \(U\) and to all terms, including the early ones. The code does not separately assume \(b>0\); if \(U\ne\varnothing\) and \(\dim E>0\), the displayed inequalities force \(b\geq a>0\).

Then there exist a **single strictly increasing** subsequence map \(\phi:\mathbb N\to\mathbb N\) and a bilinear-form-valued function \(g_\infty\), defined on all of \(E\), such that:

1. \(g_\infty\) is \(C^{K-1}\) on \(U\).
2. On **every** compact \(S\subset U\), \(g_{\phi(i)}\to g_\infty\) in \(C^{K-1}\).
3. On \(U\), \(g_\infty\) is symmetric and satisfies the same two-sided bounds with exactly the original \(a,b\).

For item 2, the code's precise convergence condition is

\[
 \forall\varepsilon>0\;\exists i_0\;\forall i\geq i_0\;
 \forall q\leq K-1\;\forall x\in S,
 \quad \|D^q(g_{\phi(i)}-g_\infty)(x)\|\leq\varepsilon.
\]

This unfolds `MapCPConvergenceOn` in [MapConvergence/Basic.lean:25](/Users/bennettchow/Documents/Codex/Geometrization/Worktrees/wtgc1/GC_BASELINE_EXPORT/DifferentialGeometry/Analysis/Calculus/MapConvergence/Basic.lean:25). Its derivatives are ordinary ambient Fréchet derivatives; openness of \(U\) ensures that at its points these depend only on the local restrictions to \(U\). Values outside \(U\) are not constrained by the conclusion.

There is no assumption that \(U\) is bounded, connected, relatively compact, convex, or nonempty. At \(K=1\), the conclusion is only a continuous positive-definite limit and uniform convergence on compact subsets. At \(U=\varnothing\), the regularity, convergence and positivity-on-\(U\) assertions are vacuous; a subsequence and arbitrary globally defined bilinear forms still exist. Dimension zero is allowed. These cases do not give a counterexample to the statement.

This is a **local coefficient compactness statement on a fixed Euclidean domain**. It has no sequence of manifolds, basepoints, injectivity-radius hypothesis, volume lower bound, complete limit metric, global atlas, overlap transitions, pointed convergence, comparison embeddings, or sectional-curvature conclusion. Those are substantial additional obligations in the full LFR14/LC81 blueprint. Uniform coordinate derivative bounds are premises here; this theorem does not derive them from curvature derivative bounds.

## FR2. Pulling back a finite-regularity metric: the exact admitted statement {#fr2}

**Lean:** `DifferentialGeometry.Geometry.exists_pullback_metric_of_finite_diffeomorph`, [Pullback:16](/Users/bennettchow/Documents/Codex/Geometrization/Worktrees/wtgc1/GC_BASELINE_EXPORT/DifferentialGeometry/Geometry/Metric/Pullback/FiniteRegularity.lean:16).

**Status: admitted with `sorry`.**

Let \(M,N\) already be smooth manifolds, with general real finite-dimensional models with corners \(I,J\), respectively. The statement does not assume compactness, connectedness, nonemptiness, completeness, boundarylessness, Hausdorffness, or second countability. It uses the manifold structures and finite-dimensional normed tangent models needed for the derivative and metric definitions. The source and target model vector spaces need not be declared to have equal dimension in advance; existence of the diffeomorphism is the relevant premise.

Let \(K,s,r\in\mathbb N\) satisfy

\[
                 r\leq K,\qquad r+1\leq s.
\]

Let \(g\) be a \(C^K\) Riemannian metric on \(N\), and let \(f:M\to N\) be a \(C^s\) diffeomorphism, meaning an actual bijection whose forward **and inverse** maps are \(C^s\). Then there exists a \(C^r\) Riemannian metric \(h\) on \(M\) satisfying the **exact tensor identity**

\[
          h_x(v,w)=g_{f(x)}(df_xv,df_xw)
          \quad\text{for every }x\in M,\;v,w\in T_xM.
\]

Here a \(C^r\) Riemannian metric means a continuously varying symmetric positive-definite bilinear form of the asserted regularity on the tangent bundle, compatible with its existing fiber topology. It is not an arbitrary semidefinite tensor. The code's `Diffeomorph` definition explicitly contains \(C^s\) regularity of the inverse; since \(s\geq1\), the derivative has the isomorphism property needed for positivity.

The order bound is the familiar one-derivative cost in pulling back a metric:

\[
                h\in C^{\min(K,s-1)},
\]

or any weaker finite order \(r\) allowed by the inequalities. The code states existence at each such specified \(r\), rather than a maximum-order formula. Natural-number subtraction and the lower bound \(s\geq1\) therefore cause no exceptional \(s=0\) case.

The conclusion contains no explicit length, distance, completeness, volume, or curvature-preservation theorem. It contains the exact tensor formula from which appropriate preservation results can subsequently be proved. It asserts neither smoothing of \(g\) nor a curvature-preserving perturbation. It also does **not** construct a compatible smooth structure on a manifold initially given only a finite-regularity atlas: both carriers are already smooth at the start of this theorem.

## FR3. The two proved regularity-budget corollaries {#fr3}

**Lean:** `exists_pullback_metric_of_diffeomorph_one_order_higher`, [Pullback:26](/Users/bennettchow/Documents/Codex/Geometrization/Worktrees/wtgc1/GC_BASELINE_EXPORT/DifferentialGeometry/Geometry/Metric/Pullback/FiniteRegularity.lean:26).

**Status: actual proof by specialization of the admission FR2.** For any natural \(K\), a \(C^{K+1}\) diffeomorphism pulls a \(C^K\) metric back to a \(C^K\) metric with the exact displayed tensor identity. This includes \(K=0\): a \(C^1\) diffeomorphism pulls a continuous metric back to a continuous metric. The proof substitutes \(s=K+1\) and \(r=K\) into FR2.

**Lean:** `exists_pullback_metric_of_diffeomorph_three_orders_lower`, [Pullback:35](/Users/bennettchow/Documents/Codex/Geometrization/Worktrees/wtgc1/GC_BASELINE_EXPORT/DifferentialGeometry/Geometry/Metric/Pullback/FiniteRegularity.lean:35).

**Status: actual proof by specialization of the admission FR2.** For an integer \(m\geq4\), a \(C^{m-3}\) diffeomorphism pulls a \(C^m\) metric back to a \(C^{m-4}\) metric with exactly the same tensor formula. The hypothesis \(m\geq4\) controls truncated natural-number subtraction. At \(m=4\) the map is \(C^1\) and the output metric is \(C^0\). The proof supplies \(r=m-4\leq m\) and \(r+1\leq m-3\) to FR2.

For the blueprint's common substitution \(m=K-1\), this second statement gives order \(K-5\), provided \(K\geq5\). It does not claim that every model map in the blueprint is automatically \(C^{m-3}\); a consumer must supply such a map. It also gives no quantitative norm bound on the pullback or its difference from another metric.

## R1. What is and is not yet connected in Lean {#topology-r1}

The statement network in this part has two actual topology assemblies (T8 and T10), and two actual regularity specializations (FR3). The mixed topology producer T9 is one large admission rather than a proof assembled from the relative constructions of the blueprint.

The local compactness theorem FR1 and finite pullback theorem FR2 are separate prepared statements. At this commit, searches of the Lean sources show no mathematical application of FR1 beyond its own declaration, and no mathematical application of FR2 beyond its two FR3 corollaries. In particular, these files do not yet demonstrate that their outputs satisfy the hypotheses of the late-flow or static-collapse producers. Importing a file or listing it in the declaration audit does not establish such an application.

Similarly, the two closed graph admissions T6 and T7 do feed T8, but they are not called in the proof body of the mixed admission T9. A future relative-refinement proof needs additional intermediate statements to expose that connection.

## R2. Approval points and weaknesses identified by this rereading {#topology-r2}

I found **no specific counterexample or internal contradiction** in these five admitted statements during this rereading. That is a bounded review judgment, not a mathematical proof or a claim that all stronger blueprint arguments have been checked. The most consequential decisions for Bennett Chow and Peng Lu are these:

1. **Approve the regular-bundle meaning of raw graph presentation.** Its fibers are all ordinary circles; exceptional Seifert fibers must be removed or represented by further regular blocks before supplying it. The bases may be nonorientable. There is no global circle action in the definition.
2. **Approve the endpoint consequence rather than a full relative export.** T6, T7 and especially T9 omit the sphere/cap ledger and comparisons preserving the given decorations. This suffices for their chosen final certificate conclusion. It does not yet provide the finer relative interfaces needed to implement the blueprint proof in parallel without further design.
3. **Check the existential freedom in T9 deliberately.** The final chosen metrics and cuts need not retain the input hyperbolic metrics or seams. This is a weaker conclusion, not an inconsistency; any task expecting to reuse those exact markings cannot treat T9 as already exporting them.
4. **Keep nonempty components separate from possibly empty seam families.** The underlying `Components` record excludes an empty carrier. Empty late-flow slices must be handled elsewhere. No-cut geometric manifolds remain legal because the torus index may be empty.
5. **Do not call FR1 the global compactness theorem.** It is only the fixed-chart coefficient subsequence lemma. Producing the chart bounds, a global limit and actual comparison embeddings remains unrepresented here.
6. **Do not call FR2 a smooth-metric category bridge.** Its tensor remains only finitely regular. Choosing the initial compatible smooth carrier and deriving metric/curvature invariance are additional steps. FR2's actual content is the precise finite pullback regularity statement.

The existing complete-interior metric convention is also essential: only hyperbolic pieces require finite volume, and extra essential product cuts are permitted. Requiring all geometries to have finite volume or demanding an uncut model for every torus bundle would change these statements substantially.

## R3. Evidence, source comparison, and review limits {#topology-r3}

This review read all five actual Lean files, then expanded their dependencies for compact carriers and components, manifold-with-boundary interiors, finite torus gluing relations, smooth oriented reconstruction, prime decomposition, endpoint geometry, metric regularity, diffeomorphism regularity, and the exact \(C^p\)-convergence predicate. Source locations and authored-declaration coverage are recorded in `topology_finite_regularity_coverage.json` next to this report.

The corresponding natural-language blueprint bodies were reread at:

- `master207A.tex`, lines 8526–8588: G01–G05, especially ordinary circle bundles, nonorientable bases, raw versus essential cuts, and actual ambient injection.
- `master207A.tex`, lines 9467–9579: RG05–RG06, actual relative graph-prime/good-block output and its terminal block list.
- `master207A.tex`, lines 10378–10431: GM06, full marked graph refinement and complete E1 witnesses.
- `master207B.tex`, lines 11895–12036: AT13–AT18, relative prime/cap data, good-block refinement, actual capped ambient injection and prime reconstruction.
- `master207A.tex`, lines 24826–24860: LFR01, compatible smooth structures and the finite derivative ledger.
- `master207A.tex`, lines 25872–25908 and 25970–26030: LFR14, finite-model construction and actual comparison maps.
- `master207A.tex`, lines 26128–26144: the \(m=K-1\) consumer regularity distinction.

Those comparisons identify which conclusions are intentionally omitted; they do not silently import them into the Lean signatures. No new theorem contract or source classification was changed. Consequently this report does not claim a new primary-source literature or erratum audit; the previously recorded source checks for these unchanged mathematical routes retain their historical scope.

Proof status was cross-checked against the recorded elaborated declaration audit at this commit: the five admitted theorem names and four admission-dependent corollary/assembly theorem names have `sorryAx`; the three collar proofs do not. This report did not rebuild Lean or reprove any admission. The previously recorded build checks elaboration and dependencies; it does not establish the mathematical truth of a `sorry` statement.
