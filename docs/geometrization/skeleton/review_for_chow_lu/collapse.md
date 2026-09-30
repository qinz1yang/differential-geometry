# Static collapse: faithful mathematical reading of the Lean skeleton

<a id="collapse-scope"></a>
## C0. Scope, conventions, and proof status

This section translates **all 35 authored declarations in the seven collapse-related modules** at commit `ea0fae60ee01ef8c8d9b57a51794c6538f679c5d`. It is a description of the actual Lean code, not a proposed improvement or a claim that all collapse nodes in the blueprint have been formalized. No Lean code was changed in preparing this report.

There are **seven admitted theorem bodies**, **four independently proved elementary monotonicity theorems**, and **two composition theorems with genuine Lean proofs that use admitted collapse theorems**. The other 22 declarations are definitions, structures, or abbreviations, including two explicitly constructed weakening operations. “Independently proved” here means their axiom audit does not contain `sorryAx`; it does not mean their entire inherited mathematical foundation was re-audited for this report. A theorem with an actual proof can still depend on admissions through the theorems it invokes.

In the three-dimensional statements, a **compact carrier** means an oriented compact Hausdorff second-countable smooth 3-manifold, modeled either on Euclidean 3-space or the standard half-space. Its orientation is part of the supplied data. It need not be connected or nonempty merely by being a compact carrier. Whenever the collapse theorems assume “connected,” the Lean `ConnectedSpace` assumption includes nonemptiness. There are smooth boundaries here, not arbitrary manifolds with corners. The notation \(\partial W\) denotes the boundary determined by the actual manifold model, not a selected subset or a boundary imported from another carrier.

Every metric \(g\) in these seven modules is a **smooth positive-definite Riemannian metric**. Finite regularity enters through cusp embeddings, not through nonsmooth input metrics to the static collapse theorem.

Write

\[
 d_g(x,y)\in[0,\infty],\qquad B_g(p,r)=\{q:d_g(p,q)<r\},\qquad
 V_g(p,r)=\operatorname{Vol}_g B_g(p,r),\qquad \omega_3=4\pi/3.
\]

The distance is the intrinsic Riemannian distance **within the specified carrier**, defined using lengths of curves in that carrier. Thus a ball in a cut piece is not automatically the intersection of that piece with a ball in a larger flow manifold. Volume is the actual Riemannian volume measure on the same carrier. The code uses extended nonnegative reals for distance and volume. For real \(r\leq0\), its open-ball definition gives the empty set; the substantive tests below always impose \(r>0\).

For the dimension-independent auxiliary definitions, the setting is a smooth manifold with a finite-dimensional real normed model, a model with corners, and the indicated Hausdorff and sigma-compact assumptions. They do not silently assume dimension three, compactness, orientation, or connectedness. The constant \(\omega_3\) and the exponent three are nevertheless explicitly three-dimensional in the collapse predicates.

The convention for sectional curvature is fixed by the identity

\[
 \sec_g\geq a\quad\Longleftrightarrow\quad
 a\bigl(g(v,v)g(w,w)-g(v,w)^2\bigr)\leq \mathrm{Rm}_g(v,w,w,v)
\]

for every point and every pair of tangent vectors. Dependent and zero vectors are included; division by a possibly zero Gram determinant is avoided.

<a id="collapse-tensor"></a>
## C1. What the curvature-derivative notation actually means

**Definitions, with no admitted proofs.** For a raw covariant \(s\)-tensor field \(T\), the code defines \(\nabla_g T\) by the usual coordinate expression for the Levi–Civita covariant derivative: differentiate the coordinate tensor and subtract the connection action in each covariant slot. The differentiation slot is prepended to the existing tensor slots. At a boundary point the derivative is taken within the range of the manifold's model with corners. The result is converted from coordinates back to a tensor in the actual tangent space.

The iteration is defined recursively:

\[
 \nabla_g^0T=T,\qquad \nabla_g^{k+1}T=\nabla_g(\nabla_g^kT).
\]

The curvature quantity used everywhere below is

\[
 D_k(g,x):=\left|\nabla_g^k\mathrm{Rm}_g(x)\right|_g,
\]

where \(\mathrm{Rm}_g\) is the actual covariant four-tensor of the Levi–Civita connection and the norm is the induced tensor Hilbert–Schmidt norm, not the operator norm or the coordinate sup norm. The norm is the square root of the corresponding tensor inner product.

**Total-definition qualification.** Lean's derivative operation is defined even for functions that are not differentiable. Consequently the raw operation \(T\mapsto\nabla_gT\) accepts an arbitrary tensor field without a regularity premise. For differentiable tensor fields its displayed formula is the ordinary covariant derivative. For arbitrary nonsmooth fields one must not read its value as asserting that a classical covariant derivative exists. Here the curvature field comes from a smooth metric; the cusp-error application below has the explicit \(C^{K+1}\) map regularity that is intended to justify the derivatives through order \(K\). The new modules do not separately prove a general finite-regularity compatibility theorem for this raw operation. This is an implementation obligation, not an extra regularity theorem already obtained from the definition.

**Lean references:** `metricCovariantDerivative` (Metric.lean:17), `iteratedMetricCovariantDerivative` (Metric.lean:30), and `curvatureDerivativeNorm` (DerivativeNorm.lean:18).

<a id="collapse-radius"></a>
## C2. Curvature radius, volume collapse, and derivative tests

**Definitions.** The curvature radius is the extended-real supremum

\[
 R_g(p)=\sup\left\{r>0:\sec_g(q)\geq-r^{-2}\ \text{for every }q\in B_g(p,r)\right\}.
\]

This radius is **not capped at 1**. It is permitted to equal \(+\infty\). It uses a sectional lower bound on the whole ball, not a curvature condition only at its center. The code does not insert a separately supplied scale function into this definition.

“Volume collapsed at curvature scale with parameter \(w\)” means exactly

\[
 \forall r>0,\quad R_g(p)=r\ \Longrightarrow\ V_g(p,r)\leq wr^3.
\]

The equality is equality in extended nonnegative reals. Therefore this condition tests the one finite positive curvature radius when it exists. **It is vacuous when \(R_g(p)=+\infty\)**, and also vacuous if a radius were zero. The latter possibility is excluded by the first admitted lemma below for the stated smooth-manifold setting. No expression \(\operatorname{Vol}B(p,\infty)/\infty^3\) is used.

For a nonnegative integer \(K\), a real-valued function \(A:\mathbb R\to\mathbb R\), and a real threshold \(w_0\), “curvature derivatives controlled” means:

\[
\begin{split}
&\text{for every }p,\ w,r\in\mathbb R\text{ with }w_0\leq w<\omega_3,\quad 0<r<R_g(p),\\
&V_g(p,r)\geq wr^3
\quad\Longrightarrow\quad
 D_k(g,q)\leq A(w)r^{-k-2}
 \quad\text{for every }0\leq k\leq K\text{ and every }q\in B_g(p,r).
\end{split}
\]

The derivative bound includes \(k=0\) and \(k=K\). The radius inequality is **strict**. The volume inequality is **nonstrict**. The estimate is on **every point of the entire same ball**. The definition by itself does not require \(A\) to be positive or \(w_0\) to be positive; the main existence theorems supply these hypotheses. No continuity or monotonicity of \(A\) is built into the predicate. The metric and the function \(A\) are the same in all tests.

**Admitted lemma 1.** For every smooth metric in the auxiliary smooth-manifold setting and every point \(p\),

\[
 R_g(p)>0.
\]

There is no compactness, completeness, connectedness, or boundaryless assumption in this lemma.

**Admitted lemma 2.** If that manifold is compact and connected, then, for every point \(p\),

\[
 R_g(p)=+\infty\quad\Longleftrightarrow\quad \sec_g\geq0\text{ everywhere}.
\]

This includes manifolds with boundary and other allowed models with corners; the lemma is not restricted to closed 3-manifolds. Its forward direction uses connectedness to reach every point from \(p\). Compactness is an explicit hypothesis even if a stronger result might be possible.

**Independently proved lemma.** If \(w_1\leq w_2\), derivative control at threshold \(w_1\) implies derivative control at threshold \(w_2\). The latter condition asks about fewer values of \(w\). This implication requires no positivity assumption on the thresholds or on \(A\).

**Lean references:** all eight declarations in CurvatureScale.lean: `curvatureRadius` (23), `ballVolume` (28), `euclideanUnitBallVolume` (31), `volumeCollapsedAtCurvatureScale` (33), `curvatureDerivativesControlled` (38), `curvatureRadius_pos` (46), `curvatureRadius_eq_top_iff` (50), and `curvatureDerivativesControlled_mono_threshold` (55).

<a id="collapse-cuspmodel"></a>
## C3. The exact model cusp and its curvature normalization

**Definitions.** The fixed topological torus is \(T^2=S^1\times S^1\), with its product smooth structure. The half-cylinder is

\[
 \mathcal H=T^2\times[0,\infty),
\]

with the product manifold-with-boundary model. The collar domain is the relatively open subset

\[
 \mathcal U=T^2\times[0,100).
\]

In particular, \(z=0\) is included and \(z=100\) is excluded.

An exact cusp consists of a **supplied** smooth metric \(q\) on this torus, the condition

\[
 \mathrm{Rm}_q(v,w,w,v)=0\quad\text{for every point and all tangent vectors},
\]

and a supplied smooth metric \(h\) on the whole half-cylinder satisfying exactly

\[
 h=dz^2+e^{-z}q.
\]

These are data and equations, not an existence theorem producing \(q\) or \(h\). No diameter, area, injectivity-radius, lattice-shape, or aspect-ratio restriction is imposed on \(q\) at this stage. There is no quotient group or chosen lattice basis in this definition.

**Admitted lemma 3.** For every such cusp and every point and pair of tangent vectors,

\[
 \mathrm{Rm}_h(v,w,w,v)
 =-\frac14\bigl(h(v,v)h(w,w)-h(v,w)^2\bigr).
\]

Thus the normalization is sectional curvature \(-1/4\), not \(-1\). The statement is a tensor identity including degenerate vector pairs. It is asserted on the whole half-cylinder, including its boundary, not merely on the depth-100 collar. It does not assert completeness of the interior \(T^2\times(0,\infty)\), finite volume for any arbitrary metric on an ambient manifold, or existence of a cusp embedding.

**Lean references:** Hyperbolic/Cusp.lean: `CuspHalfSpace` (10), `cuspDomain` (12), `HyperbolicCusp` (14), `cusp_constant_sectional_curvature` (23).

<a id="collapse-cuspembedding"></a>
## C4. Exactly what a nearly cuspidal boundary supplies

Let \(W\) be a compact carrier with smooth metric \(g\). Fix \(K\in\mathbb N\) and \(\delta\in\mathbb R\).

**Definitions of the error.** For a chosen exact cusp \((\mathcal H,h)\) and a map \(f:\mathcal H\to W\), set

\[
 E=f^*g-h,\qquad
 (f^*g)_p(v,w)=g_{f(p)}(df_pv,df_pw).
\]

The code forms this as an actual covariant two-tensor using the manifold derivative of \(f\). The error bound means

\[
 |\nabla_h^k E(p)|_h\leq\delta
 \quad(0\leq k\leq K,\ p\in T^2\times[0,100)).
\]

Both the derivatives and their tensor norms use the **reference cusp metric** \(h\). This is a pointwise uniform bound on each derivative order, not a sum over orders. It is not a coordinate coefficient norm or a bound on derivatives measured with the target metric \(g\).

**Definition of a cusp embedding onto a prescribed boundary set \(X\subset W\).** The supplied data must satisfy all of the following:

1. An exact cusp as in C3 and a map \(f:\mathcal H\to W\).
2. The map is \(C^{K+1}\) on \(\mathcal U\), including its boundary points.
3. Its restriction to \(\mathcal U\), with the subspace topology, is a topological embedding.
4. Its differential is injective at every point of \(\mathcal U\).
5. Its depth-zero torus has exactly the prescribed image: \(f(T^2\times\{0\})=X\).
6. For every \((t,z)\in\mathcal U\), \(f(t,z)\in\partial W\) if and only if \(z=0\). Thus positive-depth points do not meet any ambient boundary component.
7. The error bounds displayed above hold through order \(K\).

There are no conditions on \(f\) outside \(\mathcal U\). The map is defined there because Lean represents maps as total functions. There is no explicit field asserting a smooth inverse, a proper map on the noncompact half-open collar, or a prescribed orientation for the embedding.

**Definition of a nearly cuspidal boundary.** This consists of a positive integer \(n\), subsets \(X_i\subset W\), \(i\in\{0,\ldots,n-1\}\), and cusp embeddings onto those sets, with:

\[
 X_i\text{ connected and closed},\qquad X_i\cap X_j=\varnothing\ (i\ne j),\qquad
 \bigcup_iX_i=\partial W,
\]

and

\[
 d_g(x,y)\leq\delta\quad\text{for all }x,y\in X_i.
\]

Here connected sets are nonempty. The finite disjoint closed cover by connected sets gives the actual boundary components, not arbitrary pieces of one component. The diameter is measured by curves in **all of \(W\)**. It is not the intrinsic length distance constrained to \(X_i\), and it is not measured with the model torus metric \(q_i\). This precise convention matters for comparison with sources.

**No disjointness of the positive-depth cusp collars is required.** The sets \(X_i\) are pairwise disjoint, and each collar individually is embedded, but there is no field saying the images \(f_i(\mathcal U)\) and \(f_j(\mathcal U)\) are disjoint. Nor does the definition give common torus coordinates or compatible fiber structures on different collars.

**Constructed operations, with no admissions.** If \(\delta_1\leq\delta_2\), either a cusp embedding or a nearly cuspidal boundary with error parameter \(\delta_1\) can be viewed as one with error parameter \(\delta_2\), keeping the exact same maps, component sets, and indices. Only the inequalities are weakened. The operations impose no positivity assumption; substantive applications choose positive thresholds.

**Lean references:** CuspBoundary.lean: `cuspMetricError` (15), `cuspMetricErrorBound` (22), `CuspEmbedding` (29), `NearlyCuspidalBoundary` (43), `CuspEmbedding.weaken` (64), `NearlyCuspidalBoundary.weaken` (70).

<a id="collapse-boundarydistance"></a>
## C5. Which points must satisfy volume collapse near boundary

**Definitions.** Distance to the actual boundary is

\[
 d_g(p,\partial W)=\inf_{q\in\partial W}d_g(p,q)\in[0,\infty].
\]

For empty boundary the infimum is \(+\infty\). The boundary volume-collapse predicate requires exactly

\[
 d_g(p,\partial W)>10\quad\Longrightarrow\quad
 p\text{ is volume collapsed at curvature scale with parameter }w.
\]

The strict inequality is \(>10\), not \(\geq10\). No curvature-scale volume-collapse condition is imposed by this predicate at a point whose distance to boundary is at most 10. Whole-ball curvature-derivative tests will still be imposed at every center in the boundary theorem below.

Although the distance-to-boundary function has a mathematically defined value for empty boundary, the principal boundary theorem requires a positive number of cusp boundary components. The closed theorem uses its own separate predicate.

**Lean references:** CuspBoundary.lean: `distanceToBoundary` (56), `boundaryVolumeCollapsed` (60).

<a id="collapse-hypotheses"></a>
## C6. The three static hypothesis packages and their monotonicity

**Definitions.** For fixed \((W,g,K,A,w_0)\), the closed package is the conjunction of these three conditions:

1. \(\partial W=\varnothing\).
2. Volume collapse at curvature scale with \(w_0\) holds at every point.
3. Derivative control as in C2 holds with \(K,A,w_0\).

The boundary package is the conjunction of these three conditions:

1. There exists a nearly cuspidal boundary with \(K\) and \(\delta=w_0\).
2. The volume-collapse condition of C5 holds with \(w=w_0\).
3. Derivative control as in C2 holds with \(K,A,w_0\).

The combined static package is the **disjunction** of these two packages. None of the three definitions itself contains a graph-manifold predicate or the desired graph presentation as a hypothesis. Connectedness, the lower bound on \(K\), and positivity of \(A\) are supplied separately by the theorems, not hidden inside the definitions.

**Three independently proved monotonicity lemmas.** If \(w_1\leq w_2\), then:

- volume collapse at curvature scale with \(w_1\) implies it with \(w_2\);
- the closed package with \(w_1\) implies the closed package with \(w_2\);
- the boundary package with \(w_1\) implies the boundary package with \(w_2\).

The second and third claims combine the easier volume and collar-error inequalities with the fact that the derivative-trigger interval \([w_2,\omega_3)\) is a subset of \([w_1,\omega_3)\). These proofs do not appeal to any of the seven admissions. They are what later permits taking the minimum of two independently supplied thresholds.

**Lean references:** GraphManifold.lean: `closedCollapseHypotheses` (11), `boundaryCollapseHypotheses` (17), `staticCollapseHypotheses` (22), `volumeCollapsedAtCurvatureScale_mono` (26), `closedCollapseHypotheses_mono` (35), `boundaryCollapseHypotheses_mono` (43).

<a id="collapse-output"></a>
## C7. What “a raw graph presentation” means in the conclusions

This output is a concrete presentation on the **same supplied carrier \(W\)**. It is not an abstract assertion that some homeomorphic manifold is a graph manifold. Its complete definition is translated in the topology section of this report; the parts needed for interpreting the collapse claims are these.

The output supplies a compact oriented cut carrier with finitely many nonempty connected components. Each component is a smooth, locally trivial **ordinary circle bundle** over a compact connected smooth surface, whose base may have boundary and need not be orientable. Exceptional Seifert fibers are not encoded as exceptional fibers of these particular bundles: a further decomposition, for example separating appropriate solid-torus blocks, must account for them when such a presentation is constructed.

There are finitely many paired boundary tori, specified smooth matching maps, actual collars, a quotient reconstruction homeomorphism onto \(W\), smoothness and orientation conditions on that reconstruction, a diffeomorphism on cut interiors, and smooth signed collars across the reassembled seams. Original external boundary tori have explicit collars and labels. Their cut-side and reassembled collars agree under reconstruction. Component ownership of the paired and external tori is recorded.

The paired tori are **not required incompressible**. Neither primeness, irreducibility, a JSJ uniqueness statement, geometric metrics on the blocks, nor a geometrization certificate is part of this output. Those belong to later refinements. The collapse theorems return existence of this data; they do not construct it in their current `sorry` proofs.

**Lean dependency:** `GC.GraphManifold.RawGraphPresentation`, Presentation.lean:129, together with its `CircleFibration`, `TorusPairing`, and `BoundaryTori` fields. Its topology translation remains the authority for the full field-by-field expansion.

<a id="collapse-admitted"></a>
## C8. The three admitted graph-presentation producers

**Admitted lemma 4: the separate nonnegative-curvature case.** Let \(W\) be a connected compact oriented smooth 3-manifold, with empty boundary, and let \(g\) be any smooth metric with \(\sec_g\geq0\) everywhere. Then there exists a raw graph presentation of \(W\), in the exact sense of C7.

There is **no small-volume assumption**, no prescribed \(K\), no derivative function \(A\), and no curvature-radius finiteness assumption here. This is a topological recognition/classification input for closed nonnegative-curvature 3-manifolds. It is separate because curvature-scale volume collapse is vacuous for infinite curvature radius, and the finite-radius argument in C10 cannot absorb such components.

**Admitted theorem 5: closed static collapse.** In precisely this order:

\[
 \forall K\in\mathbb N\ (K\geq10),\quad
 \forall A:\mathbb R\to\mathbb R\ \relax
 [\forall w\in(0,\omega_3),\ A(w)>0],\quad
 \exists w_0\in(0,\omega_3),
\]

such that **for every** connected compact oriented smooth 3-carrier \(W\) and **every** smooth metric \(g\) on it, the closed package of C6 implies existence of a raw graph presentation of \(W\).

The threshold depends on \(K,A\), not on \(W\), \(g\), or a finite family chosen later. The function \(A\) is real-valued and hence finite; no monotonicity, continuity, measurability, or local boundedness of it is assumed. Its values outside \((0,\omega_3)\) are unrestricted and irrelevant to these tests. The theorem does not give an explicit numerical threshold. The output need not respect any previously chosen circle fibration because no such fibration is an input.

**Admitted theorem 6: static collapse with nearly cuspidal boundary.** The same quantifier order supplies a possibly different \(w_0\in(0,\omega_3)\). For every connected compact oriented smooth carrier \(W\), smooth metric \(g\), and **supplied specific nearly cuspidal boundary** \(B\) with \(K\) and \(\delta=w_0\), assume the C5 volume-collapse condition and the C2 derivative control. Then there exist:

\[
 G:\text{a raw graph presentation of }W,
 \qquad e:\{0,\ldots,B.n-1\}\ \xrightarrow{\ \cong\ }\ \relax
 \{0,\ldots,G.n_{\rm ext}-1\},
\]

with

\[
 \operatorname{image}(G\text{'s external torus map numbered }e(i))=B.X_i
 \quad\text{for every }i.
\]

Thus the number and identity of the original boundary components are retained through an explicit index bijection and equality of actual image sets. The theorem does **not** say that the output torus parametrization equals the supplied cusp parametrization, that the output external collar equals the finite-regularity cusp collar, that prescribed longitude/meridian classes are retained, or that their circle fibrations agree. Such stronger relative assertions cannot be read into this statement merely from the word “labels.” The raw presentation itself has its own smooth marked collars, whose compatibility is part of C7.

The boundary theorem applies at nonempty boundary because \(B.n>0\). The derivative condition is imposed at every center, including the boundary and its depth-10 neighborhood; the volume-collapse condition alone has the C5 exception there.

**Lean references:** GraphManifold.lean: `exists_rawGraphPresentation_of_nonnegative` (52), `exists_closed_graph_threshold` (60), `exists_boundary_graph_threshold` (68).

<a id="collapse-composition"></a>
## C9. The common threshold and finite-family conclusion

**Composition theorem with a genuine Lean proof.** With exactly the \(K,A\) hypotheses of C8, there is one \(w_0\in(0,\omega_3)\) such that the combined static package of C6 yields a raw graph presentation for every connected compact carrier and metric.

The proof chooses the minimum of the admitted closed and boundary thresholds, uses the proved monotonicity statements, and applies the appropriate admitted theorem. Therefore it has no `sorry` in its own body but **does depend on `sorryAx`**. In the boundary case this combined theorem deliberately discards the additional boundary-index bijection and image identities returned by the stronger producer; its conclusion only says that a raw graph presentation exists.

**Finite-family composition theorem with a genuine Lean proof.** The same choice of \(w_0\) works simultaneously for every natural number \(n\), every family of connected compact carriers \(W_i\), \(i<n\), and every family of smooth metrics \(g_i\), provided each satisfies the combined static package with the same \(K,A,w_0\). The result is a family of actual raw graph presentations, one on each \(W_i\).

The threshold is chosen **before** \(n\) and the family. The family may be empty, \(n=0\), in which case the conclusion is the empty function. Each individual connected carrier is still nonempty. The conclusion retains the family index. It does not turn the disjoint union into a single connected manifold, identify any flow carriers, or produce one set of surgery/flow parameters.

**Lean references:** GraphManifold.lean: `exists_graph_threshold` (80), `exists_componentwise_graph_threshold` (97).

<a id="collapse-uniform"></a>
## C10. Absorbing a sequence of eventual bounds into one derivative function

**Admitted lemma 7.** Fix any \(K\in\mathbb N\); this lemma does not require \(K\geq10\). Let \((W_j,g_j)\), \(j\in\mathbb N\), be a sequence of compact carriers with smooth metrics. They are not assumed connected, nonempty, or boundaryless. Supply real numbers \(R_j>0\) and \(B_j\geq0\), with the following two bounds for each \(j\):

\[
 0<r<R_{g_j}(p)\quad\Longrightarrow\quad r\leq R_j
 \quad\text{for every }p\in W_j,
\]

and

\[
 D_k(g_j,p)\leq B_j\quad
 \text{for every }p\in W_j\text{ and every }0\leq k\leq K.
\]

The same \(B_j\) bounds all these derivative orders, although it may vary arbitrarily with \(j\). The finite radius bound is a substantive premise: if a nonempty component has infinite curvature radius, it fails, since all positive real radii would have to be at most \(R_j\). An empty carrier creates no difficulty because the pointwise premises are vacuous.

Assume in addition that for each \(w\in(0,\omega_3)\) there are an integer \(N(w)\) and a finite positive real \(C(w)\) such that, for all \(j\geq N(w)\), all centers \(p\), and all \(0<r<R_{g_j}(p)\),

\[
 V_{g_j}(p,r)\geq wr^3
 \quad\Longrightarrow\quad
 D_k(g_j,q)\leq C(w)r^{-k-2}
 \quad(0\leq k\leq K,\ q\in B_{g_j}(p,r)).
\]

The conclusion is the existence of **one** function \(A:\mathbb R\to\mathbb R\) satisfying \(A(w)>0\) for every \(w>0\), such that for **every** sequence index \(j\) and **every** \(w_0>0\), the derivative-control predicate of C2 holds for \((g_j,K,A,w_0)\).

In expanded form, all the above volume-triggered tests hold for every \(j\) and every \(0<w<\omega_3\), with \(C(w)\) replaced by this one \(A(w)\). No common tail \(N\) for all \(w\) is assumed or concluded. The output \(A\) may depend on the entire sequence and all its supplied bounds. It is chosen before the static collapse theorem selects \(w_0\). The conclusion for \(w_0\geq\omega_3\) is harmlessly vacuous, because its derivative-trigger interval is empty.

The intended elementary proof, still admitted in Lean, takes a maximum of the tail bound \(C(w)\) and finitely many quantities such as

\[
 B_jR_j^{k+2},\qquad j<N(w),\quad 0\leq k\leq K,
\]

then adds a positive constant. This explains why no uniform-in-\(w\) tail is needed. It is not a proof that these bounds arise from a Ricci flow: producing the sequence, intrinsic radius bounds, and eventual whole-ball estimates belongs elsewhere.

**Lean reference:** UniformDerivativeBounds.lean: `exists_common_curvature_derivative_bound` (10).

<a id="collapse-review"></a>
## C11. Mathematical review findings and approval points

No definite false assertion or explicit logical contradiction was found in this read-through of these seven modules and their directly relevant definitions. This is a qualified review conclusion: the seven admitted claims remain mathematical obligations, and the stronger output notion of a raw graph presentation must be checked against the topology translation. A successful Lean build is not evidence that the admitted mathematics is true.

The main distinctions that must survive subsequent implementation are:

1. **Intrinsic balls and all-point estimates.** The static assumptions use the carrier's own metric distance and volume and estimate derivatives at all points of the same ball. Center estimates or estimates on ambient flow balls are not interchangeable with them.
2. **Infinite curvature radius is handled separately.** The collapse-at-radius predicate is vacuous at infinity. The closed theorem asserts a graph conclusion even in that situation; it must use nonnegative-curvature recognition. The sequence lemma cannot be applied to a nonempty infinite-radius component.
3. **Finite cusp regularity is explicit.** Maps are \(C^{K+1}\), error derivatives are measured through \(K\), and the reference metric is smooth. No assertion that an arbitrary finite-order metric can be smoothed while preserving curvature is present here.
4. **Boundary control has exact scope.** There is no requirement that different cusp collars be disjoint. Boundary diameter uses the distance in \(W\), not its induced boundary metric. The distance-10 volume exception does not remove any derivative tests. These should be accepted deliberately, not supplied by readers from habit.
5. **Retained boundary labels are weaker than retained markings.** The stronger boundary theorem returns a bijection of indices with equality of image sets; it does not retain a prescribed parametrization, slope basis, fibration, or finite-regularity collar. The generic common-threshold theorem forgets even that extra bijection.
6. **The quantifier order is load-bearing.** Fix \(K,A\); then choose one \(w_0\); then allow all carriers and metrics. In the sequence lemma, fix the sequence first, then construct one \(A\), then invoke static collapse for \(w_0\). No uniform bound across all possible flows or sequences is asserted.
7. **This is an interface for the principal static theorem.** It does not separately state the local model, marker, cloud, one-sheet, or simultaneous cutoff constructions from the blueprint. Their proof work is currently inside the two large admitted threshold producers. It would be misleading to assign every Chapter 14 construction a separate Lean statement already present here.

For this report, actual source definitions were reread in the seven modules and in the dependent carrier, graph-presentation, Riemannian distance/ball/volume, pullback, curvature, tensor metric, and coordinate covariant-derivative files. Blueprint BBR03 (`master207B.tex`, lines 10592–10651) and LC89 (`master207A.tex`, lines 31165–31204) were reread to check the selected boundary and sequence contracts. Their strict inequalities and order of quantifiers agree with the translation above. Existing exact Kleiner–Lott source and errata checks recorded in `collapse_review.md` were not rerun and are not represented here as a new literature audit. No source archive, Lean file, theorem contract, or blueprint text was changed.

<a id="collapse-files"></a>
## C12. File key and declaration coverage

All paths below are relative to the checked code repository `GC_BASELINE_EXPORT` and lie under `DifferentialGeometry/`.

| Short file reference | Actual file |
|---|---|
| CurvatureScale.lean | `Geometry/Collapse/CurvatureScale.lean` |
| CuspBoundary.lean | `Geometry/Collapse/CuspBoundary.lean` |
| GraphManifold.lean | `Geometry/Collapse/GraphManifold.lean` |
| UniformDerivativeBounds.lean | `Geometry/Collapse/UniformDerivativeBounds.lean` |
| Hyperbolic/Cusp.lean | `Geometry/Hyperbolic/Cusp.lean` |
| Metric.lean | `Geometry/Connection/TensorNabla/Iterated/Metric.lean` |
| DerivativeNorm.lean | `Geometry/Curvature/Metric/DerivativeNorm.lean` |
| Presentation.lean (dependent definition) | `Topology/ThreeManifold/GraphManifold/Presentation.lean` |

The accompanying `collapse_coverage.json` maps every authored declaration to its exact section, original source line, admitted/independent/composition/definition status, and inspected audit axiom status. It covers all 35 authored declarations in the seven modules; automatically generated structure projections and recursors are represented through the complete field-by-field descriptions of their parent structures.
