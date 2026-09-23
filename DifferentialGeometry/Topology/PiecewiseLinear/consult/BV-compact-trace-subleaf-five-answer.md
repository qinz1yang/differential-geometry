## 1. Verdict

**Existing inputs suffice mathematically, using the two quoted lane theorems and the completed sub-leaves 1–4.** The proposed cleaning route works, but its descent must construct a disk on a specified side. Reapplying the return-disk existence theorem, without controlling its output, is not that construction. Below, tracked sphere-disk theorems give the required side selection and a decrease by **at least two** in a finite point count.

This is a mathematical closure argument and an implementation contract, not a claim that sub-leaf 5 has been compiled. The two finite-diagram bridges needed by the assembly are stated precisely in §3; they can be implemented directly or matched to the lane’s existing generic lemmas. Neither requires a new named input, a change to a frozen statement, P6, or sub-leaf 6's primitive-degree theory.

**Source scope.** The inspected snapshot is `liao9yuan/differential-geometry-dev:moise-integration` at `3972017875424f604d43d26803de41fedabf21d2`. Paths below are relative to `DifferentialGeometry/Topology/PiecewiseLinear/`. The queue's item 15, the complete BQ answer, the frozen leaf and its variable block, the vocabulary, and the relevant tracked supporting modules were read. The two lane theorems are used with exactly the contracts quoted in BV §3; their untracked implementations were not independently inspected or audited. No Lean compilation was performed.

Write

\[
V_w=\texttt{section34CompactVertexBallImage src f₁ w},\qquad
S_w=\texttt{section34CompactVertexBallImage srcBd f₁ w},
\]
\[
E_e=\texttt{section34CompactSplitDiskImage src f₁ e},\qquad
\gamma_e=\texttt{section34CompactSplitDiskImage srcBd f₁ e},
\]

and put \(N=\bigcup_wV_w\), \(S=\operatorname{frontier}N\), \(\Sigma_t=\texttt{fblBd t}\), and \(F=\bigcup_t\Sigma_t\). Also write \(T_s\) for the actual face torus and \(\Theta_s=\operatorname{frontier}T_s\). A disk's boundary below is always its **intrinsic** named boundary, never its ambient frontier in \(\mathbb R^3\).

The assertion proved is: an actual separating trace circle gives a compression on some label, or a complete bigon slide on some label. For the proof, first split on whether any compression exists. In the other branch obtain the universal `hnc` and proceed below. The frozen parent already supplies this `hnc`; its universal `hnb` then excludes the resulting bigon, regardless of its label.

## 2. Shortest viable proof chain for A and B

### Frame consequences used by both arguments

Take `hf₁` from the graph frame. The following are tracked, not new geometric assumptions:

* `Section34CompactTargetCells.lean` supplies `Section34CompactCutFrame.isPLCellOn_vertexBallImage`, `isPLCellOn_splitDiskImage`, `splitDiskImage_eq_inter`, `exists_mem_splitDiskImage_of_ne`, `disjoint_splitDiskImage`, and `splitDiskImage_sdiff_subset_interior`. Consequently the vertex balls are closed PL balls with boundary exactly \(S_w\); distinct balls overlap only in splitting disks; distinct splitting disks are disjoint; and
  \[
  E_e\setminus\gamma_e\subset\operatorname{interior}N,
  \qquad S\cap E_e=S\cap\gamma_e.                 \tag{1}
  \]
* All index types needed here are finite, from the cut frame's two finite-face clauses. Sub-leaf 1 gives the finite disjoint circle decomposition for every face. Different faces' traces are also disjoint: invariant clause 4 puts the intersection of their **balls** inside \(\operatorname{interior}N\), while their traces lie on \(S\). Thus \(F\cap S\) is a finite family of mutually disjoint PL circles, with each point on precisely one circle.
* A **foreign closed splitting disk** misses \(\Sigma_s\). Indeed, if \(x\in\Sigma_s\cap E_e\), write \(E_e=V_u\cap V_v\) with the actual endpoint identity supplied by `splitDiskImage_eq_inter`. Since \(\Sigma_s\subset P_s\), invariant clause 3 forces both endpoint vertices to be incident to \(s\). Their union is the vertex set of \(e\), so \(e\) is incident to \(s\). This proves the contrapositive for the closed disk, not only for its rim.

The boundary identities and the boundary-subset facts used here are supplied by `PLCellOnBoundary.lean`. These arguments do not use `Section34CompactFaceDiskFamily` or any P6 trace-arc theorem.

### A. Extract an actual returning arc

**A1 — Start with the already supplied torus disk.** Let \(J\) be the actual trace component on \(\Sigma_s\), and let \(\Delta\subset\Theta_s\) be its PL filling disk with intrinsic boundary \(J\). Sub-leaves 3 and 4 supply this disk and the marked incident meridians, respectively. Set

\[
M=J\cap\bigcup_{e\text{ incident to }s}\gamma_e.
\]

It is finite by invariant clause 8. At a point of \(J\cap\gamma_e\), the surface-curve crossing in invariant clause 6 applies to the actual trace and actual meridian. It applies on \(\Theta_s\) as well: near that point only the two endpoint balls meet, both belong to \(T_s\), and the finite collection of other closed vertex balls can be excluded. Thus \(S\) and \(\Theta_s\) agree there. The finite disjoint circle decomposition identifies the local full trace with \(J\).

**A2 — Describe the intersections, rather than assume a collection of crosscuts.** For each incident \(e\), cut the parameter circle of \(\gamma_e\) at its finite intersections with \(J\). Between consecutive cut points, an open parameter interval is wholly in the intrinsic interior of \(\Delta\), or wholly outside \(\Delta\): its image is connected and misses the boundary \(J\). The transverse local model gives exactly one inside half-branch at each cut point. Closures of the inside intervals are therefore proper PL arcs in \(\Delta\), with distinct endpoints on \(J\), and no shared endpoints. A singleton intersection or an isolated tangency cannot occur in this description. Subdividing the finite PL circle at the cut points supplies the PL interval parametrisations.

The only possible closed intersection component would be an entire \(\gamma_e\) contained in the interior of \(\Delta\). That is impossible. In the marked boundary product, \(\gamma_e=\partial D^2\times\{\theta_e\}\) is essential in \(\partial D^2\times S^1\): projection to the first circle restricts to a circle homeomorphism, whereas a loop contained in a disk is nullhomotopic. Equivalently, the complement of the marked fibre in the boundary torus is an annulus, while a circle inside a surface disk bounds a disk and separates the torus. This is essentiality of a **specified product fibre**, not a primitive-degree assertion about \(J\), and not an inference from homology in the solid torus.

Hence the intersections with \(\Delta\) form a finite disjoint collection of proper arcs and no closed components. If \(M\ne\varnothing\), the collection is nonempty.

**A3 — Select the boundary interval by a finite integer argument.** For every intersection arc \(a\), consider the two closed intervals of \(J\) joining its endpoints. Each interval \(B_a\), together with \(a\), bounds a cap in \(\Delta\), meeting \(J\) exactly in \(B_a\). This elementary relative crosscut fact follows in a standard-simplex model of \(\Delta\) from the sphere-disk selection described in B4 below; it does not need a new surface classification theorem.

Among these finitely many pairs \((a,B_a)\), minimize

\[
\#\bigl(M\cap(B_a\setminus\partial B_a)\bigr).
\]

Suppose a marked point lies in the selected open interval. Its intersection arc \(b\) enters the selected cap. It cannot cross \(a\), and it meets \(J\) only at its two endpoints. Its other endpoint is therefore also in the selected open interval; it cannot be an endpoint of \(a\), because the intersection arcs have disjoint endpoints. The closed interval of \(J\) between these two points that stays inside \(B_a\setminus\partial B_a\) is a candidate for \(b\). Its open-interval count is smaller: at least the two endpoints of \(b\), previously counted, are no longer counted. This contradicts minimality.

Thus the selected trace interval \(B\) has endpoints \(p\ne q\) on one and the same \(\gamma_{e_0}\), and its open interval meets no incident meridian. By (1) and the foreign-disk exclusion above,

\[
 B\cap\bigcup_e E_e=\{p,q\}.                    \tag{2}
\]

A PL interval parametrisation \(\eta\) with \(\eta(0)=p\), \(\eta(1)=q\) follows by restricting and reparametrising the PL circle. `CircleArcSplit.lean` supplies the corresponding closed-circle-interval API. Notice that the selected **torus cap itself is not used as the return disk**: it may contain foreign mouths.

**A4 — Localize the trace interval to one actual vertex ball.** The connected set \(B\setminus\{p,q\}\) lies in \(S\subset N\) and misses all closed splitting disks. Its intersections with the finitely many closed \(V_w\) are a disjoint, relatively closed cover, because every overlap of distinct vertex balls lies in a splitting disk. Each member of this finite partition is also relatively open, so connectedness puts the entire open interval in one \(V_w\). Closedness puts its two endpoints there as well. Finally,

\[
 S\cap V_w\subset\operatorname{frontier}V_w=S_w,
\]

because an interior point of \(V_w\) is an interior point of \(N\). This gives \(B\subset S_w\), not an unspecified annular strip or a free target ball.

**A5 — The zero-intersection case and the supplied return disk.** If \(M=\varnothing\), (1) and foreign-disk exclusion say that \(J\) misses every splitting disk. The same finite closed-partition argument, now applied to the connected circle \(J\), gives \(J\subset V_w\) for one \(w\). The quoted `exists_compact_compression_of_vertex_trace_circle` applies with \(J\subset\Sigma_s\cap S\). It produces a compression on some label, contradicting `hnc` in the no-compression branch.

Otherwise A3–A4 supply every input of the quoted `exists_vertex_return_disk_avoiding_split_disks`. Invoke it **once to seed B**. Its output already solves the foreign-mouth problem. No step of A uses sub-leaf 6.

### B. Clean the return disk

**B1 — Specify the minimization domain and its finite measure.** A candidate is a tuple

\[
u=(t,w,e,B,R,D,\eta,\delta)
\]

satisfying all the following conditions in the fixed frame:

\[
\begin{gathered}
\eta:[0,1]\xrightarrow{\mathrm{PL}}B,\quad B\subset\Sigma_t\cap S_w,
\quad C_u:=\{\eta(0),\eta(1)\}\subset\gamma_e,
\quad B\cap\bigcup_fE_f=C_u,\\
\delta:[0,1]\xrightarrow{\mathrm{PL}}R,\quad
\delta(0)=\eta(0),\ \delta(1)=\eta(1),\quad R\subset\gamma_e,
\quad B\cap R=C_u,\\
\texttt{IsPLCellOn 2 D (B ∪ R)},\quad D\subset S_w\cap S,
\quad D\cap E_e=R,\quad
\forall f\ne e,\ \operatorname{Disjoint}(D,E_f).
\end{gathered}                                                   \tag{3}
\]

The arrows here mean `IsPLHomeomorphOn`, not merely continuous paths. Candidates range over **all face labels** and all tuples satisfying (3); cleanliness is not a membership condition. A supplies a candidate. The quoted standard-simplex parametrisation converts to the displayed `IsPLCellOn` by `isPLCellOn_id_of_isPLBall` in `PLCellOnBoundary.lean`.

Define

\[
 Z=\bigcup_t\left(\Sigma_t\cap\bigcup_f\gamma_f\right),
 \qquad \mu(u)=(R\cap F).\texttt{ncard}.
\]

The set \(Z\) is finite: there are finitely many face labels and each summand is finite by invariant clause 8. Since \(R\subset\gamma_e\), \(R\cap F\subset Z\). Thus this is a genuine finite cardinality. Minimize the nonempty set of natural numbers

\[
 \{n\in\mathbb N\mid\exists u\text{ satisfying (3)},\ \mu(u)=n\}.
\]

There is no assertion that the geometric candidate set is finite. Count the points on the **closed** arc \(R\), including its two old corners.

**B2 — Identify precisely where an interior trace can end.** Let \(L=B\cup R\) for a least candidate, and suppose \((D\setminus L)\cap F\ne\varnothing\).

At an interior point of \(D\), the disk is locally open in the surface \(S\). At an interior point of \(B\), the full trace locally equals the subarc \(B\): it is a subarc of one embedded trace circle, and all other trace circles are disjoint. Thus no additional trace branch can end on the open arc \(B\).

At a point of \(R\setminus C_u\), the disk has its usual half-disk neighbourhood in \(S\), with boundary on \(\gamma_e\). Invariant clause 6 says that the trace crosses this boundary, so exactly one half-branch is inside \(D\).

**Old corners require one more argument; transversality alone is not the whole justification.** At \(p\in C_u\), the splitting disk \(E_e\) is the intersection of its two endpoint vertex balls, and no third vertex ball contains \(p\). The endpoint statement and `subset_of_mem_splitDiskImage` prove the latter. Exclude all other balls by a neighbourhood. There \(S\) is the frontier of the union of the two endpoint balls, a PL sphere locally, by the ball-union results in `BallUnionFrontier.lean`.

On the boundary sphere \(S_w\), the complement closure of the disk \(E_e\) is a PL disk with boundary \(\gamma_e\), by `SphericalDiskComplement.lean`. Locally it is exactly \(S_w\cap S\): the relative interior of \(E_e\) lies inside the union, while the part of \(S_w\) off \(E_e\) lies on its frontier. The disk-in-sphere normal form makes this patch one of the two closed half-surfaces bounded by \(\gamma_e\). Since \(D\subset S_w\cap S\), the continuation of the trace through \(p\), opposite to the half-branch \(B\), is outside that patch and hence outside \(D\). Different faces or components cannot supply another branch at \(p\), by global trace disjointness. The same holds at the other corner.

Consequently, in a neighbourhood of either old corner, the trace lying in \(D\) is only \(B\). No interior component can end at an old corner.

**B3 — Obtain a proper trace crosscut.** Restrict the finite global trace circles to \(D\). For a circle other than the one containing \(B\), cut its parameter circle at its finite intersections with \(R\). For the circle containing \(B\), first remove the closed subarc \(B\), then cut the complementary interval at those intersections. Between cuts, membership in the interior of \(D\) is constant. The local facts in B2 exclude extra ends on \(B\), at old corners, and tangential or isolated contacts. The closures of the inside intervals are therefore finitely many proper PL arcs, with distinct endpoints in \(R\setminus C_u\). A component with no ends would be an entire PL trace circle inside \(D\).

Such a circle \(J'\) is impossible under `hnc`: it is contained in one \(\Sigma_{t'}\), in \(S\), and in \(D\subset V_w\), so the quoted vertex-circle compression theorem produces a forbidden compression. Thus the assumed dirty point yields a PL arc \(A\), parametrised by \(\alpha\), such that

\[
 A\subset\Sigma_{t'}\cap D,\qquad
 A\cap L=\{a,b\},\qquad
 \{a,b\}\subset R\setminus C_u,\qquad
 a=\alpha(0)\ne\alpha(1)=b.                       \tag{4}
\]

There is **no requirement** that \(t'\ne t\), or that this be a different trace component. A later return of the original circle is treated by precisely the same restriction argument.

**B4 — Construct the nested disk with tracked APIs.** Let \(u,v\in(0,1)\) be the unique parameters of \(a,b\) under \(\delta\). Set

\[
 R'=\delta\bigl([\min(u,v),\max(u,v)]\bigr),\qquad
 \delta'(r)=\delta((1-r)u+rv).
\]

Then \(\delta'\) is a PL parametrisation from \(a\) to \(b\),
\(R'\subset R\setminus C_u\), and \(A\cap R'=\{a,b\}\). Hence \(J'=A\cup R'\) is a PL circle. This uses only finite arc gluing; for a tracked implementation, halve both arcs and apply `isPLSphere_one_iUnion_union_iUnion_of_cycle` from `CircleArcCycle.lean` with `m = 0`.

Here is a direct replacement for any unknown `DiskCrosscutPair` signature. Put

\[
 E_{\rm out}=\overline{S_w\setminus D},\qquad X=E_{\rm out}\setminus R'.
\]

The sphere-disk complement results give

\[
 E_{\rm out}\text{ a PL disk},\quad
 D\cap E_{\rm out}=L,\quad
 \partial_{\rm intrinsic}E_{\rm out}=L.
\]

The last identity follows by applying the boundary-intersection theorem to \(E_{\rm out}\) and the double-complement identity. The exact tracked declarations are `IsPLSphere.isPLBall_closure_sdiff`, `inter_closure_sdiff_eq_image_stdSimplexBoundary`, and `closure_sdiff_closure_sdiff_eq` in `SphericalDiskComplement.lean`.

Because \(R'\subset L\), the theorem `IsPLHomeomorphOn.isPreconnected_sdiff_of_subset_boundary` in `SphereCircleCapSplit.lean` gives that \(X\) is preconnected. Moreover \(X\cap J'=\varnothing\): the part \(R'\) was removed, and (4) says that \(A\) meets \(E_{\rm out}\) only at \(a,b\in R'\).

Apply the **tracked** theorem

```lean
IsPLSphere.exists_isPLBall_with_boundary_disjoint_of_isPreconnected
```

from `SphereSchoenflies.lean`, with sphere \(S_w\), preconnected obstacle \(X\), and circle \(J'\). It returns a PL disk \(D'\subset S_w\) with intrinsic boundary \(J'\), disjoint from \(X\). Two set arguments now force the desired side:

\[
 D'\subset D,\qquad D'\cap L=R'.                 \tag{5}
\]

Indeed, a point of \(D'\setminus D\) would belong to \(E_{\rm out}\setminus R'=X\), since \(R'\subset D\). A point of \(D'\cap L\) outside \(R'\) would also belong to \(X\). Conversely, \(R'\) belongs to the prescribed boundary \(J'\) of \(D'\). In particular, \(D'\cap R=R'\). This is a proved relative subdisk selection, not a new existential disk that might be on the wrong side.

The cap fact used in A3 is obtained by the same construction after taking a standard triangular model of \(\Delta\), placing that triangle as a facet of a tetrahedral sphere, and taking a crosscut together with either of its boundary intervals. Removing that interval from the complementary disk selects the cap meeting the old boundary in exactly that interval; transport back to \(\Delta\).

**B5 — Check the new candidate and the decrease.** Equations (3)–(5) imply

\[
\begin{gathered}
 A\cap\bigcup_fE_f=\{a,b\},\qquad
 D'\cap E_e=D'\cap R=R',\\
 \forall f\ne e,\ \operatorname{Disjoint}(D',E_f),\qquad
 D'\subset S_w\cap S.
\end{gathered}
\]

For the first equality, use \(A\subset D\), the old splitting-disk avoidance, and \(A\cap R=\{a,b\}\). All other conditions in (3) follow from (4), the new parametrisations and the prescribed boundary of \(D'\). Thus
\((t',w,e,A,R',D',\alpha,\delta')\) is another candidate, whether or not its interior is already clean.

Both old corners are distinct points of \(F\cap R\), and neither belongs to \(R'\). Therefore

\[
 R'\cap F\subset (R\cap F)\setminus C_u,
 \qquad \mu(u')+2\le\mu(u),
\]

so, in particular, \(\mu(u')<\mu(u)\), contradicting minimality. Finiteness was established before using `ncard`. The new endpoints were already counted as points of the old \(R\); they are not newly introduced crossings.

It follows that the least candidate satisfies

\[
 \forall t',\quad\operatorname{Disjoint}(D\setminus(B\cup R),\Sigma_{t'}).
                                                               \tag{6}
\]

**Role of nesting.** The numerical inequality uses \(R'\subset R\setminus C_u\); it does not, by itself, use \(D'\subset D\). Nesting is how this proof preserves membership in the vertex-boundary/frontier patch and every splitting-disk avoidance clause, including the exact intersection with \(E_e\). A fresh call to the quoted return-disk existence theorem supplies no comparison with the old disk or marked arc. Without additional output-control proofs, that call is not a descent step. The construction above supplies the control directly, without making a claim that a second-side witness exists under the entire frame.

## 3. Only the missing implementation lemmas

The two statements below are **proposed, uncompiled proof interfaces**, not names attributed to existing exports. Their proofs are A1–A5 and B2–B3 above. The common context uses only the frozen vocabulary:

```lean
open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C V : Set E3} {h f₁ : E3 → E3} {ε : ℝ}
  {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3}
  {H : Finset E3 → Set E3}
  {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}
```

**First: actual separating component to an actual return arc.** Suggested new source location: `Section34CompactSeparatingReturn.lean`. The actual-component hypothesis below is supplied by sub-leaf 1; `hΔ` and `hΔT` are supplied by sub-leaf 3. The proof calls the completed marked-meridian result, sub-leaf 4, internally. It does not assume a return arc, a clean cap, or a primitive trace degree.

```lean
theorem exists_compact_vertex_return_arc_of_torus_disk
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage srcBd f₁) fbl fblBd)
    (hnc : ∀ t, ¬ Section34CompactCompression K K'
      (section34CompactVertexBallImage srcBd f₁)
      (section34CompactSplitDiskImage src f₁) fbl fblBd t)
    (s : Section34CompactSimplexIndex K 3) {J Δ : Set E3}
    (hJ : IsPLSphere 1 J)
    (hJcomp : J ∈ section34CompactTraceComponents
      (section34CompactVertexBallImage src f₁) fblBd s)
    (hΔ : IsPLCellOn 2 Δ J)
    (hΔT : Δ ⊆ frontier (section34CompactFaceTorus
      (section34CompactVertexBallImage src f₁) s)) :
    ∃ (w : Section34CompactVertexIndex K K')
      (e : Section34CompactEdgeIndex K K') (B : Set E3) (η : ℝ → E3),
      IsPLHomeomorphOn η (Icc 0 1) B ∧
      B ⊆ J ∧
      B ⊆ section34CompactVertexBallImage srcBd f₁ w ∧
      ({η 0, η 1} : Set E3) ⊆ section34CompactSplitDiskImage srcBd f₁ e ∧
      B ∩ (⋃ e' : Section34CompactEdgeIndex K K',
        section34CompactSplitDiskImage src f₁ e') = {η 0, η 1}
```

**Second: a dirty return disk contains a proper trace crosscut with no old-corner endpoints.** Suggested new source location: `Section34CompactReturnDiskDescent.lean`. Every hypothesis is a field of the existing candidate (3), a frame hypothesis, or the explicit negation of cleanliness. In particular the conclusion, not an input, says that the new endpoints avoid the old corners.

```lean
theorem exists_compact_trace_crosscut_in_return_disk
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage srcBd f₁) fbl fblBd)
    (hnc : ∀ t, ¬ Section34CompactCompression K K'
      (section34CompactVertexBallImage srcBd f₁)
      (section34CompactSplitDiskImage src f₁) fbl fblBd t)
    (s : Section34CompactSimplexIndex K 3)
    (w : Section34CompactVertexIndex K K')
    (e : Section34CompactEdgeIndex K K')
    {B R D : Set E3} {η δ : ℝ → E3}
    (hη : IsPLHomeomorphOn η (Icc 0 1) B)
    (hBP : B ⊆ fblBd s)
    (hBS : B ⊆ section34CompactVertexBallImage srcBd f₁ w)
    (hends : ({η 0, η 1} : Set E3) ⊆
      section34CompactSplitDiskImage srcBd f₁ e)
    (hmeet : B ∩ (⋃ e' : Section34CompactEdgeIndex K K',
      section34CompactSplitDiskImage src f₁ e') = {η 0, η 1})
    (hδ : IsPLHomeomorphOn δ (Icc 0 1) R)
    (hδ0 : δ 0 = η 0) (hδ1 : δ 1 = η 1)
    (hR : R ⊆ section34CompactSplitDiskImage srcBd f₁ e)
    (hBR : B ∩ R = {η 0, η 1})
    (hD : IsPLCellOn 2 D (B ∪ R))
    (hDloc : D ⊆ section34CompactVertexBallImage srcBd f₁ w ∩
      frontier (⋃ v : Section34CompactVertexIndex K K',
        section34CompactVertexBallImage src f₁ v))
    (hDE : D ∩ section34CompactSplitDiskImage src f₁ e = R)
    (hother : ∀ e' : Section34CompactEdgeIndex K K', e' ≠ e →
      Disjoint D (section34CompactSplitDiskImage src f₁ e'))
    (hdirty : ((D \ (B ∪ R)) ∩
      (⋃ t : Section34CompactSimplexIndex K 3, fblBd t)).Nonempty) :
    ∃ (t : Section34CompactSimplexIndex K 3) (A : Set E3) (α : ℝ → E3),
      IsPLHomeomorphOn α (Icc 0 1) A ∧
      A ⊆ fblBd t ∧ A ⊆ D ∧
      A ∩ (B ∪ R) = {α 0, α 1} ∧
      ({α 0, α 1} : Set E3) ⊆ R \ {η 0, η 1}
```

These are signatures only; no proof bodies are asserted here. The second deliberately stops at a crosscut. There is no need to commission another general disk theory: B4 obtains the relative subdisk from tracked results with all their hypotheses discharged. The possible verbosity of the candidate-field binder list is not extra mathematics.

**Call order.** Completed sub-leaves 1, 3 and 4 → first bridge → quoted return-disk theorem → least candidate → second bridge if dirty → interval restriction and `CircleArcCycle` → `SphericalDiskComplement` → `SphereCircleCapSplit`'s preconnectedness theorem → `SphereSchoenflies`'s obstacle-disjoint disk selector → (5), candidate inheritance, finite-cardinality contradiction → final bigon witness. The quoted vertex-circle compression theorem is used in the zero-crossing branch of the first bridge and the closed-component branch of the second. The completed homology selection of sub-leaf 2 remains upstream of this separating branch; no new use of it is needed here.

## 4. Clause-by-clause final `Section34CompactBigonSlide` witness

Choose a least candidate and, in the order of the frozen existential binders, use

\[
 (w,e,B,B',Bb,Dj,Jd)
   =(w,e,B,R,\{\eta(0),\eta(1)\},D,B\cup R)
\]

at its face label \(t\). The twelve conjuncts in `Section34CompactVocabulary.lean` are checked as follows.

| Frozen conjunct | Supply |
|---|---|
| `IsPLCellOn 1 B Bb` | The PL interval parametrisation `η`. Compose with the affine standard-one-simplex/interval identification and use `isPLCellOn_id_of_isPLBall`; its boundary is exactly the endpoint pair. |
| `B ⊆ fblBd t` | Candidate condition `hBP`. |
| `B ⊆ tgtVBd w` | Candidate condition `hBS`, with the actual `srcBd` image, not a free sphere. |
| `Bb ⊆ tgtEBd e` | Candidate condition `hends`. |
| `B ∩ ⋃ e', tgtE e' = Bb` | Candidate condition `hmeet`. A proves it for **all closed splitting disks** using (1) and foreign-disk exclusion; every descendant inherits it as in B5. |
| `IsPLCellOn 1 B' Bb` | The same standard-simplex conversion for `δ`; `hδ0` and `hδ1` identify the endpoint pair with `Bb`. |
| `B' ⊆ tgtEBd e` | Candidate condition `hR`. |
| `B ∩ B' = Bb` | Candidate condition `hBR`. |
| `IsPLCellOn 2 Dj Jd` | Candidate condition `hD`, initially from the quoted standard-simplex disk parametrisation and subsequently from the selected disk's prescribed boundary. |
| `Dj ⊆ tgtVBd w ∩ frontier (⋃ w, tgtV w)` | Candidate condition `hDloc`. It comes from the quoted return theorem and is preserved by the proved inclusion `D' ⊆ D`. |
| `Jd = B ∪ B'` | The definition of the chosen `Jd`. |
| `∀ t', Disjoint (Dj \ Jd) (fblBd t')` | Equation (6), the least-candidate contradiction. This quantifier includes the selected label itself and every other face. |

Endpoint distinctness follows from injectivity of `η` and `δ` on `[0,1]`, since `0 ≠ 1`. No injectivity of a closed loop on an interval is assumed. Nothing here substitutes an ambient `frontier D` for `Jd`. Nor is the stronger compression requirement of avoiding other **face balls** silently substituted for the bigon predicate's actual requirement of avoiding all face **boundaries** in the disk interior.

For the parent, apply `hnb t` to this witness. For a standalone operation dichotomy, return the compression from the initial case split or this bigon in the no-compression branch. Both choices respect the universal quantification in `hnc` and `hnb`.

## 5. First exact obligation and owner decision

**No step above requires a new hypothesis not derivable from the frozen frames and the supplied sub-leaves. No statement-false verdict or full-frame counterexample is asserted.** In particular, the alleged difficulty of choosing the correct side of a new disk is removed by the explicit obstacle \(\overline{S_w\setminus D}\setminus R'\); it is not delegated to another unexplained existence theorem.

The first implementation obligation not supplied by BV's two quoted contracts is the first signature in §3: under `hnc`, turn the actual torus filling disk into a parametrised return arc in one actual `srcBd` vertex-ball image, with the exact all-closed-splitting-disk intersection. **Classification: proof missing at the level of the supplied contracts, not a missing frame input and not a false statement.** The second signature is the remaining finite restriction bridge for cleaning. Its most consequential internal obligation is B2's old-corner exclusion, using the actual vertex-side patch. Proving only “the interior intersections are arcs” without that endpoint location is insufficient.

The untracked `DiskCrosscutPair` source was not accessible at the pinned commit, as the consult warns. No declaration from it is guessed. That API uncertainty is not a blocker for this route, because the relative subdisk is constructed using the tracked declarations identified in B4.

The extreme cases are accounted for: no meridian intersection gives the quoted vertex-circle compression; a closed interior trace gives the same contradiction on its actual label; two distinct old corners are counted and removed in every descent; a return to the same face or same circle is permitted; and the candidate with only its two corner crossings cannot be dirty under `hnc`, since B3 would produce two further crossing endpoints. All point counts are proved finite before invoking `ncard`. Lower-dimensional cells use their intrinsic boundary throughout.

A full nondegenerate joint inhabitant of the original cut frame, graph frame and invariant bundle was not independently constructed in this review. The conditional proof above does not certify the upstream producer or its fixture, and lack of such a checked fixture is not evidence of vacuity. The owner decision supported here is to keep the frozen interface, implement the two local bridges in §3, and use the relative sphere-disk selection of B4 rather than reopening homology, primitive-degree theory, the foreign-mouth theorem, P6, or the manifold twin.
