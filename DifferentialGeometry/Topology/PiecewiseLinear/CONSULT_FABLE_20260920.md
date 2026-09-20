# Consultation prompts — Fable lead session, 2026-09-20

Paste-ready prompts for an external consultant. Each is self-contained. They supersede
prompts 1 and 2 of `CONSULT_QUEUE_20260920.md`, whose premises have since changed.

Repository **https://github.com/liao9yuan/differential-geometry-dev**, branch
**`moise-integration`**, browsable at
**https://github.com/liao9yuan/differential-geometry-dev/tree/moise-integration**.
Read the head of that branch only; every other branch diverges and line numbers will not
match. Paths below are relative to
`DifferentialGeometry/Topology/PiecewiseLinear/` unless they start with a slash.

---

## A. Re-cutting the §34 transition: obligations strictly smaller than Moise 35.2

*(Self-contained. Paste whole. Answer in English or Chinese.)*

### State

The target is Moise, *Geometric Topology in Dimensions 2 and 3* (GTM 47), Theorem 35.2
(printed p. 251): PL approximation of a topological embedding of a polyhedral 3-manifold
with boundary `K ⊆ M₁` into a PL 3-manifold `M₂`. In Lean (`Transition361.lean:251`):

```lean
def Moise352 (n : ℕ) : Prop :=
  ∀ {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂]
    [HasGroupoid M₁ (plGroupoid n)] [HasGroupoid M₂ (plGroupoid n)]
    {K : Set M₁}, IsLocallyFinitePolyhedralManifoldWithBoundary (n := n) n K →
    ∀ {h : M₁ → M₂}, Topology.IsEmbedding (K.domRestrict h) →
    ∀ (φ : M₁ → ℝ), ContinuousOn φ K → (∀ x ∈ K, 0 < φ x) →
    ∃ f : M₁ → M₂, IsPLHomeomorphInto n f K ∧ ∀ x ∈ K, dist (f x) (h x) < φ x
```

Proved, with axioms exactly `propext, Classical.choice, Quot.sound`:

```
Moise352InwardPush 3 ∧ Moise351 ∧ Moise352SkeletonExtension 3
    → Moise352 3                         (SkeletonReduction.lean:236)
    → PLApproximationManifold 3          (Endgame.lean)
```

**What we found today, and the reason for this prompt.**
`Moise352SkeletonExtension n` (`SkeletonReduction.lean:208`) has the *same binder prefix
and the same conclusion* as `Moise352 n`, with two hypotheses inserted before the
conclusion: the inward push at every tolerance `ψ`, and Theorem 35.1 on every open
`U ⊆ K` for every locally finite polyhedral graph `G ⊆ U`. So
`Moise352 n → Moise352SkeletonExtension n` holds by weakening, and the "reduction" is modus
ponens: **the open obligation is all of 35.2 given 35.1 and the push, i.e. the whole of
the §34 argument, undecomposed.** It is true (at `n = 3`), it is faithful to the logical
shape of printed p. 251, and it records no progress.

The other two inputs:

* `Moise352InwardPush 3` (`SkeletonReduction.lean:158`) is proved for compact `K`
  (`ControlledInwardPush.lean:554`). We tried to refute the non-compact statement at the
  quantifier extremes and could not; it localises (exhaustion by compact stages, per-stage
  collar heights tapering to zero on the seams), needs no new vocabulary, and is in
  progress (~1–1.4k lines). **Not a question for you.**
* `Moise351` (`MoiseChain.lean:191`), Theorem 35.1, is open with no producer. It asks for
  `ContinuousOn φ U ∧ ∀ x ∈ U, 0 < φ x` where the book asks only strong positivity, so it is
  a slightly weaker deliverable than the book's; its only consumer feeds it continuous `ψ`.

Mismatches between the tree and the book that you should know about:

1. `Moise341` (`MoiseChain.lean:99`) is stated `EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ
   (Fin 3)` with a constant `ε` and source `IsPLBall 3 C`. Printed p. 249 applies 34.1 as
   `f_v : C''_v → M₂` with `M₂` an arbitrary PL 3-manifold. The Lean statement has no
   producer and no consumer.
2. §34 is written for a **finite** complex in **ℝ³** (Lemma 5(7) uses "the unbounded
   component of ℝ³ − …"; Lemma 8's termination uses finiteness). The Lean obligation is
   locally finite, in an arbitrary — possibly non-orientable — PL 3-manifold.
3. "One simplex at a time" (p. 251) is *not* an induction over skeleta. Pp. 244–246 perform a
   single seven-stage extension over a fixed decomposition — `Bd D_σ ∩ Bd D_e`, `Bd D_e`,
   `Bd C_v ∩ Bd D_σ`, `X(σ³,v)`, `C_v`, `D_σ`, `C(σ³)` — after Lemmas 1–11 and Operations
   1–2 have fixed the combinatorics globally. There is no inductive hypothesis, no tower and
   no agreement clause. Two earlier formulations of ours that *did* introduce a tower with an
   agreement clause (`Moise352Stages`, `Moise352StageStep`) were both **false**, for
   quantifier reasons, so please do not reintroduce one without checking it at the extremes
   (tolerance huge; tolerance sequence fixed before the family).
4. `n` is unconstrained in `Moise352*`, and `Moise352 n` is false for `n ≥ 5`
   (homeomorphic, not PL-homeomorphic closed PL manifolds). Only `n = 3` is instantiated.

Tree inventory against the book's dependency chain (status: PROVED / CONDITIONAL on … /
STATED ONLY = a `def … : Prop` with no producer / ABSENT):

| Book | Tree | Status |
| --- | --- | --- |
| 25.1 / 25.2 | `MoiseChain.lean:31,36` | STATED / CONDITIONAL (Lemma 2 of the Loop theorem chain, separate effort) |
| 26.4 extended Loop theorem | `MoiseChain.lean:57` | STATED ONLY |
| 30.4 shell ⇒ separating PL sphere | `MoiseChain.lean:86` | CONDITIONAL on 25.2 |
| 30.5 nested 3-cells | `MoiseChain.lean:92`; tame form `TameNestedCells.lean:34` | wild: STATED ONLY; tame: CONDITIONAL on 30.4 |
| 30.6 / 30.7 toroidal shell, nested solid tori | `MoiseChain.lean:118,128` | STATED ONLY |
| 30.8 spine generates π₁ of a solid torus | `MoiseChain.lean:257` | STATED ONLY |
| 27.3 / 28.8 polygon in an annulus | — (annulus infrastructure exists) | ABSENT |
| 32.1–32.4 pseudo-cells, tubes | — | ABSENT |
| 33.1 | `MoiseChain.lean:136` | STATED ONLY, faithful |
| 34.1 | `MoiseChain.lean:99` | STATED ONLY, wrong form (mismatch 1) |
| 35.1 | `MoiseChain.lean:191` | STATED ONLY |
| §34 transition | `SkeletonReduction.lean:208` | ≡ 35.2 |

Proved infrastructure that exists: dual cells and splitting disks (`DualCells.lean`, incl.
`IsCombinatorialManifold.isPLBall_dualCell`), derived and regular neighbourhoods, general
position (`GeneralPosition.lean`, ~5.7k lines), annuli, `IsTopologicalSolidTorus`, a 2-D PL
Schoenflies theorem, PL map approximation with an agreement clause
(`exists_isPLOn_dist_lt_eqOn`, `ManifoldApproximation.lean:347`, dimension-free),
locally finite piece towers with a gluing lemma (`LocallyFinitePieceTower.lean:148`).

### The questions

**Q1. The re-cut.** Replace `Moise352SkeletonExtension 3` by a DAG of obligations, each
*strictly weaker than 35.2* and each statable in the vocabulary above, such that a proved
reduction to `Moise352 3` remains. Please give exact statements (Lean-ish is ideal), not
strategy prose. In particular: (i) the precise form of each of Lemmas 1–13 and Operations
1–2 of §34 that the seven-stage extension consumes, as transported to §35's setting;
(ii) the seven stages themselves as seven extension lemmas with their exact input and
output clauses; (iii) which statement carries the tolerance, and how it is chosen — *before*
or *after* the subdivision, the regular neighbourhood and the map from 35.1. This is the
step we have twice formulated falsely.

**Q2. ℝ³ versus a manifold target, finite versus locally finite.** Where §34 uses ℝ³
(unbounded component, Lemma 5(7)) or finiteness (Lemma 8), what replaces it on printed
pp. 248–251? State exactly the "two reductions" of the first paragraph of the proof of 35.2
and say whether the argument can be run *without* them by localising to small stars whose
images lie in single charts of `M₂`. If chart-localisation works, give the precise
smallness condition and where it is chosen.

**Q3. The right 34.1.** State 34.1 in the form p. 249 uses (`M₂` a PL 3-manifold, pointwise
or constant tolerance?) and say whether it follows from the ℝ³ form by a chart argument, or
whether the ℝ³ form is genuinely weaker.

**Q4. The minimal prerequisite set.** Which of 26.4, 30.5 (does the *tame* form suffice
everywhere it is used in §§33–35?), 30.6, 30.7, 30.8, 28.8, 32.1–32.4 are genuinely on the
path to 35.2 at `n = 3`, with the page where each is consumed?

**Q5. A shorter route?** Is there a published route to the conclusion of `Moise352 3`, or
directly to `PLApproximationManifold 3` (every homeomorphism of PL 3-manifolds is
approximable by PL homeomorphisms), that is *shorter given this tree* — Bing's side
approximation (1957/1959), Hamilton's torus-trick proof (1976), Shalen (1984), or other?
For each candidate give the precise statement to import, its own prerequisites, and whether
those prerequisites are closer to what the tree has than §§32–34 are. We want this judged,
not merely listed: a route that needs the Loop theorem anyway is not a shortcut.

**Q6. Honest size.** How many independent theorems of the size of 33.1 stand between the
tree and 35.2 on the best route? We currently believe: 26.4, 32.x, 33.1, 34.1, 35.1 and the
§34-style transition — six chapter-scale items — and would like that checked rather than
confirmed.

### Constraints on the answer

Exact mathematical statements; cite Moise by printed page and say what you could not verify;
do not weaken an existing statement (several are consumed verbatim by proved reductions);
if something already built is aimed at the wrong target, say so plainly. **"This statement
of yours is false, here is the counterexample" is the most valuable answer you can give:**
seven statements on these chains have turned out false, each for a quantifier or
construction-reading reason.

---

## B. Resolving the touching seam of the cross reglue (Moise Lemma 2, Cases 3 and 4)

*(Self-contained. Paste whole. Answer in English or Chinese.)*

### State

Moise §25, Lemma 2 (printed pp. 184–187): a PL singular 2-cell `D : Δ → M`, locally a
homeomorphism and at most two-to-one, is put in *normal* position (singular set = disjoint
polygons `Γ_i` in `Int M` and broken lines `A_j` meeting `Bd M` exactly in their end-points;
crossing, never touching, singularities), and the complexity `m + n` is reduced to zero by
four cases. For a boundary arc `A_j` (Cases 3 and 4, pp. 185–187) Moise writes only:

> We "cut |D| apart at A_j," getting two normal singular 2-cells D₁ and D₂, with boundaries
> L₁ = συ⁻¹ and L₂ = σφυτ.

and then the word computation. In our formalisation the source disk is cut along the two
crosscuts `a₁b₁`, `a₂b₂` into three cells `U₁, U₂, U₃` (`LoopTheorem/CutAndPaste.lean`).

* `D₁` is the **direct candidate** `U₁ ∪_g U₃` (middle band discarded). It is proved normal,
  proved to have an *injection* of its branches into the branches of `D` missing `A_j`
  (it loses every branch with a sheet in the discarded band — a bijection is false), and so
  descends. Done.
* `D₂` is the **cross reglue**, which must use all three cells to have boundary `σφυτ`. We
  proved: same image as `D`, same double point set as `D` (**including `A_j`**), locally
  injective, fibre ≤ 2, and a normal crossing at every double point **off** `A_j`
  (`LoopTheorem/CrossRegluedCellFields.lean`, `CrossRegluedCellCrossing.lean`). Along `A_j`
  its two sheets are two bent L-shaped sheets that **touch along the axis and do not cross**;
  we proved that the crossing condition fails at every interior point of `A_j`, so the cross
  reglue is *not* a normal singular 2-cell. Moise's sentence silently includes a small push
  separating the two bent sheets. **That push is the subject of this prompt.**

What the tree has built for the push:

1. *The model* (`LoopTheorem/CrossSeamResolution.lean`, proved): in the cylinder
   `[-1,1]² × [0,1]` with the cross `{x = 0} ∪ {y = 0}`, replacing the two bent arcs by the two
   chords of the square, fibrewise, is one piecewise affine map `crossSeamResolve`, the
   identity on the lateral wall, with empty double point set.
2. *The transport* (`LoopTheorem/CrossSeamTube.lean`, `ResolvedCellNormal.lean`,
   `BoundaryCaseReduction.lean`, proved **conditionally**): given a "tube" — a map
   `chart : (ℝ × ℝ) × ℝ → M`, continuous and injective on the closed cylinder, core ↦ `A_j`,
   `chart '' (cross × [0,1]) = D(Δ) ∩ chart '' cylinder`, an open `U ⊇ chart '' cylinder` with
   `doublePointSet D ∩ U = A_j` — **and** a reading of the cross reglue `G` in the tube
   (`coord : G⁻¹(tube) → bent model source`, bijective, `G = chart ∘ include ∘ coord`), the
   resolved cell `chart ∘ crossSeamResolve ∘ coord` is normal and deletes exactly the branch
   `A_j`; then the whole boundary case is assembled into one theorem
   (`exists_descendingSurgery_of_crossSeamTube_reversing`).
3. *Ambient.* `M` is the **double** of the triangulated 3-manifold `|K|`
   (`LoopTheorem/LemmaTwo.lean:145`, charted by `combinatorialChartedSpace (double 3 K)`), so
   `Bd|K|` is a two-sided PL surface `BdM` inside a boundaryless `M`, and `B ⊆ BdM`.

What is open, and what we found wrong with our own contract today:

* The tube producer `IsCrossSeamTubeProducer` (`CrossSeamTube.lean:928`) has no proof and,
  as stated, is **insufficient**: (i) it has no PL clause, while the resolved cell must be a
  `SingularTwoCell` and hence PL — today `cell : SingularTwoCell M` is simply *assumed* with
  `resolved_eq` pinning its values; (ii) it quantifies over all `BdM B : Set M`, and
  `B := range D.boundary` (1-dimensional) is a legal instance for which the downstream
  hypothesis `chart '' endDisks ⊆ B` is false, so a 2-dimensionality hypothesis on `B` is
  missing; (iii) `[T2Space M]` and `[HasGroupoid M (plGroupoid 3)]` are missing; (iv) nothing
  records that the tube (hence the resolved cell) stays on the `|K|` side of `BdM` in the
  double; (v) the clauses saying `∂G` crosses the tube wall transversally (`hcocont`,
  `hlateral` in the assembly) cannot come from a tube producer alone — they couple the tube to
  the reglue, so the honest contract is a **joint** tube-plus-reading producer.
* The pointwise normal form (`HasPLNormalDoubleCrossingAt`: near each double point a PL chart
  carrying the two sheets to two planes `P₀, Q₀`, `P₀ ⊔ Q₀ = ⊤`, plus a transversality
  functional at boundary points) is germ-level; **nothing is uniform along the arc.**
* Nearest tools in the tree: `ArcChainNeighborhood.lean:57` and
  `ArcCellNormalizationInduction.lean:19` (a PL ball neighbourhood of a simplicial arc, and a
  cell-by-cell induction producing one PL chart along the whole arc — both **only for arcs
  interior to the manifold**, and relative to the arc alone, not to a 2-complex);
  `BicollarManifold.lean:94` `PLPieceIn.exists_bicollar` (a two-sided PL surface in a PL
  3-manifold has a PL product neighbourhood `S × [-1,1]`); `BallPair.lean` (PL ball pairs
  `(B^m, B^k)`; no (ball, 2-complex) pair predicate); a 2-D PL Schoenflies theorem;
  dual cells; derived neighbourhoods; **no** uniqueness-of-regular-neighbourhoods theorem.

### The questions

**Q1. Which construction of the push is cheapest to make rigorous here?** Candidates we see:

  (a) *Relative product tube*: a PL homeomorphism of pairs
  `(N, N ∩ D(Δ)) ≅ ([-1,1]² × [0,1], cross × [0,1])` for a regular neighbourhood `N` of `A_j`
  in the double, with `N ∩ BdM` = the two end squares. Proof sketch we have in mind: make
  `D(Δ)`, `A_j`, `BdM` subcomplexes; stars of the arc's vertices in a derived subdivision are
  cones `v * Lk(v)` with `(Lk(v), Lk(v) ∩ D(Δ)) ≅ (S², suspension of 4 points)` by 2-D
  Schoenflies; match consecutive stars along their common disk; cone-extend. Is this correct,
  what is the precise lemma list, and is there a published statement to cite (regular
  neighbourhoods of pairs / of a polyhedron *relative to* a subpolyhedron — Hudson, Rourke–
  Sanderson, Cohen)? What goes wrong, if anything, at the two end-points on `BdM`?

  (b) *Bicollar push of one bent sheet*: `G` is injective on a thin strip around one seam, so
  the strip's image `S_b` is an embedded two-sided PL disk; take its bicollar `S_b × [-1,1]`
  (existing theorem); the other bent sheet lies in `S_b × [0,1]` near the axis, touching
  `S_b × 0` exactly along `A_j`; add a PL bump to its height. No cross model, no pair
  homeomorphism. Is this sound? What exactly must be proved about (1) the other sheet lying on
  one side, (2) compatibility of the bicollar with `BdM` at the two ends so that the pushed
  boundary stays in `B`, (3) no new double points with the rest of `G(Δ')`, (4) the pushed
  cell again having normal crossings near the *ends* of the pushed region?

  (c) *Controlled general position*: a theorem "a locally injective, ≤ 2-to-1 PL singular cell
  can be perturbed to normal, moving only near the non-crossing set, without creating
  branches". We need a general-position theorem anyway to enter the induction (Moise's first
  paragraph: "we can make slight perturbations of D … so as to put |D| into general
  position"). Can one theorem serve both purposes, and what is its exact statement with the
  control needed to guarantee `complexity(D₂') < complexity(D)`? A generic perturbation can
  push touching sheets *through* each other; what hypothesis prevents that?

  (d) *Simplicial/source-level*: `D` is simplicial for `K` and `K(Δ)` (p. 187). Is there a
  purely combinatorial description of `D₂` after the push (a different simplicial map on a
  subdivided source) that avoids every ambient product structure?

Please rank (a)–(d) by total proof burden *in this tree*, and for the winner give the exact
statement(s) to prove, in Lean-ish form against the definitions quoted above.

**Q2. The ends.** At an end-point of `A_j` on `BdM`, both sheets of `D` cross `BdM`
transversally and `∂D` has a transverse self-crossing inside `B`. After the push, the boundary
curve of `D₂` must (1) still lie in `B`, (2) be freely homotopic in `B` (indeed in the tube's
end disk) to the raw cross-reglue boundary `σφυτ`. We have (2) proved *given* the tube
(`SeamBoundaryHomotopy.lean`). For your preferred construction, what makes (1) true?

**Q3. Side of the boundary.** `M` is the double. A normal cell's image meets `BdM` only in its
boundary circle (`image_inter_boundary`), so its interior lies in one of the two copies of
`Int|K|`. Is "which copy" something we must carry through the induction, or is it harmless by
the reflection symmetry of the double? If it must be carried, where does it enter?

**Q4. Is anything false?** Test at the extremes: a branch whose two end-points coincide in
`BdM`? (We believe excluded: `A_j` is an embedded arc.) An arc `A_j` for which the two
crosscuts `a₁b₁`, `a₂b₂` in `Δ` share an end-point? A boundary arc along which `D` is
orientation-*preserving* (Case 4) — does the same push work verbatim with `L₂ = στ⁻¹υφ⁻¹`?
A non-orientable neighbourhood of `A_j` cannot occur for an arc (the tube is a ball) — confirm.
**A considered "this is false" is the most valuable possible answer.**

**Q5. Closed branches, same question.** Case 1 (p. 184–185) replaces two rectangles of the
mapping torus of `(x,y) ↦ (y,x)` by the planes `x − y = ±1`; we have the model
(`ClosedSeamResolution.lean`) but no producer of the cylindrical diagram for a real closed
branch, and no straightening of an arbitrary PL monodromy of the cross to `Prod.swap`. Does
your answer to Q1 also give the closed case (tube = mapping torus), and what is the extra
lemma for the monodromy?

### Constraints on the answer

Exact statements (Lean-ish welcome); cite by printed page and say what you could not verify;
do not weaken existing statements; if the tube layer we built is aimed at the wrong target,
say so plainly and say what replaces it.
