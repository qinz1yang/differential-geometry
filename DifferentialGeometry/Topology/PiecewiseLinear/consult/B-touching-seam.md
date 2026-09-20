# B. Resolving the touching seam of the cross reglue (Moise Lemma 2, Cases 3 and 4)

*Consultation prompt, self-contained. Answer in English or Chinese.*

**Where to look.** Repository (private; reachable through the owner's GitHub account)
**https://github.com/liao9yuan/differential-geometry-dev**, branch **`moise-integration`**
(https://github.com/liao9yuan/differential-geometry-dev/tree/moise-integration). Read the head
of that branch only; every other branch diverges and line numbers will not match. Lean paths
below are relative to `DifferentialGeometry/Topology/PiecewiseLinear/`. The book is Moise,
*Geometric Topology in Dimensions 2 and 3*, GTM 47; pages are printed pages.



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
  What the tree has for this option: the entry cell of Lemma 2, the projection of the
  embedded disk upstairs, is proved locally injective and ≤ 2-to-1 with its boundary fields
  (`LoopTheorem/ProjectedCellInDouble.lean:23`); Moise's first paragraph is **proved in the
  half-space model** (`SingularGeneralPosition.lean:3447`: an ε-close simplicial map, still
  locally injective and ≤ 2-to-1, double point set a 1-manifold with boundary on `{ℓ = 0}`,
  a crossing at every double point, boundary kept in a prescribed neighbourhood); manifold
  level producers exist only one double point at a time, with an "unchanged off `V`" clause
  (`GeneralPositionWithin.lean:141`, `ProjectedBoundaryLocalNormalization.lean:20`). There is
  **no** finite-cover induction over charts and no global assembly of the singular set, and
  none of these theorems controls *which way* touching sheets separate.

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
