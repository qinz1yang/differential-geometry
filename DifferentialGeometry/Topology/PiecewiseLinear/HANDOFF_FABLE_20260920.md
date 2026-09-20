# Handoff prompt — Moise Lemma 2 and 35.2

*(Self-contained. Paste whole. Answer in English or Chinese.)*

## Where to look

Repository **https://github.com/liao9yuan/differential-geometry-dev**, branch
**`moise-integration`**, browsable at
**https://github.com/liao9yuan/differential-geometry-dev/tree/moise-integration**.
Read the head of that branch; no other branch matches these line numbers.

The book is Moise, *Geometric Topology in Dimensions 2 and 3*, GTM 47. Printed pages
cited below were read directly and are reliable.

## What this is

A Lean 4 / Mathlib formalisation of Moise's route to the 3-dimensional triangulation
theorem. Two chains are assembled. Every arrow is a **proved** theorem whose transitive
axioms are exactly `propext, Classical.choice, Quot.sound`:

```
LemmaTwoStatement --moise252_of_lemmaTwo--> Moise252 --moise304_of_moise252-->
    Moise304 --moise305_tame_of_moise304--> Moise305Tame

Moise351 --(§34 transition, open)--> Moise352 --plApproximationManifold_three_of_moise352-->
    PLApproximationManifold 3
```

`LemmaTwoStatement` (`LoopTheorem/LemmaTwoEndpoint.lean`) is Moise's Lemma 2 in the shape
the Stallings tower consumes. `NormalSystem` is now known to be inhabited
(`LoopTheorem/NormalSystemWitness.lean`, unconditional), so the chain is not vacuous at
its base.

## Read this before proposing anything: five statements here were false

Work on this chain has a specific failure mode. Five statements that everyone treated as
"true but unproved" turned out to be **false**, each found only when someone actually
instantiated them. Please assume your first formulation of anything below is also wrong
until you have instantiated it.

1. **The direct surgery's surjectivity.** `D.domain \ C ⊆ pullback '' G.domain` is false:
   `exists_boundary_surgery_cell_of_boundaryBranch` glues the two *outer* cells of
   `exists_three_cells_of_boundaryBranch` and **discards the middle band**, so
   `pullback '' G.domain = D.domain \ (D₂.domain \ A)`. Any interior point of `D₂.domain`
   refutes it. Consequence: the direct candidate admits no branch *bijection*, only an
   injection. Nobody had read the construction, only the recorded conclusions.
2. **`Moise352Stages`.** It fixed a tolerance sequence `ε : ℕ → ℝ` before the family while
   demanding agreement between consecutive stages; since stages increase, that pins the
   approximation to `h` itself. False at `n = 1`, `h x = x³`.
3. **`Moise352StageStep`**, the repair of 2. It used a pointwise `φ` bounded below but not
   above; taking `φ` large makes the closeness constraints vacuous and degenerates the
   relative clause into an *extension* statement, false at `n = 2` by Jordan and at
   `n = 3` by Alexander. Both 2 and 3 were **inventions** — see §2 below for what Moise
   actually does.
4. **`CrossSeamTubeCore`** was uninhabited: it equated the compact `chart '' crossingFigure`
   with the relatively open `figure ∩ tube`, which is clopen in the connected `figure` and
   hence all of it. Repaired to compare against `chart '' spliceCylinder`. It had a
   non-vacuity witness, and the witness was degenerate — it took `tube := univ` and
   `figure := chart '' crossingFigure`.
5. **`hcross`**, a hypothesis of the descent selection. With `pathToCircle` and Mathlib's
   nested `Path.trans`, the four-arc word `σ.trans (φ.trans (υ.trans τ))` satisfies
   `w 0 = w (3/4) = a`. Literal identification with an injective boundary parametrisation
   would put `ρ a` in the resolved cell's double point set, which
   `CrossSeamResolutionData` excludes. So the comparison must be **up to free homotopy**,
   not literal.

The two reliable tells were: nobody read how the object was *constructed*, only what the
statement *recorded*; and nobody tested the quantifiers at their extremes.

---

## 1. The normal-crossing product tube — the last geometric brick of Lemma 2

**This is the most valuable open problem here.**

Moise's Lemma 2 inducts on the branch complexity of the singular set of a normal singular
2-cell. For a **boundary** branch `c` the model-level work is done: replacing the two bent
transverse arcs by the two disjoint chords `x + y = ±1` of the cross-section square,
fiberwise along the base interval, deletes the branch exactly
(`LoopTheorem/CrossSeamResolution.lean`, `doublePointSet crossSeamResolve bentSource = ∅`).
The transport of that model result to a global cell is proved
(`LoopTheorem/CrossSeamTube.lean`), as is the resolved cell's normality
(`LoopTheorem/ResolvedCellNormal.lean`, all six fields), the deleted triangulation and
branch bijection (`LoopTheorem/BranchDeletion.lean`), the direct candidate's branch
injection (`LoopTheorem/BranchInjection.lean`), and the uniform descent and word-elimination
selection (`LoopTheorem/BoundaryBranchDescent.lean`).

What is missing is the tube itself, `IsCrossSeamTubeProducer`. In the repaired form:

> Let `M` be a PL 3-manifold charted over `EuclideanSpace ℝ (Fin 3)`, `D : SingularTwoCell M`,
> `hD : NormalSingularCellData D BdM B`, and `c` a **boundary** branch of `hD.singularSet`.
> Then there are an open `U ⊆ M` and `Φ : (ℝ × ℝ) × ℝ → M` with
> (i) `Φ` continuous and injective on `spliceCylinder = ([-1,1]×[-1,1]) × [0,1]`, with
> `Φ '' spliceCylinder ⊆ U`;
> (ii) `Φ '' ({(0,0)} × [0,1]) = hD.singularSet.branchCarrier c`;
> (iii) `Φ '' (cross × [0,1]) = D '' D.domain ∩ Φ '' spliceCylinder`;
> (iv) `doublePointSet D D.domain ∩ U = hD.singularSet.branchCarrier c`.

Clauses (ii) and (iii) are the *relative* content: not merely a ball neighbourhood of the
arc, but one meeting the singular surface in the standard transverse cross swept along the
arc. Note (iii) compares against the **closed** cylinder image — comparing against the open
`U`, as the first version did, makes the structure uninhabited (refutation 4).

What a prover may use: `hD.singularSet.complex` is finite and a combinatorial 1-manifold
with boundary; the branch carrier is a polyhedral **arc** with endpoints on `BdM`, so the
tube is a half-tube; `pairwise_disjoint_branchCarrier` plus finiteness of `Branch` give (iv)
for small `U`; `hD.fiber_le_two` gives exactly two sheets hence four half sheets; and
`hD.crossing` gives `HasPLNormalDoubleCrossingAt` at **each** double point in **some**
chart. The absolute regular-neighbourhood theorem is available:
`ArcChainNeighborhood.lean:57` gives a PL **ball** neighbourhood of a simplicial arc in a
finite combinatorial 3-manifold.

**The gap is exactly the passage from the pointwise normal form to one product chart valid
along the whole arc** — a *relative* regular neighbourhood theorem for the pair
(3-manifold, 2-complex), where only the absolute one exists.

Four further properties are needed downstream by
`CrossSeamTubeData.normalOfResolvedCell` and should probably be part of the statement:
every double point of the reglued cell outside the tube has an atlas chart at it whose
source is disjoint from `Φ '' spliceCylinder`; the two end cross sections lie in the
boundary surface `B`; over the tube a source point lies on the boundary of the source disk
exactly when it lies over an endpoint of the base interval; and the tube meets `BdM` only
in its two end cross sections.

**Questions.** Is this true, with which exact hypotheses? Is it a consequence of a
published relative regular neighbourhood theorem — Rourke–Sanderson, Hudson, Zeeman — and
if so which, with the precise statement and what must be checked to apply it? Does Moise
prove it, and on which printed page? Is the whole-arc product actually needed, or does he
use a local product at each point plus compactness? **And is it false** — can the four
sheets be locally knotted, or the branch wild? A considered counterexample is the most
valuable answer you could give.

---

## 2. The §34 transition — the only remaining obligation of Moise 35.2

Moise's actual proof of 35.2 was read on printed **p. 251** and is short:

> **Theorem 2.** Let `M₁`, `M₂` be PL 3-manifolds, `K` a polyhedral 3-manifold with
> boundary in `M₁`, `h` a homeomorphism `K → M₂`, `φ` strongly positive on `K`. Then there
> is a PLH `f : K → M₂` which is a `φ`-approximation of `h`.
>
> PROOF. Virtually a repetition of Theorem 34.1. As before, `K` can be moved into `Int K`
> by a PLH as close to the identity as we please; thus the theorem reduces to the case in
> which `h` and `φ` are defined on an open `U ⊇ K`, and then to `K` closed in `M₁` with
> `φ ≫ 0` on all of `M₁`. Now subdivide `K` so that for each simplex `σ`,
> `diam h(|St σ|) < inf φ` on `|St σ|`. Then take a regular neighborhood `N` of the
> 1-skeleton `K¹` and a PLH `f : N ↔ N' ⊂ M₂` which is a `φ`-approximation of `h|N`, with
> `N'` a neighborhood of `h(K¹)` — and for every `φ' ≫ 0` we can make `f` a
> `φ'`-approximation. **Thus the transition from 35.1 to 35.2 is essentially the same as
> the transition from 33.1 to 34.1; the argument in §34 treated the simplexes of `K`
> essentially one at a time.**

`φ ≫ 0` is *strongly positive*, defined on printed p. 247: everywhere positive and bounded
away from 0 on every compact set.

The input, printed **p. 248**, Theorem 1 of §35 — **this is 35.1, and the tree's `Moise351`
(`MoiseChain.lean:191`) is a faithful rendering of it**:

> Let `K` be a 1-dimensional polyhedron in a PL 3-manifold `M₁`, `U` an open set containing
> `K`, `h` a homeomorphism of `U` into a PL 3-manifold `M₂`, `φ` strongly positive on `U`.
> Then there is a regular neighborhood `N` of `K` in `U` and a PLH `f : N ↔ X ⊂ M₂` such
> that (1) `X` is a neighborhood of `h(K)` and (2) `f` is a `φ`-approximation of `h|N`.

§34's own proof (printed pp. 239–246) subdivides with a link condition, takes a regular
neighbourhood `N` of `K¹` with splitting disks at edge midpoints decomposing `N` into dual
cells, applies 33.1, and then extends over the 2- and 3-simplexes using solid tori, spines
(Theorem 30.8) and general position (Theorem 30.5). For a 2-simplex `σ`, the union `N_σ` of
the dual cells containing vertices of `σ` is a **solid torus**.

**Questions.** What is the precise statement of the simplex-by-simplex extension, in a form
that applies to a locally finite `K` in a general PL 3-manifold rather than a polyhedral
3-cell in `ℝ³`? Which of §34's Lemmas 1–10 generalise verbatim and which need the ambient
change? Is the local finiteness handled by supports, or does it need an extra argument?
Moise says the transition is "essentially the same" — is that accurate, or does the
non-compact, non-Euclidean setting introduce a real difficulty he is eliding?

Also: is there a shorter modern route? A. J. S. Hamilton, *The triangulation of
3-manifolds*, Quart. J. Math. Oxford (2) 27 (1976) 63–70, Theorem 2.2 (printed p. 68) is a
controlled **relative uniqueness** theorem that would give the endpoint in one step, but it
depends on Whitehead's immersion theorem, Wall's end compactification, Waldhausen–Scott
rigidity and torus unfurling. Given that Moise's own route is available and its input is
already correctly stated here, is Hamilton a shortcut or a detour?

---

## 3. Closed-branch Case 1

`LemmaTwoStatement` carries **no** orientability hypothesis, and a genuine Stallings tower
above an orientable bottom does not acquire non-orientable stages — a tower step is a
covering complex followed by a derived neighbourhood, both of which preserve orientability.
So non-orientable downstairs targets are allowed, and Case 1 — a closed branch whose
complete preimage is a single circle doubly covering it — must be **handled**, not excluded.
`LoopTheorem/../ClosedBranchOrientability.lean` proves the exclusion over an orientable
target complex; it is correct but off the dependency path.

The model-level replacement is the closed analogue of §1's chords: in the square, replace
the cross by the two disjoint chords `x - y = ±1`, which `Prod.swap` **exchanges**, so the
quotient by the period identification `(z,0) ~ (swap z, 1)` is an embedded **annulus**
rather than a Möbius band — two strips exchanged, returning after two traversals without
reversal.

What is missing is the same shape as §1: that an actual closed branch carries a cylindrical
diagram over a triangulated square with end map `Prod.swap`, and the **straightening** of an
arbitrary PL monodromy to `Prod.swap` through PL homeomorphisms preserving the cross.
Determining the *ray permutation* is not the same as obtaining the *pointwise formula*: the
connected sheet cover says one traversal exchanges the two sheet germs, and the annular
source neighbourhood (automatic, the preimage circle being embedded in the interior of the
source disk) then forces a diagonal reflection rather than a quarter turn — but the
producer must supply the whole **marked pair** `(D², X)`, not an unmarked disk bundle.

---

## What would help most

Exact mathematical statements, not strategy. Printed-page citations where you rely on
Moise, and an explicit note where you could not verify. Lean-ish statements are welcome but
the mathematics matters more. If something already built here is aimed at the wrong target,
say so plainly — given the record above, that is the likeliest useful finding, and it is
worth more than a confirmation.
