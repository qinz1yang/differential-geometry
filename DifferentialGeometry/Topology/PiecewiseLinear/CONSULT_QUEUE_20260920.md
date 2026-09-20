# Consultation queue — 2026-09-20

Paste-ready prompts for GPT Pro / Fable / Astra. Each one is self-contained: it
names the repository, the branch and the commit, so the consultant reads the right
tree. Ordered by how much they unblock.

Repository **https://github.com/liao9yuan/differential-geometry-dev**, branch
**`moise-integration`**, browsable at
**https://github.com/liao9yuan/differential-geometry-dev/tree/moise-integration**.
Read the head of that branch. Every other branch of that repository diverges and its
line numbers will not match; every prompt below repeats the warning.

| # | Question | Unblocks | Status |
| --- | --- | --- | --- |
| 1 | Relative product tube along a branch arc | Lemma 2, the last geometric brick of the boundary case | ready — **but see the tube correction below before sending it** |
| 2 | What the 35.2 stage recursion actually is, and injectivity in it | Moise 35.2 — **currently has no valid route** | ready |
| 3 | Where closed-branch Case 1 actually occurs in the tower | Lemma 2, closed case | ready |
| 4 | Lifting the boundary word from ranges to parametrised loops | Lemma 2, the selection step | ready |

All four are written and paste-ready. Prompt 1 is the most valuable: it is the only
one of the four that is a genuinely missing *theorem* rather than a missing
bookkeeping step, and lane C has since restated its four clauses in Lean-exact form
as `IsCrossSeamTubeProducer` (`LoopTheorem/CrossSeamTube.lean`), which is the precise
target for an answer.

## The Lemma 2 frontier, as of this file

The boundary-branch case is assembled end to end and every step below is proved
except where marked. Reading downwards is the order the induction uses.

| Step | Where | State |
| --- | --- | --- |
| Model seam repair: the branch is deleted exactly | `CrossSeamResolution.lean` | proved |
| Transport of the model repair to a global cell | `CrossSeamTube.lean` | proved, given a tube |
| The tube itself | `IsCrossSeamTubeProducer` | **open — prompt 1** |
| Triangulation of the double point set minus a branch | `BranchDeletion.lean` | proved |
| Branch bijection `Branch ≃ {b ≠ c}` | `BranchDeletion.lean` | proved, for *any* such triangulation |
| Normality of the resolved cell, all six fields | `ResolvedCellNormal.lean` | proved, from four tube-level hypotheses |
| `hGD`: the reglue changes no double point outside the tube | belongs with `CutAndPaste.lean` | **open** |
| Branch *injection* for the direct candidate | `BranchDescent.lean:91` is the consumer | **open** |
| Uniform descent through one door | `BoundaryBranchDescent.lean` | proved |
| Word elimination picks the surviving candidate | `BoundaryBranchDescent.lean` | proved, given the boundary words |
| The boundary words as parametrised loops | — | **open — prompt 4** |

### The closed case: the Case 1 exclusion is off the dependency path

`ClosedBranchOrientability.lean` proves that closed Case 1 cannot occur over an
orientable target complex. The answer to prompt 3 establishes that **this is not a step
in Lemma 2**, and two of the assumptions behind the prompt were mine and were wrong.

*Correction 1, mine.* Prompt 3 asserted that "intermediate systems need not be
orientable even though the bottom one is", on the reading that `CoverReduction.lean`'s
non-orientable branch means orientation can be lost going up. **That is false for the
actual tower.** A tower step is a covering complex followed by a derived neighbourhood
(`CoverNormalSystem.lean:49`, `:108`, `:106`), and both operations preserve
orientability, so an orientable bottom forces every stage orientable by induction. The
producer's `by_cases hor : S.IsOrientableManifold`
(`CoverReduction.lean:126`) handles non-orientable *starting* systems; it does not
create non-orientability during ascent.

*Correction 2, consequential.* Since `LemmaTwoStatement` carries **no** orientability
hypothesis, non-orientable downstairs targets are allowed, and **Case 1 must be handled
by an actual surgery rather than universally excluded**. Building the induction around
the exclusion would aim at the wrong target. The exclusion stays correct and useful as a
consistency check for orientable applications, but it is not on the proof's dependency
path — so the three inputs prompt 3 lists as open are not three obligations of the
general Case 1 surgery. Only the marked tube model and its connection to the source
branch are; the orientation transport is needed for the optional exclusion alone.

Two pieces of mathematics from that answer that are worth keeping:

* **What the connected sheet cover records.** A connected two-sheeted branch preimage
  says one traversal of the branch exchanges the two sheet germs. That **alone does not
  determine tube orientability**. Connected sheet cover *plus an annular source
  neighbourhood* (automatic, since the preimage circle is embedded in the interior of
  the source disk, so its normal line bundle is trivial) *plus an ordinary crossing*
  does: the annulus forces the ray permutation to be a diagonal reflection rather than a
  quarter turn, and the transverse orientation is then reversed, so the ambient tube is
  non-orientable. In bundle terms the sheet cover is the orientation double cover of
  `ν_{C/N}`, whence `p` connected ⟺ `⟨w₁(N), [C]⟩ = 1`.
* **The correct orientation transport**, for whenever the exclusion is wanted: it needs a
  genuine **codimension-zero local PL embedding** of the tube into the ambient manifold,
  not injectivity of the cylinder parametrisation. A solid torus also has a non-injective
  cylindrical parametrisation. An arbitrary PL map, an image containment, or surjectivity
  onto some set is not sufficient.

Also flagged, and it is a real gap: determining the *ray permutation* is not the same as
obtaining the *pointwise formula* `h (x, y) = (y, x)`. Straightening an arbitrary PL
monodromy to `Prod.swap`, through PL homeomorphisms preserving the cross, is a
substantive further step, and the producer must supply the whole **marked pair**
`(D², X)`, not an unmarked disk bundle or an abstract covering circle.

### Correction: the direct candidate admits no branch bijection

An earlier row of this table read *"Surjectivity `D.domain \ C ⊆ pullback '' G.domain`
— open, one conjunct"*, on the reading that the existing construction satisfies it but
does not export it. **It does not satisfy it; the statement is false of the direct
surgery.** The direct surgery glues the two *outer* cells of
`exists_three_cells_of_boundaryBranch` and discards the middle band. With its notation,
`pullback '' G.domain = D₁.domain ∪ (D₃.domain \ C) = D.domain \ (D₂.domain \ A)`, and
since `A, C ⊆ frontier D₂.domain` (`CutAndPaste.lean:1197–1198`), any point of
`interior D₂.domain` — nonempty, as `D₂.domain` is a 2-ball — lies in `D.domain \ C`
and in neither outer cell. So the direct candidate genuinely loses every branch with a
sheet in the middle band, and `doublePointSet G G.domain = doublePointSet D D.domain \
branchCarrier c` is false for it too.

This is the mathematics, not a Lean artefact: the direct candidate is `D₁ ∪_g D₃`. The
cross candidate is the one that uses all three pieces, which is exactly why it retains
the branch and needs the seam resolution. The two candidates were never symmetric here.

The repair is that a **bijection was never needed**.
`NormalSingularSetTriangulation.complexity_lt_of_injective_origin`
(`BranchDescent.lean:91`) takes an *injection* `T'.Branch → T.Branch` missing `c`, which
is what the direct candidate really supports. `BranchDeletion.lean`'s conditional
theorems stay correct and keep the cross candidate as their producer; the direct
candidate needs a new door taking an injection.

Of the open items, only the tube and the boundary-word parametrisation look like real
theorems. The branch injection and `hGD` are bookkeeping over constructions that exist,
as are the five outstanding normality fields. That is the honest shape of the remaining
work: one geometric theorem, one parametrisation question, and a bookkeeping tail — with
the caveat, twice demonstrated tonight, that items in the tail can turn out to be false
rather than merely unproved.

## The status these prompts rest on

Read this first; it is what makes the two prompts the right two. Every arrow below
is a **proved** Lean theorem on this branch, verified by focused compile, with
transitive axioms exactly `propext, Classical.choice, Quot.sound`. Every node in
**bold** is an open `Prop` with no producer.

```
  LemmaTwoStatement                      Moise352StageStep n
        │ moise252_of_lemmaTwo                 │ moise352_of_stageStep
        │ EmbeddedDiskTower.lean:173           │ CompactRelativeApproximation.lean
        ▼                                      ▼
     Moise252                               Moise352 n
        │ moise304_of_moise252                 │ plApproximationManifold_three_of_moise352
        │ SphericalShellCompression.lean:88    │ Endgame.lean:9   (only at n = 3)
        ▼                                      ▼
     Moise304                           PLApproximationManifold 3
        │ moise305_tame_of_moise304
        │ TameNestedCells.lean:34
        ▼
   Moise305Tame
```

**The second column of that diagram is no longer valid.** `Moise352StageStep` is also
false — see the second correction below — so `moise352_of_stageStep` joins
`moise352_of_stages` as a valid implication from a false hypothesis, and **the 35.2
chain currently has no route to `Moise352` at all**. The first column stands:
`LemmaTwoStatement` is a genuine open root and prompt 1 attacks the last geometric
brick under it.

### Correction: `Moise352Stages` is false, and was the wrong target

An earlier version of this file named `Moise352Stages 3` as the second root. **That
was wrong: `Moise352Stages n` is false for every `n ≥ 1`**, so it is not an open
problem but a dead end, and `moise352_of_stages`
(`LocallyFiniteApproximation.lean:479`) is a valid implication from a false
hypothesis.

The defect is the quantifier packaging, not the geometry. `Moise352Stages` takes the
tolerance as a sequence `ε : ℕ → ℝ` fixed *before* the family, while also demanding
`EqOn (f (i+1)) (f i) (T.coreSpace i)`. The stages increase
(`T.coreSpace i ⊆ T.N i ⊆ T.coreSpace (i+1)`, `LocallyFiniteApproximation.lean:20`),
so the agreement clause forces `f j = f i` on `T.coreSpace i` for every `j ≥ i`; then
for `x ∈ T.coreSpace j` the error clause reads `dist (f j x) (h x) < ε i` for **every**
`i ≥ j` at once. Feed it `ε i = 1/(i+1)` and `f j` is pinned to `h`. So
`Moise352Stages n` asserts that every topological embedding of a locally finite PL
manifold *is exactly PL* on every compact stage — false already for `n = 1`,
`M₁ = M₂ = ℝ`, `h x = x³`. The implication is proved in Lean as
`Moise352Stages.exists_isPLHomeomorphInto_eqOn`; the counterexample tower is a stated
remark, not formalised.

The repair is confined to the packaging: the tolerance must be a **pointwise**
`φ : M₁ → ℝ`, bounded below by a positive constant on each compact stage. Then on
`T.coreSpace i` the conclusion of the step *is* its own hypothesis transported along
`EqOn`, and no tolerance is ever asked to shrink where a map is already fixed. That
is `Moise352StageStep n`, and `moise352_of_stageStep` carries all the bookkeeping.
`exists_isPLHomeomorphInto_dist_lt_of_stages` has the same defect in its `hstages`
binder and is equally unusable; `exists_isPLHomeomorphInto_of_stages`, which takes a
pointwise `φ`, is fine and is what the repaired route goes through.

A second caveat on the same chain, not formalised: **`Moise352 n` is presumably false
for `n ≥ 5`.** By the argument shape of `plApproximationManifold_three_of_moise352`
it would approximate any homeomorphism of closed PL `n`-manifolds by a PL embedding,
necessarily surjective and hence a PL homeomorphism, contradicting the known
homeomorphic-but-not-PL-homeomorphic manifolds in high dimensions. So
`Moise352StageStep n` should be expected true only for small `n`, and any consultant
who claims a dimension-free proof of it has made an error.

### Second correction: `Moise352StageStep` is false too

The repair above fixed the tolerance's *shape* but not its *quantifier*, and the
relative clause is false for a different reason. `φ` is required to be bounded **below**
by a positive constant on each stage (`CompactRelativeApproximation.lean:217`) and is
not bounded above. Take `φ` constant and large: on a bounded stage both closeness
constraints become vacuous, `g` becomes an arbitrary PL embedding of `T.coreSpace i`,
and the clause asserts that **any** PL embedding of a stage extends to a PL embedding of
the next one agreeing with it — an *extension* statement, not an approximation
statement. That is false already at `n = 2` (an annulus embedded in the plane so that
its inner boundary circle encloses the image admits no extension over the disc, by
Jordan) and at `n = 3` (a knotted solid torus inside a ball: an extension would unknot
it, contradicting Alexander). Not formalised — no counterexample tower is built.

The right quantifier order is `η` **before** `g`: *there is `η > 0` such that every PL
embedding of stage `i` which is `η`-close to `h` extends to stage `i+1` within `ε`.*
That form is proved in `StageTransport.lean`, modulo injectivity alone, as
`exists_pos_forall_exists_isPLOn_injOn_eqOn_dist_lt_coreSpace_succ`. The absolute clause
needs no repair and is reduced outright.

**But the repaired clause does not assemble, and this is the finding that matters most
for planning.** Any valid `η` satisfies `η ≤ ε` whenever the previous stage is nonempty,
because the produced `f` equals `g` there, so the `ε`-bound must already hold for `g`.
A recursion therefore forces the tolerances to **increase** along the tower,
`δ_k < η_k(δ_{k+1}) ≤ δ_{k+1}`, while the constants extracted from a pointwise `φ`
**decrease**. So the present `exists_isPLHomeomorphInto_of_stages` route, which demands
exact agreement on the whole previous stage, cannot consume it. What is needed is
agreement on a strictly *smaller* stage than the one the tolerance is controlled on, or
a diagonal/limiting argument. Neither is attempted.

So the honest status of 35.2 is not "one open compact theorem" but "the stage recursion
itself is not yet correctly formulated", and that is what prompt 2 should now be asked.
Two successive formulations have been false, each for a quantifier reason, which is why
prompt 2's first question is about the shape of the recursion rather than about its
content.

Two status corrections worth recording, both verified against current source rather
than against the notes:

* `ROUTE_AUDIT_20260919.md` lists confirmed statement defects in `Moise252`,
  `Moise331` and `Moise351`. **All three are now repaired in the source.**
  `Moise252` (`MoiseChain.lean:36`) carries the non-nullhomotopy of the new boundary
  inclusion into the specified boundary component at lines 50–54, which is the book's
  third conclusion. `Moise331` (`:136`) now existentially chooses `T, L'` with
  `(derivedNeighborhood T L').space ⊆ U`, fixing the quantifier order, and adds the
  no-valence-one-vertex condition. `Moise351` (`:191`) now requires
  `IsLocallyFinitePolyhedralGraph` input and concludes
  `IsLocallyFiniteRegularNeighborhoodOf`. The audit table is stale, not wrong at the
  time it was written. That matters because `moise252_of_lemmaTwo` proves the
  *repaired* `Moise252`, so Lemma 2 buys more than the notes suggest.
* `Moise331`, `Moise341` and `Moise351` are all still open, but **none of them is
  currently wired into the 35.2 reduction**. The reduction as built goes
  through `plManifoldMapApproximation` (proved, `MoiseChain.lean:243`) and
  `CompactEmbeddingApproximation`, and what it is missing is injectivity — see
  prompt 2. Whether `Moise341` is the right thing to consume is precisely question
  2.Q2.

### Third correction: the tube contract as written is uninhabited

**`CrossSeamTubeCore` / `CrossSeamTubeData` (`LoopTheorem/CrossSeamTube.lean:170`, `:228`)
are uninhabited** for any normal singular cell with a boundary branch over a Hausdorff
manifold. Two fields collide:

```
isOpen_tube          : IsOpen tube                               -- :173
image_crossingFigure : chart '' crossingFigure = figure ∩ tube   -- :184
```

`crossingFigure ⊆ spliceCylinder` is compact and `chart` is continuous there, so the
left side is compact, hence **closed**; the right side is relatively **open** in
`figure = D '' D.domain`, which is connected, and the set is nonempty since it contains
`chart '' spliceCore = branchCarrier c`. A nonempty clopen subset of a connected space
is everything, so `D '' D.domain ⊆ U` and `chart '' crossingFigure = D '' D.domain`.
With `double_inter_tube` that forces `doublePointSet D D.domain = branchCarrier c`,
complexity exactly 1, so `complexity_lt_of_tube` could only ever descend 1 → 0 and the
induction it exists to serve cannot run. Worse: `chart` is injective and continuous on
a compact set, hence a homeomorphism onto its image, so
`D '' D.domain \ branchCarrier c` would have exactly **four** components, while its
preimage `D.domain \ (A ∪ C)` is covered by the three cells of
`exists_three_cells_of_boundaryBranch`, each connected after removing arcs of its own
frontier — three connected images cannot have four components.

Consequences. Everything built on the tube is **vacuous, not wrong**:
`exists_resolved_cell_of_tube`, `crossSeamResolutionDataOfTube`, `complexity_lt_of_tube`,
and `ResolvedCellNormal.lean`'s `normalOfResolvedCell` / `normalOfTube`. The *model*
layer below it is unaffected — `CrossSeamResolution.lean` is about the model and stands,
and `bentFigure = crossingFigure` shows the reglue changes only the pairing of the four
half sheets, exactly as intended. So is `BranchDeletion.lean`, `BranchInjection.lean`
and the descent selection, none of which mention the tube.

**How it got through.** The file carries a non-vacuity witness,
`crossSeamTubeCore_spliceEmbedding` (`:208`) — and it passes only by taking
`tube := univ` and `figure := chart '' crossingFigure`, i.e. by instantiating exactly
the degenerate configuration the argument shows is forced. The witness was reviewed for
existence but not for degeneracy. Any future witness on this chain should come with
explicit strictness theorems beside it.

**The repair direction**, and it has a working analogue in the tree:
`IsCylindricalDiagram` (`PiecewiseLinear/CylindricalDiagram.lean:10`) states its image
clause as `f '' (P ×ˢ Icc 0 1) = S`, against the **closed image**, with no open set
anywhere. The surface clause of the tube wants to be relative to `chart '' spliceCylinder`
rather than to an open `U`. **Prompt 1 below still asks about the old clause three, so
fix that clause before sending it** — or better, ask the consultant for the right clause
directly, since we have now written three statements on this chain that turned out
false.

### Non-vacuity: `NormalSystem` is now known to be inhabited

Neither `lake build` nor `#print axioms` can see a vacuous `Prop` — one whose
hypotheses nothing satisfies — and until tonight nobody had exhibited a single
`NormalSystem` (`SingularCell.lean:524`, twenty-odd fields), so a proof of
`LemmaTwoStatement` would have been worth less than it looked. That hole is now
closed at the base:

```lean
theorem nonempty_normalSystem_euclideanSpace_three :
    Nonempty (NormalSystem (EuclideanSpace ℝ (Fin 3)))
theorem exists_normalSystem_euclideanSpace_three :
    ∃ S : NormalSystem (EuclideanSpace ℝ (Fin 3)),
      S.sourceComplex.space ∩ S.singularMap ⁻¹' S.boundaryComplex.space =
        frontier S.sourceComplex.space ∧
      S.basepoint = S.boundaryLoop 0
```

unconditional, axioms exactly `propext, Classical.choice, Quot.sound`. The two extra
conjuncts are two of the three side conditions `LemmaTwoStatement` puts on its
covering system, so those are shown satisfiable too. The witness is a meridian of an
embedded solid torus, fed to the tree's existing producer
`exists_normalSystem_of_isPiecewiseAffineOn` (`LoopTheorem/SourceNormalSystem.lean:130`),
which nobody had ever supplied with concrete input.

What is **still** not anchored, and is worth a consultant's attention if prompt 1 or 3
is answered cheaply:

* a normal system with **non-empty singular set**. `S.complexity ≠ 0` iff the singular
  map is not injective, and the producer exposes the singular map only on the
  frontier, the interior coming from an opaque inward push. The only lever is a
  non-injective boundary loop, and that fails structurally: a degree-one non-injective
  map `S¹ → J` admits no continuous section, so essentiality cannot be transported by
  a retraction. This needs either a from-scratch combinatorial normal system or a spur
  cancellation free-homotopy lemma the tree does not have.
* `Nonempty (EmbeddedDisk S)` for that witness — for the meridian configuration this
  is Dehn's lemma, and note the obstruction argument is unavailable in both
  directions: by Dehn's lemma such a disk *does* exist, so one cannot prove the
  witness singular by contradiction either.
* `Nonempty (DoubleCoverReduction S T)`, which additionally needs strict complexity
  descent. Untouched.

---

## 1. The relative product tube along a branch arc

*(Self-contained. Paste whole. Answer in English or Chinese.)*

### Where to look

Public repository **https://github.com/liao9yuan/differential-geometry-dev**, branch
**`moise-integration`**, browsable at
**https://github.com/liao9yuan/differential-geometry-dev/tree/moise-integration**.

```
git clone https://github.com/liao9yuan/differential-geometry-dev
cd differential-geometry-dev && git checkout moise-integration
```

Read the head of that branch. Do not read any other branch of that repository; they
diverge and line numbers will not match. Paths below are from the repository root.

### State

Moise's Lemma 2 runs an induction on the branch complexity of the singular set of a
normal singular two-cell `D` in a combinatorial 3-manifold. For a *boundary* branch
`c` there are two candidate surgeries. The second one, the cross reglue
(`DifferentialGeometry/Topology/PiecewiseLinear/LoopTheorem/CutAndPaste.lean:1223`,
`exists_cross_reglued_cell_of_boundaryBranch`), does not delete the branch on its
own: it concludes `hD.singularSet.branchCarrier c ⊆ doublePointSet G G.domain`,
because the reglued map still sends both new seams to the centre of the transverse
cross.

The repair is now proved **in the model**, in
`DifferentialGeometry/Topology/PiecewiseLinear/LoopTheorem/CrossSeamResolution.lean`
(854 lines, 110 declarations, axioms exactly `propext, Classical.choice,
Quot.sound`). Replacing the two bent transverse arcs `[e₁,0] ∪ [0,-e₂]` and
`[-e₁,0] ∪ [0,e₂]` by the two disjoint chords of the cross-section square,
fiberwise along `Icc 0 1`, is the restriction of a single affine map of the plane,

```
crossSeamChordPos p = ((p.1 + p.2 + 1)/2, (p.1 + p.2 - 1)/2)
```

and gives `doublePointSet crossSeamResolve bentSource = ∅` exactly, is the identity
on the four lateral attaching intervals, and does not move the base coordinate.

So the model step is done. What is missing is the statement that lets the model be
applied: a neighbourhood of the branch arc in the ambient 3-manifold with a product
structure *relative to the four sheets of `D` that meet along the branch*.

### What the tree already has

- `DifferentialGeometry/Topology/PiecewiseLinear/RegularNeighborhood.lean` —
  `regularNeighborhoodIn K A`, `regularNeighborhood K A :=
  regularNeighborhoodIn (secondDerived K) A`, with
  `regularNeighborhood_mem_nhdsWithin K A hx : (regularNeighborhood K A).space ∈
  𝓝[K.space] x` for `x ∈ A`.
- `DifferentialGeometry/Topology/PiecewiseLinear/ArcChainNeighborhood.lean:57` —
  `IsCombinatorialManifoldWithBoundary.exists_isPLBall_neighborhood_arcComplexIn`:
  for a simplicial arc in a finite combinatorial 3-manifold with injective vertices
  and all arc faces interior, the derived neighbourhood of the arc is a PL **ball**
  neighbourhood.
- `DifferentialGeometry/Topology/PiecewiseLinear/CylinderSplice.lean` — the model:
  `spliceSquare`, the transverse chords `spliceArcPos`/`spliceArcNeg`, the cylinder
  `spliceSquare ×ˢ Icc 0 1`, and (`:466`, `:483`) the fact that the two sheets' rays
  meet the square's boundary in the two interleaved opposite pairs.

So *a ball neighbourhood of the arc exists*. What is not available is the product
structure carrying the four local sheets of `D` to the four model half sheets.

### The question

**Q1.** State precisely the theorem that supplies this. Informally: for a normal
singular two-cell `D` in a combinatorial 3-manifold `K` and a branch arc `c` of its
singular set, there is an open `U ⊇ branchCarrier c` and a PL homeomorphism
`Φ : spliceSquare ×ˢ Icc 0 1 → U` carrying the core `{0} ×ˢ Icc 0 1` onto
`branchCarrier c` and the four model half sheets onto the four local sheets of `D`
along the whole arc. What are the exact hypotheses — how much of "normal" is
needed, does the arc have to be interior, is finiteness needed, does the branch have
to be a single arc rather than a circle?

**Q2.** Is this a consequence of a *relative* regular neighbourhood theorem for the
pair (3-manifold, 2-complex), and if so which form — Rourke–Sanderson, Hudson,
Zeeman? Please give the precise citation and the precise statement, and say what
has to be checked to apply it here. If instead Moise proves it directly, give the
book page (Moise, *Geometric Topology in Dimensions 2 and 3*, GTM 47) and the
statement number.

**Q3.** Is the product structure *along the whole arc* actually needed, or does
Moise only ever use a local product at each point plus a compactness/uniqueness
argument? If the latter, what is the weaker statement that suffices, since it would
be much cheaper to prove.

**Q4.** Is there a hypothesis under which this is **false** — a normal singular
two-cell with a branch whose neighbourhood is not a product of that kind? Knowing
the counterexample would tell us which hypothesis of `NormalSingularCellData` is
load-bearing. If the four sheets can be locally knotted or the branch can be wild,
say so plainly. **Please take this question seriously rather than as a formality**:
two statements on this chain that everyone treated as true-but-unproved have turned
out to be false in the last few hours, so a considered "this is false, here is the
counterexample" is the single most valuable answer you could give.

**Q5.** Four further properties of the tube are now known to be needed downstream, by
`CrossSeamTubeData.normalOfResolvedCell` (`LoopTheorem/ResolvedCellNormal.lean`), and
they should probably be part of the tube statement rather than separate hypotheses.
Are they automatic for a boundary branch, or do they constrain the tube further?
(i) every double point of the reglued cell outside the tube has an atlas chart at it
whose source is disjoint from the parametrised cylinder; (ii) the two end cross
sections lie in the boundary surface `B`; (iii) over the tube, a source point lies on
the boundary of the source disk exactly when it lies over an endpoint of the base
interval — the two source strips run from one end of the tube to the other;
(iv) the tube meets `BdM` only in its two end cross sections.

### Constraints on the answer

- Exact mathematical statements, not strategy prose; Lean-ish is fine.
- Cite Moise by printed page where you rely on him, and say what you could not verify.
- Do not weaken any existing statement; anything more general must keep the old ones
  as corollaries.
- If a piece already built is aimed at the wrong target, say so plainly — that is the
  most useful possible answer.

---

## 2. Injectivity in the relative compact PL approximation

*(Self-contained. Paste whole. Answer in English or Chinese.)*

### Where to look

Public repository **https://github.com/liao9yuan/differential-geometry-dev**, branch
**`moise-integration`**, browsable at
**https://github.com/liao9yuan/differential-geometry-dev/tree/moise-integration**.
Read the head of that branch; do not read any other branch, they diverge and line
numbers will not match.

### State

Moise 35.2 — PL approximation of a topological embedding of one PL manifold in
another — is reduced to one compact statement, and all the packaging around it is
proved. **Two successive formulations of that statement have turned out to be false,
and you need both before the questions make sense.**

*First formulation, `Moise352Stages`, false for every `n ≥ 1`.* It fixed the tolerance
as a sequence `ε : ℕ → ℝ` **before** the family, while also demanding
`EqOn (f (i+1)) (f i) (T.coreSpace i)`. The stages increase, so agreement forces
`f j = f i` on `T.coreSpace i` for every `j ≥ i`; then for `x ∈ T.coreSpace j` the error
clause reads `dist (f j x) (h x) < ε i` for **every** `i ≥ j` at once. Feed it
`ε i = 1/(i+1)` and `f j` is pinned to `h`. So it asserted that every topological
embedding is *exactly PL* on every compact stage — false at `n = 1`, `M₁ = M₂ = ℝ`,
`h x = x³`. The implication is proved in Lean as
`Moise352Stages.exists_isPLHomeomorphInto_eqOn`.

*Second formulation, `Moise352StageStep`, also false.* It replaced the sequence by a
**pointwise** `φ : M₁ → ℝ` bounded **below** by a positive constant on each compact
stage — but not above. Take `φ` constant and large: on a bounded stage both closeness
constraints go vacuous, `g` becomes an arbitrary PL embedding of `T.coreSpace i`, and
the relative clause degenerates into *"any PL embedding of a stage extends to a PL
embedding of the next"* — an **extension** statement, not an approximation statement.
False at `n = 2` (an annulus embedded in the plane so its inner boundary circle encloses
the image admits no extension over the disc, by Jordan) and at `n = 3` (a knotted solid
torus in a ball: an extension would unknot it, contradicting Alexander).

Also worth knowing, not formalised: **`Moise352 n` is presumably false for `n ≥ 5`**,
since it would approximate any homeomorphism of closed PL `n`-manifolds by a PL
embedding, necessarily surjective and hence a PL homeomorphism, contradicting the known
homeomorphic-but-not-PL-homeomorphic manifolds in high dimensions. So the stage step
should be expected true only for small `n`, and a dimension-free proof of it is an error.

For reference, the second (false) formulation, since the questions refer to it:

```lean
def Moise352StageStep (n : ℕ) : Prop :=
  ∀ {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂]
    [HasGroupoid M₁ (plGroupoid n)] [HasGroupoid M₂ (plGroupoid n)]
    {K : Set M₁} (T : LocallyFinitePieceTower n M₁ K),
    (∀ i, IsCombinatorialManifoldWithBoundary n (T.piece i).piece.complex) →
    ∀ {h : M₁ → M₂}, Topology.IsEmbedding (K.domRestrict h) →
    ∀ {φ : M₁ → ℝ}, (∀ i, ∃ c : ℝ, 0 < c ∧ ∀ x ∈ T.coreSpace i, c ≤ φ x) →
      (∃ f, IsPLOn n n f (T.coreSpace 0) ∧ InjOn f (T.coreSpace 0) ∧
          ∀ x ∈ T.coreSpace 0, dist (f x) (h x) < φ x) ∧
        ∀ (i : ℕ) (g : M₁ → M₂), IsPLHomeomorphInto n g (T.coreSpace i) →
          (∀ x ∈ T.coreSpace i, dist (g x) (h x) < φ x) →
          ∃ f, IsPLOn n n f (T.coreSpace (i + 1)) ∧ InjOn f (T.coreSpace (i + 1)) ∧
            EqOn f g (T.coreSpace i) ∧ ∀ x ∈ T.coreSpace (i + 1), dist (f x) (h x) < φ x
```

with `moise352_of_stageStep : Moise352StageStep n → Moise352 n` proved in
`CompactRelativeApproximation.lean`, carrying the separation constants, the antitone
tolerance, the recursion and the limit. In words the two unproved statements are:
**(1) absolute** — a PL, injective, `φ`-close map on the first compact stage;
**(2) relative** — given a PL embedding `g` of stage `i` that is `φ`-close to `h`, a
PL injective map on stage `i+1` agreeing with `g` on stage `i` and still `φ`-close.
(1) is (2) with the previous stage empty. The pointwise `φ` is the whole repair: on
stage `i` the conclusion of (2) *is* its own hypothesis transported along `EqOn`, so
no tolerance is ever asked to shrink where a map is already fixed.

Also available:

1. `DifferentialGeometry/Topology/PiecewiseLinear/CompactEmbeddingApproximation.lean`
   reduces the compact statement to **injectivity**: the local-inverse clause of
   `IsPLHomeomorphInto` is discharged on a compact set.

And the PL-**map** half, *with the agreement clause*, is already proved, and is
**dimension-free**: `exists_isPLOn_dist_lt_eqOn` (`ManifoldApproximation.lean:347`)
is general in `{n m : ℕ}`,

```
IsPolyhedron P → IsPolyhedron Q → Q ⊆ P → ContinuousOn f P → IsPLOn n m f Q → 0 < ε →
  ∃ g, IsPLOn n m g P ∧ EqOn g f Q ∧ ∀ x ∈ P, dist (g x) (f x) < ε
```

(`PLManifoldMapApproximation`, `MoiseChain.lean:234`, is only its target-dimension-3
specialisation, which is why it looks narrower than it is.)

Two concrete things stand between that and clause (2), neither done. **Transport**:
`exists_isPLOn_dist_lt_eqOn` lives on polyhedra in `EuclideanSpace ℝ (Fin n)` while
the stages are `(T.piece (i+1)).piece.map` images — a tractable brick. **A continuous
interpolant**: the recursion has `g` on the old stage and `h` on the new part, and
the naive splice is discontinuous. And then **injectivity**, which is the genuinely
open part.

For orientation: `Moise341` (`MoiseChain.lean:99`) is the PL-**ball** case in
`EuclideanSpace ℝ (Fin 3)`, constant `ε`, no agreement clause, and its conclusion
`IsPLHomeomorphOn` is the *normed-space* notion (`Polyhedron.lean:13`), not the
manifold-level `IsPLOn`. `Moise351` (`:191`) is the locally finite polyhedral *graph*
case. `Moise331` (`:136`) is the regular neighbourhood of a graph; its earlier
quantifier-order defect is repaired, so it now chooses the neighbourhood inside the
prescribed open `U`. All three are open.

### The questions

**Q1. What is the right stage recursion?** This is now the main question, because two
successive formulations of it have been *false*, each for a quantifier reason — see both
corrections in the status section. `Moise352Stages` fixed a tolerance sequence before the
family and thereby pinned the approximation to `h`. `Moise352StageStep` used a pointwise
`φ` bounded below but not above, so its relative clause degenerated into an extension
statement, refuted by an annulus in the plane and by a knotted solid torus in a ball.
Please write down the statement Moise's §35 induction actually uses, in a form that is
both true and iterable, rather than repairing ours again.

**Q1a.** The repaired relative clause with `η` quantified before `g` is proved modulo
injectivity. But any valid `η` satisfies `η ≤ ε` when the previous stage is nonempty,
since the produced map equals `g` there. So a recursion forces tolerances to *increase*
along the tower while the constants from a pointwise `φ` *decrease*, and the existing
assembly, which demands exact agreement on the whole previous stage, cannot consume it.
Is the standard fix (i) agreement on a strictly smaller stage than the one the tolerance
controls, (ii) a diagonal or limiting argument over the whole tower, or (iii) something
else entirely? What exactly does Moise do here — please cite the page, because this is
the step we have twice got wrong by guessing.

**Q2.** Does `Moise341` imply clause (1)? It is the local, ball-shaped, absolute,
dimension-3 core, and deriving clause (1) from it appears to need chart localisation,
a PL-ball cover of the stage, and a ball-by-ball gluing induction preserving
injectivity — which is Moise 34.1 → 35.1 and is unstarted here. Confirm or correct
that, and say precisely what the gluing induction needs.

**Q3.** Moise's route to 34.1 goes through 33.1 and is long. Is there a shorter
modern route to the *relative* compact statement in dimension 3 — Bing's side
approximation theorem, Hudson's PL approximation, or the Hauptvermutung machinery
this tree has already built? Give the precise statement you would import and its
citation, and say what its own prerequisites are, so we can judge whether it is a
shortcut or a detour.

**Q4.** Is the relative form genuinely harder than the absolute one, or is there a
standard trick (approximate absolutely on a slightly larger stage, then interpolate
in a collar) that reduces it? If the collar trick works, what exactly does it need
about the previous stage's boundary?

**Q5.** Honest assessment: how far is 35.2 from being closeable, in the sense of
how many independent theorems of this size are between us and it? We currently
believe it is five chapters deep (35.2 → 35.1 → 34.1 → 33.1 → …) and would like that
checked rather than confirmed.

### Constraints on the answer

Same as prompt 1: exact statements, printed-page citations, no weakening of existing
statements, and a plain statement if something already built is aimed wrong.

---

## 3. Where closed-branch Case 1 actually occurs in the tower

*(Self-contained. Paste whole. Answer in English or Chinese.)*

### Where to look

Public repository **https://github.com/liao9yuan/differential-geometry-dev**, branch
**`moise-integration`**, browsable at
**https://github.com/liao9yuan/differential-geometry-dev/tree/moise-integration**.
Read the head of that branch; do not read any other branch, they diverge and line
numbers will not match.

### State

Moise's closed Case 1 handles a closed branch whose complete preimage is a **single**
circle doubly covering the image circle, by splicing a cylinder with the
identification `(x, y, 0) ~ (y, x, 1)` — a mapping torus whose end map is the
coordinate swap, a reflection. A previous consultation resolved the apparent tension
with orientability, and the resolution is now **proved**, in
`DifferentialGeometry/Topology/PiecewiseLinear/ClosedBranchOrientability.lean`
(747 lines, 46 declarations, axioms exactly `propext, Classical.choice, Quot.sound`):

```lean
theorem not_isCylindricalDiagram_swap_of_isOrientable {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : (ℝ × ℝ) × ℝ → F}
    (D : Geometry.SimplicialComplex ℝ (ℝ × ℝ)) (M : Geometry.SimplicialComplex ℝ F)
    [Finite D.faces] [Finite M.faces] (hD : D.space = spliceSquare)
    (hM : IsCombinatorialManifoldWithBoundary 3 M) (hor : IsOrientable 3 M)
    (hf : IsCylindricalDiagram f D.space M.space)
    (hfu : ∀ x ∈ D.space, f (x, 0) = f (Prod.swap x, 1)) : False
```

together with the concrete instance
`not_isPLCirclePositive_spliceSquareBoundary_swap : ¬ IsPLCirclePositive
spliceSquareBoundary Prod.swap`, which makes the exclusion non-vacuous. The
mathematical core is a cyclic-order argument done directly on the increasing circle
lift: for `α < β < γ < δ < α + 1` with `ψ↑α = ↑β` and `ψ↑γ = ↑δ`, one gets
`ψ↑β ≠ ↑α`; applying it twice gives `ψ(ψ↑α) = ↑γ`, contradicting the sheet exchange
being an involution on the four rays. The four rays land in the required cyclic order
unconditionally, because cutting the square's boundary at the two `crossingArcY` rays
puts exactly one `crossingArcX` ray in each open arc.

The precision the earlier consultation insisted on is preserved and is the crux of
the remaining question: `M` here is the **diagram's own target complex** — a
triangulation of the tube, since `IsCylindricalDiagram f D.space M.space` makes
`M.space` the image of the whole diagram — and *not* the ambient 3-manifold.

### The questions

**Q1.** The exclusion needs `IsOrientable 3 M` for the tube's own triangulation.
`Moise252` hypothesises `IsOrientable 3 K` for the ambient complex. What is the
correct transport step from the second to the first, and under what hypotheses is it
valid? A tube embedded in an orientable 3-manifold inherits an orientation, but the
tube here is the image of a diagram and need not be embedded. State the exact
condition.

**Q2.** Given Q1, does Case 1 arise **only** at non-orientable stages of the
Stallings tower? `DifferentialGeometry/Topology/PiecewiseLinear/LoopTheorem/CoverReduction.lean`
handles the non-orientable case by passing to the double cover, so intermediate
systems need not be orientable even though the bottom one is. Please argue from the
geometry, not from the formalisation. If Case 1 *can* arise over an orientable
ambient, the reflection model must be wrong there — say what replaces it.

**Q3.** What exactly is "the branch's preimage is a single circle doubly covering it"
in terms of the branch's normal bundle inside the disk image, and does that datum
determine the orientability of a neighbourhood? The tree's dichotomy is
`branchPreimage_isPLSphere_or_exists_two_isPLSpheres_of_not_boundaryBranch`,
`DifferentialGeometry/Topology/PiecewiseLinear/LoopTheorem/BranchPreimage.lean:1119`.

**Q4.** The three inputs the induction must still supply, none of them proved, are:
(i) that the Case 1 tube of a real closed branch carries a cylindrical diagram over a
triangulated square with end map `Prod.swap` — `CylinderSplice.lean` states the
matching fact only conditionally, as `spliceRel_iff_of_isCylindricalDiagram`, and
constructs no such diagram; (ii) the orientability transport of Q1; (iii) matching
the one-circle branch of the dichotomy to the modelled case, with the two sheets
meeting the cross-section in the four rays `spliceEnds`. Which of these three does
Moise actually prove, and where (printed page)? Which does he treat as obvious, and
is he right to?

**Q5.** Is the exclusion even the right tool? It is stated as an exclusion to use
*alongside* the general reflection model, not in place of it. If Moise's proof simply
handles Case 1 by the splice and never needs to exclude it, say so — we would rather
delete a correct theorem we do not need than build an induction around it.

### Constraints on the answer

Exact statements, printed-page citations, no weakening of existing statements, and a
plain statement if something already built is aimed at the wrong target.

## 4. Lifting the boundary word from ranges to parametrised loops

*(Self-contained. Paste whole. Answer in English or Chinese.)*

### Where to look

Public repository **https://github.com/liao9yuan/differential-geometry-dev**, branch
**`moise-integration`**, browsable at
**https://github.com/liao9yuan/differential-geometry-dev/tree/moise-integration**.
Read the head of that branch; do not read any other branch, they diverge and line
numbers will not match.

### State

The selection step of Moise's Lemma 2 for a boundary branch is now assembled, in
`DifferentialGeometry/Topology/PiecewiseLinear/LoopTheorem/BoundaryBranchDescent.lean`.
Both candidates — the direct surgery and the cross reglue repaired by
`CrossSeamResolutionData` — enter through one door,

```lean
structure NormalSingularCellData.DescendingSurgery (hD : NormalSingularCellData D BdM B) where
  cell : SingularTwoCell M
  normal : NormalSingularCellData cell BdM B
  complexity_lt : normal.singularSet.complexity < hD.singularSet.complexity
```

so the descent is literally uniform, and the word elimination then picks whichever of
the two avoids the normal subgroup. The multiplication-order question is settled and
needs no further inversion at this level: `BoundaryWordConnectors` and
`CutAndPaste.lean:2907` already instantiate `BoundaryWordElimination` at the inverses
of the four connector classes, because Mathlib's `FundamentalGroup` satisfies
`g * h = h ⬝ g`, and everything in the new file is in the traversal convention.

What blocks the theorem from being stated purely `_of_boundaryBranch` is **not** a
group-theoretic issue. It is that the tree records the boundary curves of both
candidates only as **sets**, and the elimination needs them as **parametrised loops**.

### The gap, exactly

For the direct candidate, the tree gives
`Set.range Gd.boundary = D '' (U ∪ V)`, and separately
`∀ θ, Gd (e θ) = pathToCircle (α.trans ω) θ` with `Set.range α = D '' U` and
`Set.range ω = D '' V`. What is needed is

> there is a parametrisation `edirect : loopCircle ≃ₜ frontier Gd.domain` with
> `∀ θ, ρ (pathToCircle (σ.trans υ.symm) θ) = Gd (edirect θ)`,

where `σ, τ, υ, φ` are the images in `X` of the four arcs of `frontier D.domain` at
the cut. For the cross candidate the same is needed for
`pathToCircle (σ.trans (φ.trans (υ.trans τ)))` in the endpoint-reversing case and
`pathToCircle (σ.trans (τ.symm.trans (υ.trans φ.symm)))` in the preserving case — and
that one is strictly harder, because `CrossSeamResolutionData` records no boundary
parametrisation at all and nothing yet says the seam resolution leaves the boundary
curve of the raw cross reglue unchanged. `ReplacementDisk.lean` identifies the cross
candidate's two boundary arcs as `D`-images of
`(D₁.domain ∪ D₂.domain) ∩ frontier D.domain` and `D₃.domain ∩ frontier D.domain`,
again at set level only.

### The questions

**Q1.** Does Moise actually need the parametrised statement, or does his argument go
through with the boundary class determined up to free homotopy by the four arcs and
their endpoints? If the latter, what is the exact weaker statement, and what makes it
enough for the elimination?

**Q2.** What is the standard way to lift "the boundary of the surgered disk is the
union of these two arcs" to "it is this specific concatenation, traversed in this
order"? Presumably the cut-and-paste construction produces the parametrisation for
free and the tree simply discarded it. Is that right, and is there a reason it could
fail — for instance can the two arcs meet in more than their endpoints?

**Q3.** For the cross candidate specifically: does the cross-seam resolution move the
boundary curve at all? The model theorems say the replacement is the identity on the
four lateral attaching intervals and is supported in the cross-section disks
(`crossSeamResolve*_eqOn_lateral`, `segment_crossSeamResolvePos_subset`), which
suggests the boundary moves only inside the two end disks of the tube. Is "the
boundary curve is unchanged up to a homotopy supported in the end disks" true, and is
it enough?

**Q4.** Is `DescendingSurgery` the right common shape, or does Moise's induction need
more carried along — for instance the image containment `G '' G.domain ⊆ D '' D.domain`,
which the direct candidate satisfies but the cross candidate only satisfies as
`⊆ D '' D.domain ∪ U`? If the induction needs the stronger form, the cross candidate
as built is aimed wrong and we should know now.

### Constraints on the answer

Exact statements, printed-page citations, no weakening of existing statements, and a
plain statement if something already built is aimed at the wrong target.
