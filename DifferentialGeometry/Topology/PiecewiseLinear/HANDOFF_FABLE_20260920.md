# Handoff — Moise Lemma 2 and 35.2

Repository **https://github.com/liao9yuan/differential-geometry-dev**, branch
**`moise-integration`**, browsable at
**https://github.com/liao9yuan/differential-geometry-dev/tree/moise-integration**.
Local checkout `D:\differential-geometry-moise-int`, branch `codex/moise-integration`.

The book is Moise, *Geometric Topology in Dimensions 2 and 3*, GTM 47, available locally at
`D:\differential-geometry-moise-plan\.lake\scratch\moise_gtm47.pdf`. **Offset: book page + 9
= zero-based PDF index**, so book p. 251 is PDF page 261 one-based; verified against running
heads. Read it directly rather than guessing — doing so overturned an entire invented route.

## The two chains

Every arrow is a proved theorem with transitive axioms exactly `propext, Classical.choice,
Quot.sound`:

```
LemmaTwoStatement --moise252_of_lemmaTwo--> Moise252 --moise304_of_moise252-->
    Moise304 --moise305_tame_of_moise304--> Moise305Tame

Moise352InwardPush 3 ∧ Moise351 ∧ Moise352SkeletonExtension 3
    --moise352_of_inwardPush_of_skeletonExtension--> Moise352 3
    --plApproximationManifold_three_of_moise352--> PLApproximationManifold 3
```

`NormalSystem` is known to be inhabited (`LoopTheorem/NormalSystemWitness.lean`,
unconditional), so the first chain is not vacuous at its base.

---

# Read this first: six statements here were FALSE

This is the single most important thing to know. Six statements that everyone treated as
"true but unproved" turned out to be **false**, each found only when someone actually
instantiated them or read the construction. **Four of the six were authored by the
coordinator.** Assume your own first formulation of anything below is wrong until it
compiles against something concrete.

1. **The direct surgery's surjectivity.** `D.domain \ C ⊆ pullback '' G.domain` is false:
   `exists_boundary_surgery_cell_of_boundaryBranch` glues the two *outer* cells of
   `exists_three_cells_of_boundaryBranch` and **discards the middle band**. Any interior
   point of `D₂.domain` refutes it. Consequence: the direct candidate admits no branch
   *bijection*, only an injection.
2. **`Moise352Stages`** — an invented recursion. It fixed a tolerance sequence before the
   family while demanding agreement between consecutive stages; since stages increase, that
   pins the approximation to `h`. False at `n = 1`, `h x = x³`.
3. **`Moise352StageStep`** — the repair of 2, also invented, also false. Its tolerance was
   bounded below but not above; taking it large degenerates the relative clause into an
   *extension* statement, false at `n = 2` by Jordan and `n = 3` by Alexander.
4. **`CrossSeamTubeCore` was uninhabited.** It equated the compact `chart '' crossingFigure`
   with the relatively open `figure ∩ tube`, which is clopen in the connected `figure` and
   hence all of it — forcing complexity exactly 1, so the induction it served could not run.
   **It had a non-vacuity witness, and the witness was degenerate**: it took `tube := univ`
   and `figure := chart '' crossingFigure`. Repaired; the audit now requires strictness
   theorems beside any witness.
5. **`hcross`**, a hypothesis of the descent selection, was *impossible*, not unproved. With
   `pathToCircle` and Mathlib's nested `Path.trans`, the four-arc word visits `a` at circle
   parameters `0` and `3/4`; a literal identification with an injective parametrisation puts
   `ρ a` in the resolved cell's double point set, which `CrossSeamResolutionData` excludes.
   Replaced by comparison up to free homotopy.
6. **The frontier collar.** "A collar `frontier K × [0,1] ≅ V ∩ K` restricting to the
   identity on `frontier K × {0}`" is false: every open set is a locally finite polyhedral
   3-manifold with boundary, so take `K = {0}ᶜ` in `ℝ³`, whose frontier `{0}` is **disjoint
   from `K`** while a collar lands in `V ∩ K ⊆ K`. The correct set is `K \ interior K`,
   Moise's own `K ∖ Int K`.

**The two reliable tells**, every time: nobody read how the object was *constructed*, only
what the theorem's statement *recorded*; and nobody tested the quantifiers at their extremes
(empty, degenerate, very large, very small).

---

# Open problem 1 — the normal-crossing product tube

**The largest single gap on the Lemma 2 chain.** Everything around it is built:
`LoopTheorem/CrossSeamResolution.lean` (model seam repair, branch deleted exactly),
`CrossSeamTube.lean` (transport, repaired contract, non-degenerate witness),
`ResolvedCellNormal.lean` (all six normality fields), `BranchDeletion.lean` (deleted
triangulation and branch bijection), `BranchInjection.lean` (the direct candidate's
injection, with "every other branch is wholly kept or wholly lost, never cut"),
`BoundaryBranchDescent.lean` (uniform descent, word elimination),
`BoundaryWordWitness.lean` (homotopical boundary comparison), `SeamBoundaryHomotopy.lean`
(the model homotopy and a witness producer, **in `X`**), and
`LoopTheorem/BoundaryCaseReduction.lean`, which assembles the whole boundary case into one
theorem whose hypotheses are every remaining gap.

`IsCrossSeamTubeProducer` (end of `CrossSeamTube.lean`), in the repaired form:

> For `hD : NormalSingularCellData D BdM B` and `c` a **boundary** branch, there are an open
> `U ⊆ M` and `Φ : (ℝ × ℝ) × ℝ → M` with (i) `Φ` continuous and injective on
> `spliceCylinder`, image in `U`; (ii) `Φ '' ({(0,0)} × [0,1]) = branchCarrier c`;
> (iii) `Φ '' (cross × [0,1]) = D '' D.domain ∩ Φ '' spliceCylinder`;
> (iv) `doublePointSet D D.domain ∩ U = branchCarrier c`.

Clause (iii) compares against the **closed** cylinder image — against the open `U` it is the
refutation of item 4 above. Clauses (ii) and (iii) are the *relative* content: not a ball
neighbourhood of the arc, but one meeting the singular surface in the standard transverse
cross swept along the arc.

Available: `hD.singularSet.complex` is finite and a combinatorial 1-manifold; the branch
carrier is a polyhedral **arc** with endpoints on `BdM`, so the tube is a half-tube;
`pairwise_disjoint_branchCarrier` plus finiteness give (iv) for small `U`; `hD.fiber_le_two`
gives four half sheets; `hD.crossing` gives `HasPLNormalDoubleCrossingAt` at **each** double
point in **some** chart. `ArcChainNeighborhood.lean:57` gives the **absolute** PL ball
neighbourhood of a simplicial arc.

**The gap is the passage from the pointwise normal form to one product chart valid along the
whole arc** — a *relative* regular neighbourhood theorem for the pair (3-manifold,
2-complex). Four further properties are needed downstream by
`CrossSeamTubeData.normalOfResolvedCell` and probably belong in the statement: charts at
outside double points disjoint from the cylinder; the end cross sections lying in `B`; the
source strips running end to end; and the tube meeting `BdM` only in its end cross sections.

Is it true, with which hypotheses? Is it a published relative regular neighbourhood theorem
(Rourke–Sanderson, Hudson, Zeeman)? Does Moise prove it, on which page? **Or is it false** —
can the four sheets be locally knotted?

# Open problem 2 — the §34 simplex-by-simplex transition

Moise's actual proof of 35.2 (printed p. 251, read directly) performs **no stagewise
recursion**. It pushes `K` into `Int K`, reduces to an open neighbourhood, subdivides so each
simplex has small image, applies 35.1 to a regular neighbourhood of the **1-skeleton**, and
then: *"the transition from Theorem 35.1 to Theorem 35.2 is essentially the same as the
transition from Theorem 33.1 to Theorem 34.1; the argument in Section 34 treated the
simplexes of `K` essentially one at a time."*

`Moise352SkeletonExtension` (`SkeletonReduction.lean:208`) is that transition, stated
**without** a fineness hypothesis — the tree has no global subdivision across a piece tower,
since every mesh theorem needs `[Finite K.faces]`, so the obligation must choose its own
subdivision and 1-skeleton, and is handed `Moise351` for every graph in every open subset to
let it.

§34's own proof (pp. 239–246) subdivides with a link condition, takes a regular neighbourhood
of `K¹` with splitting disks decomposing it into dual cells, applies 33.1, and extends over
2- and 3-simplexes using solid tori, spines (30.8) and general position (30.5). For a
2-simplex `σ`, the union `N_σ` of dual cells at its vertices is a **solid torus**.

Questions: the precise statement for a locally finite `K` in a general PL 3-manifold rather
than a polyhedral 3-cell in `ℝ³`; which of §34's Lemmas 1–10 generalise verbatim; whether
Moise's "essentially the same" elides a real difficulty in the non-compact, non-Euclidean
setting.

# Open problem 3 — the non-compact inward push

`Moise352InwardPush 3` is **proved for compact `K`**
(`ControlledInwardPush.lean`, `IsPolyhedralManifoldWithBoundary.exists_isPLOn_injOn_leftInvOn_dist_lt`).
Every step is insensitive to compactness **except the collar**.

After refutation 6, the corrected target is: for a locally finite polyhedral `n`-manifold
with boundary `K` in a PL `n`-manifold, a PL homeomorphism of `(K \ interior K) × [0,1]` onto
a neighbourhood of `K \ interior K` **in `K`**, identity on the zero level.
`LocallyFiniteCollar.lean` proves the needed structure on that set
(`isLocallyPolyhedralManifold_sdiff_interior`, via "the stages' frontiers glue").

The obstruction: **the tree's polyhedral-manifold vocabulary is compact-only.**
`IsPolyhedralManifold` is compact by construction, so the triangulated global form cannot be
stated; one would need a `LocallyFinitePieceTower` on `K \ interior K`, and
`N i ∩ (K \ interior K)` is a compact polyhedron that need not be a surface with boundary, so
the exhaustion needs regular neighbourhoods inside the stage frontiers.

# Open problem 4 — the boundary words

`BoundaryCaseReduction.lean` needs `BoundaryWordWitness`es for both candidates. Both recorded
boundary descriptions are **two-arc words valued in `M`**, while the witness needs a word in
`X` (the ambient loop space carrying the normal subgroup — in the tower
`S.boundaryNeighborhoodSpace`, **not** `BdM` and **not** `M`; a homotopy in `M` is worthless
since the candidate boundaries already bound disks there). Two shifts: manifold → ambient
loop space, which is mechanical, and **two arcs → four**, which is the real obligation.

# Open problem 5 — closed branch Case 1

The Case 1 exclusion (`ClosedBranchOrientability.lean`) is correct but **off the dependency
path**: `LemmaTwoStatement` has no orientability hypothesis, a genuine tower above an
orientable bottom does not acquire non-orientable stages, so Case 1 must be **handled**, not
excluded. The model replacement is built (`ClosedSeamResolution.lean`): the chords
`x - y = ±1`, which `Prod.swap` exchanges, give an untwisted band rather than a Möbius band,
with the rejected alternative `x + y = ±1` formalised to show the choice is forced.

Missing: that a real closed branch carries a cylindrical diagram with end map `Prod.swap`,
and the **straightening** of an arbitrary PL monodromy to `Prod.swap` — determining the ray
permutation is *not* the pointwise normal form. Also, `Quotient spliceSetoid` carries **no
topology and no PL structure** anywhere in the tree, so "the replacement is an annulus"
cannot even be *stated* about it.

# Open problem 6 — the cheap fixes

Each is small and each removes obligations from `BoundaryCaseReduction.lean`. These are the
ones to hand to a worker rather than think about.

* **M1**: the witness selection theorems ask for a branch *bijection*; `BranchInjection`
  proves only an injection, which is all `complexity_lt_of_injective_origin` needs. A sibling
  calling `ofBranchInjection` — about six lines in `BoundaryWordWitness.lean`.
* **M4**: `CrossSeamRegluedData.normal` is a field, which makes `normalOfTube` unusable (it
  takes the bundle whose field is what it produces). Delete the field, as its own docstring
  proposes, and restate `doublePointSet_cell_eq` on the five geometric fields.
* **M7**: `exists_cross_reglued_cell_of_boundaryBranch` never asserts the reglued cell is
  normal (verified: zero occurrences of `NormalSingularCellData G` in its conclusion). Adding
  `Nonempty (NormalSingularCellData G BdM B)` to it collapses four obligations to field
  projections.
* **M9**: a `BoundaryWordWitness.ofManifoldRealization` turning a manifold-valued boundary
  parametrisation into a witness — about ten lines, using `hρ.isInducing` to lift.
* **M2**: `hdisk` and `hendDisks` are the same inclusion in two spellings; moving
  `spliceEndDisks` down from `ResolvedCellNormal` into `CrossSeamTube` removes a four-line
  conversion.
* **M8** (not cheap, flagged here for completeness): `hGcrossing` is strictly stronger than
  the `crossing` field and is **not** obtainable by shrinking, since `atlas` need not be
  closed under restriction to opens.

---

# Verification protocol — non-negotiable

**Never run a writing git command.** No `add`, `commit`, `push`, `checkout`, `stash`,
`reset`, `restore`, `clean`. Read-only git is fine. The coordinator commits everything; hand
back a manifest of verified files.

Each worker owns **exactly one new `.lean` file** and may append **exactly one** import line
to `DifferentialGeometry.lean`, append-only — several workers append there concurrently, so
never reorder or rewrite it.

**Run the helper scripts from PowerShell, not Bash** — Bash eats the backslashes in a Windows
path, seeds into a mangled directory, and the checker then silently falls back to the shared
build and fails on a module nobody touched.

Re-run the prepare script immediately before **every** checker run:

```
python C:\Users\liao9\AppData\Local\Temp\claude-moise-shared\prepare-private-root.py <OUTPUT_ROOT> <Module.Name>
```
```
powershell -NoProfile -ExecutionPolicy Bypass -File C:\Users\liao9\AppData\Local\Temp\claude-moise-shared\checker.ps1 -Checkout D:\differential-geometry-moise-int -Token <TOKEN> -OutputRoot <OUTPUT_ROOT> -Module <Module.Name>
```

Free lanes, one per worker:

| Token | OutputRoot |
|---|---|
| `claude-agent-a-20260919` | `C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a` |
| `claude-agent-b-20260919` | `C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-b` |
| `claude-agent-c-20260919` | `C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-c` |
| `claude-agent-d-20260919` | `C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-d` |
| `claude-agent-e-20260919` | `C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-e` |

Success is exactly `Verified ... with no diagnostics; shared outputs unchanged.` The global
mutex admits **two** Lean workers at a time, so a ten-minute admission failure is ordinary
queueing — re-run. The shared build's `MoiseChain` artifact is known stale; the prepare
script detects it and a line reading `M stale refreshed` is that fix working. Never run two
Lean processes in one worker. `E:\differential-geometry-dev` is read-only.

**House rules the module compile does not catch**, each of which bounces a delivery at the
coordinator's audit: no unused hypotheses or instance binders; **no underscore in any
`def`/`abbrev`/`structure` name** (`defsWithUnderscore`; `theorem`/`lemma` keep snake_case);
every new public name unique tree-wide, checked with `grep -rE` (this shell's locale rejects
`-P`); lines ≤ 100 Unicode codepoints; a Mathlib docstring on every public declaration and
structure field; no docstring line starting with the bare word
`structure`/`instance`/`theorem`/`def`; no `sorry`, `admit`, `native_decide`, or new `axiom`;
`autoImplicit` off. `Homeomorph.toContinuousMap` does not exist in Mathlib v4.33.1.

**Non-vacuity is mandatory and is checked.** Anything introduced as a structure or `Prop`
must be instantiated, and the instance must come with **strictness theorems** showing it is
not degenerate — "the ambient is strictly larger than the model", "the double point set is
strictly larger than the one branch". A witness that takes the ambient to be the model will
be rejected. Refutation 4 above passed review precisely because nobody checked its witness
for degeneracy.

**Never weaken a statement to make it provable.** Several of these obligations are consumed
verbatim by proved reductions, and a weakened version silently breaks the route. If a target
is false, say so with a counterexample — that has been the most valuable outcome six times.
