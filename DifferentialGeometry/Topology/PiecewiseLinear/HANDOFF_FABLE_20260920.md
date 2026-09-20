# Handoff — Moise's Lemma 2 and Theorem 35.2, in Lean 4

You are taking over as lead on a Lean 4 / Mathlib formalisation of Moise's route to the
3-dimensional triangulation theorem. Read this whole file before touching anything.

**Repository** https://github.com/liao9yuan/differential-geometry-dev, branch
**`moise-integration`** —
https://github.com/liao9yuan/differential-geometry-dev/tree/moise-integration
**Local checkout** `D:\differential-geometry-moise-int`, branch `codex/moise-integration`.
Start with `git log --oneline -40`; the commit messages carry the reasoning, not just the
diffs, and several record refutations you must not re-derive.

**The book** is Moise, *Geometric Topology in Dimensions 2 and 3*, GTM 47, local copy at
`D:\differential-geometry-moise-plan\.lake\scratch\moise_gtm47.pdf`. **Book page + 9 =
zero-based PDF index**, so book p. 251 is PDF page 261 one-based. Read it directly. Doing so
once replaced an entire invented recursion with Moise's actual three-line argument.

---

## The two chains

Every arrow is a proved theorem whose transitive axioms are exactly `propext,
Classical.choice, Quot.sound`:

```
LemmaTwoStatement --moise252_of_lemmaTwo--> Moise252 --moise304_of_moise252-->
    Moise304 --moise305_tame_of_moise304--> Moise305Tame

Moise352InwardPush 3 ∧ Moise351 ∧ Moise352SkeletonExtension 3
    --moise352_of_inwardPush_of_skeletonExtension--> Moise352 3
    --plApproximationManifold_three_of_moise352--> PLApproximationManifold 3
```

`NormalSystem` is known inhabited (`LoopTheorem/NormalSystemWitness.lean`, unconditional), so
the first chain is not vacuous at its base.

---

## Read this first: SEVEN statements here were false

Seven statements that everyone treated as "true but unproved" turned out to be **false**, each
found only when someone instantiated them or read the construction. **Five were authored by
the previous coordinator.** Assume your own first formulation of anything below is wrong until
it compiles against something concrete.

1. **Direct surgery surjectivity.** `D.domain \ C ⊆ pullback '' G.domain` is false —
   `exists_boundary_surgery_cell_of_boundaryBranch` glues the two *outer* cells and **discards
   the middle band**. So the direct candidate admits no branch bijection, only an injection.
2. **`Moise352Stages`** — invented. A tolerance sequence fixed before the family, plus
   agreement between increasing stages, pins the approximation to `h`. False at `n = 1`,
   `h x = x³`.
3. **`Moise352StageStep`** — the repair of 2, also invented. Its tolerance was bounded below
   but not above; taking it large degenerates the relative clause into an *extension*
   statement, false at `n = 2` by Jordan, `n = 3` by Alexander.
4. **`CrossSeamTubeCore` was uninhabited.** It equated the compact `chart '' crossingFigure`
   with the relatively open `figure ∩ tube`, clopen in the connected `figure`, hence
   everything — forcing complexity exactly 1. **It had a non-vacuity witness and the witness
   was degenerate**: `tube := univ`, `figure := chart '' crossingFigure`. Repaired.
5. **`hcross`** was *impossible*, not unproved: the four-arc word visits `a` at circle
   parameters `0` and `3/4`, so a literal identification with an injective parametrisation
   puts `ρ a` in a double point set that `CrossSeamResolutionData` excludes. Replaced by
   comparison up to free homotopy.
6. **The frontier collar.** Every open set is a locally finite polyhedral 3-manifold with
   boundary, so take `K = {0}ᶜ` in `ℝ³`: `frontier K = {0}` is **disjoint from `K`**, while a
   collar lands in `V ∩ K ⊆ K`. The right set is `K \ interior K`, Moise's `K ∖ Int K`.
7. **`Nonempty (NormalSingularCellData G BdM B)` for the cross reglued cell** is uninhabited:
   `crossing` demands a normal double crossing at *every* double point, and
   `CutAndPaste.lean:1256` records that the branch carrier survives in `doublePointSet G`,
   where the two sheets are bent L-shapes **touching along the axis, not crossing it**. That
   is why the assembly asks `hGcrossing` only at `y ∉ U`.

**The two tells, every time:** nobody read how the object was *constructed*, only what the
statement *recorded*; and nobody tested the quantifiers at their extremes.

---

## Where the work stands

**Lemma 2, boundary branch.** Assembled end to end into one theorem,
`exists_descendingSurgery_of_crossSeamTube_reversing`
(`LoopTheorem/BoundaryCaseReduction.lean`), whose conclusion is the descent-plus-avoidance
conclusion of the selection theorems and whose hypotheses are every remaining gap. Built
under it: the model seam repair (`CrossSeamResolution`), the transport and repaired tube
contract (`CrossSeamTube`), all six normality fields of the resolved cell
(`ResolvedCellNormal`), the deleted triangulation and branch bijection (`BranchDeletion`), the
direct candidate's branch **injection** with "every other branch is wholly kept or wholly
lost, never cut" (`BranchInjection`), uniform descent and word elimination
(`BoundaryBranchDescent`), the homotopical boundary comparison (`BoundaryWordWitness`,
`BoundaryWitnessDoors`), the model homotopy and a witness producer **in `X`**
(`SeamBoundaryHomotopy`), the crossing locality lemmas (`SingularCrossingLocality`), and three
of the reglued cell's five elementary fields (`CrossRegluedCellFields`).

**Lemma 2, closed branch.** The Case 1 exclusion (`ClosedBranchOrientability`) is correct but
**off the dependency path** — `LemmaTwoStatement` has no orientability hypothesis and a
genuine tower above an orientable bottom stays orientable, so Case 1 must be *handled*. The
model replacement is built (`ClosedSeamResolution`): the chords `x - y = ±1`, which
`Prod.swap` exchanges, give an untwisted band, with the rejected `x + y = ±1` formalised to
show the choice is forced.

**35.2.** Reduced to Moise's own three inputs. `Moise352InwardPush 3` is **proved for compact
`K`** (`ControlledInwardPush`); the non-compact case is blocked on a collar, and
`LocallyFiniteCollar` supplies the structure on the corrected set.

**Off the path, now documented as such:** the whole boundary slide chain —
`BranchSeparation*`, `BranchBoundaryCollar`, `BranchCollarPrism*`, `BranchCaseThreeFour`,
`LuneCell`, `BranchBoundarySweep`, `DisplacedArcConnected`, `BranchComplexityDrop` — is
refuted at a boundary branch by
`not_boundary_slide_chart_of_isBoundaryBranch` (`BoundarySlideVacuity.lean`). Each file now
says so in its docstring.

---

## The open problems

**1. The normal-crossing product tube — the largest gap.** `IsCrossSeamTubeProducer`
(`CrossSeamTube.lean`). For a boundary branch, an open `U` and `Φ : (ℝ × ℝ) × ℝ → M` with `Φ`
continuous and injective on `spliceCylinder`, `Φ '' ({(0,0)} × [0,1]) = branchCarrier c`,
`Φ '' (cross × [0,1]) = D '' D.domain ∩ Φ '' spliceCylinder` (against the **closed** cylinder
image — against open `U` it is refutation 4), and
`doublePointSet D D.domain ∩ U = branchCarrier c`.

**A PL clause is missing and the contract as stated is insufficient.** `SingularCell.lean:30`
carries `isPLOn : IsPLOn 2 3 toFun domain`, so the cell has PL data and the tube chart must be
PL on the cylinder; a purely topological (Alexander-cone) construction proves only the current
contract. The right target is an `IsCrossSeamPLTubeProducer`. The gap proper is the passage
from `hD.crossing`'s **pointwise** normal form to **one product chart along the whole arc** —
a *relative* regular neighbourhood theorem for the pair (3-manifold, 2-complex);
`ArcChainNeighborhood.lean:57` gives only the absolute ball neighbourhood.

**2. The §34 simplex-by-simplex transition.** `Moise352SkeletonExtension`
(`SkeletonReduction.lean:208`). Moise, p. 251: *"the transition from Theorem 35.1 to Theorem
35.2 is essentially the same as the transition from Theorem 33.1 to Theorem 34.1; the argument
in Section 34 treated the simplexes of `K` essentially one at a time."* §34's own proof
(pp. 239–246) runs on dual cells, solid tori, spines (30.8) and general position (30.5); the
tree has those as stubs. Note `Moise351` is itself open with no producer, resting on §§33–34 —
that, not the transition, is the honest headline for this chain.

**3. The non-compact inward push.** Blocked on a collar of `K \ interior K` inside `K`. The
obstruction is that the tree's polyhedral-manifold vocabulary is **compact-only**:
`IsPolyhedralManifold` is compact by construction, so the triangulated global form cannot even
be stated.

**4. The boundary words — an EXPORT gap, not a theorem gap.** The direct producer's proof
builds injective source parametrisations of the two frontier arcs
(`CutAndPaste.lean:1496–1538`) and exports only `Set.range σ = D '' U`. With those exported,
the witness follows: match against the four-arc word by
`Path.Homotopic.of_injective_of_range_eq` (`LoopSpace/InjectivePathReparam.lean`, proved),
lift through `ρ` as `SeamBoundaryHomotopy` does, flip by the circle reflection if the
orientation is reversed. The cross candidate needs the same from `CellGluing`'s cross glue.

**5. Closed Case 1.** Missing: that a real closed branch carries a cylindrical diagram with
end map `Prod.swap`, and the **straightening** of an arbitrary PL monodromy to `Prod.swap` —
determining the ray permutation is *not* the pointwise normal form. Also `Quotient
spliceSetoid` carries no topology or PL structure, so "the replacement is an annulus" cannot
be stated about it.

**6. Three layers stand between the assembled boundary case and `LemmaTwoStatement`**, beyond
everything above: (i) general position and normality of the tower's singular disk — nothing
produces `NormalSingularCellData` for the cell that `LemmaTwo.lean:145` builds; (ii) the
complexity induction — `DescendingSurgery` is consumed only inside the selection files, and
there is no cell-level induction to a `NonsingularCell`; (iii) transport back to
`NonsingularCell S → EmbeddedDisk S`, partly present.

**`hGcrossing` is now dischargeable from the producer.**
`exists_cross_reglued_cell_crossing_outside_of_boundaryBranch`
(`LoopTheorem/CrossRegluedCellCrossing.lean`, commit `4906eb088`) concludes exactly the
`hGcrossing` binder of `BoundaryCaseReduction.lean:201`, unconditionally given `hD` and
`hc : IsBoundaryBranch c`. Refutation 7 bounds it from above: the crossing field cannot hold
*on* the branch carrier, so "off the branch carrier" is the strongest form available, and it
is what the assembly asks for.

**So the immediate next step is cheap:** a corollary of
`exists_descendingSurgery_of_crossSeamTube_reversing` that consumes
`exists_cross_reglued_cell_*` directly. That drops `hGim`, `hGD`, `hGinj`, `hGfiber` and
`hGcrossing` from the obligation list at once, leaving `hGboundary` and `hGimage` — the
frontier-image export gap below — and the tube-level clauses. Do this before the harder work;
it is the largest reduction in the obligation count available for the least effort.

**The next structural task**, which needs an exclusive window because `CellGluing.lean` and
`CutAndPaste.lean` sit in the closure of ten-plus modules: a **producer-strengthening pass**
adding to their conclusions the frontier equality `G '' frontier G.domain = D '' frontier
D.domain` (which closes two of the reglued cell's five fields) and the source
parametrisations (which closes problem 4), then updating the `obtain` consumers at
`BoundaryBranchDescent:226`, `CrossRegluedCellFields`, `BoundaryWordFourArcs`,
`BranchInjection`.

---

## How to work

**Delegate aggressively, and prefer Opus workers** (`model: "opus"`) for everything that is
not novel mathematics. Spend your own reasoning on problems 1 and 2. Three or four concurrent
workers is the useful range: the compile mutex admits **two** Lean processes globally.

**Compute import closures before assigning lanes.** One-new-file-per-worker does not protect
you when a worker edits several existing files.

**Never run a writing git command** — no `add`, `commit`, `push`, `checkout`, `stash`,
`reset`, `restore`, `clean`. Read-only git is fine. Hand back a manifest; the human commits.

**Run the helper scripts from PowerShell, not Bash.** Bash eats the backslashes in a Windows
path, seeds into a mangled directory, and the checker then silently falls back to the shared
build and fails on a module nobody touched.

Re-run the prepare script immediately before **every** checker run:

```
python C:\Users\liao9\AppData\Local\Temp\claude-moise-shared\prepare-private-root.py <OUTPUT_ROOT> <Module.Name>
```
```
powershell -NoProfile -ExecutionPolicy Bypass -File C:\Users\liao9\AppData\Local\Temp\claude-moise-shared\checker.ps1 -Checkout D:\differential-geometry-moise-int -Token <TOKEN> -OutputRoot <OUTPUT_ROOT> -Module <Module.Name>
```

| Token | OutputRoot |
|---|---|
| `claude-agent-a-20260919` | `C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a` |
| `claude-agent-b-20260919` | `…\claude-moise-agent-b` |
| `claude-agent-c-20260919` | `…\claude-moise-agent-c` |
| `claude-agent-d-20260919` | `…\claude-moise-agent-d` |
| `claude-agent-e-20260919` | `…\claude-moise-agent-e` |

Leases are in `D:\differential-geometry-moise-int\.lake\round-compiler-leases\*.json` and
expire **2026-09-21T06:00:00Z**. Ask the human to extend them; a worker rewriting its own
compiler authorization is flagged as self-modification, correctly.

Success is exactly `Verified ... with no diagnostics; shared outputs unchanged.` A ten-minute
admission failure is ordinary queueing — re-run. The shared build's `MoiseChain` artifact is
known stale; a `M stale refreshed` line is the prepare script's fix working. Never run two
Lean processes in one worker. `E:\differential-geometry-dev` is read-only.

**House rules the module compile does not catch**, each of which bounces a delivery: no unused
hypotheses or instance binders; **no underscore in any `def`/`abbrev`/`structure` name**
(`theorem`/`lemma` keep snake_case); every new public name unique tree-wide, checked with
`grep -rE` (the locale rejects `-P`); lines ≤ 100 Unicode codepoints; a Mathlib docstring on
every public declaration and structure field; no docstring line starting with a bare
`structure`/`instance`/`theorem`/`def`; no `sorry`, `admit`, `native_decide`, new `axiom`;
`autoImplicit` off. `Homeomorph.toContinuousMap` does not exist in Mathlib v4.33.1.

**Write audit probes with a file tool, never by assembling strings in a shell.** Two audit
rounds were lost to a missing `match` case and a missing trailing newline introduced that way.

---

## The three standing rules

**Non-vacuity is mandatory and is checked.** Anything introduced as a structure or `Prop` must
be instantiated, and the instance must carry **strictness theorems** showing it is not
degenerate — "the ambient is strictly larger than the model", "the double point set is
strictly larger than the one branch". Refutation 4 passed review precisely because nobody read
its witness for degeneracy.

**Never weaken a statement to make it provable.** Several obligations are consumed verbatim by
proved reductions — `moise352_of_inwardPush_of_skeletonExtension` consumes `Moise352InwardPush
3` literally — so a weakened version silently breaks the route.

**A target being false is a success.** Seven times now, the most valuable outcome has been a
counterexample. If you find an eighth, say so and stop rather than repairing around it.
