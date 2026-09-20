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

## Update — end of the second lead session, 2026-09-20. Read this before the rest

Everything below this section is the brief the session started from. It is kept because its
warnings stand, but several of its statements are now superseded; this section says which.
External consultation is run through `consult/` (one self-contained prompt per file, answers
digested next to them with the checked claims marked); the consultant reads the owner's
repository `liao9yuan/differential-geometry-dev`, branch `moise-integration`, which is **not**
this checkout's `origin` — sync it with
`%TEMP%\claude-moise-integration-private\sync-mirror.sh` (no force; see the script header).

### The chains now

```
GeneralPositionInDoubleBufferedStatement ∧ DescentStepStatement
    --lemmaTwoBufferedStatement_of_generalPosition_of_descentStep-->
  LemmaTwoBufferedStatement --moise252_of_lemmaTwoBuffered--> Moise252 --> Moise304 --> Moise305Tame
```

(`LoopTheorem/LemmaTwoSpine.lean`, `LoopTheorem/LemmaTwoBuffered.lean`.) `LemmaTwoStatement` is
no longer an undecomposed root. The three legs are proved: the **entry** cell is the projected
disk `DoubleCoverDiagram.exists_projected_singular_two_cell_in_double`
(`LoopTheorem/ProjectedCellInDouble.lean:23`, packaged in `ProjectedCellNormalFields.lean`) —
*not* the cell of `LemmaTwo.lean:145`, as item 6 below says; the **induction** is
`LoopTheorem/ComplexityInduction.lean`, generic in a motive; the **return** leg is
`LoopTheorem/EmbeddedDiskOfDoubleCell.lean`, straight to `EmbeddedDisk S`. The motive carries the
side of `BdM` in the double, the boundary buffer `∀ z ∈ range ∂, B ∈ 𝓝[Bd] z`, and the loop
clause. The buffer is supplied by the cover producers but dropped by the wrapper feeding
`LemmaTwoStatement`; the buffered route re-runs the Stallings inductions against the unwrapped
producer. **Hole that remains:** nothing in the tree inhabits `NormalSingularCellData`; the
descent step's hypotheses are reachable only through general position.

### Open obligations, as now understood

1. **General position across charts** (`GeneralPositionInDoubleBufferedStatement`; prompt C and
   its digest, which includes a review against the tree). `singularSet` is a **consequence** of
   the other five fields: `LoopTheorem/SingularSetOfCrossing.lean` has the chain up to the local
   line / half-line germ, the packaging into a 1-manifold complex is in progress. For `crossing`
   the existing local theorems normalise only a ball `W` around **one** double point, produced
   after `V`, so they cannot drive an induction; the needed relative theorem with a *prescribed*
   `W ⋐ V` is a **modification of the ~3000-line half-space chain**
   `SingularGeneralPosition.lean:2969 → :1607 → :3183` (expose `:1523`'s arbitrary-subset general
   position; generalise `boundaryComplex 2 K` to a subcomplex `L`; relative vertex perturbation
   on a `relDerived` subdivision). The induction invariant needs `V_j ⊆ ⋃ Wᵢ`
   (`DoublePointFibreAgreement.lean`); the step lemma is `NormalCrossingTransport.lean`.
2. **Descent step, boundary branch.** Assembly hypotheses 45 → 36
   (`CrossRegluedCellPredicate`, `BoundarySurgeryCellPredicate`; both pin an existentially
   produced cell with the producer's **full** conclusion — a corollary quantified over all cells
   with the *recorded* conclusions is a trap, `G = D` satisfies them). The resolved cell is now
   **constructed** from a PL reading (`CrossSeamResolvedCell.lean`), with a non-degenerate
   inhabitant (`CrossSeamReadingWitness.lean`: a touching seam goes in, no double point comes
   out). Remaining: (i) the PL boundary-relative **tube**, by the marked dual-cell induction
   (digests B and B2: tube relative to the chosen half `W`; two page labelings, not one `Bool`;
   end-point link = top of the model box plus its walls; boundary adaptation Theorem A because
   the crossing predicate's half-space is existential and not tied to `W`; all new geometry is
   2-dimensional — T₄, T₄-cap — then cone and glue); (ii) the **four-page source trace** of the
   cross reglue (Theorem D) feeding `PLCrossSeamReading`; (iii) the **boundary word witnesses**,
   blocked only because the three producers cut the source under independent choices — a
   shared-cut refactor is in progress (`BoundaryWordWitnessOfCell.lean` has the bricks).
3. **Descent step, closed branches.** Untouched this session. The planned "straighten the
   monodromy to `Prod.swap`" is **false** (`h(x,y) = (ψ y, ψ x)`, `h² ≠ id`): the target is a PL
   isotopy of pairs plus a mapping-torus equivalence, the ray permutation being pinned by the
   *annular* source neighbourhood (digest B, last section).
4. **35.2.** `Moise352SkeletonExtension n` is `Moise352 n` with two hypotheses inserted — the
   "reduction" is modus ponens (prompt A). `Moise341` is **not** misstated (p. 239); what §35
   needs is `ChartLocalApproximation.lean` (34.1 in one chart, proved from `Moise341`).
   `Moise308` **is** misaimed (book 30.8 is about a spine of the *inner* torus of a nested pair).
   §§34–35 are written up lemma by lemma in `consult/A-section34-lemma-list.md`; prompt A2 asks
   for the replacement DAG, answered in `consult/A2-answer-digest.md` (three transcription
   errors of ours corrected against the printed pages; the open-source reduction; preparation
   nodes P0–P8 separated from the seven extension stages; the correct 30.8). **The inward push
   is PROVED**: `moise352InwardPush_three : Moise352InwardPush.{u} 3`
   (`Moise352InwardPushProof.lean`, audited as the verbatim def, plugs into
   `moise352_of_inwardPush_of_skeletonExtension`). Method: COMPOSE stage pushes, never glue them
   (a stage fixes its own seam); compact local model chosen for `A ∪ C`; "moved once, fixed
   forever"; tolerance telescoped through `(h, ψ)`. `ToleranceControl.lean` has the
   tolerance-selection lemmas; `FourSpokeDisk.lean` and `DerivedCellSubcomplex.lean` are the
   first bricks of the marked tube.

### Eight, not seven

The list of false statements below has grown: (8) conjugating a closed-branch monodromy to
`Prod.swap`; and, caught *before* they were stated in Lean: the `∀ G` corollary; the
consultant's induction invariant without `V_j ⊆ ⋃ Wᵢ`; "general position lowers complexity"
(`y = |x|`, `y = −|x| + ε` become two crossings); "C⁰-small and locally injective keeps fibres
≤ 2" (a zig-zag path through the origin three times); target cells locally finite in all of
`M₂` (`h x = x / (1 + ‖x‖)`); the end-point chart equality `W = {t ≥ 0}`
(`H = {t = −min(|x|,|y|)}`); `∀ x, f x ∉ B` for a tapered push with vanishing height.

### Nine: the cross candidate's `hlong` is unsatisfiable (found at lane F acceptance, COMMITTED code)

`hlong : Function.Injective ⇑(τ.trans (σ.trans φ))` with `τ φ : Path b a`, `σ : Path a b` cannot
hold: the concatenation takes the value `b` at `0` and again at `3/4`, and `a` at `1/2` and `1`.
The preserving twin `Function.Injective ⇑(φ.symm.trans (σ.trans τ.symm))` starts with a loop
`φ.symm : Path a a`. So every theorem carrying `hlong` is vacuous: in committed code
`BoundaryWordWitness.exists_of_fourArcMatch_{reversing,preserving}`
(`BoundaryWordWitnessOfCell.lean:210, 230`), their `_of_endpoints` forms and
`exists_pair_of_fourArcMatch_{reversing,preserving}` (`BoundaryCandidatesOfCut.lean:146–254`);
uncommitted, all of `BoundaryCaseOfCut.lean`'s assemblies, the two assemblies of
`BoundaryCaseFromReading.lean`, and `BoundaryCaseFromCut.lean`. The module docstring claim that
`hσinj`, `hυinj`, `hlong` are "all produced by `exists_boundaryCandidates_of_cut`" is false: the
producer gives injectivity of the *source* arcs `σ₀ τ₀ υ₀ φ₀` of `frontier D.domain`, never of
the letters in `X`. This is refutation 5 again (the four arc word visits `a` twice).

It is not repairable by weakening `hlong` to injectivity of the three letters: the range of
`τ·σ·φ` is a theta graph, so a path with that range and those end points is not determined up to
homotopy (`τσφ` versus `φστ`), and in the preserving case two letters are loops, for which range
equality does not even fix the direction. Moreover the letters need not be injective at all:
another boundary branch with both its preimage arcs inside `D₁` makes `D ∘ σ₀` non-injective, so
`hσinj`, `hυinj` are satisfiable but cannot be discharged in the final wiring.

The repair (lane F, brick F7): match **in the source circle, arc by arc**. On each of its
boundary arcs the candidate is `D ∘ Fᵢ` with `Fᵢ` a homeomorphism onto one of the four source
arcs (F2's `V₁ V₂ V₃`, `F₁ = f₁∘h`, `F₂ = f₂∘h`, `F₃ = f₃`). `Fᵢ ∘ (injective source
parametrisation)` is an injective path of `frontier D.domain` with the range of `σ₀` (or `τ₀`,
`υ₀`, `φ₀`), hence homotopic to it or its reverse by `Path.Homotopic.of_injective_of_range_eq`
*there*, where injectivity is true; push the homotopy to `X` along the realisation
`f : frontier D.domain → X`, `ρ (f z) = D z`, and concatenate. No injectivity in `X` is used.

### Working method that held up

Read-only refute-or-scope lanes first; then **resume the same agent** to execute its own plan
(it keeps file:line knowledge) until its context is heavy, then hand a fresh worker the module
docstrings. Sequence lanes by reverse import closure; an edit to `CutAndPaste`/`CellGluing`
needs an exclusive window (their closure is ~20 modules plus this session's new files).
Every delivery: focused compile by the lane, then the external audit probe (13 linters, axioms,
aggregate clash) by a dedicated audit lane, then commit by explicit path. Five compiler leases
bound the number of compiling lanes; the mutex admits two Lean processes.

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

> **Correction, later on 2026-09-20 (Fable lead session). Item (i) above names the wrong
> cell.** The cell of `LemmaTwo.lean:145` is `ι ∘ S.singularMap`; it has no local injectivity
> and no fibre bound, so no general position argument can make it normal, and it belongs to
> the *return* leg. The entry cell of Lemma 2 is
> `DoubleCoverDiagram.exists_projected_singular_two_cell_in_double`
> (`LoopTheorem/ProjectedCellInDouble.lean:23`), the projection of the embedded disk upstairs,
> and it is **proved** with local injectivity, fibres of at most two points, the two boundary
> fields and the avoidance of `S.normalSubgroup`. Moise's first paragraph is **proved in the
> half space model**, preserving local injectivity and the fibre bound
> (`SingularGeneralPosition.lean:3447`; stability at `:274`, `:375`; chart form
> `SingularChart.lean:155`). What is open in (i) is only the globalisation across charts: a
> finite cover induction giving the `crossing` field, and the assembly of one global
> `NormalSingularSetTriangulation`. General position is load bearing, not cosmetic: the
> projected disk can have a *two dimensional* double point set (two disjoint sub-disks of the
> upstairs disk exchanged by the deck involution), which the fibre bound does not exclude.
> Item (ii) now exists, motive generic: `LoopTheorem/ComplexityInduction.lean`. For (iii) the
> right target is the PL level `EmbeddedDisk S` directly, not `NonsingularCell S`.
> The 35.2 chain: `Moise352SkeletonExtension n` is `Moise352 n` with two hypotheses inserted,
> so `moise352_of_inwardPush_of_skeletonExtension` is modus ponens and records no reduction;
> see prompt A of `CONSULT_FABLE_20260920.md`. Moise's Cases 3 and 4 construct no tube but
> silently push the touching sheets of the cross reglue apart; see prompt B there.

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
expire **2026-09-22T06:00:00Z**. Ask the human to extend them; a worker rewriting its own
compiler authorization is flagged as self-modification, correctly. When they lapse the
checker throws `Compiler authorization expired` and every lane stops mid-chain, so check the
remaining window before starting anything long.

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
