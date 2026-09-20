# Handoff to Codex — Moise Lemma 2 and Theorem 35.2, state at the end of 2026-09-20

Checkout `D:\differential-geometry-moise-int`, branch `codex/moise-integration`, HEAD
`12c0f04ce` plus this file. Everything below happened since commit `76c6478cc` (the start of the
Fable lead session); `git log 76c6478cc..HEAD` carries the reasoning in the commit messages.
Use your own workflow. This file only says **what changed, what is now true, and what is open**.
The longer brief is `HANDOFF_FABLE_20260920.md` — read its first section ("Update — end of the
second lead session"); the rest of that file is older and partly superseded by it.

## 1. What is now proved (all committed, each audited: 13 environment linters, axioms exactly `propext, Classical.choice, Quot.sound`)

**35.2 chain — one open obligation left.**
```
Moise352Open 3 → Moise352 3 → PLApproximationManifold 3        (Moise352OfOpen.lean)
```
* `moise352InwardPush_three : Moise352InwardPush.{u} 3` — PROVED (`Moise352InwardPushProof.lean`;
  bricks `TaperedInwardPush`, `TaperedInwardPushFixing`, `InwardPushStages`,
  `LocallyFiniteLocalModel`, `LocallyFiniteBoundaryExhaustion`, `StageInwardPushFrame`,
  `StageInwardPush`, `LocallyFiniteInwardPush`). Method: COMPOSE stage pushes, never glue them.
* `moise352_of_inwardPush_of_open` (`OpenSourceReduction.lean`), for every `n`. `Moise352Open` is
  `Moise352` for open subsets only and is implied by it. This **supersedes**
  `moise352_of_inwardPush_of_skeletonExtension`: `Moise352SkeletonExtension n` is `Moise352 n`
  with two hypotheses inserted, so that old "reduction" is modus ponens.
* Also: `ChartLocalApproximation.lean` (34.1 inside one PL chart, from `Moise341` — which is NOT
  misstated, it matches p. 239); `ToleranceControl.lean`; `LabelledNormalization.lean` (replaces
  §34's finite termination count for locally finite complexes).

**Lemma 2 chain — a machine-checked spine with two open obligations.**
```
GeneralPositionInDoubleBufferedStatement ∧ DescentStepStatement
   → LemmaTwoBufferedStatement → Moise252 → Moise304            (LoopTheorem/LemmaTwoBuffered.lean)
```
(unbuffered twin in `LoopTheorem/LemmaTwoSpine.lean`). Legs: entry cell =
`DoubleCoverDiagram.exists_projected_singular_two_cell_in_double`
(`LoopTheorem/ProjectedCellInDouble.lean:23`, packaged in `ProjectedCellNormalFields.lean`) —
**not** the cell of `LemmaTwo.lean:145`; induction = `LoopTheorem/ComplexityInduction.lean`
(generic in a motive); return leg = `LoopTheorem/EmbeddedDiskOfDoubleCell.lean`. The motive
carries the side of `BdM` in the double, the boundary buffer, and the loop clause. The buffer is
supplied by the cover producers at every call site; the wrapper feeding `LemmaTwoStatement` drops it.

**Boundary branch case.**
* Producers strengthened, append-only (`LoopTheorem/CellGluing`, `CutAndPaste`,
  `BoundaryWordFourArcs`): frontier equality `G '' frontier G.domain = D '' frontier D.domain`,
  injective source parametrisations, `hout`/`hin`; then split into **cores taking one cut**
  (`IsBoundaryBranchCut`) + wrappers with the OLD names and OLD statements verbatim.
* Existentially produced cells are pinned by predicates equal to the producer's FULL conclusion:
  `IsCrossRegluedCell` (`CrossRegluedCellPredicate.lean`), `IsBoundarySurgeryCell`
  (`BoundarySurgeryCellPredicate.lean`, with `not_isBoundarySurgeryCell_self`). **Trap:** a
  corollary `∀ G, recorded conclusions → …` is undischargeable — `G = D` satisfies them.
* `LoopTheorem/BoundaryCandidatesOfCut.lean`: from ONE cut, the four-arc word, both candidates,
  their predicates, arc matches, and boundary word witnesses for both.
* The resolved cell is CONSTRUCTED from a PL reading (`CrossSeamResolvedCell.lean`:
  `PLSeamTubeChart`, `PLCrossSeamReading`, `resolvedCell`), with a non-degenerate inhabitant
  (`CrossSeamReadingWitness.lean`: the model cell has a double point in the tube, the resolved
  cell has none there).
* `NormalCellProperness.lean`; `SingularSetOfCrossing.lean`, `SingularSetTriangulation.lean`
  (first steps of "`singularSet` follows from the other five fields");
  `NormalCrossingTransport.lean`, `DoublePointFibreAgreement.lean` (step lemmas of the
  finite-cover induction for general position).
* 2-D core of the marked tube: `FourSpokeDisk.lean` (planar T₄), `FourSpokeSector.lean`,
  `FourSpokeSquareWitness.lean`, `DerivedCellSubcomplex.lean`.

## 2. Uncommitted files in the working tree — handle these first

Verified by focused compile (`Verified … with no diagnostics`), **external audit NOT finished**
(the audit lane was stopped mid-probe; it had confirmed that all five fields are hypotheses of the
endpoint, in field order):
* `LoopTheorem/SingularSetChartGerm.lean`, `LoopTheorem/SingularSetLocalModel.lean`,
  `LoopTheorem/SingularSetOfCell.lean` — ends in
  `SingularTwoCell.nonempty_normalSingularCellData_of_fields`: the five Prop-shaped fields ⇒
  `Nonempty (NormalSingularCellData D BdM B)` for `M = K.space` with `combinatorialChartedSpace`.
  So **general position only has to produce `crossing`**.
* `LoopTheorem/BoundaryCaseOfCut.lean` — the two boundary-case assemblies with `Wdirect`, `Wraw`
  REMOVED (`…_of_boundaryCandidates`, 47 hypotheses) and a variant taking `PLCrossSeamReading` +
  `PLSeamTubeChart` (`…_of_plReading`, 43). The count rose from 36 because two witnesses were
  replaced by 13 cut-level exports that `exists_boundaryCandidates_of_cut` returns. When the cross
  cell's parametrisation is opposite to the word the witness uses `neg ∘ e` (a loop and its
  inverse are not freely homotopic); the cover clauses are transported along negation.
None of the four is registered in `DifferentialGeometry.lean`; the import lines are their module
names.

**Unverified drafts, killed mid-work — may not compile:** `FourSpokeAbstract.lean`,
`FourSpokeSectorFrontier.lean` (towards the full planar T₄-cap and its transport to abstract PL
2-balls). Finish or delete.

## 3. What is open, in the shape it now has

1. **`GeneralPositionInDoubleBufferedStatement`.** Only `crossing` is missing. The existing local
   theorems (`GeneralPositionWithin.lean:141`, `SingularManifoldLocal.lean:81, :245`,
   `LoopTheorem/ProjectedBoundaryLocalNormalization.lean:20`) normalise a ball `W` around ONE
   double point, produced after `V`; the shell `V \ W` cannot be made thin, so they cannot drive
   an induction. Needed: the relative theorem with a PRESCRIBED `W ⋐ V` — a **modification of
   the ~3000-line chain** `SingularGeneralPosition.lean:2969 → :1607 → :3183` (expose `:1523`'s
   arbitrary-subset general position; `boundaryComplex 2 K` → a subcomplex `L`; relative vertex
   perturbation on a `relDerived` subdivision). Induction invariant must include
   `V_j ⊆ ⋃ Wᵢ`. Brick list B1–B7: `consult/C-answer-digest.md`, last section (B1 is done).
2. **`DescentStepStatement`, boundary branch.** (i) the PL boundary-relative **tube**: marked
   dual-cell induction (`consult/B-answer-digest.md`, `consult/B2-answer-digest.md`): T₄ ✓ →
   T₄-cap (needs a cut-pair hypothesis on `frontier E` too — the cyclic order of the `wᵢ` on `∂E`
   is NOT implied) → abstract disks → marked cone extension (Theorem C, two-cap form) → end-point
   cone (Theorem E: link disk = top of the model box PLUS its walls) → chain → boundary adaptation
   (Theorem A: the crossing predicate's half-space is existential, not tied to the chosen half of
   the double) → tube producer. TWO page labelings must be carried (old-sheet and bent-sheet
   partitions), one `Bool` is not enough. (ii) the **four-page source trace** of the cross reglue
   (Theorem D) → an inhabitant of `PLCrossSeamReading` for the real cell; `crossRegluedPullback`
   is NOT continuous across a seam. (iii) wiring the case assemblies into `DescentStepStatement`
   (ambient loop-space bookkeeping).
3. **`DescentStepStatement`, closed branches.** Untouched. "Conjugate the monodromy to
   `Prod.swap`" is FALSE (`h(x,y) = (ψ y, ψ x)`, `h² ≠ id`); target = PL isotopy of pairs +
   mapping-torus equivalence, ray permutation pinned by the annular source neighbourhood.
4. **`Moise352Open 3`.** Replacement DAG in `consult/A2-answer-digest.md` (preparation nodes
   P0–P8 separated from seven extension stages + inserted stage 2b; uniform extension lemma;
   marked-circle sector lemma; Operation 2 via a supported ambient slide; Operation 1 needs a
   cleanliness clause; link facts (Link-E)/(Link-V); relative target local finiteness; chart-local
   exterior invariant). §§34–35 lemma by lemma: `consult/A-section34-lemma-list.md` (three
   transcriptions were wrong and are corrected — re-check any paraphrased clause against the
   page). `Moise351` (35.1) is still open and is consumed inside. The tree's `Moise308` is NOT
   book 30.8; correct statement `Moise308Nested` in the A2 digest (proof: cyclic-group
   factorisation; 30.6/30.7 not needed).
5. **Hole:** nothing in the tree inhabits `NormalSingularCellData` yet; it is reachable only
   through item 1.

## 4. Statements found false this session (do not re-derive)

Conjugating a cross monodromy to `Prod.swap`; the `∀ G` corollary; the consultant's induction
invariant without `V_j ⊆ ⋃ Wᵢ`; "general position lowers complexity" (`y=|x|`, `y=−|x|+ε`);
"C⁰-small + locally injective keeps fibres ≤ 2" (zig-zag through the origin three times);
target cells locally finite in all of `M₂` (`h x = x/(1+‖x‖)`); the end-point chart equality
`W = {t ≥ 0}` (`H = {t = −min(|x|,|y|)}`); `∀ x, f x ∉ B` for a tapered push with vanishing
height; "`q` PL on an open set containing `p '' K`" for a stage push; "`∂E ∩ Σᵢ` is one arc".

## 5. Two facts about the environment

* External consultants read `https://github.com/liao9yuan/differential-geometry-dev`, branch
  `moise-integration` — which is NOT this checkout's `origin` (that is `qinz1yang/…`, now 17+
  commits behind local). Sync the owner's repository with
  `bash %TEMP%/claude-moise-integration-private/sync-mirror.sh` (no force; read its header).
* `open Classical in` on `boundaryComplex` lemmas bakes in the classical `DecidableEq`; at a
  concrete `EuclideanSpace` Lean finds `WithLp.instDecidableEq` and burns heartbeats in `whnf` —
  bridge with `Subsingleton.elim`.
