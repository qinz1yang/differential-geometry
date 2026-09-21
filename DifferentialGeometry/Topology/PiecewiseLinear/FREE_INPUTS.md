# FREE INPUTS — the single progress ledger for the Moise route

**This page is the only yardstick of progress.** Progress is *not* the number of files, lines,
proved lemmas or conditional assemblies. Progress is this list getting shorter.

**Goal.** A closed simply connected topological 3-manifold is homeomorphic to `S³`, from the
smooth Poincaré theorem (main repository) through triangulation and smoothing. Only the
orientable case is needed (simply connected ⇒ orientable); only existence of structures is needed.

## Rules

1. An item is **OPEN** unless the tree contains a theorem whose conclusion is that item and whose
   hypotheses are only instance binders. "Proved conditionally" is OPEN, with its conditions
   listed underneath as further items.
2. A `def … : Prop` naming an obligation is OPEN until such a theorem exists. A structure or
   predicate with no inhabitant theorem on a non-degenerate object is **UNTESTED**, and nothing
   may be built on it.
3. Whoever commits a change to the hypothesis list of any endpoint named here updates this page
   **in the same commit**. An audit that disagrees with this page must point to the declaration
   (file:line) that proves the item, or the page stands.
4. Last verified against source: **2026-09-20 night, commit of `BoundaryAdaptation.lean`**.

## How to audit (no compiler needed)

```
# theorems whose conclusion is a named obligation (must print a line for an item to be CLOSED)
grep -rnE "^theorem [A-Za-z0-9_']+ *: *(Moise352Open|GeneralPositionInDoubleBufferedStatement|DescentStepOrientableStatement|PLSmoothingModel|Moise351|Moise341|Moise331)(\.\{u\})?( [0-9]+)? *:=" DifferentialGeometry
# a line `theorem foo : Item → …` CONSUMES the item and is excluded by the pattern; the pattern
# does catch proved items (try it with Moise308Nested in place of the list)
# hypotheses of the endpoints
grep -n -A4 "^theorem moise304_of_generalPositionBuffered_of_descentStepOrientable" DifferentialGeometry/Topology/PiecewiseLinear/LoopTheorem/CoverReductionOrientableProducer.lean
grep -n -A3 "^theorem plApproximationManifold_three_of_open" DifferentialGeometry/Topology/PiecewiseLinear/Moise352OfOpen.lean
grep -n -A8 "^theorem exists_isManifold_three_of_plApproximation_of_plSmoothing" DifferentialGeometry/Topology/PiecewiseLinear/Smoothing.lean
```

## The tree of inputs

### Level 0 — the top endpoint in this checkout
`exists_isManifold_three_of_plApproximation_of_plSmoothing` (`Smoothing.lean:63`): a compact
Hausdorff topological 3-manifold has a smooth structure, **from** `PLApproximation 3` **and**
`PLSmoothing 3`.

| Input | Reduced to (proved) | Status |
|---|---|---|
| `PLApproximation 3` | `PLApproximationManifold 3` (`ApproximationManifold.lean:76`) ⇐ `Moise352 3` (`Endgame.lean:9`) ⇐ **`Moise352Open 3`** (`Moise352OfOpen.lean:40,45`, inward push proved) | OPEN → **B** |
| `PLSmoothing 3` | **`PLSmoothingModel 3`** (`Smoothing.lean:27`) | OPEN → **C** |
| smooth Poincaré | main repository, not this checkout | external → **D** |

### A — loop-theorem side (orientable): delivers 30.4 and tame 30.5, which §34 consumes
Endpoint: `moise304_of_generalPositionBuffered_of_descentStepOrientable`
(`LoopTheorem/CoverReductionOrientableProducer.lean:278`), and `moise305_tame_of_moise304`.
**Two hypotheses, both OPEN.** Everything else on this side is proved: entry, complexity
induction, return leg, Stallings tower with orientability in the motive, covers of orientable
complexes orientable, `Moise252 → Moise304 → Moise305Tame`.

| ID | Item | Status |
|---|---|---|
| **A1** | `GeneralPositionInDoubleBufferedStatement` (`LoopTheorem/LemmaTwoBuffered.lean:167`) | **OPEN** |
| A1.a | cut-out piece for a source disk **with boundary** satisfying "all sheets through the region" | open, not started (delivered version is uninstantiable) |
| A1.b | relative half-space general position freezing an **interior collar** (guard `(s ∩ B).card ≤ finrank (ker ℓ) + 1`), producing normal crossings on `closure W` | open, not started (delivered version vacuous) |
| A1.c | induction over a finite cover with the **whole** union `U = ⋃ W j` | lemma exists uncommitted (`doublePointSet_subset_iUnion_of_buffered_steps`), crossing induction to be rebuilt on it |
| A1.d | global assembly: one cell `A`, same domain, maps-to, boundary neighbourhood, boundary loop avoidance (homotopy `H`, `hmap`, `hsurj` are free inputs today) | open |
| **A2** | `DescentStepOrientableStatement` (`LoopTheorem/LemmaTwoOrientable.lean:61`) | **OPEN** |
| A2.1 | closed branch, two circles, nested | **PROVED** `exists_descendingSurgery_of_nested_innermost_cleanDisk` (`LoopTheorem/ClosedBranchNestedDescent.lean:245`) |
| A2.2 | closed branch, two circles, disjoint: adapted clean-cap neighbourhood | open, not started |
| A2.3 | closed branch, one circle: impossible in an orientable manifold | open, in progress (`consult/C-or1-design.md`, 11 items) |
| A2.4a | boundary branch: PL tube with side containment, boundary equality, end-disk buffer — the obligation is now stated: `IsPLBoundaryTubeProducer` (`BoundaryAdaptation.lean:38`), with `isPLBoundarySide_double` proving that the double's side satisfies its hypothesis | open (lane S; planar four-spoke layer proved; marked cone, chain, boundary adaptation to come) |
| A2.4b | boundary branch: both boundary word witnesses from **one** cut, parametrisation exposed | open (F9; source-segment exports proved, source-match theorems under revision) |
| A2.4c | boundary branch: assemblies conclude side + buffer as the statement asks | open (F10) |
| A2.4d | joint non-degenerate fixture: branch + both candidates + tube + reading + both witnesses on one tuple | open (F11); until it exists A2.4 is UNTESTED |
| A2.5 | wiring A2.1–A2.4 into the statement (selection dichotomy is proved) | open |

### B — §34–35 side
| ID | Item | Status |
|---|---|---|
| **B1** | `Moise352Open 3` (`OpenSourceReduction.lean:297`) | **OPEN**; no proved reduction below it yet |
| B1.a | terminal labelled PL-cell assembly + corrected endpoint (`E3_ASSEMBLY_DESIGN_20260920.md`) | open, in progress; will replace B1 by B1.b |
| B1.b | the final-diagram producer = P0–P8: controlled frame, joint graph selection, generator transfer, face balls, protected compression, bigon slide, normalization, exterior face disks, tetrahedron and vertex recognition | open, not started; proved ingredients: `moise308Nested`, link connectivity, marked-circle sectors, locally finite PL gluing, labelled normalization, tolerance control, chart-local 34.1 **from** `Moise341` |
| B1.c | `Moise351` (35.1, needed in *controlled* form by P1) | OPEN, no owner |
| B1.d | `Moise341`, `Moise331` and what they rest on: §31, §32 (pseudo-cells), §33.1, surface classification 22.8–22.10 | OPEN, not started |
| B1.e | how A's output (tame 30.5, the loop theorem) enters P3/P4 | **not yet stated in Lean** — the two sides meet only in the book so far |

### C — smoothing
| **C1** | `PLSmoothingModel 3` (`Smoothing.lean:20`) | **OPEN**, not scoped |

### D — external
| **D1** | smooth Poincaré theorem and its use on the smooth manifold produced above | main repository |

## Deliberately NOT on the goal path (may stay open forever)
Unrestricted `Moise251`, `Moise264`; the non-orientable loop theorem and the one-circle closed case
in a non-orientable manifold; `Moise305` (non-tame), `Moise306`, `Moise307`,
`TopologicalCellComplementConnected`; the Hauptvermutung; boundary-relative approximation.

## Count (the number an audit should quote)
Top-level OPEN items: **A1, A2, B1, C1** (+ D1 external). Expanded leaves currently open:
**A: 4 + 7 = 11** (A2.1 closed), **B: 5**, **C: 1**. Leaves closed since this page was created: 0.
