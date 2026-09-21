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
4. Last verified against source: **2026-09-21, commit of `consult/H-section34-celldiagram-review-digest.md`**.

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
| **A1** | `GeneralPositionInDoubleBufferedStatement` (`LoopTheorem/LemmaTwoBuffered.lean:167`) | **OPEN**; leaves = the `sorry`s of `Skeleton/GeneralPositionInDouble.lean` (external review pending) |
| A1.1 | adapted half-space charts of the double, arbitrarily small: `x ∈ C ↔ 0 ≤ ℓ (e x)`, `x ∈ Bd ↔ ℓ (e x) = 0` (leaf `exists_adaptedHalfSpaceChart_in_double`) | open (lane H); **unreviewed** |
| A1.2 | finite adapted cover of the double point set with the whole-union invariant `V j ⊆ ⋃ i, W i` (leaf `exists_finiteAdaptedCover_of_doublePointSet`) | open (lane H); **unreviewed** |
| A1.3 | cut-out piece of a source disk **with boundary**: all sheets through the region, frozen outer collar (leaf `SingularTwoCell.exists_cutOutPiece_of_closure_subset`) | open (lane H); **unreviewed** |
| A1.4 | relative guarded half-space general position in an adapted chart, frozen collar, guard `(s ∩ B).card ≤ finrank (ker ℓ) + 1` (leaf `exists_small_vertexMap_relative_in_adaptedChart`) | open (lane H); **unreviewed**; the worker flags the frozen-part exemption and `Rc.vertices ⊆ Rs.vertices` as the likely defects |
| A1.5 | one normalization step on a prescribed region: same domain, maps to `C`, fibres unchanged off `V`, crossings on `O' ⊇ Z ∪ closure W`, buffered boundary homotopy (leaf `exists_normalizationStep_on_prescribedRegion`) | open (lane H); **unreviewed** |
| A1.6 | chart-by-chart induction, extraction of `crossing`, boundary loop (from the committed `exists_boundary_loop_of_buffered_homotopy`), assembly | **PROVED modulo A1.1–A1.5**: `Skeleton/GeneralPositionInDouble.lean` compiles with exactly 5 `sorry` leaves and none in the assembly (checked 2026-09-21) |
| **A2** | `DescentStepOrientableStatement` (`LoopTheorem/LemmaTwoOrientable.lean:61`) | **OPEN**; leaves = the `sorry`s of `Skeleton/DescentStepOrientable.lean` (reviewed: `consult/G-descent-skeleton-review-digest.md`) |
| A2.1 | closed branch, two circles, nested | **PROVED** `exists_descendingSurgery_of_nested_innermost_cleanDisk` (`LoopTheorem/ClosedBranchNestedDescent.lean:245`) |
| A2.2a | closed branch, two circles, disjoint — geometric cap producer: for every open `V` with `D(Q) ⊆ V ⊆ interior (C \ BdM)`, a larger source disk `E'` and a PL embedded cap `Δ' ⊆ V` (leaf `exists_adaptedCleanCap_of_disjoint_innermost_cleanDisk`) | open, not started; statement **new** (from review G, not yet re-reviewed) |
| A2.2b | the same — surgery consumer: cut-and-paste along the cap, branch retention, the three invariants (leaf `exists_descendingSurgery_of_adaptedCleanCap`); the disjoint analogue of `IsNestedDiskReplacementCell` does not exist yet | open, not started; statement **new** |
| A2.3 | closed branch, one circle: impossible in an orientable manifold (leaf `not_branchPreimage_eq_of_isOrientable`; own skeleton `Skeleton/ClosedBranchCaseOne.lean`, 4 leaves, review pending) | open, in progress; statement **frozen** |
| A2.4a | boundary branch: PL tube with side containment, boundary equality, end-disk buffer (leaf `isPLBoundaryTubeProducer_double`; `IsPLBoundarySide` now carries `IsClosed BdM`, `BoundaryAdaptation.lean:56`) | open (lane S); statement **frozen** |
| A2.4a′ | realisation of the boundary neighbourhood in the double (leaf `NormalSystem.exists_boundaryNeighborhood_realization`) | open (lane S); **frozen** |
| A2.4a″ | the quarter-turned tube chart is again a PL seam tube chart (leaf `nonempty_plSeamTubeChart_comp_crossQuarterTurn`) | open (lane S); statement **new**, small |
| A2.4b | boundary branch: both boundary word witnesses from **one** cut (leaf `exists_boundaryWordWitnesses_of_cut`) | open (F9); **frozen** |
| A2.4b′ | the PL reading, for the tube chart **or** its quarter turn, given the tube's boundary equality (leaf `exists_plCrossSeamReading_of_isCrossRegluedCell`) | open (lanes F/S); **frozen** after repair |
| A2.4c | boundary branch: assemblies conclude side + buffer (leaves `exists_descendingSurgery_side_buffer_of_crossSeamTube_reversing`, `…_preserving`) | open (F10); **frozen** |
| A2.4d | joint non-degenerate fixture: branch + both candidates + tube + reading + both witnesses on one tuple | open (F11); until it exists A2.4 is UNTESTED |
| A2.5 | wiring into the statement | **PROVED modulo the leaves above**: `descentStepOrientableStatement` in `Skeleton/DescentStepOrientable.lean` compiles with exactly 10 `sorry` leaves and none in the assembly (checked 2026-09-21) |

### B — §34–35 side
| ID | Item | Status |
|---|---|---|
| **B1** | `Moise352Open 3` (`OpenSourceReduction.lean:297`) | **OPEN**; reduced (proved, `moise352Open_of_section34CellDiagram`, `Section34Endpoint.lean`) to the single obligation **`Section34CellDiagram`** = B1.b |
| B1.a | terminal labelled PL-cell assembly + corrected endpoint | **PROVED** `exists_isPLHomeomorphInto_of_labelledCells` (`LabelledCellAssembly.lean`), manifold-level locally finite PL pasting with inverse (`LocallyFinitePLPastingManifold.lean`). Non-vacuity witness so far only in dimension 0; the tetrahedron witness is owed — until it exists the ball-extension rows are UNTESTED |
| B1.b | `Section34CellDiagram` (the final-diagram producer = P0–P8): controlled frame, joint graph selection, generator transfer, face balls, protected compression, bigon slide, normalization, exterior face disks, tetrahedron and vertex recognition | open, not started; statement externally reviewed **OK** (`consult/H-section34-celldiagram-review-digest.md`); proved ingredients: `moise308Nested`, link connectivity, marked-circle sectors, locally finite PL gluing, labelled normalization, tolerance control, chart-local 34.1 **from** `Moise341` |
| B1.b.1 | controlled source triangulation: a compatible locally finite triangulation of an arbitrary open subset of an atlas-defined PL 3-manifold, subordinate to P0's control supports (true classically; **not formalised here**) | open, not started |
| B1.b.2 | target recognition: PL-ball presentations, intrinsic boundaries and exact intersections of `V_v, E_e, Δ_σ, X''_{tv}, R_t, a'', I'', p''` (P1, P6–P8, marked-sector condition) | open, not started |
| B1.b.3 | target local finiteness `hLFt` from `T_λ ⊆ H_λ ⊆ h(U)` with `(H_λ)` locally finite in `h(U)`, without the assembled homeomorphism | open, not started (reviewer's "most likely surprise") |
| B1.b.4 | parent-carrier exporter: top-cell carriers inherited by lower cells along a chosen incident top label | open, small |
| B1.b.5 | P0 fixes control data only; the neighbourhood `N`, the cut diagram and `f₁` are chosen jointly in P1 | design constraint on B1.b, not a theorem |
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
**A: 5 + 10 = 15** (A2.1 closed; A2's open leaves are now exactly the 10 `sorry`s of `Skeleton/DescentStepOrientable.lean` — a finer cut after review G, not new work), **B: 4 + 4 = 8** (B1.a closed; B1.b split into B1.b.1–4 on 2026-09-21, a refinement, not new work), **C: 1**. Leaves closed since this page was created: 1 (B1.a).
