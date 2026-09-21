# E3 — terminal assembly of 35.2: findings and design (lead + read-only scoping, 2026-09-20 night)

Lane E3 is now run by the lead's Opus workers. This note supersedes R1–R3 of
`HANDOFF_CODEX_E3_20260920.md`; R4 (acceptance of E3.1–E3.5) is recorded at the end.

## Why the Codex session kept hitting bugs: the structure it had to inhabit is contradictory

`Section34FinalDiagram` (`Section34FinalDiagram.lean`) is uninhabited for every nonempty index
type, by three independent routes, so `hdiagram` is false and `moise352Open_of_final_diagrams`
is vacuous:

1. **Ambient frontier.** `sourceBoundary`/`targetBoundary` use `frontier (P l)` in ℝ³ for a PL ball
   of dimension `dim l ≤ 3`. For `dim l < 3` the ambient frontier is the whole ball
   (`IsPLBall.interior_eq_empty_of_lt_finrank`, `BallFrontier.lean:77`); at the minimal dimension
   present the union of proper faces is empty. Dimension 0: a point equals an empty union.
2. **Strict diagonal.** `sourceIntersection` with `m = l` reads `sourceCell l = ⋃ commonFace l l`,
   and `commonFaceDim` forces those to have strictly smaller dimension. The digest's
   `⋃_{ν ≤ λ, ν ≤ μ}` is a *reflexive* ideal; the Lean rendering made it strict.
3. **Clopen `U`.** `LocallyFinite sourceCell` is stated in `M₁`, so the union of the compact cells
   is closed, and `sourceUnion` equates it with the open `U`. Local finiteness must be in the
   subspace (as `carrierLocalFinite` two fields away already does).

`Section34CarrierControl` triangulates `U` by one complex in ℝ³, which forces `U` to embed in ℝ³;
the tree's only producer for an arbitrary open `U` is `exists_locallyFinitePieceTower_of_isOpen`
(compact pieces with their own ambient dimensions), and this repository has not formalised
a compatible locally finite triangulation of an open PL 3-manifold (the theorem is true; a
realisation of the whole triangulation in one chart need not exist).
**Carriers must be indexed by the cell labels.**
The same ambient-frontier defect makes `UniformBallExtension.lean:17` degenerate at `d = 1, 2`
and `SourceCutDiagramCertificate.lean:100` (`patchFrontier`) uninhabited.

## The intrinsic boundary in this tree

`IsPLBall d P` (`Polyhedron.lean:41`) *is* a parametrisation `r` of `stdSimplex ℝ (Fin (d+1))`;
the intrinsic boundary is `r '' stdSimplexBoundary d` (`stdSimplexBoundary 0 = ∅`): a PL sphere in
any ambient (`BallReplacement.lean:12`), chart independent (`BallMarkedExtension.lean:49`), equal
to `frontier P` only in codimension 0 (`BallFrontier.lean:27, 38`). Per-cell extension primitive at
every dimension: `exists_isPLHomeomorphOn_extension_of_stdSimplexBoundary` (`BallReplacement.lean:23`).

## Design

* **No bundling structures** (AGENTS.md:72). Explicit binders. Data: `dim ≤ 3`, `P Q`, charts,
  parametrisations `sourceParam l`, `targetParam l` (these replace `sourceBall`/`targetBall`),
  `face : Λ → Set Λ` a reflexive ideal, carriers `H : Λ → Set M₂`. Propositions: intrinsic
  boundary = union over `face l \ {l}`; `cell l ∩ cell m = ⋃ n ∈ face l ∩ face m, cell n`;
  local finiteness in the subspaces `U` and `⋃ targetCell`; `⋃ sourceCell = U`;
  `⋃ targetCell ⊆ h '' U`; `h '' sourceCell l ∪ targetCell l ⊆ H l`;
  `∀ x ∈ sourceCell l, ∀ y z ∈ H l, dist y z < η x`. `LocallyFinite H` is a producer-side fact,
  not a hypothesis of the endpoint.
* **Assembly theorem.** Conclusion `∃ f, IsPLHomeomorphInto 3 f (⋃ sourceCell) ∧ ∀ l, f ''
  sourceCell l = targetCell l`. The per-cell image equality **must be in the statement**: injectivity
  does not follow from exact intersections alone, it follows from them plus that invariant.
  Derived, not assumed: `P_λ ∩ A_{d−1} = ∂P_λ`; each cell has finitely many faces.
* **Pasting lemma to isolate:** locally finite closed PL pasting *with inverse*, in a manifold
  (`IsPLWithinAt` of a finite closed union at manifold level does not exist yet; Euclidean core
  `PLPiece.lean:11, 48`). No properness into `M₂`, no openness of the image.
* **Shalen 6.2** is not a replacement for the labelled-cell assembly, only for its top
  dimension: it fills 3-dimensional chambers *given* the map on their boundary. Use a 6.2-style
  chamber filling, stated chart-locally with carriers instead of `ρ_M`, as the proof of the
  dimension-3 row inside the assembly. **Shalen §9.2/9.3:** change nothing —
  `Moise352Open 3 → Moise352 3` already plays that role; 9.3 would be another *producer* of
  `Moise352Open 3` costing all of §7.
* **Files, in order:** `UniformBallExtensionIntrinsic` (E3.4 restated with parametrised
  boundaries), `LocallyFinitePLPastingEuclidean`, `LocallyFinitePLPastingManifold`,
  `LabelledCellAssembly`, `LabelledCellAssemblyWitness`, corrected `Section34FinalDiagram`.
  Delete (lane-owned, uncommitted): `Section34SourceData` … P0–P8 props, `Section34Contracts`
  apart from `Section34Input`, `Section34Assembly.lean`, `Section34Primitives.lean` (four
  one-line aliases), `SourceCutDiagramCertificate.lean`.
* **Witness now:** the assembly theorem on one tetrahedron with its full face poset (1 + 4 + 6 + 4
  cells, `f = id`); it is impossible under defects 1 and 2. The full §34 inhabitant (a locally
  finite triangulation of ℝ³, `h = id`, `η x = 1 + ‖x‖`) is deferred; say so wherever the endpoint
  is reported.

## Acceptance of E3.1–E3.5 (read-only statement review)

Commit: `LinkGraphConnectivity` (as is); `Moise308Nested` + `Moise308NestedShell` after deleting
dead declarations (statement verbatim, producer unconditional, shell retraction and `π₁ ≅ ℤ`
genuinely proved); `MarkedCircleSector` after deleting one alias (the sector lemma does carry the
consecutive-sector data and rejects the 1,3,2,4 labelling; it identifies sectors with labels, so
the "path" case needs padding). Fix: `UniformBallExtension`. Delete:
`SourceCutDiagramCertificate` (24 proposition fields, uninhabited: `tetrahedronInter` at `t = u`,
`patchFrontier`). Rework: `SourceCutDiagram` (three ambient-frontier traces).
