# Lane E3 restart — §34 side of Moise 35.2 (`Moise352Open 3`) — 2026-09-20 night

You are restarting lane E3 in a fresh session. Work in `D:\differential-geometry-moise-int`,
branch `codex/moise-integration`. The working tree is **shared** with other active lanes; their
uncommitted files are present. `AGENTS.md` of this checkout outranks everything below.

## Read first (in this order)

1. `AGENTS.md` — "Source discipline", "Soundness", "Linters".
2. `DifferentialGeometry/Topology/PiecewiseLinear/LANES_CODEX_20260920.md`: §0 rules, §1 report
   template, the section "车道 E3", the ruling "车道 E3 裁决", and "Prompt D 的答复已回" (the E3
   bullets and the shared discipline (a)–(e)).
3. `…/consult/D-answer-digest.md` Part 2 (the replacement assembly) and
   `…/consult/A2-answer-digest.md` (the DAG P0–P8, the seven stages, the uniform extension lemma,
   the marked-circle sector lemma).
4. Your own files in the working tree (uncommitted): `Moise308Nested.lean`,
   `Moise308NestedShell.lean`, `LinkGraphConnectivity.lean`, `MarkedCircleSector.lean`,
   `UniformBallExtension.lean`, `SourceCutDiagram.lean`, `SourceCutDiagramCertificate.lean`,
   `Section34Contracts.lean`, `Section34Primitives.lean`, `Section34Assembly.lean`,
   `Section34FinalDiagram.lean`; and the records `.lake/scratch/E3.1…E3.6-prime-acceptance.md`.

## Where the lane stands

* E3.1–E3.5 are written and self-checked; **none has been accepted or committed** — the lead has
  not yet read their statements. E3.6 (first form) was rejected: `Section34StageContract` was
  uninhabited and the stage-indexed carriers contradicted local finiteness for every tolerance.
* E3.6′ exists: `Section34CarrierControl` (simplex-indexed supports, C0a–C0c),
  `Section34FinalDiagram` (map-free labelled cell data, exact intersections, (C1)),
  `section34_error_of_cell_assembly` (the estimate from C0c + C1), and the conditional endpoint
  `moise352Open_of_final_diagrams`, whose hypothesis `hassembly` **is the terminal labelled
  PL-cell pasting theorem, still unproved**. The old `Section34SourceData` / P0–P8 scaffolding in
  `Section34Contracts.lean` is dead and misleading.

## What to do, in order

**R1. Prove `hassembly` — the locally finite labelled PL-cell assembly theorem.** Two families
`(P_λ)`, `(P'_λ)` over the same graded face poset, dimensions ≤ 3, each a compact PL ball,
boundary = union of proper faces, `P_λ ∩ P_μ = ⋃_{ν ≤ λ, ν ≤ μ} P_ν` on both sides, locally
finite in their unions (the target family inside carriers contained in `h(U)`) ⇒ a PL
homeomorphism of the unions carrying each `P_λ` onto `P'_λ`. Induct over dimension 0, 1, 2, 3;
at each dimension extend over the whole locally finite family of balls **once**
(`UniformBallExtension.lean`; stage 2 needs `MarkedCircleSector.lean`); exact intersections give
compatibility and injectivity; **locally finite closed PL pasting gives the map and its inverse**
— isolate that pasting lemma (map and inverse) as its own statement; no properness into `M₂` is
needed; openness of the image is invariance of domain. Then remove `hassembly` from
`moise352Open_of_final_diagrams`, so the endpoint reads
`(∀ D η, Nonempty (Section34FinalDiagram …)) → Moise352Open 3` with no other hypothesis.
If a clause of `Section34FinalDiagram` turns out too weak or too strong for this proof, **change
the structure, not the theorem's meaning**, and say exactly what changed and why.

**R2. Delete the dead scaffolding** (`Section34SourceData`, the old P0–P8 props, anything the
endpoint does not use). A reader must not be able to mistake it for the corrected interface.

**R3. A non-degenerate inhabitant of `Section34FinalDiagram`.** Take `h = id` on a sufficiently
fine standard PL triangulation of an open subset of `ℝ³` with a non-constant `η`; source and
target diagrams coincide. It must have infinitely many or at least several cells of every
dimension 0–3 and must exercise (C0c) and (C1) with `η` genuinely small. `∅`, `⊥`, one simplex
or `n = 0` do not count. State also what this inhabitant does **not** test (P4 moves).

**R4. Hand in E3.1–E3.5 for acceptance**, one §1 report per brick, with for every hypothesis of
every endpoint theorem the proved producer that supplies it, or "free input".

**R5. Only then** restate P0–P8 as producers whose **outputs are pieces and incidences of one
shared diagram** (table in `consult/D-answer-digest.md`), P0 not freezing the source neighbourhood
`N` (P1 chooses `N` and `f₁` jointly). Do not start proving P1–P8 geometry in this session.

## Traps this lane has already fallen into (each passed compile, 13 linters and the axiom audit)

* A tolerance sequence fixed before a family of maps that must also agree with its predecessors:
  pins every stage map to `h`. Test: hold the current bound, send the next to zero.
* A smallness condition indexed by an **increasing** family: contradicts point-finiteness. Test:
  one point, all later indices.
* A set parameter quantified universally where only "sides" make sense: take it to be the image
  itself, the empty set, the whole space.
* One-line aliases, lemmas ignoring their hypotheses, theorems returning one of their own
  hypotheses, proposition-bundling structures, probes on degenerate data. All are bounced.
* "Produced by X" in a docstring is a claim to be checked against X's actual conclusion.

## Rules of the road

No git write commands; do not touch `DifferentialGeometry.lean`; create/modify only your own
files (prefixes `Moise308Nested*`, `LinkGraph*`, `MarkedCircle*`, `UniformBallExtension*`,
`SourceCutDiagram*`, `Section34*`, and a new `LocallyFinitePLPasting*` / `LabelledCellAssembly*`
if you need them). Grep the tree for a statement's **shape** before proving it — locally finite
pasting and ball extension lemmas already exist under several names
(`exists_isPLHomeomorphOn_iUnion`, `exists_isPLHomeomorphOn_union`,
`exists_isPLHomeomorphOn_of_frontier`, `LocallyFiniteBoundaryExhaustion`, `Pasting.lean`). No
declaration docstrings, no inline comments; copyright header, imports, one module docstring. Zero
warnings, achieved by deleting unused hypotheses from statements. Save real logs under
`.lake/scratch` (`Check…`, `Audit…` with `#print axioms` output, `Lint…` with the 13-linter
output — not copies of each other). Do not edit the compiler lease files; use the lease the owner
gives you. If a target looks false, stop and give the counterexample: that is a success.

## Report (≤ 40 lines)

Verdict per item R1–R5; manifest and import lines; the exact statement of the pasting lemma and
of the assembly theorem; for each hypothesis its producer or "free"; the inhabitant of R3 and why
it is not degenerate; anything the lead must decide.
