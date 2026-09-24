# Item 14: marked rim core buffer handoff

You are taking over Codex item 14 in `D:\differential-geometry-moise-int`, branch
`codex/moise-integration`. The owner paused the previous worker and explicitly requested this
partial commit/push and an English takeover prompt. Resume proof work only in the takeover lane.
The earlier STOP at L2 was premature: it records an unproved new-theory step, not a counterexample
and not a demonstrated insufficiency of the frozen leaf hypotheses. Do not stop merely because
an existing API does not directly supply L2 or L4; those are explicitly assigned NEW_THEORY.

## Objective and required reading

Finish the zero-marked rim core buffer, then transport it through `h`, shrink inside the same
marked product, and perform the single `Moise331OnTube` assembly closing
`exists_compactCutAndGraph` in `Skeleton/Section34Compact.lean` (original line 275).
All paths below are under `DifferentialGeometry/Topology/PiecewiseLinear/` unless stated otherwise.

Read `Skeleton/FILL_QUEUE.md`, Codex item 14; then the entire
`consult/BU-marked-rim-core-buffer-answer.md` (commit `397201787`). Also retain the earlier
`consult/BT-compact-cut-graph-clauses-nine-eleven-answer.md`, `Skeleton/OPUS_FILL_LOG_B.md`
Batch 8, and the actual frame definitions in `Section34CompactVocabulary.lean`.
The current delivery and exact L2 frontier are appended under `# Codex item 14` in
`Skeleton/FILL_LOG.md`, headed `BU batch delivery: A0/L0/L1 complete; STOP at L2`.

## Checked results available now

The earlier 51-module cut-frame package, four-module exterior-buffer package (graph clause 11),
and `Section34CompactFaceTorusCycle.lean` are already accepted. In particular:
- `Section34CompactDualCutFrame.lean`: the complete actual cut frame, with `K' = K`.
- `Section34CompactExteriorNeighborhoods.lean`: the actual clause-11 neighborhood producer.
- `Section34CompactDualTetraBuffer.lean`: tetrahedron exterior buffers.
- `Section34CompactFaceTorusCycle.lean`: the exact three-cell cyclic union and unmarked torus
  recognition. It does not identify the rim with the product zero section.

This partial checkpoint adds these six real, privately checked modules:
- `Section34CompactTriangleDisk.lean`: A0, `exists_triangle_subcomplex_with_rim`.
- `GraphDualCellSurfaceTrace.lean`: disk recognition and both directions of the boundary cover.
- `GraphDualCellCurveTrace.lean`: exact curve trace, cap centroids as its endpoints, and exclusion
  of other ambient-frontier contacts on that curve.
- `BridgeDisk.lean`: `IsBridgeDisk`, equivalent to BU's proposed `BUBridge`, plus the boundary-cover
  constructor and endpoint-preserving interval parametrization.
- `GraphDualCellBridgeDisk.lean`: L1, `isBridgeDisk_graphDualCell`, with the full proposed general
  face-disk hypotheses. No extra geometric input was added.
- `BridgeDiskArc.lean`: the marked arc parametrization, `A ∩ frontier C = {a,b}`, and
  `A \ {a,b} ⊆ interior C`. These are L2 prerequisites, not L2 itself.

L0 is already supplied by `derivedNeighborhood_space_subset_interior` in
`DerivedNeighborhoodRayEmbedding.lean`; its exact E3 specialization was checked externally.

The six-module delivery audit checks the literal expanded BU L1 signature, including its two
if-expression triangle vertices. All new non-auto declarations pass the foundational axiom
whitelist and all thirteen environment linters. Current raw source hashes match their receipts.
The 1321-module local import closure has no Skeleton import.

The checkpoint also publishes the two previously accepted but untracked refutation modules:
- `TubeEdgePairOverlap.lean`: doubled edge cylinders overlap in dimension three.
- `GraphDualCellRadialBoundary.lean`: the actual graph-cell frontier is not radially injective
  from the primal vertex. Thus it is not that vertex's geometric cone base.
Their separate private module checks and axiom/thirteen-linter audits passed as recorded in FILL_LOG.
These eight modules have no dependency on another lane's untracked file. They are not added to the
flat aggregate because the lane was restricted to new files; registration remains with integration.

## Exact next obligation: L2

Let `V2 := Fin 3 → ℝ`, `Δ := stdSimplex ℝ (Fin 3)`, and `p := stdCenter 1`.
From a PL 3-ball `C`, two disjoint PL disks `D0,D1 ⊆ frontier C`, their PL coordinates
`r0,r1 : V2 → E3`, and
`hb : IsBridgeDisk C A B (r0 p) (r1 p)`, produce:

```lean
∃ ρ : V2 × ℝ → E3,
  IsPLHomeomorphOn ρ (Δ ×ˢ Icc (0 : ℝ) 1) C ∧
  ρ '' (Δ ×ˢ {(0 : ℝ)}) = D0 ∧
  ρ '' (Δ ×ˢ {(1 : ℝ)}) = D1 ∧
  ρ (p, 0) = r0 p ∧ ρ (p, 1) = r1 p ∧
  ρ '' ({p} ×ˢ Icc (0 : ℝ) 1) = A
```

The hard remaining step is relative ambient straightening of the boundary-parallel arc in the
WHOLE ball. Full cap parametrizations are not prescribed; cap sets and their centres are.
Do not substitute an unmarked prism or put the axis equation into a new named input.

After L2, implement BU L3-L6 and `exists_compactRimCoreBuffer`: cyclic gluing of SINGLE vertex
prisms; centre-preserving untwisting; a zero-marked disk-times-circle product; an outward collar
of the WHOLE cyclic union, fixed on the rim. L2 and L4 need their own genuine modules and receipts
before use in gluing/assembly. `section34CompactGraphSkeleton K` is K's own 1-skeleton, not K'.
Same-level inclusion of the smaller rim neighborhood in the interior of the larger one is false.

The last resumed investigation made no source changes or compilations before the owner paused it.
One possible starting point for new theory, not a completed reduction:
`SimplexPush.exists_isPLHomeomorphOn_push_simplex` implements a supported ambient elementary
triangle move. With a two-vertex base it changes a straight arc to the two other sides of a flat
triangle, fixing the endpoints. `ConeIsotopy.exists_isPLHomeomorphOn_coneComplex_of_continuous`
provides the local-to-global ambient extension argument via small vertex moves and a clopen
relation. A relative disk-shelling or PL isotopy-extension construction still has to be supplied.
Check all hypotheses carefully, especially support in the ball interior away from fixed endpoints.
The ordinary ball-boundary extension does not retain an interior arc. The proper-disk collar API
requires the WHOLE disk boundary on the ball frontier, whereas this bridge meets it only in the
complementary boundary arc; it cannot be applied directly to the bridge disk.

## Execution constraints and receipts

- New files only; never edit frozen statements or other lanes' files. Append to FILL_LOG only.
- No Git writes unless separately authorized. This checkpoint's commit/push was specifically
  authorized by the owner; that does not revoke the normal lane restriction for later proof work.
- No Skeleton imports, including transitive imports. No new named input, sorry/admit/axiom,
  trustMe, linter suppression, heartbeat override, declaration docstring, or inline comments.
- Read NAMING.md and STRUCTURE.md before adding public mathematics. Search new names first.
  Def/abbrev/structure roots have no underscores; source lines are at most 100 codepoints.
- Preserve the frozen leaf statement byte-for-byte, including its variable block, when restating it.
- Lease d: token `claude-agent-d-20260919`; private output root
  `C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-d`.
  The on-disk granted lease was last checked as valid until 2026-09-26 04:17:07.7791223 UTC;
  verify that authorization remains current before compiling.
- Before every compile, wait while four or more host Lean processes run; this lease uses one
  process only. Use prepare-private-root.py followed by checker.ps1, never a direct/shared build.
  The existing private `CodexItem14Check.ps1 -Module <name> -SubLeaves <list>` wraps preparation,
  both host guards, the lease-d checker, retry of ten-minute resource contention, and result logging.
- Log every result with its checker line, raw SHA-256, receipt and sub-leaf list under item 14.
  Success must be `Verified ... with no diagnostics; shared outputs unchanged.`
- Final audits are outside the tree: only propext / Classical.choice / Quot.sound, plus thirteen
  environment linters excluding docBlame/docBlameThm. Do not add diagnostic probes to the repo.

Private evidence: `AuditCodexItem14BridgeDelivery.lean` and `.receipt.json`,
`CodexItem14BridgeDeliveryReceipt.md`, `CodexItem14BridgeDeliveryStatic.json`,
`AuditCodexItem14CylinderOverlap.*`, and `AuditCodexItem14RadialBoundary.*` in the private root.
Checker success lines and raw source SHA-256 values are also in FILL_LOG for review without the root.
For concrete E3, native WithLp DecidableEq differs definitionally from Classical.decEq: use explicit
congrArg/Subsingleton transport for boundaryComplex and Finset pairs, as the new L1 module does.

Do real producer work through L2 and L4. If a proposed signature is actually false for graphDualCell,
stop with the exact clause and evidence. Distinguish such a blocker from a still-unproved theorem.
