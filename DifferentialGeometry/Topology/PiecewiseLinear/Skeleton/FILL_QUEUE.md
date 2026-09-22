# Fill queue — frozen skeleton leaves for F (2026-09-22)

This is an execution queue. Acceptance and proof debt belong only to `../FREE_INPUTS.md`;
`FILL_LOG.md` supplies worker evidence for independent verification. Original entry numbers
are retained. Do not repeat entries 1, 2, 3, 4, 6, 7, 8, 9, 13, 14, or 16.

Work in `D:\differential-geometry-moise-int`, branch `codex/moise-integration`.
`E:\differential-geometry-dev` and its outputs are read-only. Compile only in PowerShell with
lease a, token `claude-agent-a-20260919`, private output root
`C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a`. Read the live lease; only the owner
may edit it. Prepare the private root immediately before each named-module check.

Use the public definitions below. Private copies do not prove the frozen endpoint.
Never import a skeleton. Preserve exact names, binders, instances and lexical scopes.
Check possible counterexamples against every actual Lean hypothesis first; failure of one
local argument is not a counterexample to the whole leaf.

The owner authorized another pass after the previous one ended. The lead directly messaged
task F to start with entry 10 (a general planar two-cell union producer), then entry 15
(the full PL crossing normal form). If both meet new concrete blockers, choose entry 11
or 12 only with a new constructive route. Do not repeat the previous broad searches.
Entries 7/14a/14b are now accepted through `RelativeBoundaryGluing`. Entry 5 has a new
two-leaf decomposition awaiting external review and remains outside this F pass. Continue while an approach makes concrete
progress; record exact goals at genuine blockers. Stop after this pass.

## Remaining entries, in suggested order

| Entry | Leaf / skeleton | Public input | Remaining obligation |
|---|---|---|---|
| 10 | `exists_isTopologicalCellWithInterior_union_consecutive` / `Section31CanonicalConfiguration` | `CanonicalConfiguration` | Planar two-disk union when the intersection is a two-cell, including both intrinsic interiors. The proved revolution spine/interior results do not supply this planar gluing step. |
| 15 | `hasPLNormalDoubleCrossingAt_of_isStableCrossingBlock` / `GeneralPositionInDouble` | `StableCrossingBlock` | Full two-plane PL normal form from graph sheets, the shared coordinate, margin and neighborhood control. Intersection dimension alone is insufficient. Seven definitions and five helpers are public. |
| 11 | `separates_initialSurface` / `Section32PseudoCell` | `PseudoCell`, `SeparatesOfLocallyEventuallyEq` | Closedness and separation of the alternating surface using `havoid`, outer local finiteness and `IsTube.splitSeparates`. The general separating-limit lemma is proved; the geometric separator sequence and local stabilization remain to construct. Tower vocabulary and `IsTube.mem_interior_dualCell` are public. |
| 12 | `section33_faceEulerChar_handlePiece` / `Section33Approximation` | `PolyhedralTubeNeighborhood` | Global Euler/capping argument yielding `2 - deg v`, with exactly the incident trace polygons as boundary. All four needed definitions are public. |
| 5 | `section33_tube_product` / `Section33Approximation` | `PseudoCell`, `OpenEmbeddingFrontier` | Source derived-neighborhood-minus-core product, then transport. Interior-image transport already exists; a retraction or fundamental-group equivalence is insufficient. |

Module names above are under `DifferentialGeometry.Topology.PiecewiseLinear`, except
`DifferentialGeometry.Topology.OpenEmbeddingFrontier`. Smooth-stage vocabulary is also public
in `DifferentialGeometry.Topology.Handle.SmoothStage` for future smoothing leaves.

## Delivery

- Create real proof modules or continue your own WIP files. Do not edit skeletons, the flat
  aggregate, `FREE_INPUTS.md`, other lanes' files, or Git state.
- Append exact public names, imports, source hashes, compiler receipts, axiom/linter results
  and remaining goals to `FILL_LOG.md`. Real modules require zero errors, warnings and avoidable
  info diagnostics; exclude only docBlame/docBlameThm from the standard linter set.
- No new sorry/axiom, resource overrides, linter suppression, declaration docstrings or inline
  comments. Required headers and concise mathematical module docstrings are allowed.
- FALSE needs a joint witness satisfying every field, including pinned maps, exact overlaps
  and dimensions; name the actual Lean clauses so the lead can verify it independently.

The compact §34 leaves, relative torus general-position producer and new §30 / restricted
extended-loop drafts are outside this round. Definitions and conditional assemblies do not
prove their producers. Exact vocabulary moves need no new external review; substantive
statement changes must return to the lead before proving.
