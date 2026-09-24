# Section 32 descent: collaborator handoff

Prepared for the owner-requested handoff on 2026-09-24 UTC. Proof development has stopped for handoff; no collaborator message has been sent.

## Status and evidence

The frozen `exists_descentSequence` leaf is STILL OPEN. The latest completed mathematical stage is **finite-window Type 1 elimination from the actual initial separator**. Every component in each requested row is now a labelled essential annulus. This does not assert that any row is nonempty, that an annulus joins opposite ends, or that exactly one bridge remains.

- Checkout: `D:\differential-geometry-moise-int`; branch: `codex/moise-integration`.
- Read-only HEAD snapshot at handoff preparation: `f38a457a99445baa45c451f437f3fba103cb8fd6`. The lead advances this branch independently.
- Private verification root: `C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-b`.
- Last accepted stage manifest: `Codex13AnnularWindowManifest.json` (91 modules).
- Handoff audit status: PASS for all 96 modules; zero diagnostics; only propext / Classical.choice / Quot.sound; all thirteen linters passed.
- Final authoritative inventory: `Codex13HandoffManifest.json`, containing every module receipt and source SHA-256. Archived final audit receipt: `AuditCodex13Handoff.receipt.json`; probe and log: `AuditCodex13Handoff.lean` and `AuditCodex13Handoff.log`.
- All 96 current module receipts were already checked: exitCode=0, diagnosticLines=0, sourceStable=true, sharedArtifactsModified=false; their SHA-256 values match the current sources.
- No git writes, no frozen edits, no Skeleton imports, no new named inputs. The lane did not register modules in the root aggregate; integration remains with the lead. Newly delivered files remain untracked unless the lead has integrated them independently.

## Read first and preserve

Read `DifferentialGeometry/Topology/PiecewiseLinear/Skeleton/FILL_QUEUE.md`, **Codex item 13 — the Section 32 descent**, in full. Its input list and workflow remain binding. Then read `consult/BP-section32-tower-descent-codex-answer.md` section 2 and the `DescentStages` section of the probe `Skeleton/CanonicalTowerReduction.lean` as source guidance only.

Hard rules: new files only; do not write git; do not edit frozen statements; restate the final leaf and its variable block byte-identically; never import Skeleton directly or transitively. Copy any used probe material into uniquely named real declarations and revalidate it. Only the existing tube/tower/initial-surface data and h303/h286/h267/h314 are allowed named inputs. If an essential fact cannot be derived from those data, report the exact obligation to the owner instead of adding an input.

Lease b: `claude-agent-b-20260919`, one worker, expires `2026-09-26T04:17:07.7791223Z`. Before every compile or audit, inspect host `lean.exe`; do not start with four already running. A ten-minute admission refusal is contention and should be retried. Do not overlap workers under this token or assume a lease transfer has occurred. This handoff does not modify or release the lease record.

Use `prepare-private-root.py` and `checker.ps1` from `C:\Users\liao9\AppData\Local\Temp\claude-moise-shared`. Keep outputs private. Append receipts and SHA-256s under `# Codex item 13` in `Skeleton/FILL_LOG.md`. Source lines are at most 100 codepoints; no proof debt, diagnostic commands, declaration comments, linter suppression, or resource-budget overrides.

## Completed stages and exact consumer interfaces

1. **Actual finite null-seam normalization**: `CanonicalSurfaceNullNormalization.lean`, `IsCanonicalSurface.exists_window_null_normalization`. Produces a real finite split history, canonical states, zero finite seam rank, outside-support equality, and equality on the protected set.
2. **Actual finite-window component classification**: `CanonicalWindowComponentClassification.lean`, `IsCanonicalTower.exists_initial_window_component_classification` (line 117). Components are closed or marked annuli, with original lower/upper seam labels, essential ends, seam generator certificates, and boundary-fixed embeddings into the original odd torus.
3. **Actual finite-window Type 1 elimination**: `CanonicalAnnularWindow.lean`, `IsCanonicalTower.exists_initial_annular_window` (line 123). Starts from the real initial separator; retains both the null-split history and closed-component deletion history. The closed deletion part preserves every row boundary and every even-torus trace exactly, explicit surviving-component label embeddings, the protected set, and reference subsurface models.

The Type 1 producer allows any finite row set `rows` and protected set `F` satisfying disjointness from active even supports and active row interiors. These are geometric conditions on a freely chosen protected set, not extra external inputs. `F = empty` gives an unconditional initial finite window. Preserve these conditions for the guarded recursion; do not weaken the outputs to an unlabelled existence claim.

All paths below are relative to `DifferentialGeometry/Topology/PiecewiseLinear/`, except the explicitly qualified topology module.

| Module | Direct role / obligation served |
| --- | --- |
| `ComponentSubsurfaceRestriction` | Restrict existing subsurface models to actual retained components with equal spaces. |
| `CanonicalClosedComponentDeletion` | Rich Type 1 single-step certificate; exact surviving labels, boundary and trace preservation; finite `windowComponentRank` decreases. |
| `CanonicalClosedWindowReduction` | Strong induction eliminating all closed components in a finite row window while preserving the full consumer certificate. |
| `CanonicalAnnularWindow` | Completed Type 1 stage assembly, including the actual initial-surface producer. |
| `Topology/Connected/BicollaredReplacement` | `Separates.of_bicollared_frontier_replacement`: separation survives replacement inside a regular closed bicollared region when the remaining frontier opening is preconnected and the marked sets are outside the region. |
| `SurfacePatchReplacement` | `IsCombinatorialManifold.separates_of_connected_surface_patch`: derives the required region from the actual closed PL surface inside a solid torus. Reuses the Type 1 filling and bicollar proofs. |
| `TorusCirclePair` | `IsCombinatorialSolidTorus.exists_annulus_pair_of_essential_circles`: BOTH complementary annuli, with the original two end labels and exact union/intersection. Reuses the already proved `EssentialPolygonProductCoordinates` and `CircleArcs`. |
| `AnnulusPatchDeletion` | Actual closed-surface gluing of two annuli and `IsPLAnnulusWithEnds.separates_after_delete_interior`; the geometric Type 2 deletion argument is proved. |
| `CanonicalSurfaceComponentRemoval` | `IsCanonicalSurface.of_component_complement`: reconstructs the full state after removing ANY component, using the existing disjoint-union collared-trace API and exact deleted boundary. Shared by Type 2 and Type 3. |

The last five modules are checked tools for subsequent stages, not a claim that the canonical Type 2 producer or its finite iteration is complete.

## Next acceptance target: actual Type 2 finite-window elimination

First close a single-step theorem on `IsCanonicalAnnularWindow`, then iterate it. For an actual returning component `C` in row `i`, its two saved ends lie on the same even torus, indexed by `i` or `i+1`. The required result is an actual family `Y`, with:

- canonical state and annular-window classification preserved;
- `(Y i).space = (X i).space minus C`, all other rows literally unchanged;
- full tower surface exactly equal to the old surface minus the intrinsic annulus interior `C minus (J0 union J1)`; the end circles remain on the full even torus;
- an equivalence from the original components other than the discarded one to the new components, with exactly equal component spaces;
- every surviving end label, essentiality certificate, generator certificate, and subsurface model preserved;
- exact boundary removal, trace-family inclusion, and preservation of zero null-rank;
- one fewer component in the finite window and equality on every protected set disjoint from the deleted intrinsic interior;
- the actual `IsTypeTwoDeletion` certificate (copy/revalidate the probe vocabulary under a unique real name if used).

Concrete assembly, reusing Type 1 work:

1. Use `IsCombinatorialManifoldWithBoundary.exists_component_complement` in `ManifoldComponentComplement.lean`. It already gives the finite orientable remainder, exact boundary subtraction, the retained-component equivalence, and cardinality decrement. Do not rebuild these.
2. Use `CanonicalComponentSeamDisks` to transfer a current end-circle disk witness between the even torus and its original odd torus. Together with the saved essentiality this supplies the two essential-circle hypotheses of `TorusCirclePair`.
3. Glue `C` to either complementary even-torus annulus using `AnnulusPatchDeletion`. Its geometric deletion theorem supplies separation once the actual remainder is relatively closed. Carrier control comes from the same triple solid torus as Type 1 (`CanonicalTowerCarrierTorus` / `SurfaceRegionInSolidTorus`), with vertex avoidance from havoid.
4. Obtain relative closedness from `IsCanonicalTower.isClosed_towerSurface` in `CanonicalTowerSurfaceClosed.lean`, using the actual remainder complex and inherited carrier inclusions. Prove the global deletion equation carefully: row deletion removes the whole component, but its boundary remains in the full even tori.
5. Apply `CanonicalSurfaceComponentRemoval.of_component_complement` to reconstruct the state. Use `ComponentSubsurfaceRestriction` for retained models and `SurfaceTraceMonotonicity` for trace inclusion / null-rank preservation.
6. Reuse `windowComponentRank` and the Type 1 strong-induction pattern. Total component count is a valid finite phase measure while each returning-component deletion removes one component. Do not use the exact trace-equality claim specific to closed Type 1 components; Type 2/3 delete their boundary circles from the odd-row traces.

No generic `IsCanonicalComponentDeletion` structure or Type 2 normalizer has been written yet. If introducing shared step data, retain actual label maps, geometric deletion equalities, protected-set equalities, and the valid source/target states. The old Type 1 implementation need not be rewritten to start the next stage.

## Outstanding bridge nonemptiness obligation

Before redundant-bridge elimination, prove an initial same-component witness carrying BOTH a lower and an upper essential seam, and transport it through the actual split/deletion histories. Current annular classification alone is compatible with an empty row; using it as a bridge-existence theorem would be a genuine gap.

The reviewed route is in `Codex13DescentRouteDraft-20260924.md` in the private root. It is a proof plan, not a checked theorem. Its mixed-witness route uses the finite index range `2*i-1` through `2*i+3`:

- Use `PolygonCarrierOfSpine.exists_polygon_carrier_of_spine` and actual shared cores to obtain essential polygon carriers in the lower and upper solid intersections.
- Apply `TorusSubsurfaceCarrier.IsPLTorus.carriesFirstHomologyOnto_or_subsingleton_of_disjoint` to each side; rule out trivial first homology using public `SolidTorusHurewiczOne` and the checked solid-torus fundamental-group result. Do not use the private homology-isomorphism helper in `PolygonCarrierOfSpine`.
- Produce a mixed adjacent pair among the finite essential circles, then remove maximal null-disk islands from that annular band to obtain a connected piece of the actual initial odd row with both ends. The now-confirmed public `exists_product_coordinates_for_disjoint_essential_polygons` may simplify the cyclic-adjacency argument.
- Transport the two actual boundary marks through the real component equivalences in `CircleCappingComponentInvariants` / `PLHomeomorphComponents` and fixed-boundary maps in `CanonicalSurfaceSplit`. Type 1 cannot delete this nonempty-boundary component; a returning Type 2 component cannot be the mixed one.

No insufficiency of the authorized input data has been established. This is an unproved producer obligation, not permission to assume a new named input.

## Type 3, halves, recursion, and leaf

Reuse the same `SurfacePatchReplacement` theorem for Type 3: two distinct bridge annuli plus one annulus on each endpoint torus form a closed surface. Glue the pair of bridges and pair of endpoint annuli using `ManifoldDisjointUnion` and `BoundaryGluing` along their complete four-circle boundaries. The deleted patch is the discarded bridge interior. Preserve the other bridge and all surviving labels; iterate only after the nonemptiness obligation is proved.

For an even-torus half, `TorusCirclePair` gives both complementary marked annuli. Use the entire even torus as the closed surface in `SurfacePatchReplacement`, deleting the unwanted annulus interior. Keep the underlying canonical state with full even tori; store finitely chosen halves separately when constructing each displayed separator.

The reviewed guard schedule preserves completed rows `[a,b]` and chosen interior halves `a+1,...,b`; the two guard even tori stay full. Expand at the outside seams, normalize the two new boundary rows, and then choose halves at the old guards. Exact unchanged-row and protected-set equalities must keep previously chosen geometries literally fixed.

Set `M 0` to the original initial surface. Each later displayed separator comes from a finite normalized underlying state and finitely many half deletions. The frozen leaf does not impose a surgery equation between successive displayed separators. Use local finiteness of triple carriers to upgrade per-index stabilization to local eventual equality off `P'`, then prove relative closedness and every exact `IsAnnularChain` field. Do not import or use the downstream annular-chain open-cell/pseudo-cell endpoint to establish the descent.

## Verification / integration handoff

The final JSON manifest is the complete module inventory, with an absolute receipt path and SHA-256 for every module. `Skeleton/FILL_LOG.md` contains the append-only acceptance record. No broad root build, root-aggregate edit, commit, push, or lease mutation was performed by this lane.

Replay a module with its full module name using the shared preparation script, then checker with `-Checkout D:\differential-geometry-moise-int -Token claude-agent-b-20260919 -OutputRoot C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-b -Module <module>`, after the host-process guard and only while the lease is valid and not used by another worker. Audit with `-Audit <absolute tree-external probe path>` instead of `-Module`.

`AuditCodex13Handoff.lean` audits all nonautomatic declarations from all 96 modules, including private helpers and structure projections. It checks transitive axiom closures against exactly propext / Classical.choice / Quot.sound and runs all thirteen applicable environment linters. Keep the existing batches of fifteen modules; one giant audit command previously exceeded the normal heartbeat limit. Do not raise resource limits.

Runtime at final handoff: the final checker completed successfully, and no Lean process using the lane-b private output root remained at the final process check. Proof work is stopped for the owner-requested handoff. Recheck ownership, expiry, and host resources before a collaborator uses lease b.
