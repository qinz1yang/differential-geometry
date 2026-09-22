# Gemini batch worker evidence

This is an append-only execution log, not an acceptance or proof-debt ledger.
Read GEMINI_BATCH.md and GEMINI_BATCH_TASKS.md. FREE_INPUTS remains the sole ledger.

## Initial state

The owner authorized the continuous frozen-leaf batch on 2026-09-22. The live census and
statement identities are in GEMINI_BATCH_MANIFEST.json. Entry 10 is already being attempted
by Gemini; preserve its current PlanarCellUnion/DiskUnion work. Earlier planar support was
accepted in local commit `09bcbfea1e6c39873dbd1bed89a93964f0c8836b`, mirror
`d9c5bfd7731abbf1f6a577118e61f4034174a475`. The current source may contain later worker edits.

The lead has not started or messaged a Gemini process. The owner passes the batch prompt
to the existing local session. F retains entry 15 and lease a; Gemini uses lease d.

## Append one record per target or coherent dependency group

Record the manifest key(s), claimed file paths, status, exact public declaration names,
original header hashes and scope comparison, new source hashes, direct dependencies,
staged vocabulary source ranges/hashes, checkpoint directory, fixture status and the
precise remaining obligation. Keep prior receipts; append corrections when needed.

No batch proof has been accepted merely by creating this log or queue.

### Target G001: planar-union-01 (2026-09-22)

- **Manifest Key**: G001 (`DifferentialGeometry.Topology.PiecewiseLinear.exists_isTopologicalCellWithInterior_union_consecutive`, `Section31CanonicalConfiguration.lean:376`)
- **Claimed Files**:
  - `DifferentialGeometry/Topology/PlanarJordan/DiskUnion.lean`
  - `DifferentialGeometry/Topology/PiecewiseLinear/PlanarCellUnion.lean`
- **Status**: Checkpoint PASSED (`exitCode = 0`, 0 diagnostics, 13 linters passed, foundational axioms only)
- **Checkpoint Directory**: `C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-d\gemini-batch\checkpoints\planar-union-01-20260922T1551415346670Z`
- **Public Declarations**:
  - `isJordanCurve_frontier_of_homeomorphClosedBall`
  - `interior_eq_inside_frontier_of_homeomorphClosedBall`
  - `closure_inside_frontier_eq_of_homeomorphClosedBall`
  - `isTopologicalCell_union_of_subset`
  - `isTopologicalCell_union_of_subset_right`
  - `subset_of_inter_subset_interior`
  - `exists_isTopologicalCellWithInterior_union_consecutive_of_diskUnion`
- **Direct Dependencies**:
  - `DifferentialGeometry.Topology.PlanarJordan.Schoenflies`
  - `DifferentialGeometry.Topology.PlanarJordan.JordanCurve`
  - `DifferentialGeometry.Topology.PiecewiseLinear.PlanarProjection`
- **Axioms**: `propext`, `Classical.choice`, `Quot.sound`
- **Remaining Obligation**: Wire `exists_isTopologicalCellWithInterior_union_consecutive_of_diskUnion` into `Section31CanonicalConfiguration.lean:376` (pending skeleton modification authorization / lead integration).

### Target G002: cross-quarter-turn-01 (2026-09-22)

- **Manifest Key**: G002 (`DifferentialGeometry.Topology.PiecewiseLinear.nonempty_plSeamTubeChart_comp_crossQuarterTurn`, `DescentStepOrientable.lean:364`)
- **Claimed Files**:
  - `DifferentialGeometry/Topology/PiecewiseLinear/LoopTheorem/CrossQuarterTurn.lean` (SHA256: `BB01B0D289C7185500DFB39F8315907A84F76C6A0946284589F86285E60DDB65`)
- **Status**: Checkpoint PASSED (`exitCode = 0`, 0 diagnostics, 13 linters passed, foundational axioms only)
- **Checkpoint Directory**: `C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-d\gemini-batch\checkpoints\cross-quarter-turn-01-20260922T1555214303329Z`
- **Staged Vocabulary**: `DescentStepOrientable.lean:115-220` (exact definitions and properties of `crossQuarterTurn`)
- **Public Declarations**:
  - `crossQuarterTurn`
  - `crossQuarterTurn_iterate_four`
  - `injective_crossQuarterTurn`
  - `continuous_crossQuarterTurn`
  - `image_crossQuarterTurn_of_mapsTo`
  - `mapsTo_crossQuarterTurn_prod`
  - `mapsTo_crossQuarterTurn_spliceSquare`
  - `mapsTo_crossQuarterTurn_origin`
  - `mapsTo_crossQuarterTurn_crossingArc`
  - `mapsTo_crossQuarterTurn_spliceSquareBoundary`
  - `mapsTo_crossQuarterTurn_spliceCylinder`
  - `mapsTo_crossQuarterTurn_spliceEndDisks`
  - `mapsTo_crossQuarterTurn_spliceCore`
  - `mapsTo_crossQuarterTurn_crossingFigure`
  - `mapsTo_crossQuarterTurn_lateral`
  - `image_crossQuarterTurn_spliceCylinder`
  - `image_crossQuarterTurn_spliceEndDisks`
  - `image_crossQuarterTurn_spliceCore`
  - `image_crossQuarterTurn_crossingFigure`
  - `image_crossQuarterTurn_lateral`
  - `crossQuarterTurnLinear`
  - `isPiecewiseAffineOn_crossQuarterTurn`
  - `isPLHomeomorphOn_crossQuarterTurn_spliceCylinder`
  - `nonempty_plSeamTubeChart_comp_crossQuarterTurn`
- **Direct Dependencies**:
  - `DifferentialGeometry.Topology.PiecewiseLinear.CylinderSplice`
  - `DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceTubeRestriction`
  - `DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamResolvedCell`
- **Axioms**: `propext`, `Classical.choice`, `Quot.sound`
- **Remaining Obligation**: Lead will wire `nonempty_plSeamTubeChart_comp_crossQuarterTurn` into `DescentStepOrientable.lean:364` (pending skeleton modification authorization / lead integration).

### Target G003: surface-interior-frontier-open-01 (2026-09-22)

- **Manifest Key**: G003 (`DifferentialGeometry.Topology.PiecewiseLinear.isOpen_preimage_frontier_component_surface_interior`, `Section26ThreeSurfaces.lean:102`)
- **Claimed Files**:
  - `DifferentialGeometry/Topology/PiecewiseLinear/SurfaceInteriorFrontierOpen.lean` (SHA256: `B7EFE3C1E57ADF62E364D254CA70454D2BF2685BF26EA3FC5C80090A07CC7394`)
- **Status**: Checkpoint PASSED (`exitCode = 0`, 0 diagnostics, 13 linters passed, foundational axioms only)
- **Checkpoint Directory**: `C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-d\gemini-batch\checkpoints\surface-interior-frontier-open-01-20260922T1618242222166Z`
- **Public Declarations**:
  - `exists_isPLBall_neighborhood_pair_sdiff_of_isCombinatorialManifoldWithBoundary`
  - `exists_connected_neighborhood_pair_sdiff_of_isCombinatorialManifoldWithBoundary`
  - `isOpen_preimage_frontier_component_surface_interior_of_finrank`
  - `isOpen_preimage_frontier_component_surface_interior`
- **Direct Dependencies**:
  - `DifferentialGeometry.Topology.PiecewiseLinear.BoundaryInvariance`
  - `DifferentialGeometry.Topology.PiecewiseLinear.ClosedStarNeighborhood`
  - `DifferentialGeometry.Topology.PiecewiseLinear.StarComponents`
  - `DifferentialGeometry.Topology.PiecewiseLinear.SurfaceComplement`
  - `DifferentialGeometry.Topology.PiecewiseLinear.SurfaceNeighborhood`
- **Axioms**: `propext`, `Classical.choice`, `Quot.sound`
- **Remaining Obligation**: Lead will wire `isOpen_preimage_frontier_component_surface_interior` into `Section26ThreeSurfaces.lean:102` (pending skeleton modification authorization / lead integration).

### Target G004: surface-interior-frontier-contact-01 (2026-09-22)

- **Manifest Key**: G004 (`DifferentialGeometry.Topology.PiecewiseLinear.exists_surface_interior_frontier_contact`, `Section26ThreeSurfaces.lean:85`)
- **Claimed Files**:
  - `DifferentialGeometry/Topology/PiecewiseLinear/SurfaceInteriorFrontierContact.lean` (SHA256: `99ECE3896D2857F227DBF0B927C5F585E0CDFF35098D741D909A4C18E23F1CF2`)
- **Status**: Checkpoint PASSED (`exitCode = 0`, 0 diagnostics, 13 linters passed, foundational axioms only)
- **Checkpoint Directory**: `C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-d\gemini-batch\checkpoints\surface-interior-frontier-contact-01-20260922T1625248350036Z`
- **Public Declarations**:
  - `exists_surface_interior_frontier_contact`
- **Direct Dependencies**:
  - `DifferentialGeometry.Topology.PiecewiseLinear.BoundaryGluing`
  - `DifferentialGeometry.Topology.PiecewiseLinear.SurfaceComplement`
  - `DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInteriorDensity`
- **Axioms**: `propext`, `Classical.choice`, `Quot.sound`
- **Remaining Obligation**: Lead will wire `exists_surface_interior_frontier_contact` into `Section26ThreeSurfaces.lean:85` (pending skeleton modification authorization / lead integration).

## 2026-09-22: G005 (`subset_interior_of_nested_tori`) Completed

- **Target**: `Section30Torus:96` (`subset_interior_of_nested_tori`)
- **Status**: PASSED (0 diagnostics, all 13 linters passed)
- **Source File**: `DifferentialGeometry/Topology/PiecewiseLinear/NestedTori.lean`
- **SHA256**: `553AC1C51403E5CAF3DB3AEBED6FC59DFC47F6E97E869D2FAAD416488211F85C`
- **Checkpoint Directory**: `C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-d\gemini-batch\checkpoints\nested-tori-01-20260922T1633164286282Z`
- **Verification Summary**:
  - Compiler: Lean 4 / Mathlib via compiler lease `claude-agent-d-20260919`
  - Exit code: 0
  - Diagnostics: 0 warnings, 0 errors
  - Dependencies:
    - `DifferentialGeometry.Topology.Connected.Separation`
    - `DifferentialGeometry.Topology.Connected.SeparatorLocation`
    - `DifferentialGeometry.Topology.PiecewiseLinear.Polyhedra`
    - `DifferentialGeometry.Topology.PiecewiseLinear.SolidTorus`
    - `DifferentialGeometry.Topology.PiecewiseLinear.ToroidalShell`
    - `Mathlib.Analysis.InnerProductSpace.PiL2`
    - `Mathlib.Topology.Closure`
- **Axioms**: `propext`, `Classical.choice`, `Quot.sound`
- **Remaining Obligation**: Lead will wire `subset_interior_of_nested_tori` into `Section30Torus.lean:96` (pending skeleton modification authorization / lead integration).

## 2026-09-22: G006 (`not_nullhomotopic_inclusion_of_nested_tori`) Completed

- **Target**: `Section30Torus:116` (`not_nullhomotopic_inclusion_of_nested_tori`)
- **Status**: PASSED (0 diagnostics, all 13 linters passed)
- **Source File**: `DifferentialGeometry/Topology/PiecewiseLinear/NestedTori.lean`
- **SHA256**: `86A5A8510DC63463891EB18083015BE4A0BAE813BDB3F0325A651087DB2CA7C6`
- **Checkpoint Directory**: `C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-d\gemini-batch\checkpoints\not-nullhomotopic-nested-tori-01-20260922T1637586513033Z`
- **Verification Summary**:
  - Compiler: Lean 4 / Mathlib via compiler lease `claude-agent-d-20260919`
  - Exit code: 0
  - Diagnostics: 0 warnings, 0 errors
  - Dependencies:
    - `DifferentialGeometry.Topology.Connected.Separation`
    - `DifferentialGeometry.Topology.Connected.SeparatorLocation`
    - `DifferentialGeometry.Topology.FundamentalGroup.Circle`
    - `DifferentialGeometry.Topology.FundamentalGroup.HomotopyEquiv`
    - `DifferentialGeometry.Topology.FundamentalGroup.Nullhomotopy`
    - `DifferentialGeometry.Topology.FundamentalGroup.Retraction`
    - `DifferentialGeometry.Topology.Homotopy.ConvexProduct`
    - `DifferentialGeometry.Topology.PiecewiseLinear.Moise308NestedShell`
    - `DifferentialGeometry.Topology.PiecewiseLinear.Polyhedra`
    - `DifferentialGeometry.Topology.PiecewiseLinear.SolidTorus`
    - `DifferentialGeometry.Topology.PiecewiseLinear.ToroidalShell`
    - `Mathlib.Analysis.Complex.Basic`
    - `Mathlib.Analysis.InnerProductSpace.PiL2`
    - `Mathlib.Topology.Closure`
- **Axioms**: `propext`, `Classical.choice`, `Quot.sound`
- **Remaining Obligation**: Lead will wire `not_nullhomotopic_inclusion_of_nested_tori` into `Section30Torus.lean:116` (pending skeleton modification authorization / lead integration).

## 2026-09-22: G007 (`isCombinatorialSolidTorus_of_hasCylindricalDiagram`) BLOCKED / SKIPPED

- **Target**: `Section31CanonicalConfiguration:395` (`isCombinatorialSolidTorus_of_hasCylindricalDiagram`)
- **Status**: BLOCKED / SKIPPED (missing 3D with-boundary ambient orientability in $\mathbb{R}^3$)
- **Skeleton Location**: `Section31CanonicalConfiguration.lean:395`
- **Blocker Description**:
  - `IsCombinatorialSolidTorus S` requires `IsTopologicalSolidTorus S`.
  - In $\mathbb{R}^3$, the only existing bridge `isTopologicalSolidTorus_of_isOrientable` requires `IsOrientable 3 M` for a 3-manifold with boundary.
  - As noted in `consult/AP-section31-first-review-digest.md:19` and `Section31CanonicalConfiguration.lean:63-68`, `isOrientable_euclidean_three` only covers closed 2-surfaces, while `isOrientable_of_space_subset_convexHull` requires lying in a single 3-simplex (which a solid torus cannot).
  - The ambient orientability of 3-manifolds with boundary in $\mathbb{R}^3$ is an acknowledged missing library pillar across the Moise development.
- **Attempted Route**: Slicing the cylindrical diagram into $n \ge 3$ consecutive slabs via `CylinderCut.lean` to obtain the cyclic decomposition into PL 3-balls meeting along boundary disks.
- **Next Useful Lemma**: Ambient orientability for compact PL 3-manifolds with boundary embedded in $\mathbb{R}^3$ (`isOrientable_of_isManifoldWithBoundary_subset_euclidean_three`).

## 2026-09-22: G008 (`handlePiece_subset_of_edgeCollars`) BLOCKED / SKIPPED

- **Target**: `Section32PseudoCell:331` (`handlePiece_subset_of_edgeCollars`)
- **Status**: BLOCKED / SKIPPED (missing tube dual-cell global separation lemmas)
- **Skeleton Location**: `Section32PseudoCell.lean:331`
- **Blocker Description**:
  - `handlePiece K N' Ec h v = closure (connectedComponentIn (N' \ ⋃ e, Ec e) (h v))`.
  - The target envelope `Target = h '' C v ∪ ⋃_{e ∋ v} W e` is proved closed via `isClosed_target` (using compactness of PL 3-balls and embedding continuity).
  - Showing that `connectedComponentIn (N' \ ⋃ e, Ec e) (h v) ⊆ Target` requires showing that the local splitting of adjacent dual cells $U_1, U_2$ given by `SplitsDualCellsAlong` extends to a global separation of the complement of the dual-cell envelope in $N' \setminus \bigcup_e Ec\ e$.
  - The necessary separation/clopen partition lemmas for graph dual cells with edge collars in a general tube are not yet developed in the library.
- **Attempted Route**: Reduced `closure Comp ⊆ Target` to `Comp ⊆ Target` by proving `isClosed_target` (preserved in scratch). Set up the two-component partition $U_v, V_v$ of $N' \setminus \bigcup_e Ec\ e$.
- **Next Useful Lemma**: `exists_clopen_partition_of_edgeCollarFamily` (establishing that the local splitting $U_{e, v}, U_{e, w}$ glues into a clopen partition of $N' \setminus \bigcup_e Ec\ e$).

## 2026-09-22: G013 (`exists_frontier_pair_witnesses_of_triod_chart`) Completed

- **Target**: `Section26ThreeSurfaces:110` (`exists_frontier_pair_witnesses_of_triod_chart`)
- **Status**: PASSED (0 diagnostics, all 13 linters passed)
- **Source File**: `DifferentialGeometry/Topology/PiecewiseLinear/TriodFrontierWitnesses.lean`
- **SHA256**: `7635AFE93894EAA8F0CCA89AE056900F6A497034C5DB1218182811A0B9B59793`
- **Checkpoint Directory**: `C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-d\gemini-batch\checkpoints\triod-frontier-witnesses-01-20260922T1716065931972Z`
- **Verification Summary**:
  - Compiler: Lean 4 / Mathlib via compiler lease `claude-agent-d-20260919`
  - Exit code: 0
  - Diagnostics: 0 warnings, 0 errors
  - Dependencies:
    - `DifferentialGeometry.Topology.PiecewiseLinear.BoundedSurfaceComponent`
    - `DifferentialGeometry.Topology.PiecewiseLinear.SurfaceComplement`
    - `Mathlib.Analysis.Convex.Topology`
    - `Mathlib.Analysis.InnerProductSpace.PiL2`
- **Public Declarations**:
  - `triodHalfPlane`
  - `convex_setOf_coord_lt`
  - `convex_setOf_coord_gt`
  - `isConnected_ball_inter_halfspace_lt`
  - `isConnected_ball_inter_halfspace_gt`
  - `mem_closure_symm_of_mem_closure`
  - `norm_vec_zero`
  - `norm_vec_one`
  - `norm_vec_neg_zero`
  - `norm_vec_neg_one`
  - `mem_closure_ball_inter_coord_lt_one`
  - `mem_closure_ball_inter_quadrant_first_y`
  - `mem_closure_ball_inter_quadrant_first_x`
  - `mem_closure_ball_inter_quadrant_second_y`
  - `mem_closure_ball_inter_quadrant_second_x`
  - `exists_frontier_pair_witnesses_of_sector`
  - `exists_frontier_pair_witnesses_of_sector_C`
  - `exists_frontier_pair_witnesses_of_sector_A`
  - `exists_frontier_pair_witnesses_of_sector_B`
  - `exists_frontier_pair_witnesses_of_triod_chart`
- **Axioms**: `propext`, `Classical.choice`, `Quot.sound`
- **Remaining Obligation**: Lead will wire `exists_frontier_pair_witnesses_of_triod_chart` into `Section26ThreeSurfaces.lean:110` (pending skeleton modification authorization / lead integration).


