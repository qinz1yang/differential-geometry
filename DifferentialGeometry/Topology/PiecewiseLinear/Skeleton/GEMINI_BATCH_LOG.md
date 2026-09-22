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

## 2026-09-22: G009 (`section33_not_isLoopTheoremDisk`) BLOCKED / SKIPPED

- **Target**: `Section33Approximation:255` (`section33_not_isLoopTheoremDisk`)
- **Status**: BLOCKED / SKIPPED (missing 3D PL 2-disk cut-and-paste surgery apparatus)
- **Skeleton Location**: `Section33Approximation.lean:255`
- **Blocker Description**:
  - Proving that no loop theorem disk exists requires Moise Lemma 9 (pp. 231–233).
  - The proof proceeds by innermost circle/arc elimination for intersections of a PL 2-disk with pseudo-cell boundaries in $\mathbb{R}^3$, performing surgery along discs.
  - The general position 3D cut-and-paste surgery infrastructure is not yet available in the library.
- **Next Useful Lemma**: `exists_innermost_circle_surgery_of_plDisk_inter` (cut-and-paste surgery along an innermost intersection circle).

## 2026-09-22: G010 (`exists_locallyFinitePLPieceIn_of_isOpen`) BLOCKED / SKIPPED

- **Target**: `Section34Control:176` (`exists_locallyFinitePLPieceIn_of_isOpen`)
- **Status**: BLOCKED / SKIPPED (missing infinite locally finite complex assembly for open sets in $\mathbb{R}^N$)
- **Skeleton Location**: `Section34Control.lean:176`
- **Blocker Description**:
  - Requires constructing a `LocallyFinitePLPieceIn Ea 3 M₁ U` covering an arbitrary open set $U$.
  - This requires assembling an infinite locally finite piece tower into a single topologically locally finite complex in $\mathbb{R}^N$ ($N \le 7$).
- **Next Useful Lemma**: Infinite locally finite simplicial complex assembly on open subsets of $\mathbb{R}^N$.

## 2026-09-22: G011 (`exists_isSubdivision_section34CarrierSupport_subset`) BLOCKED / SKIPPED

- **Target**: `Section34Control:181` (`exists_isSubdivision_section34CarrierSupport_subset`)
- **Status**: BLOCKED / SKIPPED (missing non-uniform mesh refinement subordinate to open covers)
- **Skeleton Location**: `Section34Control.lean:181`
- **Blocker Description**:
  - Requires non-uniform mesh refinement / subdivision for a non-compact simplicial complex subordinate to an arbitrary open cover / carrier support.
- **Next Useful Lemma**: Subordinate subdivision theorem for locally finite complexes.

## 2026-09-22: G014 (`nonempty_homeomorph_torus_of_isOrientable_of_eulerChar_eq_zero`) BLOCKED / SKIPPED

- **Target**: `Section30Torus:81` (`nonempty_homeomorph_torus_of_isOrientable_of_eulerChar_eq_zero`)
- **Status**: BLOCKED / SKIPPED (missing classification of closed 2-surfaces)
- **Skeleton Location**: `Section30Torus.lean:81`
- **Blocker Description**:
  - Requires proving that any closed connected orientable 2-manifold with Euler characteristic 0 is homeomorphic to the 2-torus $T^2$.
  - The classification of 2-manifolds (canonical polygonal schema reduction) is not formalized in Mathlib or this library.
- **Next Useful Lemma**: Classification theorem for compact 2-surfaces.

## 2026-09-22: G015 (`IsPLTorus.exists_combinatorial_triangulation`) BLOCKED / SKIPPED

- **Target**: `Section30Torus:89` (`IsPLTorus.exists_combinatorial_triangulation`)
- **Status**: BLOCKED / SKIPPED (missing link recognition on general polyhedra)
- **Skeleton Location**: `Section30Torus.lean:89`
- **Blocker Description**:
  - Requires showing that a polyhedron homeomorphic to $T^2$ admits a combinatorial triangulation.
  - Requires link recognition and triangulating general 2-polyhedra.
- **Next Useful Lemma**: Triangulation theorem for 2-polyhedra.

## 2026-09-22: G016 (`exists_nontrivial_fundamentalGroup_kernel_in_solidTorus`) BLOCKED / SKIPPED

- **Target**: `Section30Torus:108` (`IsPLTorus.exists_nontrivial_fundamentalGroup_kernel_in_solidTorus`)
- **Status**: BLOCKED / SKIPPED (missing ambient/intrinsic interior identification for solid tori)
- **Skeleton Location**: `Section30Torus.lean:108`
- **Blocker Description**:
  - Requires identifying the ambient interior of a solid torus with its intrinsic interior (`interior S ≃ B² × S¹`) before computing the fundamental group kernel.
- **Next Useful Lemma**: Product structure for solid torus interior.

## 2026-09-22: G025 (`exists_annulus_parametrization_of_product_circle_cut`) BLOCKED / SKIPPED

- **Target**: `Section28Annuli:87` (`exists_annulus_parametrization_of_product_circle_cut`)
- **Status**: BLOCKED / SKIPPED (missing finite-mark cyclic decomposition for $n > 2$ points on 1-sphere)
- **Skeleton Location**: `Section28Annuli.lean:87`
- **Blocker Description**:
  - Cutting $S^1 \times S^1$ along $n > 2$ parallel circles requires cyclic ordering and decomposition of $S^1$ into $n$ intervals.
  - `CircleArcs.lean` currently only provides 2-point cuts (`exists_isPLBall_one_of_subset_sphere`).
- **Next Useful Lemma**: $n$-point cyclic decomposition of $S^1$.

## 2026-09-22: G012 (`exists_triod_chart_at_common_boundary`) BLOCKED / SKIPPED

- **Target**: `Section26ThreeSurfaces:65` (`exists_triod_chart_at_common_boundary`)
- **Status**: BLOCKED / SKIPPED (missing 3D 3-half-plane PL straightening / sector cone-gluing infrastructure)
- **Skeleton Location**: `Section26ThreeSurfaces.lean:65`
- **Blocker Description**:
  - Requires finding $p \in \partial M_0$ and a PL chart $e : U \to V$ around $p$ mapping the three combinatorial 2-manifolds with boundary $M_0, M_1, M_2$ to the three standard half-planes $T_0, T_1, T_2$.
  - At a boundary edge $e_0$, the 3 surfaces meet as 3 half-planes meeting along a line at arbitrary dihedral angles.
  - Straightening 3 arbitrary half-planes in $\mathbb{R}^3$ into the 3 coordinate half-planes cannot be achieved by a linear map (since angles between 3 rays in $\mathbb{R}^2$ are not preserved by linear maps).
  - It requires constructing a piecewise linear homeomorphism of $\mathbb{R}^2$ by subdividing the plane into convex sectors/cones, mapping each sector linearly, proving piecewise affine compatibility on ray intersections, crossing with $\mathbb{R}$, and isolating a small ball $B(p, \varepsilon)$ disjoint from all other simplices of the 3 complexes.
  - The sector-subdivision and cone-gluing infrastructure for arbitrary 3-ray configurations in $\mathbb{R}^2$ is not yet developed.

## 2026-09-22: G017 (`exists_isPLBall_superset_of_exterior_compression`) BLOCKED / SKIPPED

- **Target**: `Section30Torus:125` (`exists_isPLBall_superset_of_exterior_compression`)
- **Status**: BLOCKED / SKIPPED (missing 3D 2-handle attachment / regular neighborhood and 3D Schoenflies)
- **Skeleton Location**: `Section30Torus.lean:125`
- **Blocker Description**:
  - Requires: For a 3-manifold with boundary $R$ with $\partial R$ a torus, and an exterior essential disk $D \subseteq U$, finding a PL 3-ball $B \subseteq U$ enclosing $R$ in its interior.
  - The mathematical proof requires constructing a regular neighborhood $N(R \cup D)$ inside $U$, proving that surgery along the essential disk turns the boundary torus into a 2-sphere $\partial N \cong S^2$, and applying the 3D Schoenflies / Alexander theorem in $\mathbb{R}^3$ to show $N$ is a PL 3-ball.
  - The 3D 2-handle attachment / regular neighborhood apparatus and the 3D Schoenflies theorem (`isPLBall_of_frontier_isPLSphere`) are not formalized in Mathlib or this library.
- **Attempted Route**: Analyzed regular neighborhood construction in `RegularNeighborhood.lean` and 3D ball frontier properties in `BallFrontier.lean`.
- **Next Useful Lemma**: `isPLBall_of_frontier_isPLSphere` (3D Schoenflies theorem in $\mathbb{R}^3$).

## 2026-09-22: G018 (`exists_ball_pair_of_interior_essential_disk`) BLOCKED / SKIPPED

- **Target**: `Section30Torus:140` (`exists_ball_pair_of_interior_essential_disk`)
- **Status**: BLOCKED / SKIPPED (missing 3D solid torus cutting / cylindrical diagram from essential disk)
- **Skeleton Location**: `Section30Torus.lean:140`
- **Blocker Description**:
  - Requires cutting a 3-manifold $R$ with boundary a torus along an interior essential disk $D$ to split it into two PL 3-balls $A, B$ meeting along two boundary disks $D_0, D_1$.
  - This requires proving $R$ is a solid torus (Moise Lemma 30.1) and cutting it along a meridian disk into a cylinder $D^2 \times I$ via a relative disk regular neighborhood, followed by cutting the cylinder into two balls.
  - The relative disk neighborhood and 3D cut remainder apparatus for 3-manifolds with boundary are not available.
- **Attempted Route**: Evaluated `CylinderCut.lean` and `NeighborhoodCylinder.lean` for splitting cylinders and circles, but these do not cover cutting general 3-manifolds along embedded disks.
- **Next Useful Lemma**: `exists_cylindricalDiagram_of_essential_disk` (representing a solid torus cut along an essential disk as a cylinder).

## 2026-09-22: G019 (`exists_innerSolidTorus_toroidalShell_of_annulusImage`) BLOCKED / SKIPPED

- **Target**: `Section31CanonicalConfiguration:384` (`exists_innerSolidTorus_toroidalShell_of_annulusImage`)
- **Status**: BLOCKED / SKIPPED (missing toroidal shell revolution from a planar 2-cell collar)
- **Skeleton Location**: `Section31CanonicalConfiguration.lean:384`
- **Blocker Description**:
  - Given a revolved torus chain $N = \bigcup S_j$ and an embedding $h$, requires constructing an inner solid torus $S_1$ around $h '' A_j$ in $\text{interior}(h '' S_j)$ such that $\text{closure}(h '' S_j \setminus S_1)$ is a toroidal shell.
  - In the un-embedded model, this requires constructing a smaller 2-cell $D' \subset \text{interior}(D_j)$ around the core segment, proving that revolving the annular collar between $\partial D'$ and $\partial D_j$ yields a toroidal shell $T^2 \times I$, and transporting through the embedding $h$ using 3D Invariance of Domain.
  - The revolution of planar collars into toroidal shells is not yet developed.
- **Attempted Route**: Evaluated `ToroidalShell.lean` and `TorusShell.lean` for existing toroidal shell constructors; they only provide abstract topological properties, not the revolution constructor.
- **Next Useful Lemma**: `exists_innerSolidTorus_toroidalShell_of_revolution`.

## 2026-09-22: G020 (`exists_generalPosition_solidTorus_relative`) BLOCKED / SKIPPED

- **Target**: `Section31CanonicalConfiguration:399` (`exists_generalPosition_solidTorus_relative`)
- **Status**: BLOCKED / SKIPPED (missing relative general position for solid tori in $\mathbb{R}^3$)
- **Skeleton Location**: `Section31CanonicalConfiguration.lean:399`
- **Blocker Description**:
  - Requires: Given compact $A$, open $U$, a solid torus $S_0$ fitting $A$ in $U$, and a finite family of solid tori $F_i$, finding a solid torus $S$ fitting $A$ in $U$ in pairwise general position with each $F_i$ (transverse crossing at frontiers, intersection of frontiers is a finite disjoint union of 1-spheres).
  - This requires transversality / general position perturbation of polyhedra in $\mathbb{R}^3$ maintaining strict containment conditions.
  - As noted in `SolidTorusGeneralPosition.lean:12`, the relative general-position existence theorem remains an open proof obligation.
- **Attempted Route**: Checked `SolidTorusGeneralPosition.lean`, `GeneralPosition.lean`, and `GeneralPositionInDouble.lean`. The existing general position results only cover maps of 1-complexes and singular 2-cells, not ambient polyhedral 3-manifolds.
- **Next Useful Lemma**: `exists_generalPosition_polyhedron_relative` (relative general position perturbation for polyhedra in $\mathbb{R}^3$).

## 2026-09-22: G021 (`exists_polygon_carrier_of_spine`) BLOCKED / SKIPPED

- **Target**: `Section31CanonicalConfiguration:452` (`exists_polygon_carrier_of_spine`)
- **Status**: BLOCKED / SKIPPED (missing Moise 28.11 and 1-cycle simple curve normalization)
- **Skeleton Location**: `Section31CanonicalConfiguration.lean:452`
- **Blocker Description**:
  - Requires: Given solid tori $S_1, S_2$ and spines, finding a 1-sphere $K \subseteq \text{frontier}(S_2) \cap \text{interior}(S_1)$ carrying the generator of $S_2$.
  - Moise Theorem 28.11 produces an integer 1-cycle on the boundary carrying the generator; this 1-cycle must then be normalized into pairwise disjoint simple closed curves (Moise 28.8) to extract a single 1-sphere generator carrier.
  - Neither the 1-cycle extraction (28.11) nor the simple curve normalization (28.8) is formalized in the library.
- **Attempted Route**: Surveyed `Section31CanonicalConfiguration.lean` and `consult/AP-section31-first-review-digest.md:6-8`.
- **Next Useful Lemma**: `exists_oneCycle_boundary_of_spine` (Moise 28.11).

## 2026-09-22: G022 (`carriesGenerator_or_exists_isPLCell_of_polygon_disjoint_carrier`) BLOCKED / SKIPPED

- **Target**: `Section31CanonicalConfiguration:463` (`carriesGenerator_or_exists_isPLCell_of_polygon_disjoint_carrier`)
- **Status**: BLOCKED / SKIPPED (missing Moise 28.10 boundary torus dichotomy)
- **Skeleton Location**: `Section31CanonicalConfiguration.lean:463`
- **Blocker Description**:
  - Requires: On the boundary of a combinatorial solid torus, a simple closed curve disjoint from a generator-carrying 1-sphere either carries a generator or bounds a 2-cell on the boundary.
  - This is the polygon-carrier special case of Moise Theorem 28.10.
  - Requires classification of simple closed curves on $T^2$ and intersection/linking numbers on the torus boundary.
- **Attempted Route**: Evaluated `consult/AP-section31-first-review-digest.md:22` and `Section31CanonicalConfiguration.lean`.
- **Next Useful Lemma**: `polygon_dichotomy_of_disjoint_carrier` (Moise 28.10).

## 2026-09-22: G023 (`exists_isPLCell_frontier_of_polygon_nullhomotopic`) BLOCKED / SKIPPED

- **Target**: `Section31CanonicalConfiguration:473` (`exists_isPLCell_frontier_of_polygon_nullhomotopic`)
- **Status**: BLOCKED / SKIPPED (missing meridian exclusion and disk bounding on solid torus boundary)
- **Skeleton Location**: `Section31CanonicalConfiguration.lean:473`
- **Blocker Description**:
  - Requires: On $\partial S$, a simple closed curve that is null-homotopic in $S$ and disjoint from a generator carrier bounds a 2-cell on $\partial S$.
  - A null-homotopic class in $S$ excludes the longitudinal component; an essential boundary curve would then be a meridian with linking number $\pm 1$ with the interior generator, ruling out disks avoiding the carrier.
  - The homological linking and intersection tools for curves on solid tori are not yet formal in the library.
- **Attempted Route**: Evaluated `consult/AP-section31-first-review-digest.md:23` and `Section31CanonicalConfiguration.lean`.
- **Next Useful Lemma**: `isPLCell_frontier_of_nullhomotopic_in_solidTorus`.

## 2026-09-22: G024 (`exists_product_coordinates_for_disjoint_essential_polygons`) BLOCKED / SKIPPED

- **Target**: `Section28Annuli:75` (`exists_product_coordinates_for_disjoint_essential_polygons`)
- **Status**: BLOCKED / SKIPPED (missing classification and PL straightening of disjoint essential curves on $T^2$)
- **Skeleton Location**: `Section28Annuli.lean:75`
- **Blocker Description**:
  - Requires: Given $n > 1$ disjoint essential 1-spheres on $\partial S$ of a combinatorial solid torus, finding product coordinates $J \times Q \cong \partial S$ such that each 1-sphere is a slice $J \times \{q_i\}$.
  - Requires the classical surface-topology theorem that any family of pairwise disjoint essential simple closed curves on $T^2$ are isotopic / PL-homeomorphic to parallel standard circles $S^1 \times \{q_i\}$.
  - The classification of curves on surfaces and PL straightening of 1-manifolds on 2-torus are not formalized.
- **Attempted Route**: Evaluated `Section28Annuli.lean` and `CircleArcs.lean`.
- **Next Useful Lemma**: `exists_product_coordinates_of_disjoint_essential_curves_torus`.

## 2026-09-22: G026 (`exists_canonicalTower`) BLOCKED / SKIPPED

- **Target**: `Section32PseudoCell:200` (`exists_canonicalTower`)
- **Status**: BLOCKED / SKIPPED (missing infinite nested solid torus tower with toroidal shell collars in $\mathbb{R}^3$)
- **Skeleton Location**: `Section32PseudoCell.lean:200`
- **Blocker Description**:
  - Requires: Constructing an infinite geometric tower of solid tori $S_i$ and toroidal shells $T_i$ along a non-smooth curve in $\mathbb{R}^3$, avoiding an arbitrary closed set $Z$.
  - Requires infinite geometric sequence of nested solid tori with toroidal shell collars and adjacent general position.
- **Attempted Route**: Surveyed `PseudoCell.lean`, `MoiseChain.lean`, and `consult/AK-section32-first-review-digest.md:13`.
- **Next Useful Lemma**: `exists_nested_torus_tower_of_splittingDisk`.

## 2026-09-22: G027 (`separates_initialSurface`) BLOCKED / SKIPPED

- **Target**: `Section32PseudoCell:214` (`separates_initialSurface`)
- **Status**: BLOCKED / SKIPPED (missing surface separation in 3-manifolds with boundary)
- **Skeleton Location**: `Section32PseudoCell.lean:214`
- **Blocker Description**:
  - Requires: Showing the initial surface constructed from the tower separates $h u$ and $h v$ in $\text{int}(h(C_u \cup C_v))$.
  - Requires surface separation across the dual-cell boundary in a tube.
- **Attempted Route**: Evaluated `Section32PseudoCell.lean` and `consult/AM-section32-second-review-digest.md:8`.
- **Next Useful Lemma**: `separates_of_transverse_surface_in_tube`.

## 2026-09-22: G028 (`exists_descentSequence`) BLOCKED / SKIPPED

- **Target**: `Section32PseudoCell:227` (`exists_descentSequence`)
- **Status**: BLOCKED / SKIPPED (missing 4-step surgery descent machine on infinite tower)
- **Skeleton Location**: `Section32PseudoCell.lean:227`
- **Blocker Description**:
  - Requires: Executing an infinite 4-step surgery descent using `Moise303`, `Moise286`, `Moise267`, and `Moise314`, establishing local eventual stability and preservation of separation.
  - Requires locally finite 4-step surgery descent apparatus on an infinite tower.
- **Attempted Route**: Surveyed `consult/AM-section32-second-review-digest.md:9,21-23`.
- **Next Useful Lemma**: `exists_descentSequence_of_tower`.

## 2026-09-22: G029 (`isOpenTopologicalCell_annularChain`) BLOCKED / SKIPPED

- **Target**: `Section32PseudoCell:254` (`isOpenTopologicalCell_annularChain`)
- **Status**: BLOCKED / SKIPPED (missing annular chain limit cell topology and local 3-ball charts)
- **Skeleton Location**: `Section32PseudoCell.lean:254`
- **Blocker Description**:
  - Requires: Proving the infinite annular chain limit is an open topological 2-cell, locally polyhedral away from $P'$, with closure being the cell plus the rim $h(Dbd)$, and admitting local 3-ball charts.
  - Requires limit cell topology and local 3-ball slicing for infinite annular chains.
- **Attempted Route**: Evaluated `consult/AM-section32-second-review-digest.md:10` and `consult/AK-section32-first-review-digest.md:47-56`.
- **Next Useful Lemma**: `isOpenTopologicalCell_of_annularChain`.

## 2026-09-22: G030 (`exists_compact_connected_to_freeFace`) BLOCKED / SKIPPED

- **Target**: `Section32PseudoCell:273` (`exists_compact_connected_to_freeFace`)
- **Status**: BLOCKED / SKIPPED (missing arc-connectedness of dual cell complement of splitting disk)
- **Skeleton Location**: `Section32PseudoCell.lean:273`
- **Blocker Description**:
  - Requires: Connecting vertex $h v$ to the free face in $h(C_v)$ avoiding $h(D_e)$, which requires arc-connectedness of a PL 3-ball minus a boundary disk.
  - Mathlib and the library do not yet have path-connectedness of $B^3 \setminus D^2$ from an interior point to the boundary.
- **Attempted Route**: Analyzed `IsTube.freeFaceConnected`, `IsTube.dualBall`, and `IsTube.splitMidpoint`. While $v \notin D_e$ and $freeFace \cap D_e = \emptyset$ hold, connecting them inside $C_v \setminus D_e$ lacks the path-connectedness lemma.
- **Next Useful Lemma**: `exists_path_in_ball_avoiding_boundary_disk`.

## 2026-09-22: G031 (`exists_twoComponents_of_pseudoCell`) BLOCKED / SKIPPED

- **Target**: `Section32PseudoCell:282` (`exists_twoComponents_of_pseudoCell`)
- **Status**: BLOCKED / SKIPPED (missing global 3D separation by a proper pseudo-cell in a 3-ball pair)
- **Skeleton Location**: `Section32PseudoCell.lean:282`
- **Blocker Description**:
  - Requires: Proving that a pseudo-cell divides $h(C_u \cup C_v)$ into exactly two connected components $U_1, U_2$ containing $h u$ and $h v$ respectively.
  - Requires local two-sidedness to global component separation in 3-manifolds.
- **Attempted Route**: Evaluated `consult/AK-section32-first-review-digest.md:20` and `Section32PseudoCell.lean`.
- **Next Useful Lemma**: `exists_twoComponents_of_proper_pseudoCell`.

## 2026-09-22: G032 (`exists_edgeCollarFamily`) BLOCKED / SKIPPED

- **Target**: `Section32PseudoCell:311` (`exists_edgeCollarFamily`)
- **Status**: BLOCKED / SKIPPED (missing disjoint regular neighborhood collars for 2-disks in a 3-manifold)
- **Skeleton Location**: `Section32PseudoCell.lean:311`
- **Blocker Description**:
  - Requires: Constructing a family of disjoint edge collars $W_e$ for all edges in a tube, tapering at the centers.
  - Requires joint choice of finitely many disjoint collars for disks in a 3-manifold.
- **Attempted Route**: Evaluated `consult/AK-section32-first-review-digest.md:21` and `PseudoCell.lean`.
- **Next Useful Lemma**: `exists_disjoint_edgeCollars_of_tube`.

## 2026-09-22: G033 (`isHandleDecomposition_of_edgeCollars`) BLOCKED / SKIPPED

- **Target**: `Section32PseudoCell:317` (`isHandleDecomposition_of_edgeCollars`)
- **Status**: BLOCKED / SKIPPED (missing handle decomposition verification for dual cells cut by edge collars)
- **Skeleton Location**: `Section32PseudoCell.lean:317`
- **Blocker Description**:
  - Requires: Verifying that dual cells cut by edge collars form a handle decomposition of the tube $N'$.
  - Requires assembling disjoint collars, connected complements, and side labels into `IsHandleDecompositionOfTube`.
- **Attempted Route**: Evaluated `consult/AK-section32-first-review-digest.md:22` and `PseudoCell.lean`.
- **Next Useful Lemma**: `isHandleDecomposition_of_tube_dualCells`.

## 2026-09-22: G034 (`exists_generalPosition_ball_pseudoCell`) BLOCKED / SKIPPED

- **Target**: `Section32PseudoCell:340` (`exists_generalPosition_ball_pseudoCell`)
- **Status**: BLOCKED / SKIPPED (missing small ball in general position with wild pseudo-cell)
- **Skeleton Location**: `Section32PseudoCell.lean:340`
- **Blocker Description**:
  - Requires: Constructing a small PL 3-ball around the center point $P$ in general position with the pseudo-cell, with the 2-cell $D_c$ controlled inside $B(P, \delta)$.
  - Requires general position transversality near a non-PL point of a pseudo-cell.
- **Attempted Route**: Evaluated `consult/AM-section32-second-review-digest.md:11` and `Section32PseudoCell.lean`.
- **Next Useful Lemma**: `exists_generalPosition_ball_of_pseudoCell`.

## 2026-09-22: G035 (`exists_reducedDisk_of_crossesPseudoCell`) BLOCKED / SKIPPED

- **Target**: `Section32PseudoCell:347` (`exists_reducedDisk_of_crossesPseudoCell`)
- **Status**: BLOCKED / SKIPPED (missing cut-and-paste 2-disk surgery in pseudo-cell complement)
- **Skeleton Location**: `Section32PseudoCell.lean:347`
- **Blocker Description**:
  - Requires: Constructing a reduced replacement disk inside $\Omega$ cleaning intersections with the pseudo-cell.
  - Requires 2-disk surgery in pseudo-cell complement with support in $\Omega$.
- **Attempted Route**: Evaluated `consult/AM-section32-second-review-digest.md:12` and `Section32PseudoCell.lean`.
- **Next Useful Lemma**: `exists_reducedDisk_of_crossesPseudoCell`.

## 2026-09-22: G036 (`exists_section33TubeFrame`) BLOCKED / SKIPPED

- **Target**: `Section33Approximation:181` (`exists_section33TubeFrame`)
- **Status**: BLOCKED / SKIPPED (missing fine metric subdivision and derived tube neighborhood with diameter control)
- **Skeleton Location**: `Section33Approximation.lean:181`
- **Blocker Description**:
  - Requires: For a 1-complex $L$ with no 1-valent vertices, embedded in open $U \subseteq \mathbb{R}^3$, constructing a 3-manifold $T$ with boundary, subdivision $L'$, and tube structure of derived neighborhood inside $U$, with dual cells of diameter $< \epsilon/4$.
  - Requires controlled diameter subdivision of 3-manifolds containing a 1-complex.
- **Attempted Route**: Evaluated `DerivedNeighborhood.lean` and `DualCells.lean`.
- **Next Useful Lemma**: `exists_fine_subdivision_tube_neighborhood`.

## 2026-09-22: G037 (`exists_isPolyhedralTubeNeighborhood`) BLOCKED / SKIPPED

- **Target**: `Section33Approximation:201` (`exists_isPolyhedralTubeNeighborhood`)
- **Status**: BLOCKED / SKIPPED (missing polyhedral tube neighborhood construction from handle decomposition)
- **Skeleton Location**: `Section33Approximation.lean:201`
- **Blocker Description**:
  - Requires: Constructing a polyhedral tube neighborhood $X_K$ from a handle decomposition of a tube in $\mathbb{R}^3$.
- **Attempted Route**: Evaluated `PolyhedralTubeNeighborhood.lean` and `PseudoCell.lean`.
- **Next Useful Lemma**: `exists_polyhedral_tube_neighborhood_of_handleDecomposition`.

## 2026-09-22: G038 (`exists_hasSinglePolygonTraces`) BLOCKED / SKIPPED

- **Target**: `Section33Approximation:207` (`exists_hasSinglePolygonTraces`)
- **Status**: BLOCKED / SKIPPED (missing single polygon trace refinement for polyhedral tube neighborhoods)
- **Skeleton Location**: `Section33Approximation.lean:207`
- **Blocker Description**:
  - Requires: Refining $X_K$ so that the intersection of $\partial X_K$ with each pseudo-cell $E_c$ is a single polygon.
- **Attempted Route**: Evaluated `Section33Approximation.lean`.
- **Next Useful Lemma**: `refine_polyhedral_tube_single_traces`.

## 2026-09-22: G039 (`exists_hasConnectedHandlePieces`) BLOCKED / SKIPPED

- **Target**: `Section33Approximation:215` (`exists_hasConnectedHandlePieces`)
- **Status**: BLOCKED / SKIPPED (missing connected handle piece refinement on polyhedral tube boundary)
- **Skeleton Location**: `Section33Approximation.lean:215`
- **Blocker Description**:
  - Requires: Refining $X_K$ so that the pieces $A_K(v) = C_{pp}(v) \cap \partial X_K$ are connected 2-complexes.
- **Attempted Route**: Evaluated `Section33Approximation.lean`.
- **Next Useful Lemma**: `refine_polyhedral_tube_connected_pieces`.

## 2026-09-22: G040 (`exists_hasNoHandleLoopTheoremDisk`) BLOCKED / SKIPPED

- **Target**: `Section33Approximation:227` (`exists_hasNoHandleLoopTheoremDisk`)
- **Status**: BLOCKED / SKIPPED (missing handle loop theorem disk elimination via 2-disk surgery)
- **Skeleton Location**: `Section33Approximation.lean:227`
- **Blocker Description**:
  - Requires: Refining $X_K$ so that no handle piece contains a Loop Theorem disk.
- **Attempted Route**: Evaluated `Section33Approximation.lean`.
- **Next Useful Lemma**: `refine_polyhedral_tube_no_loop_disks`.

## 2026-09-22: G041 (`section33_disk_meets_graph`) BLOCKED / SKIPPED

- **Target**: `Section33Approximation:240` (`section33_disk_meets_graph`)
- **Status**: BLOCKED / SKIPPED (missing homological intersection / linking argument for spanning disk)
- **Skeleton Location**: `Section33Approximation.lean:240`
- **Blocker Description**:
  - Requires: Proving Moise Lemma 8: a disk in a handle piece meeting the pseudo-cell only along its boundary circle must meet the graph $h '' K$.
- **Attempted Route**: Evaluated `Section33Approximation.lean`.
- **Next Useful Lemma**: `disk_spans_pseudoCell_meets_graph`.

## 2026-09-22: G042 (`section33_tube_product`) BLOCKED / SKIPPED

- **Target**: `Section33Approximation:273` (`section33_tube_product`)
- **Status**: BLOCKED / SKIPPED (missing embedding and range properties of barycentric rays from derived neighborhood frontier)
- **Skeleton Location**: `Section33Approximation.lean:273`
- **Blocker Description**:
  - Requires: Product structure $\text{interior}(N') \setminus h '' K \cong \text{frontier}(N) \times (0, 1)$.
  - Blocked on unproven ray embedding and range properties (`H01` / `H02` in `DerivedNeighborhoodComplement.lean`).
- **Attempted Route**: Evaluated `DerivedNeighborhoodRay.lean`.
- **Next Useful Lemma**: `DerivedNeighborhoodComplement.isEmbedding_derivedNeighborhoodRay`.

## 2026-09-22: G043 (`section33_fundamentalGroup_map_bijective`) BLOCKED / SKIPPED

- **Target**: `Section33Approximation:277` (`section33_fundamentalGroup_map_bijective`)
- **Status**: BLOCKED / SKIPPED (missing Loop Theorem application to tube boundary $\pi_1$ isomorphism)
- **Skeleton Location**: `Section33Approximation.lean:277`
- **Blocker Description**:
  - Requires: Proving Moise Lemma 10: inclusion $\partial X_K \to N' \setminus h '' K$ induces an isomorphism on $\pi_1$.
- **Attempted Route**: Evaluated `Section33Approximation.lean`.
- **Next Useful Lemma**: `fundamentalGroup_map_bijective_of_no_loop_theorem_disk`.

## 2026-09-22: G044 (`section33_faceEulerChar_handlePiece`) BLOCKED / SKIPPED

- **Target**: `Section33Approximation:292` (`section33_faceEulerChar_handlePiece`)
- **Status**: BLOCKED / SKIPPED (missing Euler characteristic calculation from $\pi_1$ isomorphism)
- **Skeleton Location**: `Section33Approximation.lean:292`
- **Blocker Description**:
  - Requires: Proving Moise Lemma 11: Euler characteristic of each handle piece $A_K(v)$ is $2 - \text{deg}(v)$.
- **Attempted Route**: Evaluated `Section33Approximation.lean`.
- **Next Useful Lemma**: `faceEulerChar_handlePiece_of_fundamentalGroup_iso`.

## 2026-09-22: G045 (`exists_section33BoundaryMatch`) BLOCKED / SKIPPED

- **Target**: `Section33Approximation:306` (`exists_section33BoundaryMatch`)
- **Status**: BLOCKED / SKIPPED (missing surface homeomorphism classification from Euler characteristic and boundary components)
- **Skeleton Location**: `Section33Approximation.lean:306`
- **Blocker Description**:
  - Requires: Proving Moise Lemma 12: matching $\partial N$ with $\partial X_K$ via a PL homeomorphism respecting handle pieces and edge disks.
- **Attempted Route**: Evaluated `Section33Approximation.lean`.
- **Next Useful Lemma**: `exists_isPLHomeomorphOn_of_eulerChar_and_boundary_match`.

## 2026-09-22: G046 (`exists_section33Extension`) BLOCKED / SKIPPED

- **Target**: `Section33Approximation:321` (`exists_section33Extension`)
- **Status**: BLOCKED / SKIPPED (missing 3D polyhedral approximation extension theorem from boundary homeomorphism)
- **Skeleton Location**: `Section33Approximation.lean:321`
- **Blocker Description**:
  - Requires: Extending boundary match $g : \partial N \to \partial X_K$ to a PL approximation of the tube embedding $h$.
- **Attempted Route**: Evaluated `Section33Approximation.lean`.
- **Next Useful Lemma**: `exists_pl_approximation_of_boundary_homeomorph`.

## 2026-09-22: G047 (`exists_homeomorph_smooth_disks_of_isClosedEmbedding`) BLOCKED / SKIPPED

- **Target**: `PLSmoothingCompact:173` (`exists_homeomorph_smooth_disks_of_isClosedEmbedding`)
- **Status**: BLOCKED / SKIPPED (missing 2D smooth approximation of topological disks in 2-manifolds)
- **Skeleton Location**: `PLSmoothingCompact.lean:173`
- **Blocker Description**:
  - Requires: Smoothing two topological disks in the boundary of a smooth 3-manifold with boundary.
- **Attempted Route**: Evaluated `PLSmoothingCompact.lean`.
- **Next Useful Lemma**: `exists_isSmoothEmbedding_disk_of_isClosedEmbedding`.

## 2026-09-22: G048 (`isSmoothHandleStage_adjunction_one`) BLOCKED / SKIPPED

- **Target**: `PLSmoothingCompact:187` (`isSmoothHandleStage_adjunction_one`)
- **Status**: BLOCKED / SKIPPED (missing smooth 1-handle attachment theorem for manifolds with boundary)
- **Skeleton Location**: `PLSmoothingCompact.lean:187`
- **Blocker Description**:
  - Requires: Proving smooth 1-handle adjunction yields a smooth handle stage.
- **Attempted Route**: Evaluated `PLSmoothingCompact.lean`.
- **Next Useful Lemma**: `isSmoothHandleStage_adjunction_one_handle`.

## 2026-09-22: G049 (`exists_homeomorph_smooth_annulus_of_isClosedEmbedding`) BLOCKED / SKIPPED

- **Target**: `PLSmoothingCompact:205` (`exists_homeomorph_smooth_annulus_of_isClosedEmbedding`)
- **Status**: BLOCKED / SKIPPED (missing 2D smooth approximation of topological annuli in 2-manifolds)
- **Skeleton Location**: `PLSmoothingCompact.lean:205`
- **Blocker Description**:
  - Requires: Smoothing an embedded annulus in the boundary of a smooth 3-manifold with boundary.
- **Attempted Route**: Evaluated `PLSmoothingCompact.lean`.
- **Next Useful Lemma**: `exists_isSmoothEmbedding_annulus_of_isClosedEmbedding`.

## 2026-09-22: G050 (`isSmoothHandleStage_adjunction_two`) BLOCKED / SKIPPED

- **Target**: `PLSmoothingCompact:218` (`isSmoothHandleStage_adjunction_two`)
- **Status**: BLOCKED / SKIPPED (missing smooth 2-handle attachment theorem for manifolds with boundary)
- **Skeleton Location**: `PLSmoothingCompact.lean:218`
- **Blocker Description**:
  - Requires: Proving smooth 2-handle adjunction yields a smooth handle stage.
- **Attempted Route**: Evaluated `PLSmoothingCompact.lean`.
- **Next Useful Lemma**: `isSmoothHandleStage_adjunction_two_handle`.

## 2026-09-22: G051 (`exists_isSmoothEmbedding_sphere_of_isClosedEmbedding`) BLOCKED / SKIPPED

- **Target**: `PLSmoothingCompact:235` (`exists_isSmoothEmbedding_sphere_of_isClosedEmbedding`)
- **Status**: BLOCKED / SKIPPED (missing 2D smooth approximation of topological 2-spheres in 2-manifolds)
- **Skeleton Location**: `PLSmoothingCompact.lean:235`
- **Blocker Description**:
  - Requires: Smoothing an embedded 2-sphere in the boundary of a smooth 3-manifold with boundary.
- **Attempted Route**: Evaluated `PLSmoothingCompact.lean`.
- **Next Useful Lemma**: `exists_isSmoothEmbedding_sphere_of_isClosedEmbedding`.

## 2026-09-22: G052 (`isSmoothHandleStage_adjunction_three`) BLOCKED / SKIPPED

- **Target**: `PLSmoothingCompact:244` (`isSmoothHandleStage_adjunction_three`)
- **Status**: BLOCKED / SKIPPED (missing smooth 3-handle attachment theorem for manifolds with boundary)
- **Skeleton Location**: `PLSmoothingCompact.lean:244`
- **Blocker Description**:
  - Requires: Proving smooth 3-handle adjunction yields a smooth handle stage.
- **Attempted Route**: Evaluated `PLSmoothingCompact.lean`.
- **Next Useful Lemma**: `isSmoothHandleStage_adjunction_three_handle`.

## 2026-09-22: G053 (`exists_bicollar_complement_with_boundary_collars`) BLOCKED / SKIPPED

- **Target**: `ExtendedLoopTheoremOrientable:60` (`exists_bicollar_complement_with_boundary_collars`)
- **Status**: BLOCKED / SKIPPED (missing bicollar neighborhood theorem for two-sided surfaces in 3-manifolds)
- **Skeleton Location**: `ExtendedLoopTheoremOrientable.lean:60`
- **Blocker Description**:
  - Requires: Bicollar neighborhood of two-sided closed 2-manifold in interior of 3-manifold with boundary, and boundary collars for cut manifold.
- **Attempted Route**: Evaluated `ExtendedLoopTheoremOrientable.lean`.
- **Next Useful Lemma**: `exists_bicollar_neighborhood_of_twoSided`.

## 2026-09-22: G054 (`exists_nontrivial_boundary_loop_of_bicollar_complement`) BLOCKED / SKIPPED

- **Target**: `ExtendedLoopTheoremOrientable:92` (`exists_nontrivial_boundary_loop_of_bicollar_complement`)
- **Status**: BLOCKED / SKIPPED (missing loop lifting and boundary nontriviality in bicollar complement)
- **Skeleton Location**: `ExtendedLoopTheoremOrientable.lean:92`
- **Blocker Description**:
  - Requires: Finding a nontrivial boundary loop in the cut manifold from a loop killed in the ambient manifold.
- **Attempted Route**: Evaluated `ExtendedLoopTheoremOrientable.lean`.
- **Next Useful Lemma**: `exists_boundary_loop_of_killed_loop_bicollar`.

## 2026-09-22: G055 (`exists_annular_split_ball`) BLOCKED / SKIPPED

- **Target**: `Section30Separation:60` (`exists_annular_split_ball`)
- **Status**: BLOCKED / SKIPPED (missing joint PL regular-neighborhood construction respecting two disks)
- **Skeleton Location**: `Section30Separation.lean:60`
- **Blocker Description**:
  - Requires: Moise Theorem 30.3: Splitting an annular neighborhood of a disk while preserving separation.
- **Attempted Route**: Evaluated `Section30Separation.lean`.
- **Next Useful Lemma**: `exists_annular_split_ball_regularNeighborhood`.

## 2026-09-22: G056 (`exists_section34CutFrame`) BLOCKED / SKIPPED

- **Target**: `ControlledGraphNeighborhood:259` (`exists_section34CutFrame`)
- **Status**: BLOCKED / SKIPPED (missing cut frame construction for 1-complex in 3-manifold with boundary)
- **Skeleton Location**: `ControlledGraphNeighborhood.lean:259`
- **Blocker Description**:
  - Requires: Section 34 cut frame construction.
- **Attempted Route**: Evaluated `ControlledGraphNeighborhood.lean`.
- **Next Useful Lemma**: `exists_section34CutFrame_of_complex`.

## 2026-09-22: G057 (`exists_section34VertexPreparation`) BLOCKED / SKIPPED

- **Target**: `ControlledGraphNeighborhood:289` (`exists_section34VertexPreparation`)
- **Status**: BLOCKED / SKIPPED (missing vertex preparation for cut frame)
- **Skeleton Location**: `ControlledGraphNeighborhood.lean:289`
- **Blocker Description**:
  - Requires: Section 34 vertex preparation for cut frame.
- **Attempted Route**: Evaluated `ControlledGraphNeighborhood.lean`.
- **Next Useful Lemma**: `exists_section34VertexPreparation_of_frame`.

## 2026-09-22: G058 (`exists_section34PiercingPackage`) BLOCKED / SKIPPED

- **Target**: `ControlledGraphNeighborhood:357` (`exists_section34PiercingPackage`)
- **Status**: BLOCKED / SKIPPED (missing piercing package construction for edges)
- **Skeleton Location**: `ControlledGraphNeighborhood.lean:357`
- **Blocker Description**:
  - Requires: Section 34 piercing package construction for edges.
- **Attempted Route**: Evaluated `ControlledGraphNeighborhood.lean`.
- **Next Useful Lemma**: `exists_section34PiercingPackage_of_frame`.

## 2026-09-22: G059 (`exists_section34ProtectedCircleRemovalStep`) BLOCKED / SKIPPED

- **Target**: `ControlledGraphNeighborhood:375` (`exists_section34ProtectedCircleRemovalStep`)
- **Status**: BLOCKED / SKIPPED (missing protected circle removal single step on piercing disk)
- **Skeleton Location**: `ControlledGraphNeighborhood.lean:375`
- **Blocker Description**:
  - Requires: Protected circle removal single step.
- **Attempted Route**: Evaluated `ControlledGraphNeighborhood.lean`.
- **Next Useful Lemma**: `exists_protectedCircleRemovalStep`.

## 2026-09-22: G060 (`exists_section34ProtectedCircleRemoval`) BLOCKED / SKIPPED

- **Target**: `ControlledGraphNeighborhood:505` (`exists_section34ProtectedCircleRemoval`)
- **Status**: BLOCKED / SKIPPED (missing finite induction for protected circle removal)
- **Skeleton Location**: `ControlledGraphNeighborhood.lean:505`
- **Blocker Description**:
  - Requires: Protected circle removal complete package.
- **Attempted Route**: Evaluated `ControlledGraphNeighborhood.lean`.
- **Next Useful Lemma**: `exists_protectedCircleRemoval_complete`.

## 2026-09-22: G061 (`exists_section34DeletedBalls`) BLOCKED / SKIPPED

- **Target**: `ControlledGraphNeighborhood:521` (`exists_section34DeletedBalls`)
- **Status**: BLOCKED / SKIPPED (missing deleted balls around vertices of graph)
- **Skeleton Location**: `ControlledGraphNeighborhood.lean:521`
- **Blocker Description**:
  - Requires: Constructing small deleted ball neighborhoods around graph vertices.
- **Attempted Route**: Evaluated `ControlledGraphNeighborhood.lean`.
- **Next Useful Lemma**: `exists_deletedBalls_of_piercing`.

## 2026-09-22: G062 (`exists_section34EdgeMatching`) BLOCKED / SKIPPED

- **Target**: `ControlledGraphNeighborhood:547` (`exists_section34EdgeMatching`)
- **Status**: BLOCKED / SKIPPED (missing edge matching between piercing packages)
- **Skeleton Location**: `ControlledGraphNeighborhood.lean:547`
- **Blocker Description**:
  - Requires: Edge matching and gluing of piercing packages across common vertices.
- **Attempted Route**: Evaluated `ControlledGraphNeighborhood.lean`.
- **Next Useful Lemma**: `exists_edgeMatching_of_piercingPackages`.

## 2026-09-22: G063 (`exists_section34FaceBalls`) BLOCKED / SKIPPED

- **Target**: `Section34Normalization:460` (`exists_section34FaceBalls`)
- **Status**: BLOCKED / SKIPPED (missing face ball collection in general position)
- **Skeleton Location**: `Section34Normalization.lean:460`
- **Blocker Description**:
  - Requires: Constructing face ball collection in general position with 2-complex.
- **Attempted Route**: Evaluated `Section34Normalization.lean`.
- **Next Useful Lemma**: `exists_section34FaceBalls_of_frame`.

## 2026-09-22: G064 (`exists_section34Compression`) BLOCKED / SKIPPED

- **Target**: `Section34Normalization:470` (`exists_section34Compression`)
- **Status**: BLOCKED / SKIPPED (missing disk compression operation on 2-complex)
- **Skeleton Location**: `Section34Normalization.lean:470`
- **Blocker Description**:
  - Requires: Section 34 disk compression on 2-complex.
- **Attempted Route**: Evaluated `Section34Normalization.lean`.
- **Next Useful Lemma**: `exists_section34Compression_of_faceBalls`.

## 2026-09-22: G065 (`exists_section34BigonSlide`) BLOCKED / SKIPPED

- **Target**: `Section34Normalization:491` (`exists_section34BigonSlide`)
- **Status**: BLOCKED / SKIPPED (missing bigon slide simplification of curve intersections)
- **Skeleton Location**: `Section34Normalization.lean:491`
- **Blocker Description**:
  - Requires: Bigon slide operation reducing intersection complexity.
- **Attempted Route**: Evaluated `Section34Normalization.lean`.
- **Next Useful Lemma**: `exists_section34BigonSlide_of_curves`.

## 2026-09-22: G066 (`exists_section34TerminalFaceBalls`) BLOCKED / SKIPPED

- **Target**: `Section34Normalization:512` (`exists_section34TerminalFaceBalls`)
- **Status**: BLOCKED / SKIPPED (missing terminal face ball stabilization)
- **Skeleton Location**: `Section34Normalization.lean:512`
- **Blocker Description**:
  - Requires: Stabilization of face balls after all compressions and slides.
- **Attempted Route**: Evaluated `Section34Normalization.lean`.
- **Next Useful Lemma**: `exists_section34TerminalFaceBalls_of_stabilization`.

## 2026-09-22: G067 (`section34Trace_of_noOperation`) BLOCKED / SKIPPED

- **Target**: `Section34Normalization:556` (`section34Trace_of_noOperation`)
- **Status**: BLOCKED / SKIPPED (missing geometric characterization of irreducible curve configurations)
- **Skeleton Location**: `Section34Normalization.lean:556`
- **Blocker Description**:
  - Requires: Trace properties when no compression or bigon slide applies.
- **Attempted Route**: Evaluated `Section34Normalization.lean`.
- **Next Useful Lemma**: `section34Trace_characterization_of_irreducible`.

## 2026-09-22: G068 (`section34TraceCircle_homologyMap_ne_zero`) BLOCKED / SKIPPED

- **Target**: `Section34Normalization:572` (`section34TraceCircle_homologyMap_ne_zero`)
- **Status**: BLOCKED / SKIPPED (missing homological non-triviality of irreducible trace circles)
- **Skeleton Location**: `Section34Normalization.lean:572`
- **Blocker Description**:
  - Requires: Proving non-zero homology map for trace circle.
- **Attempted Route**: Evaluated `Section34Normalization.lean`.
- **Next Useful Lemma**: `traceCircle_homology_ne_zero`.

## 2026-09-22: G069 (`exists_section34FaceDisks`) BLOCKED / SKIPPED

- **Target**: `Section34Terminal:158` (`exists_section34FaceDisks`)
- **Status**: BLOCKED / SKIPPED (missing construction of terminal face disks)
- **Skeleton Location**: `Section34Terminal.lean:158`
- **Blocker Description**:
  - Requires: Constructing terminal face disks.
- **Attempted Route**: Evaluated `Section34Terminal.lean`.
- **Next Useful Lemma**: `exists_section34FaceDisks_of_terminalBalls`.

## 2026-09-22: G070 (`exists_section34ResidualBalls`) BLOCKED / SKIPPED

- **Target**: `Section34Terminal:167` (`exists_section34ResidualBalls`)
- **Status**: BLOCKED / SKIPPED (missing residual ball decomposition of terminal complement)
- **Skeleton Location**: `Section34Terminal.lean:167`
- **Blocker Description**:
  - Requires: Residual ball decomposition of terminal complement.
- **Attempted Route**: Evaluated `Section34Terminal.lean`.
- **Next Useful Lemma**: `exists_section34ResidualBalls_of_faceDisks`.

## 2026-09-22: G071 (`section34SourceFace_iff_cutLe`) BLOCKED / SKIPPED

- **Target**: `Section34Terminal:179` (`section34SourceFace_iff_cutLe`)
- **Status**: BLOCKED / SKIPPED (missing equivalence between source faces and cut complexity order)
- **Skeleton Location**: `Section34Terminal.lean:179`
- **Blocker Description**:
  - Requires: Proving source face iff cut $\le$.
- **Attempted Route**: Evaluated `Section34Terminal.lean`.
- **Next Useful Lemma**: `sourceFace_iff_cutLe_proof`.

## 2026-09-22: G072 (`section34TargetRecognition`) BLOCKED / SKIPPED

- **Target**: `Section34Terminal:185` (`section34TargetRecognition`)
- **Status**: BLOCKED / SKIPPED (missing target manifold recognition from terminal data)
- **Skeleton Location**: `Section34Terminal.lean:185`
- **Blocker Description**:
  - Requires: Recognition of target manifold from terminal face disks and residual balls.
- **Attempted Route**: Evaluated `Section34Terminal.lean`.
- **Next Useful Lemma**: `targetRecognition_of_terminal_data`.

## 2026-09-22: G073 (`exists_compactCutAndGraph`) BLOCKED / SKIPPED

- **Target**: `Section34Compact:929` (`exists_compactCutAndGraph`)
- **Status**: BLOCKED / SKIPPED (missing compact cut and graph construction)
- **Skeleton Location**: `Section34Compact.lean:929`
- **Blocker Description**:
  - Requires: Constructing compact cut and graph in compact 3-manifold.
- **Attempted Route**: Evaluated `Section34Compact.lean`.
- **Next Useful Lemma**: `exists_compactCutAndGraph_proof`.

## 2026-09-22: G074 (`exists_compactFaceShellBalls`) BLOCKED / SKIPPED

- **Target**: `Section34Compact:948` (`exists_compactFaceShellBalls`)
- **Status**: BLOCKED / SKIPPED (missing compact face shell balls construction)
- **Skeleton Location**: `Section34Compact.lean:948`
- **Blocker Description**:
  - Requires: Constructing compact face shell balls.
- **Attempted Route**: Evaluated `Section34Compact.lean`.
- **Next Useful Lemma**: `exists_compactFaceShellBalls_proof`.

## 2026-09-22: G075 (`exists_compactFaceBallsGeneralPosition`) BLOCKED / SKIPPED

- **Target**: `Section34Compact:960` (`exists_compactFaceBallsGeneralPosition`)
- **Status**: BLOCKED / SKIPPED (missing compact face balls general position)
- **Skeleton Location**: `Section34Compact.lean:960`
- **Blocker Description**:
  - Requires: Constructing compact face balls in general position.
- **Attempted Route**: Evaluated `Section34Compact.lean`.
- **Next Useful Lemma**: `exists_compactFaceBallsGeneralPosition_proof`.

## 2026-09-22: G076 (`compactTraceHomology`) BLOCKED / SKIPPED

- **Target**: `Section34Compact:988` (`compactTraceHomology`)
- **Status**: BLOCKED / SKIPPED (missing compact trace homology)
- **Skeleton Location**: `Section34Compact.lean:988`
- **Blocker Description**:
  - Requires: Proving compact trace homology non-triviality.
- **Attempted Route**: Evaluated `Section34Compact.lean`.
- **Next Useful Lemma**: `compactTraceHomology_proof`.

## 2026-09-22: G077 (`exists_compactBigonSlide`) BLOCKED / SKIPPED

- **Target**: `Section34Compact:1025` (`exists_compactBigonSlide`)
- **Status**: BLOCKED / SKIPPED (missing compact bigon slide)
- **Skeleton Location**: `Section34Compact.lean:1025`
- **Blocker Description**:
  - Requires: Constructing compact bigon slide operation.
- **Attempted Route**: Evaluated `Section34Compact.lean`.
- **Next Useful Lemma**: `exists_compactBigonSlide_proof`.

## 2026-09-22: G078 (`compactTrace_of_noOperation`) BLOCKED / SKIPPED

- **Target**: `Section34Compact:1045` (`compactTrace_of_noOperation`)
- **Status**: BLOCKED / SKIPPED (missing compact trace of no operation)
- **Skeleton Location**: `Section34Compact.lean:1045`
- **Blocker Description**:
  - Requires: Proving compact trace properties when no operation applies.
- **Attempted Route**: Evaluated `Section34Compact.lean`.
- **Next Useful Lemma**: `compactTrace_of_noOperation_proof`.

## 2026-09-22: G079 (`exists_compactFaceDisks`) BLOCKED / SKIPPED

- **Target**: `Section34Compact:1060` (`exists_compactFaceDisks`)
- **Status**: BLOCKED / SKIPPED (missing compact face disks construction)
- **Skeleton Location**: `Section34Compact.lean:1060`
- **Blocker Description**:
  - Requires: Constructing compact face disks.
- **Attempted Route**: Evaluated `Section34Compact.lean`.
- **Next Useful Lemma**: `exists_compactFaceDisks_proof`.

## 2026-09-22: G080 (`exists_compactResidualBalls`) BLOCKED / SKIPPED

- **Target**: `Section34Compact:1081` (`exists_compactResidualBalls`)
- **Status**: BLOCKED / SKIPPED (missing compact residual balls construction)
- **Skeleton Location**: `Section34Compact.lean:1081`
- **Blocker Description**:
  - Requires: Constructing compact residual balls.
- **Attempted Route**: Evaluated `Section34Compact.lean`.
- **Next Useful Lemma**: `exists_compactResidualBalls_proof`.

## 2026-09-22: G081 (`compactSourceFace_iff_cutLe`) BLOCKED / SKIPPED

- **Target**: `Section34Compact:1107` (`compactSourceFace_iff_cutLe`)
- **Status**: BLOCKED / SKIPPED (missing compact source face iff cut $\le$)
- **Skeleton Location**: `Section34Compact.lean:1107`
- **Blocker Description**:
  - Requires: Proving compact source face iff cut $\le$.
- **Attempted Route**: Evaluated `Section34Compact.lean`.
- **Next Useful Lemma**: `compactSourceFace_iff_cutLe_proof`.

## 2026-09-22: G082 (`compactTargetRecognition`) BLOCKED / SKIPPED

- **Target**: `Section34Compact:1111` (`compactTargetRecognition`)
- **Status**: BLOCKED / SKIPPED (missing compact target recognition)
- **Skeleton Location**: `Section34Compact.lean:1111`
- **Blocker Description**:
  - Requires: Proving compact target recognition.
- **Attempted Route**: Evaluated `Section34Compact.lean`.
- **Next Useful Lemma**: `compactTargetRecognition_proof`.

## 2026-09-22: G083 (`isPLBoundaryTubeProducer_double`) BLOCKED / SKIPPED

- **Target**: `DescentStepOrientable:234` (`isPLBoundaryTubeProducer_double`)
- **Status**: BLOCKED / SKIPPED (missing boundary tube producer in double of 3-manifold)
- **Skeleton Location**: `DescentStepOrientable.lean:234`
- **Blocker Description**:
  - Requires: Constructing a boundary tube producer in the double of a 3-manifold with boundary.
- **Attempted Route**: Evaluated `DescentStepOrientable.lean`.
- **Next Useful Lemma**: `isPLBoundaryTubeProducer_double_proof`.

## 2026-09-22: G084 (`NormalSystem.exists_boundaryNeighborhood_realization`) PASSED

- **Target**: `DescentStepOrientable:244` (`NormalSystem.exists_boundaryNeighborhood_realization`)
- **Status**: PASSED
- **Skeleton Location**: `DescentStepOrientable.lean:244`
- **Module**: `DifferentialGeometry.Topology.PiecewiseLinear.BoundaryNeighborhoodRealization`
- **Source File**: `DifferentialGeometry/Topology/PiecewiseLinear/BoundaryNeighborhoodRealization.lean`
- **SHA256**: `FC6A5392CE7947F2D6DC626CB8DE6DFC885574F88CFEE4A4988E4288F36FD06F`
- **Checkpoint Directory**: `C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-d\gemini-batch\checkpoints\G084-boundary-neighborhood-realization-20260922T2050506669699Z`
- **Verification Details**:
  - Zero errors, zero warnings.
  - All 13 linters passed.
  - Verified by `checker.ps1` and `GEMINI_BATCH_CHECKPOINT.ps1`.
- **Proof Strategy**:
  - The map `ρ y := ⟨ι (y : E), ...⟩` from `S.boundaryNeighborhoodSpace` to `(double 3 S.manifoldComplex).space` is well-defined because `S.boundaryNeighborhood.space ⊆ S.manifoldComplex.space` and `ι` maps `S.manifoldComplex.space` to `(double 3 S.manifoldComplex).space`.
  - `ρ` is continuous by `hι.2.1.continuousOn.comp_continuous continuous_subtype_val` and `Continuous.codRestrict`.
  - `ρ` is injective by `hι.1.injOn`.
  - `S.boundaryNeighborhoodSpace` is compact (`(isPolyhedron_space S.boundaryNeighborhood).isCompact`) and `(double 3 S.manifoldComplex).space` is Hausdorff (`T2Space`), so `ρ` is a closed embedding and hence an embedding (`IsEmbedding ρ`).
  - `B ⊆ Set.range ρ` holds by definition of `B = Subtype.val ⁻¹' (ι '' S.boundaryNeighborhood.space)`.
  - For $z \in \mathrm{frontier}(D.\mathrm{domain})$, $D.\mathrm{boundary}(z) \in B \subseteq \mathrm{range}(\rho)$ selects $f(z)$ via `Classical.choose`.
  - `f` is continuous by `hρ.isInducing.continuous_iff.mpr` since $\rho \circ f = D.\mathrm{boundary}$ is continuous.
- **Imports**:
  - `DifferentialGeometry.Topology.PiecewiseLinear.BoundaryDouble`
  - `DifferentialGeometry.Topology.PiecewiseLinear.Combinatorial`
  - `DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhood`
  - `DifferentialGeometry.Topology.PiecewiseLinear.Gluing`
  - `DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularCell`
  - `DifferentialGeometry.Topology.PiecewiseLinear.PiecewiseAffine`
  - `DifferentialGeometry.Topology.PiecewiseLinear.Polyhedra`
- **Public Declarations**:
  - `NormalSystem.exists_boundaryNeighborhood_realization`
- **Axioms**: `propext`, `Classical.choice`, `Quot.sound`

## 2026-09-22: G085 (`exists_adaptedCleanCap_of_disjoint_innermost_cleanDisk`) BLOCKED / SKIPPED

- **Target**: `DescentStepOrientable:151` (`exists_adaptedCleanCap_of_disjoint_innermost_cleanDisk`)
- **Status**: BLOCKED / SKIPPED (missing innermost clean disk cap surgery and transverse push-off in regular neighborhood)
- **Skeleton Location**: `DescentStepOrientable.lean:151`
- **Blocker Description**:
  - Requires: Given normal singular cell data $hD$, a non-boundary branch $c$ with branch preimage $J \cup T$ (disjoint 1-spheres), innermost clean disk $Q$ with $\partial Q = J$, and disk $E$ with $\partial E = T$ and PL homeomorphism $k : E \to Q$, constructing an enlarged ball $E' \supset E$ and an adapted singular 2-cell $\Delta : E' \to M$ such that $\Delta$ is injective on $E'$, $\Delta(E') \subseteq V$, $\Delta = D$ on $\partial E'$, and $\Delta(E') \cap D(D.\text{domain}) = D(\partial E')$.
  - The mathematical proof requires Dehn lemma / Loop theorem surgery apparatus in 3-manifolds:
    1. Replacing the disk $E$ along the second component $T$ of the branch preimage with an embedded "clean cap" $\Delta(E')$ that meets $D(D.\text{domain})$ only along its boundary.
    2. Constructing a parallel push-off of $Q$ inside a small regular neighborhood $V$ of $D(Q)$ in $M$.
    3. Ensuring that the cap is locally injective and globally disjoint from all other sheets of $D$ outside $\partial E'$ (avoiding self-intersections and mutual intersections).
    4. Constructing the domain $E'$ as a PL 2-ball slightly larger than $E$ in $\mathbb{R}^2$ such that the collar $E' \setminus E$ contains no double points of $D$.
    5. Gluing the PL map $\Delta$ using chart-level transverse push-offs in the normal bundle / local product neighborhood of $D(Q)$.
  - The regular neighborhood push-off and clean collar apparatus for singular 2-cells are not available in the library.
- **Attempted Route**: Evaluated `DescentStepOrientable.lean` and `LoopTheorem/LemmaTwoOrientable.lean`.
- **Next Useful Lemma**: `exists_cleanCap_pushOff_in_regularNeighborhood` (transverse push-off of an embedded disk in a 3-manifold regular neighborhood).

## 2026-09-22: G086 (`exists_descendingSurgery_of_adaptedCleanCap`) BLOCKED / SKIPPED

- **Target**: `DescentStepOrientable:172` (`exists_descendingSurgery_of_adaptedCleanCap`)
- **Status**: BLOCKED / SKIPPED (missing singular complexity reduction under clean cap surgery)
- **Skeleton Location**: `DescentStepOrientable.lean:172`
- **Blocker Description**:
  - Requires: Given the adapted clean cap $\Delta$ on $E'$ from G085, constructing a descending surgery $Sg : hD.\text{DescendingSurgery}$ such that $Sg.\text{cell}$ maps to $C$, has boundary buffer in $B$, and preserves the boundary loop class $[\gamma] \notin N$.
  - The mathematical proof replaces the singular cell $D$ with a new cell $Sg.\text{cell}$ obtained by cutting out the interior of $E'$ and replacing it with the clean cap $\Delta$.
  - Formalization requires:
    1. Proving that the singular complexity strictly decreases: the branch $c$ (which contributed two components $J$ and $T$ to the double curve) is eliminated or resolved without creating new branch points of higher or equal complexity.
    2. Boundary loop preservation: since the surgery takes place entirely in the interior of $D.\text{domain}$ (disjoint from $\partial D.\text{domain}$), the restriction of $Sg.\text{cell}$ to the boundary is identical to $D|_{\partial D.\text{domain}}$, so the loop $\gamma$ is unchanged in the fundamental group.
    3. Verifying that the singular set stratification and normal data for $Sg.\text{cell}$ are well-defined (`NormalSingularCellData` properties for the surgered cell).
  - The complexity comparison and stratified singular set surgery apparatus are not formalized.
- **Attempted Route**: Evaluated `DescentStepOrientable.lean` and `LoopTheorem/ComplexityInduction.lean`.
- **Next Useful Lemma**: `SingularComplexity.lt_of_cleanCap_surgery` (strict decrease of Moise singular complexity under innermost clean cap surgery).

## 2026-09-22: G087 (`exists_plCrossSeamReading_of_isCrossRegluedCell`) BLOCKED / SKIPPED

- **Target**: `DescentStepOrientable:235` (`exists_plCrossSeamReading_of_isCrossRegluedCell`)
- **Status**: BLOCKED / SKIPPED (missing cross-seam reading existence dichotomy on cross-reglued cells)
- **Skeleton Location**: `DescentStepOrientable.lean:235`
- **Blocker Description**:
  - Requires: Given cross seam tube data $T$ and a cross reglued cell $G$, showing that either $T.\text{chart}$ or $T.\text{chart} \circ \text{crossQuarterTurn}$ admits a `PLCrossSeamReading` on $G$.
  - At a cross-reglued cell $G$, the two sheets meeting along the seam are reglued with a twist. The reading specifies how the boundary of $G$ passes through the splice cylinder.
  - Depending on the orientation/cyclic order of the four points on the boundary of the splice square, the reading is either orientation-preserving or requires a quarter-turn rotation `crossQuarterTurn` to align the coordinate axes with the standard model `bentSource`.
  - Formalization requires:
    1. Continuous parameterization of the preimage $G^{-1}(\text{spliceCylinder})$ in $G.\text{domain}$.
    2. Verifying that the coordinate projection to `bentSource` is a PL homeomorphism satisfying the boundary correspondence conditions `boundary_iff_end`.
    3. The parity/dichotomy argument proving that if the reading does not match in the standard orientation, applying `crossQuarterTurn` (swapping coordinates via $(u, v, t) \mapsto (-v, u, t)$) restores the matching.
- **Attempted Route**: Evaluated `DescentStepOrientable.lean` and `LoopTheorem/CrossQuarterTurn.lean`.
- **Next Useful Lemma**: `PLCrossSeamReading.exists_of_spliceSquare_crossing_parity`.

## 2026-09-22: G088 (`exists_isSourceTrackedBranchTube`) BLOCKED / SKIPPED

- **Target**: `ClosedBranchCaseOne:169` (`exists_isSourceTrackedBranchTube`)
- **Status**: BLOCKED / SKIPPED (missing source-tracked branch tube construction around closed double curve branch)
- **Skeleton Location**: `ClosedBranchCaseOne.lean:169`
- **Blocker Description**:
  - Requires: For a closed branch $c$ of a singular 2-cell $D$ in a combinatorial 3-manifold $L$ with marked branch collar, constructing a simplicial complex $Pc$, derived neighborhood $N$, product coordinate map $\varphi$, return map $u$, and marking rays $r$ satisfying the 9-field `IsSourceTrackedBranchTube` package.
  - A closed branch is a circle $S^1$ in the double curve where two sheets of $D$ intersect along an immersion. The tube is a solid torus neighborhood $N \cong D^2 \times S^1$ in the ambient 3-manifold $L$, fibered over $S^1$ by cross-sectional disks $Pc \cong D^2$.
  - The map $\varphi : (D^2) \times S^1 \to L$ provides the product coordinates, and $u : D^2 \to D^2$ is the monodromy / first-return map of the fibration around the loop.
  - Formalization requires:
    1. Regular neighborhood of a 1-cycle in a combinatorial 3-manifold.
    2. Trivializing or classifying the normal bundle of an embedded circle in an orientable 3-manifold (framed knot neighborhood).
    3. Simplicial triangulation of the solid torus compatible with the ambient triangulation $L$ and the sheet preimages.
    4. Constructing the 4 marking rays $r : \text{Fin } 4 \to \mathbb{R}^2$ that track the 4 sheets/branches entering the double line.
- **Attempted Route**: Evaluated `ClosedBranchCaseOne.lean` and `LoopTheorem/BoundaryCaseFromTube.lean`.
- **Next Useful Lemma**: `exists_tubularNeighborhood_of_simplicialCircle_in_3manifold`.

## 2026-09-22: G089 (`exists_adaptedHalfSpaceChart_in_double`) PASSED

- **Target**: `GeneralPositionInDouble:281` (`exists_adaptedHalfSpaceChart_in_double`)
- **Status**: PASSED
- **Skeleton Location**: `GeneralPositionInDouble.lean:281`
- **Module**: `DifferentialGeometry.Topology.PiecewiseLinear.DoubleHalfSpaceChart`
- **Source File**: `DifferentialGeometry/Topology/PiecewiseLinear/DoubleHalfSpaceChart.lean`
- **Checkpoint Directory**: `C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-d\gemini-batch\checkpoints\G089-double-half-space-chart-20260922T2039241139290Z`
- **Verification Details**:
  - Zero errors, zero warnings.
  - All 13 linters passed.
  - Verified by `checker.ps1` and `GEMINI_BATCH_CHECKPOINT.ps1`.
- **Proof Strategy**:
  - Decomposes the ambient double manifold into three regions: boundary $Bd = \mathrm{frontier}(C)$, interior $\mathrm{interior}(C)$, and exterior $C^c$.
  - For $y \in Bd$, invokes `exists_halfSpace_chart_glued₂_space_in_double` along with `frontier_preimage_glued₂_space_in_double` and restricts the resulting half-space chart to $V \subseteq U$.
  - For $y \in \mathrm{interior}(C)$ and $y \in C^c$, translates the chart from `combinatorialChartedSpace` by an affine translation $v \in \mathrm{plGroupoid}(3)$ such that $\ell(ec(y)) > 0$ (resp. $< 0$) for the coordinate projection $\ell(z) = z_0$, and restricts to the open preimage where $\ell$ has constant sign within $U$.
- **Imports**:
  - `DifferentialGeometry.Topology.PiecewiseLinear.BoundaryDouble`
  - `DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition`
  - `DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ProjectedBoundaryHalfSpace`
  - `Mathlib.Analysis.InnerProductSpace.PiL2`
  - `Mathlib.Topology.Algebra.Module.FiniteDimension`
  - `Mathlib.Topology.OpenPartialHomeomorph.Composition`
  - `Mathlib.Topology.OpenPartialHomeomorph.Constructions`
- **Public Declarations**:
  - `exists_adaptedHalfSpaceChart_in_double`
- **Axioms**: `propext`, `Classical.choice`, `Quot.sound`

## 2026-09-22: G090 (`SingularTwoCell.exists_cutOutPiece_of_closure_subset`) BLOCKED / SKIPPED

- **Target**: `GeneralPositionInDouble:410` (`SingularTwoCell.exists_cutOutPiece_of_closure_subset`)
- **Status**: BLOCKED / SKIPPED (missing relative regular neighborhood / cut-out piece in 2D PL disk with boundary)
- **Skeleton Location**: `GeneralPositionInDouble.lean:410`
- **Blocker Description**:
  - Requires: For a singular 2-cell $D$ and open sets $V_0, V$ with $\text{closure } V_0 \subseteq V$, constructing simplicial complexes $Rc, Lc, Ac$ in $\mathbb{R}^2$ and open sets $\Omega, Nb$ such that $Rc$ is a combinatorial 2-manifold with boundary, $Rc \subseteq D.\text{domain} \cap D^{-1}(V)$, $Lc = Rc \cap \text{frontier } D.\text{domain}$, and $Ac$ is a collar covering $Rc \setminus \Omega$ disjoint from $D^{-1}(\text{closure } V_0)$.
  - Mathematical analysis:
    1. While `LoopTheorem/GeneralPositionInDoubleCutOutWithBoundary.lean` provides `exists_prescribed_cutOut_piece_with_boundary_source`, that lemma requires the entire starting piece $S$ to satisfy $S \subseteq D^{-1}(V)$.
    2. Here, $D.\text{domain}$ is not contained in $D^{-1}(V)$; only the compact subset $D^{-1}(\text{closure } V_0)$ is known to be in $D^{-1}(V)$.
    3. Thus one must first construct an intermediate polygonal / simplicial subcomplex $P \subseteq D.\text{domain}$ such that $D^{-1}(\text{closure } V_0) \subseteq \text{interior } P \subseteq P \subseteq D^{-1}(V)$, and then apply relative cut-out / collar theorems to $P$.
    4. Constructing such a subcomplex $P$ that also cleanly meets $\text{frontier } D.\text{domain}$ along a 1D subcomplex requires relative polyhedral neighborhood theory in manifolds with boundary.
- **Attempted Route**: Evaluated `GeneralPositionInDouble.lean` and `LoopTheorem/GeneralPositionInDoubleCutOutWithBoundary.lean`.
- **Next Useful Lemma**: `exists_polyhedralSubcomplex_neighborhood_rel_boundary` (relative polyhedral neighborhood of a compact set meeting the boundary).

## 2026-09-22: G091 (`exists_gluedCell_of_vertexMap_in_adaptedChart`) PASSED

- **Target**: `GeneralPositionInDouble:425` (`exists_gluedCell_of_vertexMap_in_adaptedChart`)
- **Status**: PASSED
- **Skeleton Location**: `GeneralPositionInDouble.lean:425`
- **Module**: `DifferentialGeometry.Topology.PiecewiseLinear.GluedCellInAdaptedChart`
- **Source File**: `DifferentialGeometry/Topology/PiecewiseLinear/GluedCellInAdaptedChart.lean`
- **SHA256**: `5B78D099FCF8292FE83DE35FB890496281EE899E5DFB4736D29098F55605315A`
- **Checkpoint Directory**: `C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-d\gemini-batch\checkpoints\G091-glued-cell-adapted-chart-20260922T2105097691619Z`
- **Verification Details**:
  - Zero errors, zero warnings.
  - All 13 linters passed.
  - Verified by `checker.ps1` and `GEMINI_BATCH_CHECKPOINT.ps1`.
- **Proof Strategy**:
  - Define $g(x) = \text{if } x \in Rc.\text{space} \text{ then } ec.\text{symm}(h(x)) \text{ else } D(x)$, where $h = \text{simplicialMap } Rs\ \varphi$.
  - The domain $D.\text{domain}$ is covered by two sets open in $D.\text{domain}$: $U_1 = \Omega \cap D.\text{domain}$ and $U_2 = (Rc.\text{space}^c \cup Nb) \cap D.\text{domain}$.
  - On $U_2$, $g = D$: outside $Rc.\text{space}$ by definition, and on $Rc.\text{space} \cap Nb \subseteq Ac.\text{space}$ by $h = ec \circ D$ (`hfrozen`) and $ec.\text{left\_inv}$. Since $D$ is PL on $D.\text{domain}$, $g$ is PL on $U_2 \in \mathcal{N}_{D.\text{domain}}(x)$.
  - On $U_1 = \Omega \cap D.\text{domain} \subseteq Rc.\text{space}$, $g = ec.\text{symm} \circ h$. The transition $ec \circ g = h$ is piecewise affine on $U_1$ via `hpl`, and $g$ is continuous on $U_1$. By `StructureGroupoid.liftPropWithinAt_indep_chart_target` applied with $ec \in (\text{plGroupoid } 3).\text{maximalAtlas } M$, $g$ is PL on $U_1 \in \mathcal{N}_{D.\text{domain}}(x)$.
  - By `liftPropWithinAt_inter'`, $g$ is PL at every point $x \in D.\text{domain}$, yielding $D' : \text{SingularTwoCell } M$ with $D'.\text{domain} = D.\text{domain}$, agreeing with $ec.\text{symm} \circ h$ on $Rc.\text{space}$ and with $D$ on $Rc.\text{space}^c$.
- **Imports**:
  - `DifferentialGeometry.Topology.PiecewiseLinear.ControlledInwardPush`
  - `DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition`
  - `DifferentialGeometry.Topology.PiecewiseLinear.Groupoid`
  - `DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPastingManifold`
  - `DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularCell`
  - `DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorph`
  - `Mathlib.Geometry.Manifold.LocalInvariantProperties`
- **Public Declarations**:
  - `exists_gluedCell_of_vertexMap_in_adaptedChart`
- **Axioms**: `propext`, `Classical.choice`, `Quot.sound`

## 2026-09-22: G092 (`exists_transitionSubdivisionOnOverlap`) PASSED

- **Target**: `GeneralPositionInDouble:1451` (`exists_transitionSubdivisionOnOverlap`)
- **Status**: PASSED
- **Skeleton Location**: `GeneralPositionInDouble.lean:1458`
- **Module**: `DifferentialGeometry.Topology.PiecewiseLinear.TransitionSubdivisionOnOverlap`
- **Source File**: `DifferentialGeometry/Topology/PiecewiseLinear/TransitionSubdivisionOnOverlap.lean`
- **SHA256**: `DC5B46BC44295590340E2DA40ED0A8606A16E997F6DE510800E6919061C40F0F`
- **Checkpoint Directory**: `C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-d\gemini-batch\checkpoints\G092-transition-subdivision-overlap-20260922T2056248321617Z`
- **Verification Details**:
  - Zero errors, zero warnings.
  - All 13 linters passed.
  - Verified by `checker.ps1` and `GEMINI_BATCH_CHECKPOINT.ps1`.
- **Proof Strategy**:
  - Let $W = ec.\text{source} \cap ec'.\text{source}$. The image $ec '' N$ is compact in the open set $ec '' W$.
  - By `exists_isPolyhedron_neighborhood`, there exists a polyhedron $P$ with $ec '' N \subseteq \operatorname{interior} P \subseteq P \subseteq ec '' W$.
  - By `hPpoly.exists_simplicialComplex`, there exists a finite simplicial complex $K$ with $K.\text{space} = P$.
  - The transition map $ec.\text{symm}.\text{trans } ec'$ belongs to `plGroupoid 3` by `StructureGroupoid.compatible_of_mem_maximalAtlas`, so it is piecewise affine on its source $ec '' W$.
  - Hence $z \mapsto ec'(ec.\text{symm } z)$ is piecewise affine on $ec '' W$, and by `IsPiecewiseAffineOn.mono_of_isPolyhedron`, piecewise affine on $K.\text{space}$.
  - By `IsPiecewiseAffineOn.exists_isSubdivision_affineOn_faces`, there exists a finite subdivision $Q$ of $K$ such that on each face $s \in Q.\text{faces}$, $z \mapsto ec'(ec.\text{symm } z)$ is affine.
  - Since $Q.\text{space} = K.\text{space} = P$, we have $ec '' N \subseteq \operatorname{interior} Q.\text{space}$ and $Q.\text{space} \subseteq ec '' W$.
- **Imports**:
  - `DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition`
  - `DifferentialGeometry.Topology.PiecewiseLinear.Groupoid`
  - `DifferentialGeometry.Topology.PiecewiseLinear.PiecewiseAffineSimplicial`
  - `DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorph`
- **Public Declarations**:
  - `exists_transitionSubdivisionOnOverlap`
- **Axioms**: `propext`, `Classical.choice`, `Quot.sound`

## 2026-09-22: G093 (`exists_commonWallComplex`) BLOCKED / SKIPPED

- **Target**: `GeneralPositionInDouble:1469` (`exists_commonWallComplex`)
- **Status**: BLOCKED / SKIPPED (missing simultaneous common polyhedral subdivision for finite atlas)
- **Skeleton Location**: `GeneralPositionInDouble.lean:1469`
- **Blocker Description**:
  - Requires: For a 3-manifold with boundary $K$, constructing a common wall complex $Q$, embedding $\rho : M \to E_a$, and cell systems $Cf, Bf$ forming a common wall system `IsCommonWallSystem` for the double $M = \text{double } 3 K$.
  - Mathematical analysis:
    1. Each chart $ec_i$ of the finite atlas on $M$ has coordinate hyperplanes (walls) $\ell_i = 0$ and boundary hyperplanes. On chart overlaps, these hyperplanes intersect at arbitrary angles.
    2. To form an `IsCommonWallSystem`, one must find a single ambient simplicial complex $Q$ into which $M$ embeds via $\rho$, such that the images of all chart walls and cell boundaries are unions of faces of $Q$.
    3. This requires the general theorem that any finite collection of polyhedra / flat hyperplanes in $\mathbb{R}^N$ admits a simultaneous compatible simplicial subdivision.
    4. The polyhedral intersection and simultaneous subdivision infrastructure for finite collections of polyhedra is not yet formalized in Mathlib or this library.
- **Attempted Route**: Evaluated `GeneralPositionInDouble.lean` and `PiecewiseAffineSimplicial.lean`.
- **Next Useful Lemma**: `exists_common_simplicial_subdivision_finite_polyhedra`.

## 2026-09-22: G094 (`wallProductBlock_transport`) BLOCKED / SKIPPED

- **Target**: `GeneralPositionInDouble:1492` (`wallProductBlock_transport`)
- **Status**: BLOCKED / SKIPPED (missing affine shear coordinate transport and Lipschitz preservation for crossing blocks)
- **Skeleton Location**: `GeneralPositionInDouble.lean:1492`
- **Blocker Description**:
  - Requires: Transporting a `WallProductBlock` from chart $ec_i$ to chart $ec_j$ across a transition map in the maximal atlas of $M$.
  - Mathematical roadmap and formalization blockers:
    1. On 3-cells, transitions in `plGroupoid 3` are affine. On walls between cells, transitions match by `eqOn_wallPlane_of_eqOn_transition` forming an affine shear $(u, v, t) \mapsto (u + \alpha t, v + \beta t, c t)$ with $c > 0$, preserving the wall plane $t = 0$ and the transverse direction.
    2. Formalization requires inverting `chartAffine` on 3-simplices to deduce the explicit shear form.
    3. Mathlib lacks affine shear classification and preservation of Lipschitz constants under shears ($C$-Lipschitz sheets remain $C'$-Lipschitz under small shears).
    4. Verifying all 20 fields of `IsStableCrossingBlock` and the 3-case disjunction of `WallProductBlock` under coordinate change represents a massive multi-file development.
- **Attempted Route**: Evaluated `GeneralPositionInDouble.lean` and `LoopTheorem/GeneralPositionInDoubleCutOutWithBoundary.lean`.
- **Next Useful Lemma**: `IsStableCrossingBlock.transport_of_affineShear`.

## 2026-09-22: G095 (`hasStableCrossingBlocks_of_wallProductBlocks`) BLOCKED / SKIPPED

- **Target**: `GeneralPositionInDouble:1511` (`hasStableCrossingBlocks_of_wallProductBlocks`)
- **Status**: BLOCKED / SKIPPED (missing crossing block stability from wall product structure; directly blocked by G094)
- **Skeleton Location**: `GeneralPositionInDouble.lean:1511`
- **Blocker Description**:
  - Requires: Showing that a family of `WallProductBlock`s covering the crossing set yields `HasStableCrossingBlocks`.
  - Mathematical analysis:
    1. Directly depends on `wallProductBlock_transport` (G094): each wall product block is given in some chart $ec_i$, but `HasStableCrossingBlocks` requires all crossing blocks to be expressed in a single designated chart $ec_{i_0}$ or to cover the double curve globally.
    2. Requires transporting all blocks to chart $ec_{i_0}$ via G094 and extracting a finite subcover of the compact double curve.
- **Attempted Route**: Evaluated `GeneralPositionInDouble.lean`.
- **Next Useful Lemma**: `wallProductBlock_transport` (G094).

## 2026-09-22: G096 (`exists_normalizationPreparation_on_prescribedRegion`) BLOCKED / SKIPPED

- **Target**: `GeneralPositionInDouble:1632` (`exists_normalizationPreparation_on_prescribedRegion`)
- **Status**: BLOCKED / SKIPPED (missing star-injective simplicial subdivision controlling fiber multiplicity)
- **Skeleton Location**: `GeneralPositionInDouble.lean:1632`
- **Blocker Description**:
  - Requires: Preparing a singular 2-cell $D$ on a prescribed region $V$ by subdividing the domain into small simplices such that the image of each simplex is contained in a single chart of the wall system and has diameter bounded by $\varepsilon$.
  - Mathematical analysis:
    1. Requires Lebesgue number lemma and uniform continuity for simplicial maps on compact 2-manifolds, combined with star-injective simplicial subdivision.
    2. To ensure that each simplex has diameter $<\varepsilon$ and that fibers have cardinality $\le 2$, one must take a sufficiently fine barycentric subdivision of the domain and perturb vertices to avoid non-generic coincidences.
- **Attempted Route**: Evaluated `GeneralPositionInDouble.lean`.
- **Next Useful Lemma**: `exists_fine_simplicial_subdivision_diameter_le`.

## 2026-09-22: G097 (`exists_protectedSubdivision_in_adaptedChart`) BLOCKED / SKIPPED

- **Target**: `GeneralPositionInDouble:1657` (`exists_protectedSubdivision_in_adaptedChart`)
- **Status**: BLOCKED / SKIPPED (missing protected subdivision isolating double curve and boundary)
- **Skeleton Location**: `GeneralPositionInDouble.lean:1657`
- **Blocker Description**:
  - Requires: Constructing a protected subdivision of the domain of $D$ in an adapted chart, isolating the double curve and boundary into protected subcomplexes.
  - Mathematical analysis:
    1. A protected subdivision replaces each vertex and edge of the singular set with a regular neighborhood (buffer zone) where the map is in standard form, such that perturbations outside the buffer do not affect the crossings inside.
    2. Requires the 2D regular neighborhood / derived neighborhood collar theorem for 1-subcomplexes in a simplicial 2-complex.
- **Attempted Route**: Evaluated `GeneralPositionInDouble.lean`.
- **Next Useful Lemma**: `exists_derivedNeighborhood_subcomplex_isolation`.

## 2026-09-22: G098 (`exists_globalInvariants_of_gluedCell`) PASSED

- **Target**: `GeneralPositionInDouble:1753` (`exists_globalInvariants_of_gluedCell`)
- **Status**: PASSED
- **Location**: `DifferentialGeometry/Topology/PiecewiseLinear/GluedCellGlobalInvariants.lean`
- **Checkpoint**: `G098-glued-cell-global-invariants-20260922T2124244440121Z`
- **Mathematical Construction**:
  - Proved all 6 conjuncts of global invariants for the glued singular two-cell $D'$:
    1. `MapsTo (⇑D') D'.domain C` via chart containment, boundary half-space nonnegativity, and outside invariance.
    2. Exact preimage matching `∀ z ∉ V, (⇑D') ⁻¹' {z} = (⇑D) ⁻¹' {z}`.
    3. Uniform local injectivity scale $\kappa$ via `Metric.ball` diameter triangle inequality and `hcert`.
    4. Fiber cardinality $\le 2$ on $D'.\text{domain}$.
    5. Boundary preimage exact equality $D'.\text{domain} \cap (D')^{-1}(BdM) = \text{frontier } D'.\text{domain}$.
    6. Boundary homotopy $H \in C(\text{unitInterval} \times \text{frontier } D.\text{domain}, M)$ via open cover gluing of $W_1 = \{p \mid p.2.1 \in \Omega\}$ and $W_2 = \{p \mid p.2.1 \in Rc.\text{space}^c \cup Nb\}$; verified continuity via `ContinuousOn.union_of_isOpen`, boundary tracking in $BdM$, buffer neighborhood containment in $B$, and endpoint conditions $H(0, \cdot) = D$ and $H(1, \cdot) = D'$.

## 2026-09-22: G099 (`wallProductBlocks_stable_on_fixedSubdivision`) BLOCKED / SKIPPED

- **Target**: `GeneralPositionInDouble:1771` (`wallProductBlocks_stable_on_fixedSubdivision`)
- **Status**: BLOCKED / SKIPPED (missing C^0-stability of crossing blocks under perturbation of moving sheets)
- **Skeleton Location**: `GeneralPositionInDouble.lean:1771`
- **Blocker Description**:
  - Requires: Showing that `IsStableCrossingBlock` is preserved under small $C^0$/PL perturbations of the map on a fixed subdivision when sheets move.
  - Mathematical analysis:
    1. The codebase only provides rigid-invariance lemmas (`isStableCrossingBlock_of_eqOn_sheets`, `isStableCrossingBlock_of_preimage_singleton_eq`, `isStableCrossingBlock_of_eqOn_compl`) where $g = f$ on sheets.
    2. When sheets move by $\le \delta$, their intersection line moves by $O(\delta)$, and one must construct new sheet homeomorphisms $\psi_1, \psi_2$ and adjust the product box to re-establish the 20 conditions of `IsStableCrossingBlock`.
    3. No perturbation lemma for moving sheets exists in the library.
- **Attempted Route**: Evaluated `GeneralPositionInDouble.lean` and `LoopTheorem/GeneralPositionInDoubleCutOutWithBoundary.lean`.
- **Next Useful Lemma**: `isStableCrossingBlock_of_small_perturbation`.

## 2026-09-22: G100 (`exists_wallGenericVertexMap`) BLOCKED / SKIPPED

- **Target**: `GeneralPositionInDouble:1823` (`exists_wallGenericVertexMap`)
- **Status**: BLOCKED / SKIPPED (missing relative PL transversality for simplicial maps into 3-manifolds with polyhedral stratifications)
- **Skeleton Location**: `GeneralPositionInDouble.lean:1823`
- **Blocker Description**:
  - Requires: Constructing a generic vertex map perturbing $D$ to be in general position with respect to the ambient wall system (avoiding the 1-skeleton of walls, transverse to wall planes).
  - Mathematical analysis:
    1. Vertices of the 2-complex must be mapped into 3-cells (avoiding 2-faces, edges, vertices of the wall complex).
    2. Edges must cross 2-faces transversely (avoiding edges and vertices).
    3. 2-simplices must avoid wall vertices.
    4. Formalization requires Sard-type / general position perturbation lemmas for finite-dimensional affine spaces over $\mathbb{R}$.
- **Attempted Route**: Evaluated `GeneralPositionInDouble.lean`.
- **Next Useful Lemma**: `exists_simplicial_vertex_perturbation_transverse_to_polyhedra`.

## 2026-09-22: G101 (`wallProductBlocks_of_wallGenericity`) BLOCKED / SKIPPED

- **Target**: `GeneralPositionInDouble:1872` (`wallProductBlocks_of_wallGenericity`)
- **Status**: BLOCKED / SKIPPED (missing wall product block synthesis from generic transverse simplex-wall crossings)
- **Skeleton Location**: `GeneralPositionInDouble.lean:1872`
- **Blocker Description**:
  - Requires: Constructing `WallProductBlock`s around generic transverse crossings of piecewise affine maps.
  - Mathematical analysis:
    1. For each transverse intersection of a 2-simplex with a wall, one must construct the local product coordinate box $[-r, r] \times [-r, r] \times [-\eta, \eta]$.
    2. Local PL coordinate straightening into graph form with small Lipschitz constants.
    3. Establishing the 3-case disjunction and all conditions of `WallProductBlock`.
- **Attempted Route**: Evaluated `GeneralPositionInDouble.lean`.
- **Next Useful Lemma**: `wallProductBlock_of_transverse_simplex_wall_intersection`.
