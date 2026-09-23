# Opus fill log, lease a (claude-agent-a-20260919), 2026-09-22

# Batch 1 (IsTube producer)

Files (both new, untracked, sorry-free; no existing file touched):

| file | lines | SHA-256 |
|---|---|---|
| `DifferentialGeometry/Topology/PiecewiseLinear/SplittingDiskRim.lean` | 515 | `8f40ca13edcbc06bbd971c9380a52bd0b76351982cce542b1f323f3ec8011b04` |
| `DifferentialGeometry/Topology/PiecewiseLinear/TubeOfGraphDualCells.lean` | 433 | `fd1e2719086e38f578e5dc0c23d0ea4ae597e0cbdae9b4514286bbe4eed6f500` |

Import lines to register (in this order; the second imports the first):

    import DifferentialGeometry.Topology.PiecewiseLinear.SplittingDiskRim
    import DifferentialGeometry.Topology.PiecewiseLinear.TubeOfGraphDualCells

Checker lines:

- `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\SplittingDiskRim.lean with no diagnostics; shared outputs unchanged.` (2026-09-22T23:41:56Z)
- `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\TubeOfGraphDualCells.lean with no diagnostics; shared outputs unchanged.` (2026-09-22T23:49:31Z)

Audit (`C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a\AuditTube1.lean`, copy of
`AuditOpusF3.lean` over both modules: every declaration within `propext`/`Classical.choice`/
`Quot.sound`, the thirteen linters without docBlame/docBlameThm):

- `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a\AuditTube1.lean with no diagnostics; shared outputs unchanged.` (2026-09-22T23:50:46Z)

## isTube_graphDualCell (deliverable 1, producer with the identity) — CLOSED

- Files: both modules above; the endpoint is in `TubeOfGraphDualCells.lean`.
- New public names, `SplittingDiskRim.lean`:
  `IsCombinatorialManifoldWithBoundary.isPLBall_graphDualCell`,
  `IsCombinatorialManifoldWithBoundary.isPLBall_splittingDisk`,
  `IsCombinatorialManifoldWithBoundary.mem_boundaryComplex_starComplex_faces_iff`,
  `IsCombinatorialManifoldWithBoundary.notMem_boundaryComplex_faces_of_forall_mem_interior`,
  `IsCombinatorialManifoldWithBoundary.space_subset_interior_of_forall_vertex`,
  `IsCombinatorialManifoldWithBoundary.space_subset_interior_iUnion_graphDualCell`,
  `graphDualCell_space_inter_of_mem`,
  `IsCombinatorialManifoldWithBoundary.exists_isPLHomeomorphOn_splittingDisk_inter_frontier`.
  `TubeOfGraphDualCells.lean`: `IsPLSphere.isConnected_sdiff_iUnion_of_isPLBall_two`,
  `isTube_graphDualCell`. All grepped tree-wide: no clash.
- Statement: for `A K : Geometry.SimplicialComplex ℝ E3` with `A.faces.Finite`,
  `IsCombinatorialManifoldWithBoundary 3 A`, `K.faces ⊆ A.faces`, `∀ s ∈ K.faces, s.card ≤ 2`,
  `∃ e ∈ K.faces, e.card = 2` and `∀ v ∈ K.vertices, v ∈ interior A.space`,
  `IsTube K N C D Dbd id N` with `C v = (graphDualCell A K v).space`,
  `D e = if he : e ∈ A.faces then (splittingDisk A e he).space else ∅`,
  `Dbd e = D e ∩ frontier N`, `N = ⋃ v ∈ K.vertices, C v`.
  The interior hypothesis is on vertices only; `space_subset_interior_of_forall_vertex` turns it
  into `K.space ⊆ interior A.space` (a face with an interior vertex is not a boundary face).
- Route, field by field.
  `dualBall`: the closed-manifold proof of `IsCombinatorialManifold.isPLBall_graphDualCell` uses
  the manifold hypothesis only to make `dualCell K {v}` a 3-ball, which
  `IsCombinatorialManifoldWithBoundary.isPLBall_dualCell` already gives; the with-boundary theorem
  is that proof with the hypothesis type changed (no interior condition needed).
  `splitCell`/`splitProper`: the splitting disk is the closed star of `ê` in the first derived
  `X` of the 2-ball `dualCell A e`, a ball (`isPLBall_closedStar`); when the link of `ê` in `X`
  is a sphere (edge not in `∂A`, from the interior hypothesis) its boundary complex is exactly the
  faces missing `ê` (`mem_boundaryComplex_starComplex_faces_iff`, via unique cofaces and
  `mem_boundaryComplex_faces_iff`).  Barycentric coordinates in `A'` then give
  `D e ∩ Fr N = |∂D e|`: on a face through `ê` the weight of `ê` is the unique maximum
  (`weights_sum_centroid_lt_of_notMem_min`) so the point is in `Int N`
  (`mem_interior_derivedNeighborhood_of_barycentricCoordinate_lt`); on a face missing `ê` the
  bottom of the flag holds `ê` and some `t̂`, `e ⊊ t`, with equal maximal weight
  (`weights_sum_centroid_le_of_mem_min`), `t̂ ∉ K'` since `t` is bigger than every face of `K`,
  so the point is off `Int N` (`notMem_interior_derivedNeighborhood_of_barycentricCoordinate_le`).
  `r '' ∂Δ = |∂D e|` is `image_stdSimplexBoundary_eq_boundaryComplex`.
  `isNeighborhood`: `derivedNeighborhood_mem_nhdsWithin` plus `K ⊆ Int |A|`.
  `splitSeparates`: pure point set: in `Int (C u ∪ C v)` take `U = {p ∉ C v}`, `V = {p ∉ C u}`;
  they are open, disjoint (cover), `U ∪ V` is the complement of `D e`, which equals the
  complement of `D e \ Dbd e` there because `Dbd e ⊆ Fr N` misses `Int N`; `u ∉ C v` by
  `mem_graphDualCell_space_iff_of_singleton_mem`.
  `freeFaceConnected`: the free face equals `Fr C v \ ⋃_{e ∋ v} D e` (a point of `Fr C v` in
  `Int N` lies in a second cell, hence in a splitting disk at `v`); `Fr C v` is a PL 2-sphere
  (`image_stdSimplexBoundary_eq_frontier`), the `D e` are disjoint PL disks in it
  (`inter_subset_frontier_of_isPLBall`, `disjoint_splittingDisk_space`), and
  `IsPLSphere.isConnected_sdiff_iUnion_of_isPLBall_two` (new, general `E`) proves the sphere
  minus disjoint closed PL disks connected: Janiszewski
  (`isPreconnected_compl_iUnion_of_isPreconnected_compl`) in the simply connected disk
  `closure (S \ D i₀)` (PL Schoenflies `isPLBall_closure_sdiff`), with the complement of each other
  disk connected by `isPreconnected_left_of_isClosed_union` (sphere minus that disk = it ∪ `D i₀`
  glued along the rim circle); nonemptiness by `subset_of_isPreconnected_of_iUnion_isClosed`.
  `isEmbedding`/`imageEq`: `IsEmbedding.subtypeVal`, `image_id`.
- Hypotheses and their producers: all six are supplied by `exists_isTube` below (explicit
  construction); none is an IsTube field in disguise.
- No `IsTube` field turned out to be unsatisfiable by the dual-cell model: no DEFECT.

## IsTube.of_isEmbedding (deliverable 2, transport) — CLOSED

- File: `TubeOfGraphDualCells.lean`. New public name: `IsTube.of_isEmbedding` (no clash).
- Statement: `IsTube K N C D Dbd h₀ N₀ → IsEmbedding (N.domRestrict h) →
  IsTube K N C D Dbd h (h '' N)` (stated from an arbitrary `h₀ N₀`, which contains the requested
  `id`, `N` case).  Proof: structure update of `isEmbedding` and `imageEq`, the only fields that
  mention `h` or `N'`.

## exists_isTube (deliverable 3, inhabitant) — CLOSED

- File: `TubeOfGraphDualCells.lean`. New public name: `exists_isTube` (no clash).
- Statement: `∃ K N C D Dbd h N', IsTube K N C D Dbd h N'` (in `ℝ³`), through
  `isTube_graphDualCell`.
- What it instantiates: `T` = an affinely independent 4-point set of `ℝ³`
  (`exists_affineIndependent_openSimplex_subset`), `A` = second barycentric subdivision of
  `simplexComplex T` (`IsCombinatorialManifoldWithBoundary 3` from
  `isPLBall_convexHull_of_affineIndependent` and `IsPLBall.isCombinatorialManifoldWithBoundary`),
  `K = subcomplexGeneratedBy A {u}` where `u` is the edge of `A` from the flag
  `σ₁ = {T̂} ⊂ σ₂ = {t̂, T̂}` of the first derived, `t` a facet of `T`: its ends are `T̂` and the
  midpoint of `T̂ t̂`, both in `openSimplex T = interior |A|` (`mem_openSimplex_top`,
  `interior_convexHull_eq_openSimplex`).  `K` is a genuine one-edge graph (`u.card = 2`), `N` its
  second-derived neighbourhood in the tetrahedron, `h = id`.  Not degenerate: `hasEdge`,
  `dualBall`, the two-ball splitting disk and the free-face connectedness are all exercised.

## Notes for the lead

- The closed-manifold theorems `IsCombinatorialManifold.isPLBall_graphDualCell`
  (`DualCellDecomposition.lean`) and `IsCombinatorialManifold.isPLBall_splittingDisk`
  (`DualCells.lean`) are now corollaries of the with-boundary versions
  (`h.isCombinatorialManifoldWithBoundary`).  The with-boundary graph-dual-cell proof is a copy of
  the closed one with only the hypothesis type changed, because existing files could not be
  edited; moving it into `DualCellDecomposition.lean` and deriving the closed one would remove
  the duplication.
- The `PseudoCell.lean` module docstring still says `IsTube` is untested and lacks producers for
  `dualBall`, `splitSeparates`, `freeFaceConnected`; that is now outdated.
- `IsPLSphere.isConnected_sdiff_iUnion_of_isPLBall_two` is a general sphere fact; it lives in the
  tube module only because the Janiszewski wrapper it uses sits in
  `HandleDecompositionOfEdgeCollars.lean`.

# Batch 2 (tube frame)

Files (new, untracked, sorry-free; no existing file touched):

| file | lines | SHA-256 |
|---|---|---|
| `DifferentialGeometry/Topology/PiecewiseLinear/SubdivisionEndPoints.lean` | 233 | `b7798a1ef8b9d626c7abe48305d71507f47fae9175a06befa58a27f16dbe8406` |
| `DifferentialGeometry/Topology/PiecewiseLinear/FineSimplexTriangulation.lean` | 61 | `8b1af5e38f19c81982e4f27f484018fc27ded3cf18ec5eabd29bd9af8bfd744b` |
| `DifferentialGeometry/Topology/PiecewiseLinear/Section33TubeFrame.lean` | 124 | `58d564581401610411b7bd18a613b88b34ef7187d9e73c8a7393d101b7202af0` |

Import lines to register (the third imports the first two and `TubeOfGraphDualCells`):

    import DifferentialGeometry.Topology.PiecewiseLinear.SubdivisionEndPoints
    import DifferentialGeometry.Topology.PiecewiseLinear.FineSimplexTriangulation
    import DifferentialGeometry.Topology.PiecewiseLinear.Section33TubeFrame

Checker lines:

- `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\SubdivisionEndPoints.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T00:07:00Z)
- `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\FineSimplexTriangulation.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T00:03:48Z)
- `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\Section33TubeFrame.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T00:08:25Z)

Audit `C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a\AuditTube2.lean` (the three
modules; axioms within `propext`/`Classical.choice`/`Quot.sound`, thirteen linters):

- `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a\AuditTube2.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T00:09:25Z)

The first audit run rejected one unused `[Finite L.faces]` in
`IsSubdivision.edgeGraph_neighborSet_ncard_ne_one`; it was removed and the chain recompiled.
Setup note: the lead's uncommitted docstring edit of `PseudoCell.lean` invalidated its accepted
object, so `PseudoCell` was compiled into the private root (no diagnostics) before the frame.

## exists_section33TubeFrame — CLOSED

- File: `Section33TubeFrame.lean`.  The `open Classical in` prefix, the `section Leaves`
  `variable` block and the statement are copied verbatim from
  `Skeleton/Section33Approximation.lean` (a `diff` of the statement lines is empty).  The skeleton
  leaf of the same name must be deleted and the skeleton must import this module, as for Lemma 12.
- New public names: `exists_section33TubeFrame` (this module only), plus the bricks below.
- Route.  `δ` with `cthickening δ |L| ⊆ U` (`IsCompact.exists_cthickening_subset_open`); `h` is
  uniformly continuous on that compact thickening (`IsCompact.uniformContinuousOn_of_continuous`,
  continuity from `hh`), modulus `η` for `ε / 4`.  `exists_simplex_subdivision_graphDualCell_diam_lt`
  with bound `min δ η` gives `T`, `L'`.  Every dual cell contains its vertex, which lies on `|L|`,
  so the cell lies in the thickening and has diameter `< η`: this gives `N ⊆ U` and the `ε / 4`
  bound.  `isTube_graphDualCell` (edge from `IsSubdivision.exists_mem_faces_card_eq_two`,
  vertices in the open simplex = `interior T.space`) and `IsTube.of_isEmbedding` with
  `hh.comp (IsEmbedding.inclusion hNU)` give the tube with `h`; no end points from
  `IsSubdivision.edgeGraph_neighborSet_ncard_ne_one`; `C v` pinned by `rfl`;
  `IsCombinatorialManifoldWithBoundary.derivedNeighborhood` gives the manifold clause.  The frozen
  statement elaborates `derivedNeighborhood` with the `ℝ³` instance `WithLp.instDecidableEq`, the
  dual-cell lemmas with the classical one; both are bridged by `Subsingleton.elim` on
  `DecidableEq` (subst of a universally quantified instance), no statement change.
- Hypotheses used: all of the leaf's (`hdim`, `hedge`, `hend`, `hU`, `hLU`, `hh`, `hε`, finite
  `L`); `hend` only for the no-end-point clause.  `T` is a triangulation of a large tetrahedron
  around `|L|` (not inside `U`); only `N ⊆ U` is asked for.

## SubdivisionEndPoints (brick) — CLOSED

- New public names: `exists_pair_mem_faces_of_forall_add_smul_mem_space`,
  `IsSubdivision.edgeGraph_neighborSet_ncard_ne_one`,
  `IsSubdivision.exists_mem_faces_card_eq_two` (grepped: no clash).  General normed `E`.
- Route: the closed star of a vertex is a neighbourhood in the space (`closedStar_mem_nhdsWithin`),
  so a ray from `v` staying in the space meets a face `{v, x}`; a second edge at `v` comes from
  the ray away from `w` inside the carrier edge of `L`, or, at a vertex of `L`, from a second edge
  of `L` (no end points of `L`), which meets the first only in `v` (`inter_subset_convexHull`).

## FineSimplexTriangulation (brick) — CLOSED

- New public name: `exists_simplex_subdivision_graphDualCell_diam_lt` (grepped: no clash).
  For a finite complex `L` in a space of dimension `n + 1` and `ε > 0`: a finite triangulation
  `T` of a simplex with `IsCombinatorialManifoldWithBoundary (n + 1) T`, a subdivision `L'` of `L`
  with `L'.faces ⊆ T.faces`, `|L| ⊆ interior |T|`, card bounds kept, and every graph dual cell of
  diameter `< ε`.
- Route: `exists_affineIndependent_openSimplex_superset`, `exists_isSubdivision_affineMap` with
  the identity (makes a subdivision of `L` a subcomplex of a subdivided simplex),
  `exists_isSubdivision_graphDualCell_diam_lt`, `isPLBall_convexHull_of_affineIndependent`,
  `interior_convexHull_eq_openSimplex`.
