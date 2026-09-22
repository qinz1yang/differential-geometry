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
