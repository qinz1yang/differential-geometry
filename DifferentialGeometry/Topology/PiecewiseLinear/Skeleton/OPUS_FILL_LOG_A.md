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

# Batch 3 (Section 34 normalization)

Files (new, untracked, sorry-free; no existing file touched):

| file | lines | SHA-256 |
|---|---|---|
| `DifferentialGeometry/Topology/PiecewiseLinear/Section34FaceBallVocabulary.lean` | 183 | `6eea7823e2491999c2e7c3d947a4fbeb52ffb53493fcca9e829cb6d292a3adcf` |
| `DifferentialGeometry/Topology/PiecewiseLinear/Section34TerminalFaceBalls.lean` | 261 | `4e9b6dbf4f052678e3396660e9cc4c6f25ea7b110dce0f069a5d1be85235d3f1` |

Import lines (the second imports the first):

    import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceBallVocabulary
    import DifferentialGeometry.Topology.PiecewiseLinear.Section34TerminalFaceBalls

Checker lines:

- `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\Section34FaceBallVocabulary.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T00:17:07Z)
- `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\Section34TerminalFaceBalls.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T00:20:00Z)

Audit `C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a\AuditTube3.lean` (both modules):

- `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a\AuditTube3.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T00:21:03Z)

## Section34FaceBallVocabulary (hoisted vocabulary, not a leaf)

- The skeleton's `universe u` and sections `CurveCrossing`, `FirstHomology`, `Vocabulary`
  (skeleton lines 262-411 at HEAD 584f0c2e4) copied verbatim into a real module with a short
  module docstring, because real modules cannot import the skeleton.  Names duplicated with the
  skeleton until it imports this module and deletes those sections: `HasPLCurveCrossingOnAt`,
  `CarriesFirstHomologyOnto`, `carriesFirstHomologyOnto_self`, `section34VertexBallImage`,
  `section34SplitDiskImage`, `section34TraceComponents`, `section34TraceCount`,
  `section34CrossingCount`, `section34FaceBallRank`, `section34FaceBallRank_congr`,
  `section34FaceBallRank_lt_of_compression`, `section34FaceBallRank_lt_of_bigonSlide`,
  `Section34FaceBallInvariants`, `Section34Compression`, `Section34BigonSlide`.

## exists_section34TerminalFaceBalls — CLOSED (statement minus three unused hypotheses)

- File: `Section34TerminalFaceBalls.lean`.  New public names: `finite_setOf_section34Incident`,
  `exists_section34FaceBallInvariants_forall_not_rank_lt`, `exists_section34TerminalFaceBalls`.
- Deviation from the frozen text, decided by the linter gate: `hcut`, `hgraph` and `hctrl` are
  not used by any proof (the limit needs neither local finiteness of carriers nor countability),
  so `unusedArguments` would reject the frozen signature; they are deleted, everything else is
  verbatim (same implicit families, same `hinv hcomp hslide` and conclusion).  The assembly
  `section34NormalFamily` must call `exists_section34TerminalFaceBalls hinv₀ (…) (…)`, i.e. drop
  `hcut hgraph hctrl` from its call; nothing else changes.
- Route: Zorn (`exists_maximal_of_chains_bounded`) on the families satisfying the invariants,
  ordered by "at every label equal or of strictly smaller `section34FaceBallRank`".  Chains:
  the rank at each label attains a minimum (`WellFounded.has_min` on `ℕ`), members with the
  minimal rank agree at that label, the family of these values is an upper bound; it satisfies
  `Section34FaceBallInvariants` because each clause reads one or two labels, except the last
  clause of `Section34Exterior`, which reads the faces incident to a tetrahedron, finitely many
  by `finite_setOf_section34Incident` (vertices of an incident face are vertices of the
  tetrahedron); a chain member agrees with the bound on any finite label set (induction on the
  `Finset`).  A maximal family admits no single-label rank-lowering step
  (`exists_section34FaceBallInvariants_forall_not_rank_lt`, general `tgtV`/`tgtEBd`), so
  `hcomp`/`hslide` give the two impossibility clauses.  The docstring's worry (fair enumeration,
  locally finite limit, carriers) is not needed; no countability of the labels is used.
- Hypotheses used: `hinv`, `hcomp`, `hslide` only.

## exists_section34FaceBalls — STUCK (not attempted beyond the survey; deep)

- Remaining goal: the frozen statement itself (P3, Lemmas 3-5).  Missing tree inputs, checked by
  grep today: a producer of nested shell-separated PL balls around `h '' σ` inside a chart of
  `Section34CarrierControl` (the application of `Moise305Tame` in a chart and the pull-back of
  the ball); a general-position perturbation of a PL 2-sphere against the PL surface
  `frontier (⋃ w, tgtV w)` producing `HasPLCrossingAt` at every trace point and
  `HasPLCurveCrossingOnAt` at every point on a splitting circle (the tree has only
  consumers of `HasPLCrossingAt`: `CrossingFiber`, `CrossingNeighborhood`, `HeightChange`);
  Lemma 4's auxiliary-disk argument for the `H₁` generator clause; the component clause of
  `Section34Exterior`.

## exists_section34Compression — STUCK (deep)

- Remaining goal: the frozen statement (P4a, Operation 1 and Lemma 6).  Needs: cutting a
  PL 3-ball along a clean compression disk into two balls inside one chart of `H t`
  (local PL Schoenflies is available as `IsPLSphere` / `SphereSchoenflies`, but no producer of
  the two spheres from a compression disk), preservation of the ten invariant fields, and the
  exact count `c⁺ + 1 ≤ c` (needs the trace to be a 1-manifold whose components are circles,
  derivable from field 5 but not stated anywhere).

## exists_section34BigonSlide — STUCK (deep)

- Remaining goal: the frozen statement (P4b, Operation 2 and Lemma 7).  Needs an ambient PL
  homeomorphism supported in a small neighbourhood of `Dj` fixing the face torus, the other
  face balls and the markers, and the exact count `p⁺ + 2 = p`; no producer of such an isotopy
  across a bigon disk exists in the tree.

## section34Trace_of_noOperation — STUCK (deep, external input)

- Remaining goal: the frozen statement (Lemmas 9-11).  Lemma 11 needs Moise 28.8, which the
  tree does not state (grep `28.8`/`Moise288`: nothing outside the skeleton text).

## section34TraceCircle_homologyMap_ne_zero — STUCK (deep, but the statement checks out)

- Remaining goal: the frozen statement.  Checked on paper: with `k ≥ 3` incident splitting
  circles, a circle on the torus surface meeting each in exactly one point cannot bound a disk
  of the surface (the open disk would lie in one annulus and reach at most two circles) and
  cannot only touch a circle (passing a third circle forces a second meeting), so it crosses
  every meridian disk once and is nonzero in `H₁ T_σ`; the statement is true.  Missing in the
  tree: the cyclic chain structure of the vertex balls on `∂σ` (that the `𝒦'`-vertices and
  edges on the boundary of a triangle form one polygon, and that `T_σ` is the resulting cyclic
  union of balls meeting in the incident splitting disks), and an `H₁` computation of such a
  union with a degree/lifting argument for a circle crossing each meridian once.

# Batch 4 (Section 34 P3-P4 bricks)

Files (new, untracked, sorry-free; no existing file touched):

| file | lines | SHA-256 |
|---|---|---|
| `DifferentialGeometry/Topology/PiecewiseLinear/ChartTameNestedCells.lean` | 154 | `3efdc18480fc28238d0d4986779114e6832029a20f3fb145bf95338c51a5bbc4` |
| `DifferentialGeometry/Topology/PiecewiseLinear/CurveCrossingGeneralPosition.lean` | 341 | `6094f69fad8d702dbc31adc5f62abd43661d3870d4879eee7e2156c9e5deddb8` |

Import lines (independent of each other; the second imports the accepted
`Section34FaceBallVocabulary`, the home of `HasPLCurveCrossingOnAt`):

    import DifferentialGeometry.Topology.PiecewiseLinear.ChartTameNestedCells
    import DifferentialGeometry.Topology.PiecewiseLinear.CurveCrossingGeneralPosition

Checker lines:

- `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\ChartTameNestedCells.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T00:36Z)
- `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\CurveCrossingGeneralPosition.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T00:51Z; `Section34FaceBallVocabulary` recompiled into the private root first, same verdict)

Audit `C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a\AuditTube5.lean` (both modules;
`AuditTube4.lean`, the first module alone, also passed):

- `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a\AuditTube5.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T00:52:10Z)

## Brick 1: Theorem 30.5 in a chart (`ChartTameNestedCells`) — CLOSED

- Public names: `isPLHomeomorphInto_symm_of_mem_maximalAtlas`,
  `Moise305Tame.exists_isPLCellOn_of_mem_maximalAtlas`.
- Statement (minimal, chosen by me; the leaf does not force one): for `c` in the maximal
  atlas of `M` and `C₁ C₂ ⊆ M` with `C₂ ⊆ c.source`, `C₁ ⊆ interior C₂`, if `c '' C₁`, `c '' C₂`
  are topological `3`-cells, `closure (c '' C₂ \ c '' C₁)` is a spherical shell between their
  frontiers and `frontier (c '' C₂)` is bicollared, then `∃ C B, IsPLCellOn 3 C B ∧
  C₁ ⊆ interior C ∧ C ⊆ interior C₂`.  Exactly the hypotheses of `Moise305Tame` read in the
  chart; nothing added.  No `HasGroupoid` instance: the P3 context has none for `M₂`.
- Route: `c.symm` restricted to a polyhedron of `c.target` is `IsPLHomeomorphInto` using only
  maximal-atlas compatibility (`compatible_of_mem_maximalAtlas_left/right`): PL-ness is the
  transition `c.symm ≫ₕ chartAt`; the left inverse `c` is PL on the image because the inverse
  transition is PL and injective on `D ∩ Q` for a polytope neighbourhood `Q`
  (`isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn`).  The ball `D` of `Moise305Tame` is then
  pulled back: `C = c.symm '' D`, `B = c.symm '' (r '' stdSimplexBoundary 3)`.

## Brick 2: curve crossing by general position (`CurveCrossingGeneralPosition`) — CLOSED

- Grep of producers first: `HasPLCrossingAt` has the producers
  `exists_small_homeomorph_generalPosition(_relative, _off_subcomplex, …)` and the pointwise
  `hasPLCrossingAt_of_transverse_faces` (reused here); `HasPLCurveCrossingOnAt` had none.
- Public names: `HasPLCurveCrossingOnAt.congr` (locality, for the chart transfer of fields 5/6),
  `exists_isPLHomeomorphOn_linearize_coface_pair_fixing`,
  `finrank_vectorSpan_add_one_of_mem_faces`, `hasPLCurveCrossingOnAt_of_transverse_faces`,
  `exists_small_homeomorph_transverse_relative`, `exists_small_homeomorph_curveCrossing_relative`.
- Level: the chart model, `E` finite-dimensional with `finrank = 3` (covers
  `EuclideanSpace ℝ (Fin 3)`); "inside a chart" = in the chart target.
- Pointwise lemma hypotheses, each necessary: `K` of dimension `≤ 2` (a `3`-simplex would make
  `K ∩ L` a plane), `L` a combinatorial surface with boundary, `C.faces ⊆ L.faces`, `C` of
  dimension `≤ 1`, edges of `C` not in `boundaryComplex 2 L` (at a boundary edge `K ∩ L` is a
  ray, not a line), faces of `K` transverse to faces of `L`.  Route: transversality forces the
  carriers of `x` to be an open triangle `σ` of `K` and an open edge `τ` of `C`, complementary;
  the two triangles of `L` on `τ` are straightened by
  `exists_isPLHomeomorphOn_straighten_two_halfSpaces_sub_mem` with `S = span τ`,
  `T = span σ`; then `L ↦ S ⊔ ℝu`, `K ∩ L ↦ T ⊓ (S ⊔ ℝu) = ℝu`, `C ↦ S`.
- Producer: `exists_small_homeomorph_curveCrossing_relative K B L C …`: a PL homeomorphism of
  `E`, `ε`-small, `EqOn h id Uᶜ` (support in the prescribed open `U ⊇ K.space`), `EqOn h id
  B.space` (the prescribed fixed subcomplex, assumed already transverse to `L`, as in the tree's
  relative lemma), with `HasPLCrossingAt (h '' K.space) L.space` at every common point and
  `HasPLCurveCrossingOnAt L.space (h '' K.space ∩ L.space) C.space` at every point of
  `h '' K.space ∩ C.space`.  Non-relative use: `B := ⊥`.
- Duplication, for the lead: `…_linearize_coface_pair_fixing` repeats the proof of
  `exists_isPLHomeomorphOn_linearize_coface_pair_sub_mem` because that statement does not export
  that the map fixes the edge line (`EqOn F id S` is dropped there); and
  `exists_small_homeomorph_transverse_relative` repeats the body of
  `exists_small_homeomorph_generalPosition_relative` because that statement hides the transverse
  image complex.  At merge, exporting both facts from `GeneralPosition` would let these two go.

## exists_section34FaceBalls (P3) — STUCK (bricks 1-2 in place; four inputs missing)

- Remaining goal: the frozen statement.  With the bricks, what is still missing:
  1. Source nested balls and transfer (Lemma 3): for each `s`, topological `3`-cells
     `C₁ ⊆ interior C₂`, `C₂ ⊆ c.source` for a carrier chart `c` (`hctrl`, last clause), with
     `h '' simplexBody 𝒦 s.1 ⊆ interior C₁` and `C₂` inside a prescribed open `W_s`, whose chart
     images satisfy `IsSphericalShell` and `IsBicollared` (then brick 1 gives the PL cell).  Needs
     a shell-separated pair of regular neighbourhoods of `σ` in `U` with an outer collar, and
     `h (interior B) = interior (h B)` (invariance of domain for the embedding `hh`).
  2. Choice of `W_s` giving fields 3, 4 and `Section34Exterior`: inside `interior (H t.1)` for
     the finitely many incident `t`, off the compact `tgtV w` of non-incident `w` (graph-frame
     clause 8), pairwise meeting only inside `interior (⋃ w, tgtV w)`, and the component clause
     of `Section34Exterior`.
  3. General position (fields 5, 6, 8, 9): a finite complex `L` in the chart triangulating a
     compact piece of `c '' (frontier (⋃ w, tgtV w) ∩ c.source)` around the ball, as a
     combinatorial surface, with a `1`-subcomplex `C` for the splitting circles `tgtEBd e`
     through interior edges, and a triangulation `K` of the chart image of `fblBd s`; then brick
     2 plus `HasPLCrossingAt.congr` / `HasPLCurveCrossingOnAt.congr`.  The frontier of the
     `f₁`-image of the cut neighbourhood being a PL surface is not stated in the tree.
  4. Field 7 (Lemma 4): `CarriesFirstHomologyOnto (fblBd s ∩ frontier T_s) T_s`.  The graph
     frame gives `CarriesFundamentalGroupOnto (h '' simplexRim 𝒦 s.1) T_s`, which
     `hurewiczOne_surjective` (integral, `Homology/HurewiczOne.lean`) would turn into `H₁`
     surjectivity of the rim once naturality of `hurewiczOne` is stated (it is not); missing is
     Lemma 4's passage from the rim to the trace, a homology in `T_s` between the rim and a
     cycle of the trace (the auxiliary-disk argument).

## exists_section34Compression (P4) — STUCK (not attempted beyond the survey)

- Remaining goal: the frozen statement.  Missing: (1) the surgery in one chart: `w` is incident
  to `s` (from field 3 and `Jd ⊆ fbl s ∩ tgtV w`, which needs `tgtVBd w ⊆ tgtV w` from the cut
  frame boundary formula), hence to every tetrahedron `t` incident to `s`, so the first clause of
  `Section34Exterior` puts `fbl s ∪ Dj` in `interior (H t.1) ⊆ c.source`; `Jd` cuts the PL
  sphere `fblBd s` into two disks (Jordan-Schoenflies on a PL `2`-sphere), each glued to a
  push-off of `Dj` gives a PL sphere bounding a ball in the chart (PL Schoenflies in `ℝ³`;
  `SphereSchoenflies` / `PLSchoenflies` exist, fit not checked); keep the one containing
  `h '' simplexRim 𝒦 s.1`; (2) general position of the push-off, by brick 2 relative to the
  untouched part of the sphere; (3) the ten fields afterwards, field 7 needing `Jd`
  null-homologous in `T_s` (it bounds `Dj` there); (4) `c⁺ + 1 ≤ c` and `p⁺ ≤ p`, needing the
  trace to be a finite union of disjoint circles (a consequence of field 5 not stated in the
  tree) and `Dj` disjoint from every `tgtE e`.
