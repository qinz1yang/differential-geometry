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

# Batch 5 (P3 inputs)

## Input (4): Hurewicz naturality and Lemma 4's rim-to-trace step — CLOSED (step 2 takes the trace retraction as a hypothesis, produced in (3))

Files (new, untracked, sorry-free; no existing file touched):

| file | lines | SHA-256 |
|---|---|---|
| `DifferentialGeometry/Topology/PiecewiseLinear/FirstHomologyCarrying.lean` | 377 | `d0270bb6ba82208a34fe76ce5a46969d57f92355a7e6a229652eb1ec5a66eb78` |
| `DifferentialGeometry/Topology/PiecewiseLinear/CellTraceFirstHomology.lean` | 330 | `698e1cce8118b524f1e92c9e1bd52cb03a6cf844665642ff941c47aade7ef4ec` |

Import lines (the second imports the first; the first imports the accepted
`Section34FaceBallVocabulary`):

    import DifferentialGeometry.Topology.PiecewiseLinear.FirstHomologyCarrying
    import DifferentialGeometry.Topology.PiecewiseLinear.CellTraceFirstHomology

Checker lines:

- `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\FirstHomologyCarrying.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T01:20Z)
- `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\CellTraceFirstHomology.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T01:24Z)

Audit `C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a\AuditTube6.lean` (both modules):

- `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a\AuditTube6.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T01:25:52Z)

Grep before writing: `Homology/` has `hurewiczOne`, `hurewiczOne_surjective` and the field
version `FieldHurewiczOne` with no naturality; `HandlePieceEulerChar` has only the field-coefficient
factorisation `exists_linearMap_fieldHurewiczOne`.  No integral degree-one cycle class with a
naturality lemma existed (degree 0 has `integralZeroChainClass_map`), so one was added.

Public names, `DifferentialGeometry.Topology`: `integralOneCycleClass` (def),
`integralOneCycleClass_surjective`, `integralOneCycleClass_eq_iff`,
`mem_ker_sc_one_of_mem_integralSingularCycles`, `integralOneCycleClass_eq_moduleHomologyClass`,
`integralSingularChainMap_mem_integralSingularCycles`, `integralOneCycleClass_map`,
`integralPathChain_map`, `integralLoopHomologyClass_map`, `hurewiczOne_map`.
`DifferentialGeometry.Topology.PiecewiseLinear`:
`CarriesFundamentalGroupOnto.carriesFirstHomologyOnto`, `CarriesFirstHomologyOnto.mono`,
`CarriesFirstHomologyOnto.of_homotopic`, `integralSingularChainMap_inclusion_apply`,
`integralSingularChains_d_eq_zero_of_inclusion`, `integralSingularChains_d_inclusion_eq_zero`,
`CarriesFirstHomologyOnto.exists_cycle`, `carriesFirstHomologyOnto_of_forall_cycle`,
`exists_boundary_of_subsingleton_integralSingularHomology`,
`exists_boundary_sub_mem_integralSingularChainsIn_inter`,
`CarriesFirstHomologyOnto.of_mayerVietoris`, `IsPLCellOn.exists_homeomorph`,
`IsPLCellOn.subsingleton_integralSingularHomology_one`,
`IsPLCellOn.subsingleton_integralSingularHomology_one_boundary`, `dist_radialDeformation_le`,
`IsPLCellOn.carriesFirstHomologyOnto_inter_interior`,
`CarriesFirstHomologyOnto.inter_frontier_of_homotopic`.  All grepped tree-wide: no clash.

What each gives P3 (the consumer shapes were chosen by me; the leaf forces none of them):

- Naturality: `hurewiczOne_map f x γ : (hurewiczOne (f x) (map f x γ)).toAdd =
  integralSingularHomologyMap 1 f (hurewiczOne x γ).toAdd`, through `integralOneCycleClass_map`.
- The graph frame's generator clause to `H₁`:
  `CarriesFundamentalGroupOnto.carriesFirstHomologyOnto (h : CarriesFundamentalGroupOnto J T)
  (hJ : J.Nonempty) (hT : IsPathConnected T) : CarriesFirstHomologyOnto J T`.  Both extra
  hypotheses are necessary (`H₁` of a path component missed by `J` is not hit).  For P3,
  `J = h '' simplexRim 𝒦 s.1` and `T = section34FaceTorus tgtV s`; path-connectedness of `T` is
  still to be derived there (every vertex ball of `T` meets `J`).
- Lemma 4, step 1 (`IsPLCellOn.carriesFirstHomologyOnto_inter_interior`), in a metric
  `3`-manifold: `IsPLCellOn 3 C Bd`, `C'` compact with `Subsingleton (H₁ C')`, `R ⊆ C'`,
  `R ⊆ interior C`, `C ∩ C' ⊆ interior T`, `CarriesFirstHomologyOnto R T` give
  `CarriesFirstHomologyOnto (Bd ∩ interior T) T`.  Route: Mayer--Vietoris in `C'` for the open
  cover `interior C \ (C' \ interior T)` and the complement of the inner shell image
  `{minimumCoordinate ≥ δ}` (chain level: small chains of the cover,
  `exists_small_boundary_of_boundary`), then the tree's `radialDeformation` of the simplex onto
  its boundary, which moves a point by at most `6 · minimumCoordinate`
  (`dist_radialDeformation_le`), inside an `ε`-thickening of `C ∩ C'` contained in
  `interior T` (uniform continuity of the cell parametrisation).  `C'` is the book's auxiliary
  ball `C'` around the disk `τ'`; any compact set with trivial `H₁` works, e.g. a PL cell
  (`IsPLCellOn.subsingleton_integralSingularHomology_one`).
- Lemma 4, step 2 (`CarriesFirstHomologyOnto.inter_frontier_of_homotopic`): `S` closed with
  `Subsingleton (H₁ S)` (for `S = Bd`: `IsPLCellOn.subsingleton_integralSingularHomology_one_boundary`,
  through the tree's `stdSimplexNormedBoundarySphereHomeomorph` into the sphere of
  `EuclideanSpace ℝ (ULift (Fin 3))`, which keeps the universe of `M₂`), `T` closed,
  `CarriesFirstHomologyOnto (S ∩ interior T) T`, an open `N ⊇ S ∩ frontier T` and a map
  `g : C(S ∩ interior T ∩ N, S ∩ frontier T)` homotopic in `T` to the inclusion give
  `CarriesFirstHomologyOnto (S ∩ frontier T) T`: field 7 of the invariants.  The retraction
  `(N, g)` is the one input of Lemma 4 not produced here: it is a collar of the trace in
  `Bd ∩ T`, to come from the triangulation of (3) (a triangulation of `Bd` with subcomplexes
  `Bd ∩ T` and `Bd ∩ frontier T`, and the tree's `derivedNeighborhoodStrongDeformationRetract`
  of the trace, which must additionally keep `Bd ∩ T` invariant).
- Remaining for field 7 in P3 itself: the choice of the auxiliary compact `C'` with
  `C ∩ C' ⊆ interior T` (the book's disk `τ` spanning `∂σ` in a tetrahedron, thickened), the
  path-connectedness of `T`, and the retraction above.

## Input (3): triangulation `L ⊇ C` of a surface with a curve system, and the trace retraction — CLOSED (abstract form; its P3 hypotheses are listed below)

Files (new, untracked, sorry-free; no existing file touched):

| file | lines | SHA-256 |
|---|---|---|
| `DifferentialGeometry/Topology/PiecewiseLinear/SurfaceCurveTriangulation.lean` | 239 | `18693202d3bef50c139ffa04f8c84a9ea47f13dba2bfbc0cec692b636e3c538a` |
| `DifferentialGeometry/Topology/PiecewiseLinear/DerivedNeighborhoodOpenRetraction.lean` | 72 | `f7242214a867408bfb1209b3f7d822c08c8af3e091de6875b29599b39bc9c6e8` |

Import lines (independent of each other and of input (4)):

    import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCurveTriangulation
    import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodOpenRetraction

Checker lines:

- `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\SurfaceCurveTriangulation.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T01:34Z)
- `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\DerivedNeighborhoodOpenRetraction.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T01:37Z)

Audit `C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a\AuditTube7.lean` (both modules):

- `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a\AuditTube7.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T01:38:58Z)

Public names (grepped, no clash): `notMem_boundaryComplex_two_of_two_cofaces`,
`exists_isCombinatorialManifoldWithBoundary_two_curve_eventually_mem_iff`,
`exists_isOpen_homotopic_retraction_of_faces_subset`.

- `exists_isCombinatorialManifoldWithBoundary_two_curve_eventually_mem_iff` (finite-dimensional
  `E`, the lowest layer; the chart target is the case `E = ℝ³`): `S` a topological surface
  (every point has an open `W` with `W ∩ S` homeomorphic to an open subset of `ℝ²`),
  `IsLocallyPolyhedral S`, a finite complex `G` with faces of card `≤ 2` and `|G| ⊆ S`, `Q ⊆ S`
  compact give finite `L`, `C` with `IsCombinatorialManifoldWithBoundary 2 L`,
  `C.faces ⊆ L.faces`, faces of `C` of card `≤ 2`, edges of `C` not in `boundaryComplex 2 L`,
  and near every `x ∈ Q`: `y ∈ L.space ↔ y ∈ S` and `y ∈ C.space ↔ y ∈ |G|`.  These are
  literally the hypotheses `hL hCL hC hCB` of `exists_small_homeomorph_curveCrossing_relative`
  (brick 2), and the local agreement is what `HasPLCrossingAt.congr` /
  `HasPLCurveCrossingOnAt.congr` need to read the crossings on the actual sets.  Route: polyhedral
  neighbourhood of `Q` in `S` (`exists_isPolyhedron_neighborhood_of_isCompact`), triangulate it
  with `|G|`, common subdivision with `G` (`exists_isSubdivision_restrict_isSubdivision`), fine
  subdivision (`exists_isSubdivision_diam_lt_restrict_isSubdivision`), `LocalSurfaceLink`
  (`isPLSphere_one_geometricLink_of_homeomorph`,
  `exists_isSubdivision_neighborhood_of_forall_geometricLink` on a compact neighbourhood `Q₁`);
  `C` = faces of `L` inside `|G| ∩ Q₁`, of card `≤ 2` via `IsSubdivision.card_le`; every face of
  the subdivision at a vertex of `Q₁` lies in `L`, so the hinge lemmas
  `exists_card_three_superset_of_inter_eq`, `exists_second_triangle_of_inter_eq` give each edge of
  `C` two triangles of `L`, and `notMem_boundaryComplex_two_of_two_cofaces` excludes it from the
  boundary.
- `exists_isOpen_homotopic_retraction_of_faces_subset` (for Lemma 4, step 2): a subcomplex `B` of
  a finite `A` has an open `N ⊇ |B|` and `g : C(|A| ∩ N, |B|)` homotopic in `|A|` to the
  inclusion (the tree's `derivedNeighborhoodStrongDeformationRetract` of the derived
  neighbourhood, a neighbourhood of `|B|` in `|A|` by `derivedNeighborhood_mem_nhdsWithin`).  With
  `|A| = Bd ∩ T`, `|B| = Bd ∩ frontier T` (chart images) it gives the `(N, g)` of
  `CarriesFirstHomologyOnto.inter_frontier_of_homotopic` by restriction.
- Still owed in P3 to use these: (a) that the chart image of `frontier (⋃ w, tgtV w)` is, near
  the face ball, a locally polyhedral topological surface containing the chart images of the
  splitting circles `tgtEBd e` as a finite `1`-complex (from `IsLocallyFinitePolyhedralManifoldWithBoundary 3`
  of the cut neighbourhood in the graph frame, the PL embedding `f₁` and the cut frame's
  boundary formula for splitting disks; not stated in the tree); (b) a triangulation of the
  chart image of `fblBd s` with `fblBd s ∩ T` and `fblBd s ∩ frontier T` as subcomplexes
  (`exists_isSubdivision_restrict_space` twice, once `fblBd s ∩ T` and its frontier trace are
  known polyhedra).

## Input (1): source-side balls around a disk, shell and outer collar, carried through `h` — CLOSED

Files (new, untracked, sorry-free; no existing file touched):

| file | lines | SHA-256 |
|---|---|---|
| `DifferentialGeometry/Topology/PiecewiseLinear/TopologicalCellNestedShell.lean` | 539 | `68b4cb43189c4bbd1ebcef56e98cfe7e0d408b2137450e86ae9572a621af15ff` |
| `DifferentialGeometry/Topology/PiecewiseLinear/LocalDiskBallNeighborhood.lean` | 105 | `8d7b83e0162c40a023669f33249be3eabb8d9c4294e9152780f9cfc13e6819ef` |
| `DifferentialGeometry/Topology/PiecewiseLinear/DiskBallNeighborhoodImage.lean` | 313 | `df2d568ff3a4fe866112427dc8b90b0823bc788dfefd06a9917c2023713ad5eb` |

Import lines (the first imports brick 1 `ChartTameNestedCells`; the third imports the other two):

    import DifferentialGeometry.Topology.PiecewiseLinear.TopologicalCellNestedShell
    import DifferentialGeometry.Topology.PiecewiseLinear.LocalDiskBallNeighborhood
    import DifferentialGeometry.Topology.PiecewiseLinear.DiskBallNeighborhoodImage

Checker lines:

- `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\TopologicalCellNestedShell.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T02:05Z)
- `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\LocalDiskBallNeighborhood.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T02:08Z)
- `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\DiskBallNeighborhoodImage.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T02:14Z)

Audit `C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a\AuditTube8.lean` (all three):

- `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a\AuditTube8.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T02:14:58Z)

Public names (grepped, no clash): `closedBallParam_image_norm_le`,
`IsTopologicalCell.exists_nested_isSphericalShell_isBicollared`,
`Moise305Tame.exists_isPLBall_of_isTopologicalCell`,
`Moise305Tame.exists_isPLCellOn_of_isTopologicalCell`,
`isPLSphere_two_geometricLink_of_isSubdivision_of_forall_vertex`,
`exists_isPLBall_nhdsWithin_of_isPLBall_two`, `LocallyFinitePLPieceIn.card_le_four`,
`LocallyFinitePLPieceIn.finite_faces_inter_of_isCompact`,
`LocallyFinitePLPieceIn.exists_isPLBall_nhdsWithin_space_of_isPLBall_two`,
`Moise305Tame.exists_isPLCellOn_superset_image_of_isPLBall_two`.

The route differs from the book's wording in one respect, chosen by me: the shell and the outer
collar are built on the target side, inside one topological cell, rather than carried from the
source.  Then only a topological ball around the image of `σ` is needed from the source, and
PL structure is not needed on it.

- Shell and collar (`IsTopologicalCell.exists_nested_isSphericalShell_isBicollared`, `ℝ³`): for
  a topological `3`-cell `Y ≅ B³` and compact `K ⊆ interior Y`, the images `C₁ ⊆ C₂` of two
  round balls of radii `r₀ < ρ₁ < ρ₂ < 1` (`r₀` bounds the preimage of `K`) are cells with
  `K ⊆ interior C₁`, `C₁ ⊆ interior C₂`, `C₂ ⊆ interior Y`; the closure of `C₂ \ C₁` is the
  spherical shell `(u, t) ↦ φ⁻¹((ρ₁ + t(ρ₂ - ρ₁)) u)`; the frontier of `C₂` is bicollared
  through the tree's `exists_twoSidedCollar_of_closedInterval`, using the radial collar
  `(x, s) ↦ φ⁻¹((1 + s) φ x)`.  The collar's range is a neighbourhood of the frontier because
  the image of the open annulus is `interior (image of the outer ball)` minus a closed set,
  interiors of such images coming from `interior_range_eq_image_preimage_interior` (invariance of
  domain).  Hence `Moise305Tame.exists_isPLBall_of_isTopologicalCell` (a PL ball between `K` and
  `Y`), and its chart form `Moise305Tame.exists_isPLCellOn_of_isTopologicalCell` (through brick 1).
- Source balls (`exists_isPLBall_nhdsWithin_of_isPLBall_two`): in a finite complex of dimension
  at most three, over an open `O` whose faces have only vertices with `2`-sphere links, every
  vertex of every subdivision in `O` has a `2`-sphere link (local version of
  `IsCombinatorialManifold.of_isSubdivision`: `geometricLink_insert`,
  `isPLSphere_geometricLink_faces_of_isPLSphere`,
  `isPLSphere_geometricLink_of_isPLSphere_geometricLink`,
  `isPLSphere_geometricLink_of_forall_card_le`).  So
  `exists_isSubdivision_neighborhood_of_forall_geometricLink` (`LocalSurfaceLink`, `n = 2`)
  gives a combinatorial `3`-manifold with boundary around a PL disk `D`, and
  `exists_isPLBall_derivedNeighborhood_disk` gives a PL `3`-ball neighbourhood of `D` in `O`.
  For a locally finite `𝒦` (`...exists_isPLBall_nhdsWithin_space_of_isPLBall_two`) the finite
  complex is `restrict 𝒦 (⋃ closed stars of the vertices of the faces meeting D)`.  `O` is then
  shrunk off the faces having a vertex outside that set.
- Lemma 3 (`Moise305Tame.exists_isPLCellOn_superset_image_of_isPLBall_two`): with `U` open,
  `𝒦` a combinatorial `3`-manifold (`isCombinatorialManifold_of_locallyFinitePLPieceIn` or the
  cut frame), `h` continuous and injective on `U`, a PL disk `D ⊆ |𝒦|` (for P3:
  `convexHull s.1`, via `isPLBall_convexHull_of_affineIndependent`), a chart `c` of the maximal
  atlas and an open `W ⊆ c.source` containing `h(𝒦.map D)`, there is `IsPLCellOn 3 C B` with
  `h(𝒦.map D) ⊆ interior C` and `C ⊆ W`.  The images of relative neighbourhoods are open by
  `isOpen_image_of_continuousOn_injOn` (invariance of domain on manifolds).  No `HasGroupoid`,
  no metric, no `T2Space`.  In P3, `W` is the open set that input (2) must supply.

## Input (2): neighbourhood choice for fields 3, 4 and `Section34Exterior` — IN PROGRESS (two bricks closed; the component clause of `Section34Exterior` is being built)

Files (new, untracked, sorry-free; no existing file touched):

| file | lines | SHA-256 |
|---|---|---|
| `DifferentialGeometry/Topology/PiecewiseLinear/LocallyFiniteSeparatingNeighborhoods.lean` | 102 | `b28a9696c26cf4cc1e37a1210bec591daaa3c85ca36fc9b4b85fd97f16a6fcee` |
| `DifferentialGeometry/Topology/PiecewiseLinear/Section34VertexBallStar.lean` | 281 | `041743fb69ea4a2d86e111592309b77c388abff397dbfce31ac53467b3a0b76c` |

Import lines (the first imports only Mathlib; the second imports the accepted
`Section34FaceBallVocabulary`, `OpenStar`, `LinkDimension`, `LocallyFiniteSplittingDisks`):

    import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteSeparatingNeighborhoods
    import DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexBallStar

Checker lines:

- `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\LocallyFiniteSeparatingNeighborhoods.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T02:20Z)
- `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\Section34VertexBallStar.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T02:50Z)

Audits (`AuditTube9.lean`, `AuditTube10.lean` in `C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a`):

- `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a\AuditTube9.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T02:22:14Z)
- `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a\AuditTube10.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T02:52:27Z)

Public names (grepped, no clash): `exists_isOpen_inter_subset_interior_of_locallyFinite`,
`LocallyFinitePLPieceIn.isClosed_preimage_avoidingUnion`,
`LocallyFinitePLPieceIn.subset_openStar_of_isPreconnected`, `IsPLCellOn.isConnected`,
`image_openStar_subset_section34CarrierSupport`, `image_vertexBall_subset_image_openStar`,
`image_vertexBall_subset_interior_of_incident`, `section34TetraObstacle_subset_interior`.

- Fields 3 and 4 (`exists_isOpen_inter_subset_interior_of_locallyFinite`, any metric space): a
  locally finite family of closed `A i` whose pairwise intersections lie in `interior Z`, and open
  `G i ⊇ A i`, give open `W i` with `A i ⊆ W i ⊆ G i` and `W i ∩ W j ⊆ interior Z` for `i ≠ j`
  (Voronoi cells of the `A i \ interior Z` against the union of the others).  For P3, in the
  metric space `h '' U`: `A s = h '' simplexBody 𝒦 s.1` (locally finite by the carrier control),
  `Z = ⋃ w, tgtV w` (pairwise intersections of triangles lie on the graph, inside
  `interior (f₁ '' N)` by graph-frame clause 4), and `G s` = `c.source` ∩ the interiors of the
  `H t`, `t ⊇ s` ∩ the complement of the non-incident `tgtV` (graph-frame clause 8) ∩
  `h '' 𝒦.map '' ⋃ v ∈ s, openStar v`.  Lemma 3 (input (1)) then puts the face ball in `W s`.
- `Section34Exterior`, clause 1: the vertex-ball part holds with no smallness of the vertex balls
  (`section34TetraObstacle_subset_interior`, given `fbl s ⊆ interior (H t)` for incident `t`,
  which the choice of `G s` gives).  Route: `f₁ '' V_w` is connected, lies in `h '' U` and misses
  `h` of every triangle not incident to `w` (clause 8); pulled back along the embedding
  `h ∘ 𝒦.map` it lies in the open star of each vertex of the carrier of `w`, because a
  preconnected set meeting the open star of `a` and missing the triangles not containing `a`
  stays in it (the link of `a` is a PL `2`-sphere, so every face of the link lies in a triangle
  of the link: `exists_face_superset_card_eq_of_isPLSphere`); and that open star lies in the
  carrier support of every face containing `a`.  Clause 2 is graph-frame clause 6.
- `Section34Exterior`, clause 3 (not yet built): `y ∉ obstacle` follows from field 3 and
  `interior (tgtV w) ∩ tgtV w' = ∅` for `w ≠ w'` (the cut frame's intersection formula,
  `IsPLCellOn.image_boundary_interior`).  The component half is true for every frame, by this
  route, now being formalised: (a) the obstacle lies in `h` of `O_t = ⋃ v ∈ t, openStar v`, so
  the full subcomplex `K₀` on the vertices outside `t` misses it, and `frontier (H t)` lies in
  `h '' K₀`; (b) a chain of target vertex balls and splitting disks along the subdivided edge of
  `y` reaches a vertex of `K₀` avoiding the obstacle; (c) if the component of `y` stayed in
  `interior (H t)`, the points whose carrier has a vertex of `K₀` in that component form a
  relatively clopen subset `R` of `|𝒦| \ hull t`, and because `closedStar v \ hull t` is
  connected for each vertex `v` of `t` (the cone on `|lk v| \ hull (t.erase v)`, connected by
  `exists_isPLHomeomorphOn_sphere_disk_to_simplex`), `R` or `R ∪ hull t` is clopen in `|𝒦|`, so
  the connected `H t` would equal its interior.

## Input (2), completed: `Section34Exterior` from four properties of the face balls — CLOSED

Files (new, untracked, sorry-free; no existing file touched), in addition to the two above:

| file | lines | SHA-256 |
|---|---|---|
| `DifferentialGeometry/Topology/PiecewiseLinear/TetrahedronStarComplement.lean` | 360 | `bf08e9cf96c6e041289ce79694f02c4998796be6b003a80863ae38ecde42a32d` |
| `DifferentialGeometry/Topology/PiecewiseLinear/SubdivisionSegmentStep.lean` | 118 | `7d71171000a1f883ebca38e486b1e3abe73b795311341f224f424e805b69c64e` |
| `DifferentialGeometry/Topology/PiecewiseLinear/Section34ExteriorComponent.lean` | 757 | `a44377ef705851ae56c7b60e573303195d01c14ce19cb717f01e1fea6bedd986` |

Import lines (the third imports the other two and `Section34VertexBallStar`):

    import DifferentialGeometry.Topology.PiecewiseLinear.TetrahedronStarComplement
    import DifferentialGeometry.Topology.PiecewiseLinear.SubdivisionSegmentStep
    import DifferentialGeometry.Topology.PiecewiseLinear.Section34ExteriorComponent

Checker lines:

- `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\TetrahedronStarComplement.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T03:05Z)
- `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\SubdivisionSegmentStep.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T03:10Z)
- `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\Section34ExteriorComponent.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T03:27:47Z)

Audit `C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a\AuditTube11.lean` (the three modules):

- `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a\AuditTube11.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T03:28:42Z)

Public names (grepped, no clash): `isConnected_closedStar_sdiff_convexHull`,
`LocallyFinitePLPieceIn.exists_insert_mem_faces_ne`,
`LocallyFinitePLPieceIn.isPreconnected_iUnion_closedStar_sdiff_convexHull`,
`LocallyFinitePLPieceIn.exists_isClopen_of_isClopen_sdiff_convexHull`,
`LocallyFinitePLPieceIn.isOpen_preimage_of_carrier_class`,
`LocallyFinitePLPieceIn.exists_pair_mem_faces_lt_of_mem_segment`,
`exists_mem_frontier_connectedComponentIn_of_joinedIn`, `IsPLCellOn.isConnected_of_sdiff_subset`,
`src_vertexBall_inter_subset_srcBd`, `interior_image_vertexBall_inter_image_vertexBall`,
`exists_mem_src_vertexBall_inter_of_subset_edge`, `image_mem_connectedComponentIn_of_mem_segment`,
`section34Exterior_component`, `section34Exterior_of_subset`.

The P3-facing statement (`Section34ExteriorComponent.lean`):

    theorem section34Exterior_of_subset (hh : IsEmbedding (U.domRestrict h))
        (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (hctrl : Section34CarrierControl U 𝒦 h η H)
        (hgraph : Section34GraphFrame U W h ψ H 𝒦 𝒦' src cr f₁)
        {fbl : Section34SimplexIndex 𝒦 3 → Set M₂} (hfblc : ∀ s, IsClosed (fbl s))
        (hfblH : ∀ s t, Section34Incident s.1 t.1 → fbl s ⊆ interior (H t.1))
        (hfblV : ∀ s w, ¬ Section34Incident w.1 s.1 → fbl s ∩ section34VertexBallImage src f₁ w = ∅)
        (hfblS : ∀ s, fbl s ⊆ h '' (𝒦.map '' ⋃ v ∈ s.1, openStar 𝒦.complex v)) :
        Section34Exterior 𝒦 𝒦' h H (section34VertexBallImage src f₁) fbl

(the displayed binder types of `s t w` are abbreviated here; in the file they are
`Section34SimplexIndex 𝒦 3`, `Section34SimplexIndex 𝒦 4`, `Section34VertexIndex 𝒦 𝒦'`).  `hfblV`
is literally field 3 of the invariants; the other three are met by choosing the open sets `W s`
of the Voronoi brick inside `interior (H t)` and inside `h '' 𝒦.map '' ⋃ v ∈ s, openStar v` (an
open set of `M₂` by invariance of domain).  So `Section34Exterior` is not a frame defect: all
three clauses follow from the frozen frames, whatever the size of the vertex balls.

Route of the component clause (formerly the open question): if the component `Z` of `y` in the
complement of the (closed) obstacle left `interior (H t)`, a path in `Z` exits through the
frontier (`exists_mem_frontier_connectedComponentIn_of_joinedIn`).  Otherwise: the obstacle lies
in `h` of the open stars of the vertices of `t`, so the faces of `𝒦` without vertices in `t` map
into its complement; the vertex balls of `𝒦'` along the subdivided edge `ax` of `y` (`x ∉ t`),
minus the incident balls, link `y` to `h x` inside the complement (splitting disks of consecutive
vertices; `exists_pair_mem_faces_lt_of_mem_segment` walks the subdivided edge); the points whose
carrier has a vertex outside `t` with image in `Z` form a relatively clopen subset of `|𝒦| \ t`
(`isOpen_preimage_of_carrier_class`), and since each `closedStar v \ t` is connected (the cone on
the link minus a disk: `IsPLSphere.isConnected_sdiff_of_isPLBall_two`,
`IsConeBase.isConnected_sdiff_coneComplex`) and these meet pairwise (second coface of a triangle
from its `0`-sphere link), that set extends to a clopen subset of `|𝒦|` inside its union with `t`
(`exists_isClopen_of_isClopen_sdiff_convexHull`); it contains the preimage of the connected cell
`H t` and maps into `interior (H t)`, so the frontier of `H t` would be empty, contradicting
`IsPLCellOn 3 (H t) (frontier (H t))`.

## P3 brick: neighbourhoods and cells for the face balls (`Section34FaceBallNeighborhoods`) — CLOSED

| file | lines | SHA-256 |
|---|---|---|
| `DifferentialGeometry/Topology/PiecewiseLinear/Section34FaceBallNeighborhoods.lean` | 310 | `4fea2cc791f99ec55793c3d5eb17fc0603e3b9644dfc26d21c9107cd0fb59787` |

    import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceBallNeighborhoods

- `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\Section34FaceBallNeighborhoods.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T03:39Z)
- `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a\AuditTube12.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T03:40:39Z)

Public name (grepped, no clash): `exists_section34FaceBallNeighborhoods`.  From `h305 hU hh hcut
hctrl hgraph` and any closed `Bad s` missing `h '' simplexBody 𝒦 s.1`, it gives open `Wn s` in a
maximal-atlas chart `c s` (the chart of a carrier of a tetrahedron containing `s`), with
`h '' simplexBody 𝒦 s.1 ⊆ Wn s`, `Wn s ⊆ interior (H t.1)` for every incident `t`,
`Wn s ∩ tgtV w = ∅` for non-incident `w`, `Wn s ∩ Wn s' ⊆ interior (⋃ w, tgtV w)` for `s ≠ s'`,
`Wn s ⊆ h '' 𝒦.map '' ⋃ v ∈ s.1, openStar v`, `Disjoint (Wn s) (Bad s)`, and a PL cell `C ⊆ Wn s`
with `h '' simplexBody 𝒦 s.1 ⊆ interior C` (input (1)'s Lemma 3).  Any closed family of cells
`fbl s ⊆ Wn s` with `h '' simplexRim 𝒦 s.1 ⊆ interior (fbl s)` then satisfies invariant fields 1,
2, 3, 4 and, through `section34Exterior_of_subset`, field 10 (`Section34Exterior`).  Route:
Voronoi brick in the metric space `h '' U` (open by invariance of domain); the bodies are locally
finite there (each lies in its own carrier); `h ∘ 𝒦.map` is an embedding of `|𝒦|` onto
`h '' U`, so the image of the (relatively open) open stars is open.

## exists_section34FaceBalls (P3) — IN PROGRESS (all four inputs closed; fields 1-4 and 10 constructed; fields 5-9 open)

State: with `exists_section34FaceBallNeighborhoods` and `section34Exterior_of_subset`, the frozen
statement is reduced to making the cells satisfy fields 5-9 without leaving `Wn s` and keeping
`h '' simplexRim 𝒦 s.1` inside.  Nothing found false; no frame defect (the earlier worry about
`Section34Exterior` is resolved above).  Remaining obligations, independent of each other:

1. (surface) For each `s`, with `T_s = section34FaceTorus tgtV s` (only incident vertex balls, all
   inside `interior (H (ts s))`, hence in the chart `c s`): `S = frontier (c '' T_s)` satisfies the
   hypotheses of input (3)'s `exists_isCombinatorialManifoldWithBoundary_two_curve_eventually_mem_iff`.
   Locally polyhedral: `c '' tgtV w` is a PL ball in `ℝ³` (PL cell in a maximal-atlas chart; a
   lemma to state), so `c '' T_s` and its frontier are polyhedra (`IsPolyhedron.frontier`).
   Topological surface: a point lies in at most two vertex balls (cut-frame clauses 22-23), so
   near it `S` is the frontier of one ball or of the union of two adjacent ones, a PL ball by
   `isPLBall_union_of_inter_isPLBall_two`; owed: a PL `2`-sphere in `ℝ³` is locally homeomorphic
   to open subsets of `ℝ²` (through `stdSimplexNormedBoundarySphereHomeomorph` and the sphere's
   charts).  Curves `G`: the chart images of the splitting circles `tgtEBd e` of incident edges,
   finitely many PL circles in `S` (their points lie in exactly two vertex balls), triangulated.
   Near `c '' Wn s`, `frontier (⋃ tgtV)` and `frontier T_s` agree (non-incident balls miss `Wn s`).
2. (sphere triangulation) a finite combinatorial triangulation `K` of `c '' fblBd s` (a PL
   `2`-sphere in `ℝ³`).
3. (general position) brick 2 `exists_small_homeomorph_curveCrossing_relative` with `B = ⊥`,
   `U = c '' Wn s` and `ε` below the distance from `c '' h '' simplexRim` to `c '' fblBd s`; the
   moved cell stays in `Wn s` (identity off `U`) and keeps the rim inside; transfer by
   `HasPLCrossingAt.congr` / `HasPLCurveCrossingOnAt.congr` with the local agreement from 1
   (fields 5, 6).  Field 8: a transverse triangle and edge in `ℝ³` meet in at most one point.
   Field 9: the transverse intersection is a closed `1`-manifold with finitely many faces
   (`exists_isPLSphere_cover_inter_of_transverse_faces`).
4. (field 7) input (4) step 1 with `R = h '' simplexRim 𝒦 s.1` (carries `H₁ T_s` by graph-frame
   clause 10, `CarriesFundamentalGroupOnto.carriesFirstHomologyOnto`; `T_s` path connected as a
   union of path-connected vertex-ball images each meeting the connected rim image), and the
   auxiliary compact `C' = h '' 𝒦.map '' B'` for a PL ball `B'` around the disk
   `closure (∂t \ s)` of an incident tetrahedron (`IsPLSphere.isPLBall_closure_sdiff`, then
   `LocallyFinitePLPieceIn.exists_isPLBall_nhdsWithin_space_of_isPLBall_two` inside the open set
   missing `s \ (h ∘ 𝒦.map)⁻¹ (interior T_s)`); pass `Bad s = C' \ interior T_s` to the
   neighbourhood brick so that `fbl s ∩ C' ⊆ interior T_s`.  Step 2 needs the retraction of the
   trace, from `exists_isOpen_homotopic_retraction_of_faces_subset` applied to a subdivision of
   the moved `K` in which `K ∩ L` is a subcomplex (faces inside `c '' T_s` form `A`, faces in
   `L` form `B`), transported by the chart.

# Batch 6 (P3 assembly)

## P3 obligation 2 — CLOSED (no new declaration)

A finite combinatorial triangulation of a PL `2`-sphere `S` in a finite-dimensional space is the
composite of two accepted lemmas: `hS.isPolyhedron.exists_simplicialComplex` gives `K` with
`K.faces.Finite` and `K.space = S`, and `IsPLSphere.isCombinatorialManifold (n := 1)` makes it a
combinatorial `2`-manifold.  To avoid a thin wrapper it is used inline in obligation 3's theorem
(first four lines of its proof).  For P3 the sphere is the chart image of `fblBd s`; its PL
sphere property comes from the chart image lemma of obligation 1.

## P3 obligation 3 — CLOSED at chart level (`ChartBallGeneralPosition`); the transfer to `M₂` by `.congr` is part of the assembly

| file | lines | SHA-256 |
|---|---|---|
| `DifferentialGeometry/Topology/PiecewiseLinear/ChartBallGeneralPosition.lean` | 169 | `c5e0293ecb837a6fa6fc4c1b2bcb59187c900ac9c4db6e15fbbac4e67ff7a49e` |

    import DifferentialGeometry.Topology.PiecewiseLinear.ChartBallGeneralPosition

- `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\ChartBallGeneralPosition.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T03:52Z)
- `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a\AuditTube13.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T03:53:32Z)

Public names (grepped, no clash): `subsingleton_convexHull_inter_convexHull_of_sup_eq_top`,
`exists_isPLBall_transverse_of_isPLBall`.

- `exists_isPLBall_transverse_of_isPLBall` (in `EuclideanSpace ℝ (Fin 3)`): a PL `3`-ball `P`,
  compact `A ⊆ interior P`, open `U ⊇ P`, a finite combinatorial surface `L` and a subcomplex `C`
  of dimension `≤ 1` through interior edges give a PL ball `P'` with `A ⊆ interior P'`,
  `P' ⊆ U`, `HasPLCrossingAt (frontier P') L.space x` at every common point (field 5),
  `HasPLCurveCrossingOnAt L.space (frontier P' ∩ L.space) C.space x` at every point of `C`
  (field 6), `(frontier P' ∩ C.space).Finite` (field 8), and finite `M ⊇ N` with
  `M.space = frontier P'`, `N.space = frontier P' ∩ L.space` and every open face of `M` outside
  `N` disjoint from `L.space`.  The trace is thus a finite union of convex sets (field 9: finitely
  many components), and `(M, N)` is the input of `exists_isOpen_homotopic_retraction_of_faces_subset`
  for obligation 4 step 2.  Route: brick 2's `exists_small_homeomorph_transverse_relative` with
  `B = ⊥` and a move smaller than the thickening margins of `P ⊆ U` and `A ⊆ interior P` (the
  same margin argument as `exists_generalPosition_solidTorus_relative`); crossings by
  `hasPLCrossingAt_of_transverse_faces` and `hasPLCurveCrossingOnAt_of_transverse_faces`;
  finiteness because a transverse triangle and edge of `ℝ³` meet in at most one point
  (`subsingleton_convexHull_inter_convexHull_of_sup_eq_top`, dimension count); `M` from
  `exists_isSubdivision_subcomplexes` with the polyhedron `frontier P' ∩ L.space`.
- Decidability note: the statement is over `EuclideanSpace ℝ (Fin 3)`, so `boundaryComplex` in
  `hCB` uses its `DecidableEq` instance, while brick 2 and input (3) (stated for general `E` under
  `open Classical`) use the classical one; the two are bridged by `convert` (subsingleton
  instances), as done inside the proof.

## P3 obligation 4 — CLOSED (both steps of field 7 reduced to lemmas; the complexes `A ⊇ B` of step 2 are built in the assembly from obligation 3's `(M, N)`)

| file | lines | SHA-256 |
|---|---|---|
| `DifferentialGeometry/Topology/PiecewiseLinear/Section34FaceTorusHomology.lean` | 394 | `d674d4324bd01e77d70dac738775259500b0dfcb855e986073cefdaba9b5e10c` |

    import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceTorusHomology

- `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\Section34FaceTorusHomology.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T04:01Z)
- `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a\AuditTube14.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T04:02:19Z)

Public names (grepped, no clash): `CarriesFirstHomologyOnto.inter_frontier_of_chart`,
`IsPLCellOn.isPathConnected`, `isPathConnected_section34FaceTorus`,
`carriesFirstHomologyOnto_image_simplexRim`, `exists_section34FaceTorusAuxiliary`.

- Step 1 (`IsPLCellOn.carriesFirstHomologyOnto_inter_interior`, input (4)) with `C = fbl s`:
  the carrying set `R = h '' simplexRim 𝒦 s.1` carries `H₁ T_s`
  (`carriesFirstHomologyOnto_image_simplexRim`: graph-frame clause 10 through
  `CarriesFundamentalGroupOnto.carriesFirstHomologyOnto`, `R` nonempty, `T_s` path connected by
  `isPathConnected_section34FaceTorus`: each incident vertex-ball image is path connected and
  contains `h` of its centre, which lies on the rim).  The auxiliary set
  (`exists_section34FaceTorusAuxiliary`, from `hh hcut hgraph` only): `C' = h '' 𝒦.map '' B'`
  with `B'` a PL ball around the disk `⋃ v ∈ s, hull (t.erase v)` of an incident tetrahedron `t`
  (equal to `closure (∂t \ s)`, a disk by `IsPLSphere.isPLBall_closure_sdiff` and
  `isPLSphere_biUnion_erase`), taken inside the open set missing the points of `s` whose image
  leaves `interior T_s`; so `C'` is compact with trivial `H₁` (a topological ball), contains
  `h '' simplexRim 𝒦 s.1`, and `C' \ interior T_s` misses `h '' simplexBody 𝒦 s.1`.  Passing
  `Bad s := C' \ interior T_s` to `exists_section34FaceBallNeighborhoods` gives
  `fbl s ∩ C' ⊆ interior T_s`, the last hypothesis of step 1.
- Step 2 (`CarriesFirstHomologyOnto.inter_frontier_of_chart`): if `S ⊆ c.source` is closed with
  trivial `H₁`, `T` closed, `S ∩ interior T` carries, and finite `A ⊇ B` in the chart have
  `A.space = c '' (S ∩ T)` and `B.space = c '' (S ∩ frontier T)`, then `S ∩ frontier T` carries.
  The derived-neighbourhood retraction of `B` in `A` (input (3)) is transported by `c.symm`.  In
  the assembly `S = fblBd s` (trivial `H₁` by
  `IsPLCellOn.subsingleton_integralSingularHomology_one_boundary`), and `A`, `B` are the faces of
  obligation 3's `M` lying in `c '' T_s`, resp. in `N`, using the local agreement of `L` with the
  chart image of `frontier T_s` from obligation 1.

## P3 obligation 1 — CLOSED (both general lemmas; Codex Q1 had not landed, grep at 04:05Z found no module or statement of either shape, so the lead can withdraw Q1)

| file | lines | SHA-256 |
|---|---|---|
| `DifferentialGeometry/Topology/PiecewiseLinear/ChartImagePLCell.lean` | 83 | `49fde77b60fbf484ec602b71d376aaa82e46ade00e59fb27cc8e3154df5eabae` |
| `DifferentialGeometry/Topology/PiecewiseLinear/PLSphereLocallyPlanar.lean` | 70 | `998daa2f15c4f14eed9687a68c092fc389b8f5e368cb00bc47b275eb820c6461` |

    import DifferentialGeometry.Topology.PiecewiseLinear.ChartImagePLCell
    import DifferentialGeometry.Topology.PiecewiseLinear.PLSphereLocallyPlanar

- `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\ChartImagePLCell.lean with no diagnostics; shared outputs unchanged.`
- `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\PLSphereLocallyPlanar.lean with no diagnostics; shared outputs unchanged.`
- `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a\AuditTube15.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T04:14:55Z, both modules)

Public names (grepped, no clash): `isPLAt_of_mem_maximalAtlas`,
`IsPLCellOn.exists_isPLHomeomorphOn_image_chart`, `IsPLCellOn.isPLBall_image_chart`,
`IsPLSphere.exists_isOpen_inter_homeomorph_of_two`.

- `isPLAt_of_mem_maximalAtlas`: a chart `c` of `(plGroupoid n).maximalAtlas M` is `IsPLAt n n c y`
  on its source; no `HasGroupoid` instance (`liftPropWithinAt_self_target` plus
  `compatible_of_mem_maximalAtlas_right`).
- `IsPLCellOn.isPLBall_image_chart`: `IsPLCellOn 3 S B`, `S ⊆ c.source` give
  `IsPLBall 3 (c '' S) ∧ c '' B = frontier (c '' S)` (general `B`, so it covers Q1's
  `B = frontier C`); the `d`-dimensional form returns the PL parametrisation `q` with
  `c '' B = q '' stdSimplexBoundary d`.
- `IsPLSphere.exists_isOpen_inter_homeomorph_of_two` (any finite-dimensional `E`): every
  `x ∈ S` has an open `W ∋ x` and an open `U ⊆ ℝ²` with `W ∩ S ≃ₜ U` (sphere chart of Mathlib's
  stereographic atlas pulled back through `stdSimplexNormedBoundarySphereHomeomorph`).  This is
  the local-surface hypothesis of input (3).
- The remaining obligation-1 content (the chart image of `frontier T_s` near `c '' Wn s` is locally
  one vertex-ball frontier or that of a union of two, with the splitting circles as the curves)
  is specific to P3 and is done inside the assembly module.

## P3 `exists_section34FaceBalls` — CLOSED (statement and variable block byte-identical to `Skeleton/Section34Normalization.lean`; no hypothesis dropped)

| file | lines | SHA-256 |
|---|---|---|
| `DifferentialGeometry/Topology/PiecewiseLinear/BallUnionFrontier.lean` | 315 | `2982c4cf3838b590986ff2838dce3135e3ec3fe592421826891f34a09220276d` |
| `DifferentialGeometry/Topology/PiecewiseLinear/Section34FaceBalls.lean` | 686 | `d63f8484d29982d889a1c8a68ffa714173674dcee18cd30e9919b774ed7e7e8f` |

    import DifferentialGeometry.Topology.PiecewiseLinear.BallUnionFrontier
    import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceBalls

- `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\BallUnionFrontier.lean with no diagnostics; shared outputs unchanged.`
- `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\Section34FaceBalls.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T04:49:15Z)
- `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a\AuditTube16.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T04:50:32Z, both modules: only `propext`, `Classical.choice`, `Quot.sound`; thirteen linters clean)

Public names (grepped, no clash except the intended leaf name):
`BallUnionFrontier`: `IsPreconnected.subset_of_disjoint_frontier`,
`exists_isOpen_inter_homeomorph_of_inter_eq`, `mem_frontier_iUnion_of_mem_frontier`,
`finite_image_connectedComponentIn_of_eq_iUnion`, `IsLocallyPolyhedral.of_forall_isOpen_inter_eq`,
`restrict_space_eq_inter_of_openSimplex`, `exists_simplicialComplex_iUnion_isPLSphere_one`,
`exists_isOpen_inter_frontier_iUnion_eq_isPLSphere`, `image_stdSimplexBoundary_subset_frontier_iUnion`.
`Section34FaceBalls`: `eq_or_eq_of_card_eq_one_of_subset_union`,
`exists_section34FaceBall_of_neighborhood`, `exists_section34FaceBalls`.

- Lead action: `exists_section34FaceBalls` has the leaf's name, so importing the module into the
  skeleton requires deleting the `sorry` leaf there (as for P5); the skeleton then has 4 leaves.
- Remaining obligation-1 content, done here: in the chart `c` of `H t` (`t` a tetrahedron on `s`;
  `T_s` and `Wn s` lie in `H t` by `image_vertexBall_subset_interior_of_incident` and the brick),
  the incident vertex-ball images are PL 3-balls meeting pairwise in chart images of splitting
  disks inside both frontiers (`src_vertexBall_inter_subset_srcBd`,
  `exists_splitDisk_src_eq_inter_vertexBall`) with no triple point (cut clauses 22, 23).  Hence
  `frontier (c '' T_s)` agrees near each point with the frontier of one ball or of a glued pair
  (`isPLBall_union_of_inter_isPLBall_two`), i.e. with a PL 2-sphere: locally planar and locally
  polyhedral.  The splitting circles of the incident edges are pairwise disjoint PL circles on it
  (each is in the closure of `frontier B_w` minus the disk, by
  `IsPLSphere.inter_closure_sdiff_eq_image_stdSimplexBoundary`), triangulated with at most two
  vertices per simplex through `IsPLSphere.isCombinatorialManifold`.  `Q := frontier (c '' T_s)`.
- Transfers: `c '' frontier T_s = frontier (c '' T_s)` (`image_frontier_of_isCompact`), and
  `frontier (⋃ w, tgtV w) ∩ Wn = frontier T_s ∩ Wn` because non-incident vertex balls miss `Wn`
  (`frontier_inter_open_inter`); fields 5, 6 by `.congr`; field 8 through `C.space`; the faces of
  `M` whose open simplex meets `c '' T_s` (resp. the surface) lie in it (convex open simplex,
  resp. the local agreement of `L` with the surface on the connected hull of an `N`-face), giving
  `A ⊇ B` by `restrict`; field 7 = step 1 (`Bad s = C' \ interior T_s`) + step 2; field 9 since
  the trace is `c.symm '' B.space`, a finite union of connected hulls; field 10 by
  `section34Exterior_of_subset`.

# Batch 7 (P4, bigon)

## P4 brick: compression of a ball along an inner proper disk (`ProperDiskCompression`) — CLOSED

| file | lines | SHA-256 |
|---|---|---|
| `DifferentialGeometry/Topology/PiecewiseLinear/ProperDiskCompression.lean` | 273 | `c18ac3d964546c880e886104759bf8e8b5c8ed1df6f6a122a2f8f2a713568716` |

    import DifferentialGeometry.Topology.PiecewiseLinear.ProperDiskCompression

- `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\ProperDiskCompression.lean with no diagnostics; shared outputs unchanged.`
- `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a\AuditTube17.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T05:22:48Z)

Public names (grepped, no clash): `exists_pos_forall_le_of_isCompact`,
`IsPLBall.exists_subset_disjoint_of_subset_frontier`, `IsPLBall.exists_compression_of_proper_disk`.

- `IsPLBall.exists_subset_disjoint_of_subset_frontier` (in `ℝ³`): a PL `3`-ball `Q`, a PL disk
  `D ⊆ frontier Q`, compact `K ⊆ interior Q`, open `U ⊇ D` give a PL ball `Q' ⊆ Q` with
  `K ⊆ interior Q'`, `Disjoint Q' D` and `Q ⊆ Q' ∪ C` for a compact `C ⊆ U`.  Route: the pair
  `(frontier Q, D)` goes to (tetrahedron boundary, face) by
  `exists_isPLHomeomorphOn_sphere_disk_to_simplex`, extends over the balls by
  `exists_isPLHomeomorphOn_extension_of_stdSimplexBoundary`; `Q'` is the pull-back of the
  H-polytope `{coord_a ≥ ε}` of the tetrahedron (`IsHPolytope.isPLBall`), `ε` below the minima of
  `coord_a` on `H '' K` and `H '' (Q \ U)`.
- `IsPLBall.exists_compression_of_proper_disk` (case (a) of Operation 1): `D ⊆ P` with
  `D ∩ frontier P = ∂D`, `K` compact preconnected in `interior P \ D`, `U ⊇ D` open give
  `P' ⊆ P` a PL ball with `K ⊆ interior P'`, `Disjoint P' D`, and an open `O` with
  `P' ∩ O = P ∩ O` and `frontier P' \ O ⊆ U` (split by
  `IsPLBall.exists_pair_union_eq_inter_eq_of_boundary_trace`, keep the side of `K`, shrink).
- Use in P4 case (a) (`Dj \ Jd ⊆ interior (fbl s)`): chart `c` of `H t`, `t` a tetrahedron on
  `s` (`w` is incident to `s` by field 3, so `fbl s ∪ Dj ⊆ interior (H t)` by `Section34Exterior`);
  `P = c '' fbl s`, `D = c '' Dj`, `K = c '' h '' simplexRim` (preconnected; it misses `D` since
  the rim is in `interior T_s` and `Dj` in the frontier of the vertex-ball union), and `U` with
  `U ∩ Σ ∩ P ⊆ D` (`Σ` the chart surface).  Then the new trace is the clopen part `trace ∩ O` of
  the old one, missing `Jd`: fields 1–6, 8–10 and both counts follow (`P' ⊆ P` gives 3, 4, 10;
  agreement on `O` gives 5, 6 by `.congr`; the old component through `Jd` has no successor, so
  `c⁺ + 1 ≤ c`; crossings are a subset).

## exists_section34Compression (P4) — STUCK (brick above closed; three obligations remain)

Exact remaining goals, in order of difficulty:
1. Local lemma for `U` (case (a)): an open `U ⊇ c '' Dj` with `U ∩ Σ ∩ c '' fbl s ⊆ c '' Dj`.
   At `x ∈ Dj \ Jd`: `Σ = tgtVBd w` near `x` and `Dj ∩ closure (tgtVBd w \ Dj) = Jd`
   (`IsPLSphere.inter_closure_sdiff_eq_image_stdSimplexBoundary`), so `Dj` is a neighbourhood of
   `x` in `Σ`.  At `x ∈ Jd`: the half of `Σ` beyond `Jd` lies outside `fbl s`; this needs field 5's
   crossing model at `x` with `α = β = 0` (a PL sphere is not locally a half-plane).
2. Field 7 after compression (case (a)): with `Z = fblBd s ∩ frontier T_s = Z₀ ⊔ Jd ⊔ Z₁` (sides
   `E₀`, `E₁` of `Jd` on the sphere, rim on the `E₁` side), old `Z` carries `H₁ T_s`, show `Z₁`
   carries.  Not a consequence of the rim alone (a ball containing the rim can meet `∂T_s` in a
   punctured torus with inessential boundary).  Proof route: (i) `Z` is a finite disjoint union of
   PL circles; (ii) disjoint essential circles on `∂T_s` are homologous up to sign in `T_s`
   (the tree has 28.9, `SeparatingPolygonDisk`, and only the carrying transfer
   `IsCombinatorialSolidTorus.carriesFundamentalGroupOnto_of_isPreconnected_sdiff`); (iii) the
   rim makes `P₁ ∩ ∂T_s` carry (`CarriesFirstHomologyOnto.of_mayerVietoris` on the ball `P₁` plus
   a retraction); (iv) a planar subsurface of the torus that carries has a carrying boundary
   circle, and if `P₁ ∩ ∂T_s` contains a punctured torus then `Z₀ ∪ Jd` is null, contradicting (ii).
3. Case (b) (`Dj \ Jd` outside `fbl s`): the only rim-side ball is `fbl s ∪ X ∪ (collar beyond
   Dj)`, `X` the pocket bounded by `E₁ ∪ Dj`.  Needs an enlargement brick (collar of a boundary disk
   on the exterior side; `exists_collar_of_boundary_disk_subset` in a shell) and the invariants of
   the grown ball; field 7 as in 2.  Field 3 and `Section34Exterior` look provable by one
   enclosure argument: a vertex ball not incident to `s` inside `X` forces, along the chain of
   vertex balls of an edge leaving the chart tetrahedron `t₁`, a point of
   `h '' simplexBody 𝒦' w''` (`w''` not incident to `t₁`) enclosed by `∂X ⊆ obstacle t₁` inside
   `H t₁`, contradicting `Section34Exterior`; the same argument gives `X ⊆ H t₂` for the other
   tetrahedron on `s`.  It needs a vertex of each link outside the tetrahedron (from
   `IsCombinatorialManifold 3`).  **Field 4 is at risk**: when `X`
   lies outside the vertex-ball union (the pocket under a dome of `fbl s` resting on `∂V_w`),
   another face ball `fbl s'` may enter `X` through `E₁ ∩ interior V_{w₂}` (`w₂` a common vertex)
   and leave `V_{w₂}` inside `X`; `hinv` does not exclude this, and then `(fbl s ∪ X) ∩ fbl s'`
   leaves `interior (⋃ w, tgtV w)`.  Not a certified counterexample (another ball could exist), but
   the book's Operation 1 (Lemma 6 checks 5(5) only on boundaries) fails there.  Suggest a review of
   the case-(b) branch before further work on it.
4. Counts: routine from the brick (clopen part of the trace, one component lost).

## exists_section34BigonSlide (P4b) — STUCK (soft half in place; the drag itself is missing)

- Checked: the other face balls miss `Dj` entirely (`Dj \ Jd` misses every `fblBd s'` by
  hypothesis; `B'` misses `fblBd s'` since a crossing of `s'`'s trace with the splitting circle
  inside `B'` would enter `Dj` (field 6), and `Bb ⊆ fbl s ∩ Σ` cannot lie in `fbl s'` (field 4));
  `w` and the other end `u` of `e` are incident to `s` (field 3), so a drag `Φ` supported near
  `Dj` plus a strip beyond `B'` inside `V_w ∪ V_u` keeps fields 3, 4, 10 (`Φ` preserves
  `⋃ tgtV`, the obstacles and `H t`), fields 5, 6 (`HasPLCrossingAt.of_isPLHomeomorphOn_mem_nhds`,
  `HasPLCurveCrossingOnAt.congr`), field 7 (`Φ ≃ id` on `T_s`: `CarriesFirstHomologyOnto.of_homotopic`),
  the trace count (homeomorphism of traces) and `p⁺ + 2 = p` (`x ≠ y` removed, no new crossings).
- Remaining goal: the chart-level drag.  In `ℝ³`: `Y = c '' (tgtV w ∪ tgtV u)` a PL ball
  (`isPLBall_union_of_inter_isPLBall_two`), the bigon `D ⊆ frontier Y` with `∂D = B ∪ B'`,
  `B' ⊆` the splitting circle, the sphere `S = c '' fblBd s` crossing `frontier Y` with
  `S ∩ D = B`; produce a PL homeomorphism `Φ` of `ℝ³`, the identity off a compact subset of a
  given `U ⊇ D`, with `Φ '' Y = Y`, `Φ` PL-isotopic to the identity through maps preserving `Y`,
  and `Φ '' S ∩ frontier Y ∩ circle = (S ∩ frontier Y ∩ circle) \ Bb`.  Plan: straighten `Y`
  ambiently (`IsPLSphere.isSimplyEmbedded`), a disk neighbourhood of `D ∪` strip in `frontier Y`
  to a face (`exists_isPLHomeomorphOn_straighten_disk_in_tetrahedron`), the bigon in that face
  (planar Schoenflies), write the model drag, isotope it to the identity (Alexander trick,
  `ConeIsotopy`, `IsPLPseudoIsotopicToId`) and extend over a product neighbourhood of the face
  with a taper.  The missing piece is the relative normal form (trace arcs of `fbl s` and the
  splitting circle inside the straightened face).

# Batch 8 (P4 bricks)

## P4 item 1: neighbourhood of the compression disk (`CompressionDiskNeighborhood`) — CLOSED

| file | lines | SHA-256 |
|---|---|---|
| `DifferentialGeometry/Topology/PiecewiseLinear/CompressionDiskNeighborhood.lean` | 303 | `2fb1ee456a3709c6076628ddd711e91b967e982e7365a25d3f838d7c89f1254f` |

    import DifferentialGeometry.Topology.PiecewiseLinear.CompressionDiskNeighborhood

- `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\CompressionDiskNeighborhood.lean with no diagnostics; shared outputs unchanged.`
- `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a\AuditTube18.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T05:39:50Z)

Public names (grepped, no clash): `mem_closure_sdiff_image_stdSimplexBoundary`,
`exists_isOpen_inter_inter_subset_of_hasPLCrossingAt`, `exists_isOpen_inter_inter_subset_of_isPLSphere`.

- `exists_isOpen_inter_inter_subset_of_hasPLCrossingAt` (in `ℝ³`): `P` a PL `3`-ball, `D ⊆ S ∩ P`
  a PL disk with `D ∩ frontier P = ∂D`, `D` a neighbourhood in `S` of each point off `∂D`, and at
  each point of `∂D` the field-5 crossing `HasPLCrossingAt (frontier P) S x` plus small planar
  disks in `S`; then some open `U ⊇ D` has `U ∩ S ∩ P ⊆ D`.  Proof: at `x ∈ ∂D` the side chart
  `HasPLCrossingAt.exists_sideChart` (applied to the symmetric crossing, `X = P`) makes `S ∩ P` the
  half-disk `z₃ = 0, z₂ ≥ 0`; `D` fills its open half by connectedness (`D` is relatively open there
  and closed, and `x` is a limit of `D \ ∂D`, `mem_closure_sdiff_image_stdSimplexBoundary`), hence
  the closed half.  No half-plane case is needed: `exists_sideChart` rules it out itself.
- `exists_isOpen_inter_inter_subset_of_isPLSphere`: the same conclusion when `S` agrees on an open
  `O ⊇ D` with a PL `2`-sphere containing `D` (in P4: `tgtVBd w` near `Dj`, since `Dj` misses the
  other vertex balls); both local hypotheses are then derived (complement disk and local
  planarity).  Remaining for the P4 consumer: the open `O` with `O ∩ frontier (⋃ tgtV) =
  O ∩ tgtVBd w` near `Dj` (local finiteness of the vertex balls), in the chart.

## P4 item (2): the bigon drag in a normal-form chart (`BigonDrag`) — CLOSED as a chart lemma; `exists_section34BigonSlide` STUCK on the normal form

| file | lines | SHA-256 |
|---|---|---|
| `DifferentialGeometry/Topology/PiecewiseLinear/BigonDrag.lean` | 223 | `1eb762002ce7c6ccb061c572d195015621f9232f1b061cf3d880aa86fc13c74b` |

    import DifferentialGeometry.Topology.PiecewiseLinear.BigonDrag

- `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\BigonDrag.lean with no diagnostics; shared outputs unchanged.`
- `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a\AuditTube19.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T05:48:29Z)

Public names (grepped, no clash): `slideMap_fst_le_of_tent`, `slideMapAt` (def),
`continuous_slideAmount`, `continuous_slideMapAt`, `slideAmount_eq_zero_of_notMem`,
`slideMapAt_eq_self_of_notMem`, `slideMapAt_zero`, `slideMapAt_one`, `slideMapAt_snd`,
`mapsTo_slideMapAt_of_subset`, `exists_bigonDrag`.

- The normal form (hypotheses of `exists_bigonDrag`, any T2 space `X`): an
  `e : OpenPartialHomeomorph X (ℝ × ℝ × ℝ)` with `slideSupport ⊆ e.target` such that on
  `e.source`, in coordinates `(v, u, z)`: the surface `Sf` is `z = 0`, the side `Y` (union of the
  two vertex balls) is `z ≥ 0`, the splitting circle(s) `C` is `v = 0, z = 0`, and the trace `Tr`
  is the tent `z = 0, v = (1/2 - |u|)/2`.  The bigon is `z = 0, 0 ≤ v ≤ (1/2 - |u|)/2`, the
  crossings are `(0, ±1/2, 0)`.
- Conclusion: `Φ = e.conjugateMap slideMap` (the model slide of `ModelSlide`, conjugated) is a
  bijection, the identity off the compact `e.symm '' slideSupport`, keeps `Sf` and `Y`, and
  `Φ '' Tr ∩ C = (Tr ∩ C) \ e.source` (the tent goes to `v ≤ -1/4`, `slideMap_fst_le_of_tent`);
  a continuous `H : X × [0,1] → X` (the partial slides `slideMapAt t`) joins the identity to `Φ`,
  keeping `Sf`, `Y` and the complement of the support fixed.  When `X` is a normed space and `e`,
  `e.symm` are piecewise affine, `Φ` is piecewise affine on `univ` by the existing
  `isPiecewiseAffineOn_conjugateMap` (`ChartConjugate`).
- `exists_section34BigonSlide` remains STUCK: the exact remaining goal is the normal form, i.e.
  from `hinv` and `hop` an `e` as above (composite of the chart of `H t` with a PL chart of `ℝ³`)
  with `Sf = frontier (⋃ w, tgtV w)`, `Y = section34FaceTorus tgtV s` (both near `Dj`),
  `C = ⋃ e', tgtEBd e'`, `Tr = fblBd s ∩ Sf`, source missing every other `fbl s'` and every other
  crossing point, and `e.symm (0, ±1/2, 0) = Bb`.  Its content: a PL collar of the frontier of
  `tgtV w ∪ tgtV u` near `Dj ∪` a strip beyond `B'`, plus a planar normal form (inside one face,
  after `IsPLSphere.isSimplyEmbedded` and `exists_isPLHomeomorphOn_straighten_disk_in_tetrahedron`)
  of the arc of `tgtEBd e`, the trace arcs and the bigon, using the field-6 crossing charts at `Bb`.
  Given the normal form the rest of the leaf is covered: fields 3, 4, 10 (support near `Dj`, which
  every other face ball misses), 5 (`HasPLCrossingAt.of_isPLHomeomorphOn_mem_nhds`), 6 (identity
  near the other crossings), 7 (`CarriesFirstHomologyOnto.of_homotopic` with `H`), 8, 9, the equal
  trace count and `p⁺ + 2 = p`.

## P4 item (1a): disjoint nonseparating circles on a torus (`TorusCircleHomology`) — CLOSED

| file | lines | SHA-256 |
|---|---|---|
| `DifferentialGeometry/Topology/PiecewiseLinear/TorusCircleHomology.lean` | 393 | `c0bd2676246511d7ea52728163e89c7222380a12872f033b462ce1c3a32c82a9` |

    import DifferentialGeometry.Topology.PiecewiseLinear.TorusCircleHomology

- `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\TorusCircleHomology.lean with no diagnostics; shared outputs unchanged.`
- `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a\AuditTube20.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T06:12:21Z)

Public names (grepped, no clash): `range_integralSingularHomologyMap_inclusion_eq_of_homotopic`,
`range_integralSingularHomologyMap_eq_of_continuousOn`,
`range_integralSingularHomologyMap_inclusion_eq_bot`,
`subsingleton_integralSingularHomology_image_of_convex`,
`IsPLTorus.range_integralSingularHomologyMap_eq_bot_of_not_isPreconnected`,
`IsPLTorus.range_integralSingularHomologyMap_eq_of_disjoint`,
`IsPLTorus.carriesFirstHomologyOnto_image_of_disjoint`.

- Form ("homologous up to sign" as equal images): `Θ ⊆ ℝ³` a PL torus, `φ : ℝ³ → Y` continuous
  and injective on `Θ`, `Y` Hausdorff in any universe, `φ '' Θ ⊆ S`.  For disjoint PL circles
  `K, G ⊆ Θ` with `Θ \ K`, `Θ \ G` preconnected, the ranges of `H₁ (φ '' K) → H₁ S` and
  `H₁ (φ '' G) → H₁ S` are equal; a separating circle has range `⊥` (28.9 disk, contractible
  image); carrying `H₁ S` onto passes from `φ '' K` to `φ '' G`.  `φ` is there for the universe
  gap (`M₂ : Type u`, charts to `ℝ³`): apply it with `φ` a chart inverse on a chart containing
  `Θ`.
- Route: `exists_connected_annulus_complement` around `G` (collar missing `K`),
  `χ = 0` gives the annulus parametrization, `exists_disk_or_annulus_of_subset_prism_lateral` for
  `K`; the disk case contradicts `IsPreconnected (Θ \ K)` via
  `inter_closure_sdiff_eq_image_stdSimplexBoundary`; the annulus case and the half collar of `G`
  are fed to `range_integralSingularHomologyMap_eq_of_continuousOn` (end maps homotopic, ends
  homeomorphic by `homeoOfEquivCompactToT2`).
- Consumer gap (for Lead): to apply this to field 7 one needs `frontier (section34FaceTorus tgtV s)`
  to be a PL torus inside one chart (the image of a PL torus of `ℝ³` under a chart inverse).  No
  current lemma produces that from `hinv` (same gap as the P6 bridge leaf
  `section34TraceCircle_homologyMap_ne_zero`).

## P4 item (1b): carrying unions of circles and subsurfaces of a torus (`TorusSubsurfaceCarrier`) — CLOSED

| file | lines | SHA-256 |
|---|---|---|
| `DifferentialGeometry/Topology/PiecewiseLinear/TorusSubsurfaceCarrier.lean` | 811 | `3a33374fe009d4053c3f7505f6973afb6f3c5155537523591aeff3fe0de8dc30` |

    import DifferentialGeometry.Topology.PiecewiseLinear.TorusSubsurfaceCarrier

- `Verified D:\differential-geometry-moise-int\DifferentialGeometry\Topology\PiecewiseLinear\TorusSubsurfaceCarrier.lean with no diagnostics; shared outputs unchanged.`
- `Verified C:\Users\liao9\AppData\Local\Temp\claude-moise-agent-a\AuditTube22.lean with no diagnostics; shared outputs unchanged.` (2026-09-23T06:42:32Z)

Public names (grepped, no clash): `range_integralSingularHomologyMap_le_of_continuousOn`,
`integralSingularChainsIn_union_le`, `range_integralSingularHomologyMap_inclusion_mono`,
`exists_homologous_cycle_of_range_le`, `CarriesFirstHomologyOnto.of_union_of_range_le`,
`CarriesFirstHomologyOnto.of_union_of_subsingleton`,
`CarriesFirstHomologyOnto.of_union_iUnion_of_range_le`, `CarriesFirstHomologyOnto.subsingleton`,
`carriesFirstHomologyOnto_of_subsingleton`, `CarriesFirstHomologyOnto.subsingleton_of_iUnion`,
`IsPLTorus.carriesFirstHomologyOnto_or_subsingleton_of_iUnion`,
`IsPLTorus.carriesFirstHomologyOnto_or_subsingleton_of_disjoint`,
`IsPLTorus.carriesFirstHomologyOnto_iUnion_of_disjoint`.

Same setting as (1a) (`Θ` a PL torus, `φ` continuous and injective on `Θ`, `φ '' Θ ⊆ S`, `Y`
Hausdorff in any universe).
- Planar-subsurface lemma (`..._or_subsingleton_of_disjoint`): `K ⊆ Θ` a nonseparating PL
  circle, `C : ι → Set E3` finitely many pairwise disjoint PL circles in `Θ \ K`, `W ⊆ Θ` closed,
  disjoint from `K`, with `W ∩ closure (Θ \ W) ⊆ ⋃ i, C i`, and `φ '' W` carrying `H₁ S`: then
  some `φ '' C i` carries, or `H₁ S` is trivial (the disjunct is needed: `ι` empty forces
  `W = ∅`).  `..._iUnion_of_disjoint` packages it as "`φ '' ⋃ i, C i` carries".  Route: annulus
  complement `R ⊇ W` of a collar of `K`; the vertical retraction of `R` (Lemma `..._le_of_...`)
  makes the end circle `K₋` carry; an annulus-case `C i` has the range of `K₋`; if all `C i` are
  disk-case, the disks are nested or disjoint in the prism sphere
  (`isPLSphere_stdSimplex_prism_boundary`, sphere `inter_closure_sdiff`, complement of a disk
  connected), `W` lies in the union of the maximal ones (clopen argument on the connected
  complement of disjoint disks, `IsPLSphere.isConnected_sdiff_iUnion_of_isPLBall_two`), and
  finitely many disjoint disks carry only a trivial `H₁` (chain splitting,
  `integralSingularChainsIn_union_le`).
- Step A of field 7 (`..._or_subsingleton_of_iUnion`): if `φ '' ⋃ i, C i` carries `H₁ S`
  (disjoint PL circles in `Θ`), some `C i` is nonseparating in `Θ` and `φ '' C i` carries, or
  `H₁ S` is trivial (separating circles have range `⊥`, nonseparating ones one common range; a
  piece whose range lies in another's is removed by `of_union_iUnion_of_range_le`).

Field 7 of P4 case (a) after these bricks (old trace `Z = Z₀ ⊔ Jd ⊔ Z₁` carries `H₁ T_s`):
Step A gives a nonseparating carrying component `K`; if `K ⊆ Z₁`, `mono`; otherwise
`K ⊆ Z₀ ∪ Jd` misses `P'` and `..._iUnion_of_disjoint` with `W = P' ∩ Θ` gives that the new trace
carries.  Remaining inputs, all outside these modules: (i) the chart: `Θ = c '' frontier T_s` a PL
torus inside one PL chart with the trace components PL circles (the T_s gap of (1a), same as the
P6 bridge leaf); (ii) `P' ∩ Θ` carries `H₁ T_s` (the rim `h '' simplexRim ⊆ interior P'` plus
`CarriesFirstHomologyOnto.of_mayerVietoris` on the ball `P'`, step (iii) of the Batch 7 note);
(iii) `P' ∩ Θ` has frontier in `Θ` inside the new trace (from `P' ∩ O = P ∩ O` and field 5).
