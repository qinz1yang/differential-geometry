# Collaborator brief (Lean): three more independent packages, each on its own branch

Written by the lead on 2026-09-23. Same setting and rules as `COLLABORATOR-section31-request.md`
(repository `https://github.com/qinz1yang/differential-geometry-dev`, branch `codex/moise-integration`;
branch from its head; NEW FILES ONLY; restate frozen leaves byte-identically; never import a
`Skeleton/` file; no `sorry`/docstrings/comments in delivered modules; lines ≤ 100 codepoints; zero
warnings; grep before proving; do not touch `DifferentialGeometry.lean` or `FREE_INPUTS.md`; open a
pull request with a ≤ 40-line report and `#print axioms` for every public theorem). Paths are
relative to `DifferentialGeometry/Topology/PiecewiseLinear/`. Pick any package; say which one you
take so the lead does not assign it elsewhere. None of them touches a lane in flight (P4
compression, §33 Lemma 10, smoothing, P8 target recognition, the CGN edge matching, the C1 tube).

## Package B — the source face order (Section 34, compact then non-compact)

Leaf: `compactSourceFace_iff_cutLe` in `Skeleton/Section34Compact.lean`
(`∀ l m, src m ⊆ src l ↔ Section34CompactCutLe m l` under `hcut : Section34CompactCutFrame …`).
Reviewed OK as stated (digest `consult/BM-section34-compact-source-face-cut-order-review-digest.md`,
read it first; no frame clause may be added). A reconnaissance probe
`Skeleton/CompactSourceFaceOrderReduction.lean` already proves both directions of the leaf from four
named frontiers, which are your targets (restate them in real modules, then copy the probe's two
assemblies `cut_order_of_source_subset`, `source_subset_of_cut_order` and close the leaf):
1. `exists_facet_above_of_source_subset` (line 25): between two nested source cells of different
   dimensions there is a codimension-one facet (the pure-dimensional boundary tiling from clauses
   7–10 of `Section34CompactCutFrame`, `Section34CompactVocabulary.lean` line 291).
2. `split_disk_boundary_thin` (line 33): a marked boundary point of a split disk lies on exactly
   two one-cells of that disk's boundary circle.
3. `vertex_ball_boundary_thin` (line 45): a one-cell of a vertex-ball boundary sphere lies on
   exactly two two-cells.
4. `cut_step_iff_codimension_one_source_subset` (line 57): each codimension-one containment is
   one of the `Section34CompactCutStep` constructors (`Section34CompactVocabulary.lean` line 233).
Tools: `PLCellOnBoundary.lean` (`IsPLCellOn.dim_eq`, `boundary_eq`, `boundary_eq_frontier`,
`sdiff_boundary_eq_interior`), `Section34CompactSplitDiskIntersection.lean`,
`Section34CompactFacePoset.lean` (the step-dimension lemma), `Section34CompactTargetCells.lean`.
Then the non-compact twin `section34SourceFace_iff_cutLe` in `Skeleton/Section34Terminal.lean`
(input `Section34NormalPlus`, cut frame `Section34CutFrame` at `Section34Frame.lean` line 656, step
relation line 594): same route, but a `tetraBall` there has only carrier support, so the third
tetraBall is excluded by local two-sidedness in dimension three, not by `Q_t ⊆ conv t` (BM §4).

## Package C — the three unclaimed Section 32 leaves

Leaves in `Skeleton/Section32PseudoCell.lean`: `isOpenTopologicalCell_annularChain` (line 277),
`exists_generalPosition_ball_pseudoCell` (line 296), `exists_reducedDisk_of_crossesPseudoCell`
(line 303). Read the skeleton's module docstring and `Skeleton/FILL_LOG.md`, section
"Codex day queue item 5 — Section 32 reconnaissance" (what each sub-leaf needs). Three probes
reduce them to named sub-leaves (read/copy, never import):
- `Skeleton/Section32AnnularChainProbe.lean`: `open_cell_of_two_ends`, `closure_adds_intrinsic_rim`,
  `local_two_ball_pair` open; `locally_polyhedral_off_center` is real
  (`AnnularChainLocalPolyhedral.lean`); assembly `annular_chain_topology_of_subleaves`.
- `Skeleton/Section32GeneralPositionProbe.lean`: `exists_small_transverse_ball` (a small PL ball whose
  frontier has a finite transverse polygon trace and crosses the pseudo-cell),
  `exists_trace_absorbing_subdisk`; assembly `general_position_ball_of_subleaves`.
- `Skeleton/Section32ReducedDiskProbe.lean`: `exists_outermost_disk_with_intrinsic_rim`,
  `exists_pseudoCell_subdisk_with_rim` (a Jordan / innermost-disk step inside the pseudo-cell, whose
  centre may be wild); assembly `reduced_disk_of_subleaves`.
Tools: `PseudoCell.lean`, `PLDiskPseudoCell`, `SplitDiskPseudoCellFamily`, `TubeSplitDiskComponents`,
`TubeCenteredPrismCoordinates`, `SphereInnermostDisk`, `CircleClosedCover`, `PolygonalSchoenflies`,
`External/Schoenflies/JordanSchoenflies.lean`, `GeneralPosition`, `CurveCrossingGeneralPosition`.

## Package D — the P4 bigon slide (Section 34 normalisation)

Leaf: `exists_section34BigonSlide` in `Skeleton/Section34Normalization.lean` (line 366; it received
`hctrl : Section34CarrierControl U 𝒦 h η H` on 2026-09-23 by the owner's decision, so the chart
containing the face ball exists: `exists_chart_section34FaceBall`), and its compact twin
`exists_compactBigonSlide` in `Skeleton/Section34Compact.lean` (line 264, with `hcar`). The drag
itself is real: `BigonDrag.lean`, `exists_bigonDrag` (line 117), in a normal-form chart
`e : OpenPartialHomeomorph X (ℝ × ℝ × ℝ)` where the surface `Sf` is `z = 0`, the side `Y` (the union
of the two vertex balls) is `z ≥ 0`, the splitting circle is `v = 0, z = 0` and the trace is the
tent `z = 0, v = (1/2 − |u|)/2`, with crossings at `(0, ±1/2, 0)`. What is missing is the
normal-form producer from `hinv` and `hop` and the assembly: read `Skeleton/OPUS_FILL_LOG_A.md`,
sections "exists_section34BigonSlide (P4b) — STUCK" (Batch 7 and Batch 9) for the exact plan (a
disk `D⁺` around `Dj` in `∂(c '' (tgtV w ∪ tgtV u))`, ambient straightening of `D⁺` onto a
tetrahedron face by `IsPLSphere.isSimplyEmbedded` and
`exists_isPLHomeomorphOn_straighten_disk_in_tetrahedron`, then the planar θ-with-four-tails
normal form inside that face: a PL disk `Q` around the bigon meeting the circle and the trace in the
model configuration, mapped onto the model rectangle face by face, Alexander trick per face,
`exists_isPLHomeomorphOn_union`), and which fields of `Section34FaceBallInvariants` follow how
(support near `Dj`, `HasPLCrossingAt.of_isPLHomeomorphOn_mem_nhds`,
`CarriesFirstHomologyOnto.of_homotopic`, the equal trace count and `p⁺ + 2 = p`). Tools also:
`CompressionDiskNeighborhood`, `Section34FaceTorusCycle`, `Section34FaceBallUpdate`,
`Section34CompressionTools`, `BoundaryCollarExtension`, `PlanarBoundaryCollars`, `PlanarOuterCollar`.
The compression leaf `exists_section34Compression` is being done by another lane; do not touch it.

## Order of value

B closes a Compact leaf and a Terminal leaf with a fully reviewed route; C closes up to three §32
leaves from bounded sub-leaves; D is the hardest (a planar normal form) but is a whole P4 leaf on
the critical path. Report which you take; deliver as small modules with checker-clean compiles.
