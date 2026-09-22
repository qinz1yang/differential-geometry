# Fill queue — frozen skeleton leaves for the overnight proving lane (2026-09-21)

Every leaf below is a `sorry` in a skeleton file whose *statement* has been frozen by external
review. A lane proves a leaf by creating ONE new real module that restates the theorem
byte-identically (same name, binders, instance arguments) and proves it; the lead wires the
skeleton to the module afterwards. Skeleton files are never edited by a lane.

Order = the lead's estimate of tractability (short first). Skip a leaf whose statement you can
refute — record the counterexample in your log; that is a success, not a failure.

| # | Leaf | Skeleton file | Size | Hints |
|---|---|---|---|---|
| 1 | `IsPLHomeomorphInto.mono_of_isPLCellOn` | `Section34Normalization.lean` | S | restrict a PL embedding to a PL cell inside its domain; the tree has `mono_of_isPolyhedron` for model-space domains; `PLCellOn*.lean` API; suggested home `PLCellOnBoundary`-style module |
| 2 | `exists_splitDisk_src_eq_inter_vertexBall` | `Section34Normalization.lean` | S | derivable from `Section34CutFrame` alone: patch/face-arc labels force the vertex-ball label unique (`IsPLCellOn.dim_eq`, `PLCellOnBoundary.lean:180`); digest AH §"Docstring corrections" |
| 3 | `separates_of_locally_eventually_eq` | `Section32PseudoCell.lean` | S | general topology: a limit of separators that is locally eventually constant separates; compactness along the contradiction path (digest AM) |
| 4 | `isTopologicalSphere_image_splitRim` | `Section32PseudoCell.lean` | S | the intrinsic boundary of `splitCell` under the embedding `h` is a circle |
| 5 | `section33_tube_product` | `Section33Approximation.lean` | S | `Bd N × (0,1) ≅ Int N' − K'` from `IsTube.derivedModel` and the source de-cored product transported by `h` (digest AI) |
| 6 | `boundaryComplex_space_of_isPLCellAttachmentWith_zero` | `PLSmoothingCompact.lean` | S | attached ball disjoint from the old stage; `BoundaryInvariance.lean`, `DerivedNeighborhoodCellBoundary.lean` |
| 7 | `boundaryComplex_space_of_isPLCellAttachmentWith_three` | `PLSmoothingCompact.lean` | S | the attaching sphere is one old boundary component, which disappears |
| 8 | `isSmoothHandleStage_adjunction_zero` | `PLSmoothingCompact.lean` | S | empty attaching region = disjoint union with the standard smooth 3-ball; `Handle/Manifold.lean`, `Cell/Coordinates.lean` |
| 9 | `revolutionOf_cellInterior_subset_interior` | `Section31CanonicalConfiguration.lean` | M | planar invariance of domain; the open half-plane keeps the axis away |
| 10 | `exists_isTopologicalCellWithInterior_union_consecutive` | `Section31CanonicalConfiguration.lean` | S–M | `D_j ∪ D_{j+1}` is a 2-cell containing both interiors; the overlap is a 2-cell (`IsPlanarCellChain.overlap`) |
| 11 | `separates_initialSurface` | `Section32PseudoCell.lean` | M | Lemmas 1 + 3 of §32 with `havoid`; transport `IsTube.splitSeparates` (digest AK/AM) |
| 12 | `section33_faceEulerChar_handlePiece` | `Section33Approximation.lean` | S–M | `χ(A'_v) = 2 − deg v`; grep `faceEulerChar`, `isPLSphere_two_of_faceEulerChar_eq_two` |
| 13 | `isCombinatorialManifold_of_locallyFinitePLPieceIn` | `Section34Control.lean` | M | vertex links are PL 2-spheres from the local PL Euclidean model (digest AF Part 1) |
| 14 | `boundaryComplex_space_of_isPLCellAttachmentWith_one` / `_two` | `PLSmoothingCompact.lean` | M | relative interiors of the attaching disks / annulus removed, the free part added (digest AN) |
| 15 | `hasPLNormalDoubleCrossingAt_of_isStableCrossingBlock` | `GeneralPositionInDouble.lean` | M | a margin-stable block is a PL normal double crossing at each inner double point |
| 16 | `isSpine_revolutionOf_of_mem_cellInterior` | `Section31CanonicalConfiguration.lean` | M | revolved planar 2-cell = solid torus with the interior point's circle as spine (clears `IsRevolvedTorusChain`'s conditional inhabitant) |

Not in the queue (deep, or under repair): everything in `ControlledGraphNeighborhood.lean`,
`Section34Terminal.lean`, `DescentStepOrientable.lean`, `ClosedBranchCaseOne.lean`; the remaining
A1 leaves; `exists_generalPosition_solidTorus_*` (being restated); the compact §34 skeleton
(being written); all leaves marked deep in the skeleton docstrings.
