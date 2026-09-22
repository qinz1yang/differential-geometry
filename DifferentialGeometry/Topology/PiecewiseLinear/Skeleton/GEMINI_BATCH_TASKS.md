# Gemini frozen-leaf execution queue

This is the task inventory for [GEMINI_BATCH.md](GEMINI_BATCH.md), not the acceptance ledger.
Source snapshot: `09bcbfea1e6c39873dbd1bed89a93964f0c8836b`. Live source census: **108 physical sorry leaves**;
**101 proof candidates** and **7 held/assembly entries**. Current proofs remain OPEN until
independent lead acceptance. The manifest preserves full source/header hashes and raw headers.

## Suggested pass order

The first nine entries provide an initial mix of the ongoing attempt and isolated interfaces.
This ordering does not certify that a theorem is easy. Then proceed family by family; reorder
when actual dependencies justify it and revisit blocked targets only when something changes.
Every candidate may be attempted in this authorization. Do not stop after a single entry.

| Queue | Skeleton and source line | Frozen declaration, under `DifferentialGeometry.Topology.PiecewiseLinear` |
|---|---|---|
| G001 | [Section31CanonicalConfiguration:376](Section31CanonicalConfiguration.lean#L376) | `exists_isTopologicalCellWithInterior_union_consecutive` |
| G002 | [DescentStepOrientable:364](DescentStepOrientable.lean#L364) | `nonempty_plSeamTubeChart_comp_crossQuarterTurn` |
| G003 | [Section26ThreeSurfaces:102](Section26ThreeSurfaces.lean#L102) | `isOpen_preimage_frontier_component_surface_interior` |
| G004 | [Section26ThreeSurfaces:85](Section26ThreeSurfaces.lean#L85) | `exists_surface_interior_frontier_contact` |
| G005 | [Section30Torus:96](Section30Torus.lean#L96) | `subset_interior_of_nested_tori` |
| G006 | [Section30Torus:116](Section30Torus.lean#L116) | `not_nullhomotopic_inclusion_of_nested_tori` |
| G007 | [Section31CanonicalConfiguration:395](Section31CanonicalConfiguration.lean#L395) | `isCombinatorialSolidTorus_of_hasCylindricalDiagram` |
| G008 | [Section32PseudoCell:331](Section32PseudoCell.lean#L331) | `handlePiece_subset_of_edgeCollars` |
| G009 | [Section33Approximation:255](Section33Approximation.lean#L255) | `section33_not_isLoopTheoremDisk` |
| G010 | [Section34Control:176](Section34Control.lean#L176) | `exists_locallyFinitePLPieceIn_of_isOpen` |
| G011 | [Section34Control:181](Section34Control.lean#L181) | `exists_isSubdivision_section34CarrierSupport_subset` |
| G012 | [Section26ThreeSurfaces:65](Section26ThreeSurfaces.lean#L65) | `exists_triod_chart_at_common_boundary` |
| G013 | [Section26ThreeSurfaces:110](Section26ThreeSurfaces.lean#L110) | `exists_frontier_pair_witnesses_of_triod_chart` |
| G014 | [Section30Torus:81](Section30Torus.lean#L81) | `IsCombinatorialManifold.nonempty_homeomorph_torus_of_isOrientable_of_eulerChar_eq_zero` |
| G015 | [Section30Torus:89](Section30Torus.lean#L89) | `IsPLTorus.exists_combinatorial_triangulation` |
| G016 | [Section30Torus:108](Section30Torus.lean#L108) | `IsPLTorus.exists_nontrivial_fundamentalGroup_kernel_in_solidTorus` |
| G017 | [Section30Torus:125](Section30Torus.lean#L125) | `exists_isPLBall_superset_of_exterior_compression` |
| G018 | [Section30Torus:140](Section30Torus.lean#L140) | `exists_ball_pair_of_interior_essential_disk` |
| G019 | [Section31CanonicalConfiguration:384](Section31CanonicalConfiguration.lean#L384) | `exists_innerSolidTorus_toroidalShell_of_annulusImage` |
| G020 | [Section31CanonicalConfiguration:399](Section31CanonicalConfiguration.lean#L399) | `exists_generalPosition_solidTorus_relative` |
| G021 | [Section31CanonicalConfiguration:452](Section31CanonicalConfiguration.lean#L452) | `exists_polygon_carrier_of_spine` |
| G022 | [Section31CanonicalConfiguration:463](Section31CanonicalConfiguration.lean#L463) | `carriesGenerator_or_exists_isPLCell_of_polygon_disjoint_carrier` |
| G023 | [Section31CanonicalConfiguration:473](Section31CanonicalConfiguration.lean#L473) | `exists_isPLCell_frontier_of_polygon_nullhomotopic` |
| G024 | [Section28Annuli:75](Section28Annuli.lean#L75) | `exists_product_coordinates_for_disjoint_essential_polygons` |
| G025 | [Section28Annuli:87](Section28Annuli.lean#L87) | `exists_annulus_parametrization_of_product_circle_cut` |
| G026 | [Section32PseudoCell:200](Section32PseudoCell.lean#L200) | `exists_canonicalTower` |
| G027 | [Section32PseudoCell:214](Section32PseudoCell.lean#L214) | `separates_initialSurface` |
| G028 | [Section32PseudoCell:227](Section32PseudoCell.lean#L227) | `exists_descentSequence` |
| G029 | [Section32PseudoCell:254](Section32PseudoCell.lean#L254) | `isOpenTopologicalCell_annularChain` |
| G030 | [Section32PseudoCell:273](Section32PseudoCell.lean#L273) | `exists_compact_connected_to_freeFace` |
| G031 | [Section32PseudoCell:282](Section32PseudoCell.lean#L282) | `exists_twoComponents_of_pseudoCell` |
| G032 | [Section32PseudoCell:311](Section32PseudoCell.lean#L311) | `exists_edgeCollarFamily` |
| G033 | [Section32PseudoCell:317](Section32PseudoCell.lean#L317) | `isHandleDecomposition_of_edgeCollars` |
| G034 | [Section32PseudoCell:340](Section32PseudoCell.lean#L340) | `exists_generalPosition_ball_pseudoCell` |
| G035 | [Section32PseudoCell:347](Section32PseudoCell.lean#L347) | `exists_reducedDisk_of_crossesPseudoCell` |
| G036 | [Section33Approximation:181](Section33Approximation.lean#L181) | `exists_section33TubeFrame` |
| G037 | [Section33Approximation:201](Section33Approximation.lean#L201) | `exists_isPolyhedralTubeNeighborhood` |
| G038 | [Section33Approximation:207](Section33Approximation.lean#L207) | `exists_hasSinglePolygonTraces` |
| G039 | [Section33Approximation:215](Section33Approximation.lean#L215) | `exists_hasConnectedHandlePieces` |
| G040 | [Section33Approximation:227](Section33Approximation.lean#L227) | `exists_hasNoHandleLoopTheoremDisk` |
| G041 | [Section33Approximation:240](Section33Approximation.lean#L240) | `section33_disk_meets_graph` |
| G042 | [Section33Approximation:273](Section33Approximation.lean#L273) | `section33_tube_product` |
| G043 | [Section33Approximation:277](Section33Approximation.lean#L277) | `section33_fundamentalGroup_map_bijective` |
| G044 | [Section33Approximation:292](Section33Approximation.lean#L292) | `section33_faceEulerChar_handlePiece` |
| G045 | [Section33Approximation:306](Section33Approximation.lean#L306) | `exists_section33BoundaryMatch` |
| G046 | [Section33Approximation:321](Section33Approximation.lean#L321) | `exists_section33Extension` |
| G047 | [PLSmoothingCompact:173](PLSmoothingCompact.lean#L173) | `exists_homeomorph_smooth_disks_of_isClosedEmbedding` |
| G048 | [PLSmoothingCompact:187](PLSmoothingCompact.lean#L187) | `isSmoothHandleStage_adjunction_one` |
| G049 | [PLSmoothingCompact:205](PLSmoothingCompact.lean#L205) | `exists_homeomorph_smooth_annulus_of_isClosedEmbedding` |
| G050 | [PLSmoothingCompact:218](PLSmoothingCompact.lean#L218) | `isSmoothHandleStage_adjunction_two` |
| G051 | [PLSmoothingCompact:235](PLSmoothingCompact.lean#L235) | `exists_isSmoothEmbedding_sphere_of_isClosedEmbedding` |
| G052 | [PLSmoothingCompact:244](PLSmoothingCompact.lean#L244) | `isSmoothHandleStage_adjunction_three` |
| G053 | [ExtendedLoopTheoremOrientable:60](ExtendedLoopTheoremOrientable.lean#L60) | `exists_bicollar_complement_with_boundary_collars` |
| G054 | [ExtendedLoopTheoremOrientable:92](ExtendedLoopTheoremOrientable.lean#L92) | `exists_nontrivial_boundary_loop_of_bicollar_complement` |
| G055 | [Section30Separation:60](Section30Separation.lean#L60) | `exists_annular_split_ball` |
| G056 | [ControlledGraphNeighborhood:259](ControlledGraphNeighborhood.lean#L259) | `exists_section34CutFrame` |
| G057 | [ControlledGraphNeighborhood:289](ControlledGraphNeighborhood.lean#L289) | `exists_section34VertexPreparation` |
| G058 | [ControlledGraphNeighborhood:357](ControlledGraphNeighborhood.lean#L357) | `exists_section34PiercingPackage` |
| G059 | [ControlledGraphNeighborhood:375](ControlledGraphNeighborhood.lean#L375) | `exists_section34ProtectedCircleRemovalStep` |
| G060 | [ControlledGraphNeighborhood:505](ControlledGraphNeighborhood.lean#L505) | `exists_section34ProtectedCircleRemoval` |
| G061 | [ControlledGraphNeighborhood:521](ControlledGraphNeighborhood.lean#L521) | `exists_section34DeletedBalls` |
| G062 | [ControlledGraphNeighborhood:547](ControlledGraphNeighborhood.lean#L547) | `exists_section34EdgeMatching` |
| G063 | [Section34Normalization:460](Section34Normalization.lean#L460) | `exists_section34FaceBalls` |
| G064 | [Section34Normalization:470](Section34Normalization.lean#L470) | `exists_section34Compression` |
| G065 | [Section34Normalization:491](Section34Normalization.lean#L491) | `exists_section34BigonSlide` |
| G066 | [Section34Normalization:512](Section34Normalization.lean#L512) | `exists_section34TerminalFaceBalls` |
| G067 | [Section34Normalization:556](Section34Normalization.lean#L556) | `section34Trace_of_noOperation` |
| G068 | [Section34Normalization:572](Section34Normalization.lean#L572) | `section34TraceCircle_homologyMap_ne_zero` |
| G069 | [Section34Terminal:158](Section34Terminal.lean#L158) | `exists_section34FaceDisks` |
| G070 | [Section34Terminal:167](Section34Terminal.lean#L167) | `exists_section34ResidualBalls` |
| G071 | [Section34Terminal:179](Section34Terminal.lean#L179) | `section34SourceFace_iff_cutLe` |
| G072 | [Section34Terminal:185](Section34Terminal.lean#L185) | `section34TargetRecognition` |
| G073 | [Section34Compact:929](Section34Compact.lean#L929) | `exists_compactCutAndGraph` |
| G074 | [Section34Compact:948](Section34Compact.lean#L948) | `exists_compactFaceShellBalls` |
| G075 | [Section34Compact:960](Section34Compact.lean#L960) | `exists_compactFaceBallsGeneralPosition` |
| G076 | [Section34Compact:988](Section34Compact.lean#L988) | `compactTraceHomology` |
| G077 | [Section34Compact:1025](Section34Compact.lean#L1025) | `exists_compactBigonSlide` |
| G078 | [Section34Compact:1045](Section34Compact.lean#L1045) | `compactTrace_of_noOperation` |
| G079 | [Section34Compact:1060](Section34Compact.lean#L1060) | `exists_compactFaceDisks` |
| G080 | [Section34Compact:1081](Section34Compact.lean#L1081) | `exists_compactResidualBalls` |
| G081 | [Section34Compact:1107](Section34Compact.lean#L1107) | `compactSourceFace_iff_cutLe` |
| G082 | [Section34Compact:1111](Section34Compact.lean#L1111) | `compactTargetRecognition` |
| G083 | [DescentStepOrientable:234](DescentStepOrientable.lean#L234) | `isPLBoundaryTubeProducer_double` |
| G084 | [DescentStepOrientable:244](DescentStepOrientable.lean#L244) | `NormalSystem.exists_boundaryNeighborhood_realization` |
| G085 | [DescentStepOrientable:269](DescentStepOrientable.lean#L269) | `exists_adaptedCleanCap_of_disjoint_innermost_cleanDisk` |
| G086 | [DescentStepOrientable:290](DescentStepOrientable.lean#L290) | `exists_descendingSurgery_of_adaptedCleanCap` |
| G087 | [DescentStepOrientable:353](DescentStepOrientable.lean#L353) | `exists_plCrossSeamReading_of_isCrossRegluedCell` |
| G088 | [ClosedBranchCaseOne:169](ClosedBranchCaseOne.lean#L169) | `exists_isSourceTrackedBranchTube` |
| G089 | [GeneralPositionInDouble:274](GeneralPositionInDouble.lean#L274) | `exists_adaptedHalfSpaceChart_in_double` |
| G090 | [GeneralPositionInDouble:405](GeneralPositionInDouble.lean#L405) | `SingularTwoCell.exists_cutOutPiece_of_closure_subset` |
| G091 | [GeneralPositionInDouble:418](GeneralPositionInDouble.lean#L418) | `exists_gluedCell_of_vertexMap_in_adaptedChart` |
| G092 | [GeneralPositionInDouble:1451](GeneralPositionInDouble.lean#L1451) | `exists_transitionSubdivisionOnOverlap` |
| G093 | [GeneralPositionInDouble:1497](GeneralPositionInDouble.lean#L1497) | `exists_commonWallComplex` |
| G094 | [GeneralPositionInDouble:1520](GeneralPositionInDouble.lean#L1520) | `wallProductBlock_transport` |
| G095 | [GeneralPositionInDouble:1539](GeneralPositionInDouble.lean#L1539) | `hasStableCrossingBlocks_of_wallProductBlocks` |
| G096 | [GeneralPositionInDouble:1660](GeneralPositionInDouble.lean#L1660) | `exists_normalizationPreparation_on_prescribedRegion` |
| G097 | [GeneralPositionInDouble:1685](GeneralPositionInDouble.lean#L1685) | `exists_protectedSubdivision_in_adaptedChart` |
| G098 | [GeneralPositionInDouble:1753](GeneralPositionInDouble.lean#L1753) | `exists_globalInvariants_of_gluedCell` |
| G099 | [GeneralPositionInDouble:1845](GeneralPositionInDouble.lean#L1845) | `wallProductBlocks_stable_on_fixedSubdivision` |
| G100 | [GeneralPositionInDouble:1897](GeneralPositionInDouble.lean#L1897) | `exists_wallGenericVertexMap` |
| G101 | [GeneralPositionInDouble:1946](GeneralPositionInDouble.lean#L1946) | `wallProductBlocks_of_wallGenericity` |

## Held and assembly entries

These entries are visible so that all 108 physical leaves are accounted for. They are not
additional independent proof assignments in this batch. F remains active on its own leaf.

| Entry | Skeleton and declaration | Status and reason |
|---|---|---|
| H01 | `DerivedNeighborhoodComplement.isEmbedding_derivedNeighborhoodRay` | **REVIEW_HOLD**: AY is a review request; this subsidiary leaf is not frozen. |
| H02 | `DerivedNeighborhoodComplement.range_derivedNeighborhoodRay` | **REVIEW_HOLD**: AY is a review request; this subsidiary leaf is not frozen. |
| H03 | `DescentStepOrientable.not_branchPreimage_eq_of_isOrientable` | **ASSEMBLY_AFTER_UPSTREAM**: Use the ClosedBranchCaseOne source-tracked tube and its proved orientation assembly; do not duplicate the deep proof search. |
| H04 | `GeneralPositionInDouble.hasPLNormalDoubleCrossingAt_of_isStableCrossingBlock` | **RESERVED_F**: F is actively proving entry 15 and owns NormalCrossingTransport on lease a. Historical H ownership does not permit editing current dirty candidate files or F files. |
| H05 | `Section34Compact.exists_compactFaceEnvelopes` | **REVIEW_HOLD**: AS prescribes hV and the repair is checked, but explicitly freezes only the other ten; no current refreeze recorded. |
| H06 | `Section34Compact.exists_compactCompression` | **REVIEW_HOLD**: AS prescribes hcar and the repair is checked, but explicitly freezes only the other ten; no current refreeze recorded. |
| H07 | `Section34Terminal.exists_section34NormalFamily` | **ASSEMBLY_REVIEW_HOLD**: Composite supplied by the Section34Normalization assembly after its upstream inputs close; current shared-interface revision lacks explicit refreeze. |

## Current review evidence

Later explicit freezes take precedence over stale introductory prose. For repaired compact
envelopes/compression, no explicit refreeze is recorded; these two are held. See the manifest
for exact identities and review paths.

| Family | Physical leaves | Proof candidates | Latest applicable evidence |
|---|---:|---:|---|
| Section34Control | 2 | 2 | [AF](../consult/AF-p0-and-sec3132-definitions-review-digest.md); current source/ledger |
| Section26ThreeSurfaces | 4 | 4 | [BA](../consult/BA-section26-three-surfaces-first-review-digest.md); current source/ledger |
| Section30Torus | 7 | 7 | [BC](../consult/BC-section30-torus-first-review-digest.md); current source/ledger |
| Section31CanonicalConfiguration | 7 | 7 | [AP](../consult/AP-section31-first-review-digest.md), [AQ](../consult/AQ-section31-relative-review-digest.md); current source/ledger |
| Section28Annuli | 2 | 2 | [BB](../consult/BB-section28-annuli-first-review-digest.md); current source/ledger |
| Section32PseudoCell | 11 | 11 | [AM](../consult/AM-section32-second-review-digest.md); current source/ledger |
| Section33Approximation | 12 | 12 | [AI](../consult/AI-section33-first-review-digest.md); current source/ledger |
| PLSmoothingCompact | 6 | 6 | [AN](../consult/AN-c1-first-review-digest.md); current source/ledger |
| ExtendedLoopTheoremOrientable | 2 | 2 | [AZ](../consult/AZ-orientable-extended-loop-first-review-digest.md); current source/ledger |
| Section30Separation | 1 | 1 | [BD](../consult/BD-section30-separation-first-review-digest.md); current source/ledger |
| ControlledGraphNeighborhood | 7 | 7 | [AE](../consult/AE-controlled351-eighth-review-digest.md); current source/ledger |
| Section34Normalization | 6 | 6 | [AJ](../consult/AJ-section34-normalization-second-review-digest.md); current source/ledger |
| Section34Terminal | 5 | 4 | [P](../consult/P-section34-third-review-digest.md), [Q](../consult/Q-section34-terminal-due-diligence.md); current source/ledger |
| Section34Compact | 12 | 10 | [AS](../consult/AS-section34-compact-first-review-digest.md); current source/ledger |
| DescentStepOrientable | 7 | 6 | [G](../consult/G-descent-skeleton-review-digest.md), [M](../consult/M-frozen-leaves-due-diligence.md); current source/ledger |
| ClosedBranchCaseOne | 1 | 1 | [I](../consult/I-caseone-skeleton-review-digest.md); current source/ledger |
| GeneralPositionInDouble | 14 | 13 | [AG](../consult/AG-generalposition-tenth-review-digest.md); current source/ledger |
| DerivedNeighborhoodComplement | 2 | 0 | [AY](../consult/AY-derived-neighborhood-complement-review-request.md); current source/ledger |

## Vocabulary and dependency preparation

- **Section 31:** CanonicalConfiguration, SolidTorusGeneralPosition, TopologicalCellInterior
  and PlanarCellUnion provide the public inputs. Hoist any needed proved revolution or
  fundamental-group helper still confined to its skeleton by a staged exact move.
- **Section 32:** PseudoCell and MoiseChain provide the tower, separator, annular-chain,
  collar, splitting and crossing vocabulary. Reuse the accepted separating-limit and
  split-rim proofs. Supply all outer local-finiteness, avoidance and support controls.
- **Section 33:** stage `IsLoopTheoremDisk` and `HasNoHandleLoopTheoremDisk` from
  Section33Approximation:152 onward into their natural tube/disk home before importing them.
  Other tube vocabulary is public in PolyhedralTubeNeighborhood. The frozen tube-product
  target remains eligible, but its alternate two-leaf ray skeleton is unreviewed. Reuse
  DerivedNeighborhoodRay and CompactEmbeddingComplement without importing that skeleton.
  `Moise264Orientable` does not replace its explicit `Moise264` hypothesis.
- **Smoothing:** leaf inputs are public in CellAttachment and Topology/Handle/SmoothStage.
  Compact smoothing propositions and the later stage-attachment assembly still need staged
  moves for eventual integration, but they do not block the six remaining leaf signatures.
- **Section 34 control / graph / terminal:** current signatures use public Section34Frame
  and Section34Statements. Do not redo the accepted P0 and PLCellOn API proofs.
- **Section 34 normalization:** stage the curve-crossing/homology predicates, image and trace
  components/count/rank, face-ball invariants, compression and bigon data from approximately
  lines 268–409, with any used proved rank lemmas and the later named endpoint.
- **Compact Section 34:** its ten-kind labels, indices, cut/carrier/graph/exterior data,
  envelopes, counts, operations, trace, face disks and residuals remain skeleton-only
  around lines 188–863. Stage them together coherently into natural compact frame and
  face-ball modules. Coordinate common curve-crossing and homology API with normalization;
  retain the different universe contexts and all frozen predicate meanings.
- **General position in the double:** UniformInjectivityScale, StarInj, free-source germs,
  HasStableCrossingBlocks, wall-system cells/stars/certificates, WallProductBlock,
  HasWallProductBlocks and AdmissibleVertexMap still need staged public homes. Relevant
  definition blocks begin around 292, 439, 508, 785, 1180, 1324 and 1553. M/Ea universes
  and the Ambient/MetricAmbient scopes differ; preserve them. The stable block itself is
  already public and owned by F for its current proof. Do not modify F's shared modules.
- **Orientable descent / closed branch:** reuse public BoundaryAdaptation and the marked
  chart / branch-tube transport modules. The quarter-turn image identities and derived
  tube data in the descent skeleton can be staged without carrying its sorried leaves.
  The single-circle obstruction is assembled through the source-tracked tube, not an
  unrelated second proof search. Existing dirty cross-reglued files remain protected.

The task log must distinguish exact vocabulary moves, helper proofs, frozen endpoint proofs,
and fixtures. No number in this table is a claim of proof completion.
