/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusFrontierSides
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusOnPolyhedralCylinder
import DifferentialGeometry.Topology.PiecewiseLinear.CenteredPrismBallPair
import DifferentialGeometry.Topology.PiecewiseLinear.CylinderFrontierSides
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodCircleLevels
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodCoreBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.DisjointSupportedPLEmbeddings
import DifferentialGeometry.Topology.PiecewiseLinear.IsAnnulusOnCompact
import DifferentialGeometry.Topology.PiecewiseLinear.LocalFrontierCrossing
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteOpenEnlargements
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteSeparationScales
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldPointTransport
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellEnlargement
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellMarkerMove
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundarySphere
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnPolyhedralBall
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnStabilityScales
import DifferentialGeometry.Topology.PiecewiseLinear.PLPieceBallInterior
import DifferentialGeometry.Topology.PiecewiseLinear.PLPieceConjugateEmbedding
import DifferentialGeometry.Topology.PiecewiseLinear.PLPieceCrossingFrontiers
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularGenerators
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CellEnlargements
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ChartLocalEnlargements
import DifferentialGeometry.Topology.PiecewiseLinear.Section34EdgeEnds
import DifferentialGeometry.Topology.PiecewiseLinear.Section34EdgeGraphRegions
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphCores
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphCoveringEdgeCells
import DifferentialGeometry.Topology.PiecewiseLinear.Section34LensImages
import DifferentialGeometry.Topology.PiecewiseLinear.Section34LensIsolation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34LocalMargins
import DifferentialGeometry.Topology.PiecewiseLinear.Section34MarkedNestedAnnuli
import DifferentialGeometry.Topology.PiecewiseLinear.Section34MarkedPiercedCells
import DifferentialGeometry.Topology.PiecewiseLinear.Section34NestedAnnularNeighborhoods
import DifferentialGeometry.Topology.PiecewiseLinear.Section34NestedPiercingRegularNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.Section34NestedPiercingSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercedBallFrontiers
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercedBallHeightMove
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercedBallModel
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercedBallRoof
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercedBallTransport
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercedEdgeCells
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercedVertexCells
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingCircleNeighborhoods
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingMarkerRoutes
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SeparationMargins
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SmallRegularNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SmallSolidTorus
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SplitDiskNeighborhoods
import DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexCellIntersections
import DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexEdgePasting
import DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexPreparation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexScales
import DifferentialGeometry.Topology.PiecewiseLinear.SignedHeightCrossing
import DifferentialGeometry.Topology.PiecewiseLinear.SupportedPLCellExtension
import DifferentialGeometry.Topology.PiecewiseLinear.SupportedPLPieceConjugate
import DifferentialGeometry.Topology.PiecewiseLinear.SupportedPLPrismShift
import Lean.Util.CollectAxioms

namespace DifferentialGeometry.Topology.PiecewiseLinear

run_cmd Lean.Elab.Command.liftTermElabM do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let names : Array Lean.Name := #[
    ``exists_isAnnulusOn_with_frontier_sides,
    ``exists_isAnnulusOn_of_crossing_trace,
    ``IsAnnulusOn.symm,
    ``isAnnulusOn_of_homeomorph_stdSimplexBoundary_prod,
    ``annulus_level_subset_sdiff_ends,
    ``exists_isAnnulusOn_of_homeomorph_stdSimplexBoundary_prod,
    ``IsPLHomeomorphOn.boundaryComplex_eq_annulus_ends,
    ``exists_centered_prism_piece_of_boundary_disk_pair,
    ``continuous_cylinder_frontier_sides,
    ``isConnected_range_inter_and_sdiff_of_frontier_level,
    ``carriesFundamentalGroupOnto_derivedNeighborhood,
    ``IsPLSphere.not_isPLBall_between_derivedNeighborhood,
    ``exists_isPLHomeomorphOn_annulus_derivedNeighborhood_circle_level,
    ``IsCombinatorialManifold.disjoint_derivedNeighborhood_boundary,
    ``exists_isPL_embedding_of_finite_disjoint_support,
    ``IsPLCellOn.exists_image_of_finite_disjoint_support,
    ``IsAnnulusOn.isCompact,
    ``IsAnnulusOn.isCompact_first,
    ``IsAnnulusOn.isCompact_second,
    ``interior_inter_eq_of_inter_eq]
  for name in names do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms in {name}: {axioms.toList}"

run_cmd Lean.Elab.Command.liftTermElabM do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let names : Array Lean.Name := #[
    ``frontier_inter_eq_of_isClosed_of_inter_eq,
    ``closure_subset_of_inter_eq,
    ``frontier_sides_of_inter_eq,
    ``exists_locallyFinite_open_supersets,
    ``exists_separation_scales_of_locallyFinite,
    ``exists_separation_scales_of_locallyFinite_on,
    ``exists_isPL_homeomorph_map_point_eqOn_compl,
    ``IsPLCellOn.exists_enlargement,
    ``exists_locallyFinite_isPLCellOn_enlargements,
    ``IsPLCellOn.exists_excluding_point_preserving_union,
    ``exists_marked_cell_pair_preserving_frontier_neighborhood,
    ``exists_marked_cell_pair_of_disjoint_connected_routes,
    ``IsPLHomeomorphInto.exists_pLPiece_of_isPolyhedron,
    ``IsPLCellOn.isPolyhedralSphere_boundary,
    ``IsPLCellOn.isPolyhedralBall,
    ``IsPolyhedralBall.exists_isPLCellOn,
    ``IsPolyhedralBall.isPLCellOn,
    ``exists_core_stability_scales_lt,
    ``PLPieceIn.frontier_image_of_isPLBall,
    ``PLPieceIn.image_interior_of_isPLBall]
  for name in names do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms in {name}: {axioms.toList}"

run_cmd Lean.Elab.Command.liftTermElabM do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let names : Array Lean.Name := #[
    ``PLPieceIn.exists_equiv_conjugate,
    ``PLPieceIn.crossing_sides_of_isPLBall,
    ``IsLocallyFiniteRegularNeighborhoodOf.carriesFundamentalGroupOnto,
    ``IsAnnulusOn.boundaries_carry_of_core,
    ``PLPieceIn.isPLOn_conjugate,
    ``bicollar_sides_of_regular_closed,
    ``subset_interior_image_of_bicollar_shift,
    ``IsPLCellOn.enlargement_of_bicollar_shift,
    ``exists_section34_chart_local_enlargements,
    ``exists_section34_edge_ends,
    ``isCompact_inter_graphSkeletonSpace,
    ``exists_section34_splitDisk_vertex_neighborhood,
    ``exists_section34_compact_edge_graph_region,
    ``isClosed_preimage_graphSkeletonSpace,
    ``isClosed_graphSkeletonSpace_in_domain,
    ``exists_section34_graph_cores,
    ``exists_section34_graph_cores_of_isPLCellOn,
    ``exists_section34_graph_covering_edge_cells,
    ``exists_section34_crossing_marked_edge_cells,
    ``exists_section34_marked_graph_covering_edge_cells]
  for name in names do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms in {name}: {axioms.toList}"

run_cmd Lean.Elab.Command.liftTermElabM do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let names : Array Lean.Name := #[
    ``locallyFinite_image_of_embedding,
    ``section34_lens_images,
    ``exists_section34_overlap_isolation_scales,
    ``exists_locallyFinite_disjoint_cthickening_intersections,
    ``exists_section34_vertex_scales_with_isolated_overlaps,
    ``exists_section34_local_margins,
    ``IsPLDerivedNeighborhoodExhaustion.exists_marked_nested_piercing_annuli,
    ``exists_crossing_pierced_cell_pair_excluding_opposite_markers,
    ``exists_crossing_marked_pierced_cell_pair_covering_compact,
    ``exists_pierced_cell_pair_excluding_opposite_markers,
    ``exists_marked_pierced_cell_pair_covering_compact,
    ``IsPLDerivedNeighborhoodExhaustion.exists_nested_piercing_annuli,
    ``LocallyFinitePLPieceIn.finiteRestriction,
    ``LocallyFinitePLPieceIn.exists_derivedNeighborhood_stage,
    ``LocallyFinitePLPieceIn.isLocallyFiniteRegularNeighborhoodOf_derivedNeighborhood,
    ``IsPLDerivedNeighborhoodExhaustion.exists_ambient_derivedNeighborhoods,
    ``exists_isSubdivision_union_of_preserved_intersection,
    ``exists_isSubdivision_restrict_space_of_finite_patch,
    ``LocallyFinitePLPieceIn.exists_isSubdivision_restrict_space_finite_change,
    ``LocallyFinitePLPieceIn.locallyFinite_of_isSubdivision_of_finite_new_faces]
  for name in names do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms in {name}: {axioms.toList}"

run_cmd Lean.Elab.Command.liftTermElabM do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let names : Array Lean.Name := #[
    ``restrict_faces_finite_of_finite_new_faces,
    ``LocallyFinitePLPieceIn.exists_isSubdivision_restrict_family_finite_change,
    ``LocallyFinitePLPieceIn.exists_isSubdivision_restrict_pair_finite_change,
    ``LocallyFinitePLPieceIn.isLocallyFiniteRegularNeighborhoodOf_locallyFinite_subdivision,
    ``LocallyFinitePLPieceIn.isLocallyFiniteRegularNeighborhoodOf_subdivision,
    ``LocallyFinitePLPieceIn.exists_stage_of_isCompact,
    ``LocallyFinitePLPieceIn.isPLSphere_preimage_of_isPolyhedralSphere,
    ``LocallyFinitePLPieceIn.isPLBall_preimage_of_isPolyhedralBall,
    ``IsPLDerivedNeighborhoodExhaustion.exists_regularNeighborhood_of_isPolyhedralSphere,
    ``frontier_inter_signed_height_balls,
    ``piercingHeightMove,
    ``piercingHeightMove_strictMono,
    ``piercingHeightMove_injective,
    ``piercingHeightMove_eq_self,
    ``piercingHeightMove_image_diff_slab,
    ``piercingHeightMove_apply_zero,
    ``isPiecewiseAffineOn_piercingHeightMove,
    ``piercingHeightMove_image_lower,
    ``piercingHeightMove_image_upper,
    ``piercingHeightMove_image_prism]
  for name in names do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms in {name}: {axioms.toList}"

run_cmd Lean.Elab.Command.liftTermElabM do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let names : Array Lean.Name := #[
    ``isPLHomeomorphOn_piercingHeightMove,
    ``isPLHomeomorphOn_piercingHeightMove_self,
    ``exists_pierced_prism_ball_pair,
    ``exists_crossing_pierced_square_ball_pair,
    ``exists_pierced_square_ball_pair,
    ``isPLBall_square_closedBall,
    ``exists_piercing_square_roof_with_sign_closures,
    ``exists_piercing_square_roof,
    ``exists_crossing_pierced_cell_pair_in_prism,
    ``exists_pierced_cell_pair_in_prism,
    ``exists_crossing_pierced_cell_pair_covering_compact,
    ``exists_pierced_cell_pair_covering_compact,
    ``exists_section34_pierced_edge_cells,
    ``exists_section34_crossing_pierced_vertex_cells,
    ``exists_section34_pierced_vertex_cells,
    ``exists_section34_unmarked_vertex_cells,
    ``exists_section34_piercing_circle_neighborhoods,
    ``exists_disjoint_piercing_marker_routes,
    ``exists_section34_separation_margins,
    ``IsPLDerivedNeighborhoodExhaustion.exists_regularNeighborhood_subset_open]
  for name in names do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms in {name}: {axioms.toList}"

run_cmd Lean.Elab.Command.liftTermElabM do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let names : Array Lean.Name := #[
    ``IsPLDerivedNeighborhoodExhaustion.exists_nested_regularNeighborhoods_subset_open,
    ``IsPLDerivedNeighborhoodExhaustion.exists_solidTorus_regularNeighborhood_subset_open,
    ``IsPLDerivedNeighborhoodExhaustion.exists_nested_solidTorus_regularNeighborhoods,
    ``section34_splitDisks_pairwise_disjoint,
    ``exists_section34_splitDisk_neighborhoods,
    ``Section34CutFrame.exists_edge_of_vertex_intersection,
    ``section34_vertex_cells_intersection_of_ne,
    ``section34_vertex_cells_disjoint_of_nonadjacent,
    ``section34_vertex_cells_triple_inter_eq_empty,
    ``section34_graph_subset_vertex_interiors_union_splitDisks,
    ``exists_section34_vertex_embeddings,
    ``exists_section34VertexPreparation,
    ``exists_section34_vertex_scales_with_sum_margins,
    ``section34CellThickening_mono,
    ``Section34VertexPreparation.mono,
    ``graph_mem_frontier_lower_height_region,
    ``graph_mem_frontier_upper_height_region,
    ``signed_height_regions_cross_along_zero_set,
    ``exists_supported_isPL_homeomorph_extension,
    ``PLPieceIn.exists_supported_conjugate]
  for name in names do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms in {name}: {axioms.toList}"

run_cmd Lean.Elab.Command.liftTermElabM do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let names : Array Lean.Name := #[
    ``PLPieceIn.exists_supported_prism_shift]
  for name in names do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms in {name}: {axioms.toList}"

end DifferentialGeometry.Topology.PiecewiseLinear
