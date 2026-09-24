/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ChartRelativeGeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.CrossingSurfaceLineChart
import DifferentialGeometry.Topology.PiecewiseLinear.CrossingTracePolyhedron
import DifferentialGeometry.Topology.PiecewiseLinear.DisjointSupportedHomeomorphs
import DifferentialGeometry.Topology.PiecewiseLinear.IsAnnulusOnCompact
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundarySphere
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnInteriorRegionStability
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnThickeningStability
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralSurfaceCharts
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingAnnularCrossings
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingAuxiliaryScales
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingBufferStability
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingCircles
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingComponentStability
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingConditionsOfCrossings
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingIntersectionConfinement
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingNonempty
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingPackage
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingRegionStability
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingSideStability
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingSourceBicollar
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingSourceBuffers
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingSourceSides
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingSurfacePatches
import DifferentialGeometry.Topology.PiecewiseLinear.Section34RelativeVertexCrossings
import DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexChartScales
import DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexSupportedMoves
import DifferentialGeometry.Topology.PiecewiseLinear.SupportedSurfaceGeneralPosition
import Lean.Util.CollectAxioms

/-! # Section34Piercing Package Axioms -/

namespace DifferentialGeometry.Topology.PiecewiseLinear

run_cmd Lean.Elab.Command.liftTermElabM do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let names : Array Lean.Name := #[
    ``exists_small_isPL_homeomorph_generalPosition_off_polyhedron_in_chart,
    ``exists_small_isPL_homeomorph_sphere_crossing_in_chart,
    ``HasPLCrossingAt.exists_lineChart_of_local_disks,
    ``HasPLCrossingAt.exists_lineChart_of_surface_charts,
    ``HasPLCrossingAt.exists_lineChart_of_eventuallyEq_surface_charts,
    ``HasPLCrossingAt.exists_isPolyhedron_nhdsWithin_inter,
    ``isLocallyPolyhedral_inter_of_hasPLCrossingAt,
    ``isPolyhedron_inter_of_isCompact_of_hasPLCrossingAt,
    ``isPolyhedron_chart_inter_of_isCompact_of_hasPLCrossingAt,
    ``exists_isPL_homeomorph_of_finite_disjoint_support,
    ``homeomorph_eqOn_of_disjoint_support,
    ``homeomorph_image_eq_of_disjoint_support,
    ``dist_lt_of_disjoint_support,
    ``IsAnnulusOn.isCompact,
    ``IsAnnulusOn.isCompact_first,
    ``IsAnnulusOn.isCompact_second,
    ``IsPLHomeomorphInto.exists_pLPiece_of_isPolyhedron,
    ``IsPLCellOn.isPolyhedralSphere_boundary,
    ``exists_cthickening_subset_image_interior_stable_of_subset_isPLCellOn,
    ``exists_cthickening_subset_image_interior_stable_of_isPLCellOn,
    ``IsPolyhedralSphere.exists_isOpen_inter_homeomorph_of_two,
    ``IsPolyhedralSphere.exists_isOpen_inter_chart_image_homeomorph_of_two,
    ``IsPLCellOn.exists_isOpen_inter_boundary_homeomorph,
    ``IsPLCellOn.exists_isOpen_inter_boundary_chart_image_homeomorph,
    ``section34_piercing_annular_crossings,
    ``exists_auxiliary_scales_preserving_piercing_sides_of_connected_buffers,
    ``exists_auxiliary_scales_preserving_piercing_sides,
    ``exists_section34_component_stability_scales_of_connected_buffers,
    ``exists_positive_finite_crossing_circle_family,
    ``exists_positive_finite_piercing_circle_family,
    ``IsPLCellOn.isConnected_interior_three,
    ``IsPLCellOn.frontier_inter_interior_nonempty,
    ``compact_connected_sides_of_component_pair,
    ``exists_compact_connected_buffers_of_bicollar,
    ``piercing_components_of_connected_buffers,
    ``piercing_conditions_of_crossings_and_margins,
    ``exists_intersection_confinement_of_compact,
    ``IsAnnulusOn.isConnected,
    ``IsAnnulusOn.boundaries_nonempty,
    ``IsAnnulusOn.image_inter_frontier_nonempty,
    ``section34_piercing_trace_nonempty,
    ``exists_section34PiercingPackage,
    ``exists_section34_region_image_stability_scales,
    ``exists_section34_outer_annulus_stability_scales,
    ``exists_section34_inner_end_stability_scales,
    ``exists_section34_trace_interior_stability_scales,
    ``exists_section34_second_trace_interior_stability_scales,
    ``IsAnnulusOn.locallyConnectedSpace,
    ``IsPolyhedralSphere.isConnected,
    ``IsPLCellOn.exists_piercing_bicollar,
    ``exists_section34_connected_buffers_of_source_sides,
    ``exists_section34_connected_buffers,
    ``IsPLCellOn.isConnected_boundary_three,
    ``section34_piercing_source_sides,
    ``IsPolyhedralManifoldWithBoundary.exists_patch,
    ``exists_section34_relative_vertex_crossings,
    ``Moise341.exists_chart_local_cell_approximations,
    ``Moise341.exists_section34VertexApproximation,
    ``exists_chart_stability_scales_of_isCompact,
    ``exists_section34_vertex_chart_stability_scales,
    ``exists_section34_vertex_supported_moves,
    ``IsPolyhedralManifoldWithBoundary.exists_chart_complex,
    ``eventually_mem_chart_image_iff_of_eventually,
    ``exists_small_isPL_homeomorph_surface_crossing_in_chart]
  for name in names do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms in {name}: {axioms.toList}"

end DifferentialGeometry.Topology.PiecewiseLinear
