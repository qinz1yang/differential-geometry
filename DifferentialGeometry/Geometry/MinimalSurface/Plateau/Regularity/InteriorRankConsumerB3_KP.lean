import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Embeddedness.RegularCollisionNodalArcs
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Embeddedness.CoincidentGermClosure
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.ProfileBranchDeckExclusion
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.ProjectionGraphHessian
import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientGraphResidualBounds

set_option autoImplicit false

open DifferentialGeometry.Geometry CuspIncompressibility.ConsumerAudit DiskRegularity.ConsumerAudit

namespace DifferentialGeometry.Geometry

/-- Consumer of the K16b batch B3 (regular collision / nodal arcs, coincident germ closure,
regular-value restriction, deck exclusion, graph jets). -/
example := @morrey_regular_collision_zero_germ_or_smooth_nodal_arcs

example := @IMS03Embeddedness.actual_morrey_coincident_germ_pairs_isClosed

example := @profile_regular_value_restriction_no_coincident_germs

example := @profile_branched_height_not_zero_germ

example := @morrey_branched_coordinate_with_projection_graph_hessian_bound

example := @chartLeadingPlaneProjection_graph_residual_jet_bounds

end DifferentialGeometry.Geometry
