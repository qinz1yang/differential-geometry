import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.ProfileBoundaryRank
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.ProfileFiniteCriticalSet
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.BranchedCoordinate
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.FiniteFibers
import DifferentialGeometry.Geometry.HarmonicMap.BranchedDeckGerms
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Embeddedness.TangentGraphDifference

set_option autoImplicit false

open DifferentialGeometry.Geometry

namespace DifferentialGeometry.Geometry

/-- Consumer of the K16b batch B2 (boundary rank in the completed profile metric, finite
critical set, branched coordinate, finite fibers, coincident regular germs). -/
example := @boundary_immersion_of_profile_metric

example := @DiskRegularity.ConsumerAudit.profile_boundary_singletons_and_finite_critical_set

example := @DiskRegularity.ConsumerAudit.morrey_leading_projection_branched_coordinate

example := @DiskRegularity.ConsumerAudit.morrey_finite_fibers_of_boundary_fibers_singleton

example := @IsMorreyDisk.coincident_regular_germs_of_branched_height_zero_germ

example := @CuspIncompressibility.ConsumerAudit.morrey_regular_collision_elliptic_height_difference

end DifferentialGeometry.Geometry
