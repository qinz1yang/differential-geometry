import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.ProfileInteriorRank

set_option autoImplicit false

open DifferentialGeometry.Geometry

namespace DifferentialGeometry.Geometry

/-- Consumer of the K16b batch B4: the headline theorem `interior_immersion_of_completed_profile`
(the confined Morrey disk in the completed profile metric has no interior branch points), and
the branched-deck nodal chart theorem it rests on. -/
example := @interior_immersion_of_completed_profile

example := @IsMorreyDisk.exists_branched_deck_nodal_chart_of_not_injective

example := @DifferentialGeometry.Analysis.exists_branch_deck_c1_nodal_chart

end DifferentialGeometry.Geometry
