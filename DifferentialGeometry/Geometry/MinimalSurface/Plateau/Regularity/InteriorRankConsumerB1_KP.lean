import DifferentialGeometry.Geometry.MinimalSurface.Plateau.BranchSlitFold
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.BranchedDeckSlit
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.BranchSlitRegularBuffer
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ChartFoldShortening
import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientConformality

set_option autoImplicit false

open DifferentialGeometry.Geometry

namespace DifferentialGeometry.Geometry

/-- Consumer of the K16b batch B1 (branch-slit / fold-shortening / deck-slit kernels):
the exclusion of a regular branched height-zero arc, as used in
`interior_immersion_of_completed_profile` (batch B4). -/
example := @IsMorreyDisk.not_regular_branched_height_zero_arc

example := @IsMorreyDisk.root_height_fderiv_eq_zero_of_not_transverse

example := @IsMorreyDisk.not_transverse_of_actual_slit_straightening

example := @exists_branch_slit_regular_buffer

example := @exists_disk_area_lt_of_chart_fold_divergence_neg

example := @chartComplexGradient_isotropic

end DifferentialGeometry.Geometry
