import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.CoreHomotopy
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.ParabolicHoroballs
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.Retruncation
import DifferentialGeometry.Analysis.Integration.Measure.CylindricalCore
import DifferentialGeometry.Analysis.Integration.Measure.GroupQuotient.FiniteIndex
import DifferentialGeometry.Geometry.Curvature.Bounds.RawPullbackSectionalPinching
import DifferentialGeometry.Geometry.Measure.UniversalCoverDomain
import DifferentialGeometry.Geometry.Metric.Distance.SetComparison
import DifferentialGeometry.Geometry.Metric.Pullback.LocalDiffeomorph
import DifferentialGeometry.Topology.FundamentalGroup.Product.Slice
import DifferentialGeometry.Topology.GroupAction.EquivariantDistance
import DifferentialGeometry.Topology.MetricSpace.CoarseInverse

/-!
# Consumer of the G3 intake (S-HG-INTAKE-2, suffix `_HGI2`)

HG03-side helpers of the donor line: the cylindrical-core homotopy equivalence, retruncation of a
cusp truncation, precisely invariant horoballs, the finite-index covolume formula, and a few small
metric lemmas.
-/

set_option autoImplicit false

open DifferentialGeometry.CuspTruncation.FiniteCuspTruncation in
example := @exists_homotopyEquiv_quotient_truncatedSet

open DifferentialGeometry.CuspTruncation.FiniteCuspTruncation in
example := @core_subset_retruncate_core

example := @DifferentialGeometry.ParabolicHoroballs.exists_precisely_invariant_horoball

example := @DifferentialGeometry.Topology.exists_pos_subset_cylindricalCore_measure_compl_lt

example := @DifferentialGeometry.FiniteIndexCovolume.covolume_subgroup

open DifferentialGeometry.Geometry.Curvature in
example := @exists_pos_sectional_pinching_of_raw_pullback_derivatives

open DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover in
example := @exists_fundamental_domain_volume_eq

open DifferentialGeometry.Geometry.Metric in
example := @exists_partialDiffeomorph_of_injOn_of_metric_lower

open DifferentialGeometry.Geometry.Metric in
example := @lt_iInf_riemannianEDistOf_of_le_near_set

example := @DifferentialGeometry.Topology.bijective_fundamentalGroup_map_prodMk_const

example := @MulAction.exists_dist_le_on_quotient_preimage_of_equivariant

example := @Metric.exists_quasi_isometry_bounds_of_coarse_left_inverse
