import DifferentialGeometry.Geometry.Hyperbolic.CuspSlice
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspSliceTransport
import DifferentialGeometry.Geometry.Hyperbolic.Cusp.FlatUniversalCover
import DifferentialGeometry.Geometry.Hyperbolic.Cusp.FlatCoverProjection
import DifferentialGeometry.Geometry.Hyperbolic.Cusp.OrthonormalCoverProjection
import DifferentialGeometry.Geometry.Hyperbolic.Cusp.PositiveDepthMap
import DifferentialGeometry.Geometry.Hyperbolic.Horospherical.MetricAlgebra
import DifferentialGeometry.Geometry.Hyperbolic.Horospherical.ManifoldMetric
import DifferentialGeometry.Geometry.Hyperbolic.Horospherical.ModelLocalDiffeomorph
import DifferentialGeometry.Geometry.Hyperbolic.Horospherical.ShiftedModel
import DifferentialGeometry.Geometry.Hyperbolic.Horospherical.ShiftedModelFrame
import DifferentialGeometry.Geometry.Hyperbolic.Cusp.PositiveDepthFrame
import DifferentialGeometry.Geometry.Hyperbolic.Cusp.NormalizedCoverFrame
import DifferentialGeometry.Geometry.Hyperbolic.Cusp.PositiveMetric
import DifferentialGeometry.Geometry.Hyperbolic.Cusp.CoverCommutation
import DifferentialGeometry.Geometry.Hyperbolic.Cusp.SliceLift
import DifferentialGeometry.Geometry.Hyperbolic.ProjectedNormalizedCoverJet
import DifferentialGeometry.Geometry.Hyperbolic.Cusp.CoverAssembly
import DifferentialGeometry.Topology.Covering.FundamentalGroup.CoveringSquareInjective
import DifferentialGeometry.Topology.Covering.FundamentalGroup.CoveringSquareConsumers
import DifferentialGeometry.Geometry.Hyperbolic.Cusp.FundamentalGroup
import DifferentialGeometry.Geometry.Hyperbolic.Cusp.BoundaryFromCover
import DifferentialGeometry.Geometry.Hyperbolic.Cusp.Incompressibility

/-!
# Consumer of the G7 intake (S-HG-INTAKE-2, suffix `_HGI2`)

Cusp covering squares and incompressibility of the truncation boundary (DM version of the DM / DR
fork zone): the boundary tori of a hyperbolic truncation are incompressible, built from the native
normalized covering square of each cusp.
-/

set_option autoImplicit false

open DifferentialGeometry.Geometry.Hyperbolic

universe u

example {H : FiniteVolumeHyperbolicModel.{u}} (Tr : HyperbolicTruncation H) :
    Tr.boundary.incompressible :=
  Tr.boundary_incompressible

example := @HyperbolicTruncation.exists_native_cover_square_of_curvature_identity

example := @HyperbolicTruncation.boundary_incompressible_of_covering_square

example := @cuspSlice_fundamentalGroup_bijective

example := @HyperbolicCusp.exists_flat_cover_projection

example := @HyperbolicCusp.exists_orthonormal_cover_projection

example := @Horospherical.model_isLocalDiffeomorph

example := @isLocalDiffeomorph_proj_normalizedUniversalCoverIsometryEquiv
