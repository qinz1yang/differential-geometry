import DifferentialGeometry.Analysis.Elliptic.WithBoundary.CompactDiskStabilityTransport

set_option autoImplicit false

open DifferentialGeometry.Geometry.Metric

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

/-- Type-alignment consumer: the compact-test stability inequality on the open unit disk
transports to every smooth Dirichlet test on a closed cell pulled back along an immersion. -/
example := @integral_stability_closedCell_pullback_of_compact_tests

/-- Type-alignment consumer: a closed cell pullback metric whose image contains a given
Riemannian closed ball. -/
example := @exists_closedCell_pullback_containing_riemannianClosedBallOf

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
