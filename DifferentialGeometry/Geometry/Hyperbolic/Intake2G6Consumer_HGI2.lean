import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.JetCongruence
import DifferentialGeometry.Geometry.Metric.Pullback.FiniteInnerRegularity
import DifferentialGeometry.Geometry.Connection.TensorNabla.FixedChart.RawMetricDerivative
import DifferentialGeometry.Geometry.Connection.TensorNabla.FixedChart.FiniteMetricRegularity
import DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.CoordinateJets
import DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.SmoothCompatibility
import DifferentialGeometry.Geometry.Metric.Pullback.FiniteCovariantJets
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.FiniteJetRealization
import DifferentialGeometry.Geometry.Curvature.Metric.Parallel
import DifferentialGeometry.Geometry.Curvature.Metric.ConstantSectionalNorm
import DifferentialGeometry.Geometry.Curvature.Bounds.MetricPerturbation
import DifferentialGeometry.Geometry.Comparison.Volume.InteriorBallLowerBound

/-!
# Consumer of the G6 intake (S-HG-INTAKE-2, suffix `_HGI2`)

Finite-jet / metric-regularity infrastructure of the donor line: iterated derivatives depend only
on finite jets, the metric covariant derivative in coordinates, pullback errors depend only on the
jet of the map, constant sectional curvature is parallel, and a partial diffeomorphism can realise a
prescribed finite jet.
-/

set_option autoImplicit false

open DifferentialGeometry

example := @Analysis.iteratedFDeriv_comp_eq_of_eq_jets

example := @contMDiffAt_localPullInner_of_contMDiffAt

example := @Geometry.Connection.tensor0SModelInChart_metricCovariantDerivative

example := @Geometry.Connection.iteratedMetricCovariantDerivative_eq_of_coordinate_jets

example := @CheegerGromovCompactness.metricDerivNorm_eq_iteratedMetricCovariantDerivative

example := @Geometry.metricDerivNorm_eq_raw_pullbackError_of_map_jets

example := @Analysis.exists_partialDiffeomorph_finiteTaylorPolynomial

example := @Manifold.exists_partialDiffeomorph_eq_finiteJet

example := @Geometry.Curvature.curvatureDerivativeNorm_eq_zero_of_constant_sectional

example := @Geometry.Curvature.curvatureDerivativeNorm_zero_le_one_of_constant_sectional_neg_quarter

example := @Geometry.Curvature.exists_pos_bound_intrinsic_curvature_derivative_of_metric_error

example := @Geometry.Riemannian.VolumeComparison.riemannianBallOf_volume_lower_of_nearby_center
