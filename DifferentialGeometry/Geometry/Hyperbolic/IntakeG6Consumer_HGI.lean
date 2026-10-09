import DifferentialGeometry.Geometry.Hyperbolic.QuantitativeRigidity

/-!
# Consumer of the G6 intake (S-HG-INTAKE, suffix `_HGI`)

The quantitative rigidity theorem `exists_isometry_close_of_homotopyEquiv` (all small `ε`, all
orders `k ≥ ⌈ε⁻¹⌉`), elaborated with its explicit hypotheses.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Hyperbolic

variable {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

example (g : SmoothRiemannianMetric (𝓡 3) M) (K : ℝ) (hK : K < 0)
    (hgcurvature : hasConstantSectionalCurvature g K) (hgcomplete : RiemannianMetricComplete g)
    (hgvolume : Integral.Measure.riemannianVolumeMeasure (𝓡 3) M g Set.univ < ⊤)
    (o : M) {η : ℝ} (hη : 0 < η) :=
  exists_isometry_close_of_homotopyEquiv g K hK hgcurvature hgcomplete hgvolume o hη

end DifferentialGeometry.Geometry.Hyperbolic
