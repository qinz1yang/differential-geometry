import DifferentialGeometry.Geometry.Hyperbolic.TruncationGeometry

/-!
# Consumer of the G4 intake (S-HG-INTAKE-2, suffix `_HGI2`)

The proved twin of the skeleton `has_hyperbolic_atlas_of_curvature_neg_one` (a metric of constant
curvature `-1` on a 3-manifold has a hyperbolic Thurston atlas), its rescaled form for constant
curvature `κ < 0`, the hyperbolic geometric structure built from it, and the hyperbolic structure
on the interior of a truncated image.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Hyperbolic

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

example (g : SmoothRiemannianMetric (𝓡 3) M) (hcurvature : hasConstantSectionalCurvature g (-1)) :
    GC.Geometry.HasThurstonAtlas g .hyperbolic :=
  has_hyperbolic_atlas_of_curvature_neg_one_HGI2 g hcurvature

example (g : SmoothRiemannianMetric (𝓡 3) M) (κ : ℝ) (hκ : κ < 0)
    (hcurvature : hasConstantSectionalCurvature g κ) :
    GC.Geometry.HasThurstonAtlas (scaleMetric (-κ) (neg_pos.mpr hκ) g) .hyperbolic :=
  has_hyperbolic_atlas_scaleMetric g κ hκ hcurvature

example [T2Space M] [SigmaCompactSpace M] (g : SmoothRiemannianMetric (𝓡 3) M)
    (hcurvature : hasConstantSectionalCurvature g (-(1 / 4 : ℝ)))
    (hcomplete : RiemannianMetricComplete g)
    (hvolume : Integral.Measure.riemannianVolumeMeasure (𝓡 3) M g Set.univ < ⊤) :
    (hyperbolicGeometricStructure_HGI2 g hcurvature hcomplete hvolume).model = .hyperbolic :=
  hyperbolicGeometricStructure_HGI2_model g hcurvature hcomplete hvolume

open HyperbolicTruncation in
example := @exists_hyperbolic_structure_interior_of_truncated_image

end DifferentialGeometry.Geometry.Hyperbolic
