import DifferentialGeometry.Geometry.Surface.GaussCurvature
import DifferentialGeometry.Geometry.Metric.Sphere.RoundMetric

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open DifferentialGeometry.Geometry
open Metric
open scoped Manifold ContDiff

local instance : Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

local instance : NeZero (Module.finrank Real (EuclideanSpace Real (Fin 2))) :=
  ⟨by rw [finrank_euclideanSpace_fin]; norm_num⟩

theorem roundMetric_gaussCurvature_eq_one
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    gaussCurvature (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x = 1 := sorry

end DifferentialGeometry.Integral.Connection
