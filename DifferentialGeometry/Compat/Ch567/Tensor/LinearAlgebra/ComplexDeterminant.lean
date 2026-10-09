import DifferentialGeometry.Tensor.LinearAlgebra.ComplexDeterminant

/-!
# PORT567 compatibility names: determinant of a real-linear endomorphism of `ℂ`

Later-layout name `LinearMap.det_complex` of the integration-layout theorem
`DifferentialGeometry.Geometry.complex_linearMap_det` (identical statement and proof).
-/

set_option autoImplicit false

namespace LinearMap

theorem det_complex (A : ℂ →ₗ[ℝ] ℂ) :
    A.det = (A 1).re * (A Complex.I).im - (A Complex.I).re * (A 1).im :=
  DifferentialGeometry.Geometry.complex_linearMap_det A

end LinearMap
