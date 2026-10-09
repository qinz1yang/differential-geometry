import Mathlib.LinearAlgebra.Complex.Determinant

namespace DifferentialGeometry.Geometry

theorem complex_linearMap_det (A : ℂ →ₗ[ℝ] ℂ) :
    A.det = (A 1).re * (A Complex.I).im - (A Complex.I).re * (A 1).im := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.coe_basisOneI]

end DifferentialGeometry.Geometry
