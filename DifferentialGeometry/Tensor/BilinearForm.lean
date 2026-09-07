import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.BilinearForm

namespace LinearMap.BilinForm

theorem det_toMatrix_basis_change
    {R E i : Type*} [CommRing R] [AddCommGroup E] [Module R E]
    [Fintype i] [DecidableEq i] (B : LinearMap.BilinForm R E) (b c : Module.Basis i R E) :
    (toMatrix c B).det = b.det c ^ 2 * (toMatrix b B).det := by
  rw [← B.toMatrix_mul_basis_toMatrix b c, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, Module.Basis.det_apply]
  ring

end LinearMap.BilinForm
