import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.ContDiff.Comp



noncomputable section

open InnerProductSpace Laplacian
open scoped ContDiff

namespace DifferentialGeometry.Analysis




theorem continuous_laplacian {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ 2 f) : Continuous (laplacian f) := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  apply continuous_finsetSum
  intro i _
  exact (hf.continuous_iteratedFDeriv' (m := 2)).eval_const _

end DifferentialGeometry.Analysis
