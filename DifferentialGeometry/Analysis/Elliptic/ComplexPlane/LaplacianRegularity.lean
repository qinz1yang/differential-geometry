import DifferentialGeometry.Analysis.InnerProductSpace.Laplacian



noncomputable section

open InnerProductSpace Laplacian
open scoped ContDiff

namespace DifferentialGeometry.Analysis




theorem continuous_laplacian {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ 2 f) : Continuous (laplacian f) := by
  exact continuous_iff_continuousAt.mpr (fun _ => hf.contDiffAt.continuousAt_laplacian)

end DifferentialGeometry.Analysis
