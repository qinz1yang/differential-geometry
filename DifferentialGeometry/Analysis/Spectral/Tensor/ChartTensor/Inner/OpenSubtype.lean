import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.InnerBridge
import DifferentialGeometry.Topology.Manifold.OpenSubtypeModel

noncomputable section
open scoped Manifold
namespace DifferentialGeometry.Analysis.Parabolic.TensorSpectral
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]

theorem chartGramBilin_opens_model
    (U : TopologicalSpace.Opens E) (g : SmoothRiemannianMetric 𝓘(ℝ, E) U)
    (α b : U) (u w : E) :
    chartGramBilin (I := 𝓘(ℝ, E)) g α b u w = g.inner b u w := by
  rw [chartGramBilin_eq_innerJinv]
  simp only [Integral.L2.modelInnerAt_apply]
  unfold Tensor.Tensor0SRiemannian.chartTrivializationLinearMapSymm
  rw [symmL_opens_model]
  rfl

end DifferentialGeometry.Analysis.Parabolic.TensorSpectral
