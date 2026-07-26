import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SmoothCcDense
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.DenseSubset

/-!
# Injectivity of smooth spectral embeddings

The spectral Sobolev embedding retains every coefficient of the underlying
`L2` tensor.  Since the smooth-to-`L2` map is injective, the spectral embedding
of smooth covariant tensors is injective at every real Sobolev order.
-/

noncomputable section

open Bundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.L2

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- The generic smooth covariant-tensor spectral embedding is injective at
every real Sobolev order. -/
theorem ccToHs_injective (g : SmoothRiemannianMetric I M) (s : ℕ) (σ : ℝ) :
    Function.Injective (ccTensorToHs (I := I) (M := M) g s σ) := by
  intro S T hST
  apply SmoothCcTensor.smoothCcTensor_eq_of_toL2_eq S T
  let hcompact := tensorResolventL2_isCompactOperator
    (I := I) (M := M) g 0 s
  apply (tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) hcompact).repr.injective
  funext i
  have hi := congrArg (fun u => u.coeff i) hST
  simpa only [ccTensorToHs_coeff, tensorL2Coeff] using hi

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
