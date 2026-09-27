import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.GreenIdentity
import DifferentialGeometry.Analysis.Integration.Convolution.Laplacian



noncomputable section

open Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution

namespace DifferentialGeometry.Analysis



theorem fderiv_convolution_smooth_right_apply {k f : ℂ → ℝ}
    (hk : LocallyIntegrable k volume) (hc : HasCompactSupport f)
    (hf : ContDiff ℝ 1 f) (z v : ℂ) :
    fderiv ℝ (k ⋆[ContinuousLinearMap.mul ℝ ℝ] f) z v =
      (k ⋆[ContinuousLinearMap.mul ℝ ℝ] (fun q => fderiv ℝ f q v)) z := by
  rw [(hc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hk hf z).fderiv]
  exact convolution_precompR_apply _ hk (hc.fderiv ℝ)
    (hf.continuous_fderiv (by norm_num)) z v



theorem laplacian_convolution_smooth_right {k f : ℂ → ℝ}
    (hk : LocallyIntegrable k volume) (hc : HasCompactSupport f)
    (hf : ContDiff ℝ 2 f) (z : ℂ) :
    Laplacian.laplacian (k ⋆[ContinuousLinearMap.mul ℝ ℝ] f) z =
      (k ⋆[ContinuousLinearMap.mul ℝ ℝ] Laplacian.laplacian f) z := by
  exact MeasureTheory.laplacian_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hk hc hf z

end DifferentialGeometry.Analysis
