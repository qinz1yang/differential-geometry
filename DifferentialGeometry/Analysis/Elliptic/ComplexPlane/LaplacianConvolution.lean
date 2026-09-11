import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.GreenIdentity
import Mathlib.Analysis.Calculus.ContDiff.Convolution



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
  let L := ContinuousLinearMap.mul ℝ ℝ
  have hconv : ContDiff ℝ 2 (k ⋆[L] f) := hc.contDiff_convolution_right L hk hf
  have hpartial (v : ℂ) : ContDiff ℝ 1 (fun q => fderiv ℝ f q v) :=
    (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have he (v : ℂ) : (fun q => fderiv ℝ (k ⋆[L] f) q v) =
      k ⋆[L] (fun q => fderiv ℝ f q v) := by
    funext q
    exact fderiv_convolution_smooth_right_apply hk hc (hf.of_le (by norm_num)) q v
  rw [← complexDivergence_gradient hconv.contDiffAt, complexDivergence,
    he 1, he Complex.I,
    fderiv_convolution_smooth_right_apply hk (hc.fderiv_apply ℝ 1) (hpartial 1),
    fderiv_convolution_smooth_right_apply hk (hc.fderiv_apply ℝ Complex.I) (hpartial Complex.I)]
  have hi (v : ℂ) : Integrable (fun w : ℂ => k w *
      fderiv ℝ (fun q => fderiv ℝ f q v) (z - w) v) :=
    ((hc.fderiv_apply ℝ v).fderiv_apply ℝ v).convolutionExists_right L hk
      (((hpartial v).continuous_fderiv (by norm_num)).clm_apply continuous_const) z
  simp only [convolution_def, ContinuousLinearMap.mul_apply']
  rw [← integral_add (hi 1) (hi Complex.I)]
  apply integral_congr_ae
  filter_upwards with w
  rw [← mul_add, ← complexDivergence_gradient hf.contDiffAt]
  rfl



theorem laplacian_comp_const_sub (f : ℂ → ℝ) (a z : ℂ) :
    Laplacian.laplacian (fun w => f (a - w)) z = Laplacian.laplacian f (a - z) := by
  let e : ℂ ≃L[ℝ] ℂ := ContinuousLinearEquiv.neg ℝ
  have he := e.iteratedFDerivWithin_comp_right (fun w => f (a + w))
    (s := univ) uniqueDiffOn_univ (x := z) (mem_univ _) 2
  simp only [preimage_univ, iteratedFDerivWithin_univ] at he
  have hfun : (fun w => f (a - w)) = (fun w => f (a + w)) ∘ e := by
    ext w
    simp [e, sub_eq_add_neg]
  simp only [laplacian_eq_iteratedFDeriv_complexPlane, hfun, he,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe, iteratedFDeriv_comp_add_left]
  change iteratedFDeriv ℝ 2 f (a - z) (-![1, 1]) +
    iteratedFDeriv ℝ 2 f (a - z) (-![Complex.I, Complex.I]) = _
  have hneg (m : Fin 2 → ℂ) : iteratedFDeriv ℝ 2 f (a - z) (-m) =
      iteratedFDeriv ℝ 2 f (a - z) m := by
    change iteratedFDeriv ℝ 2 f (a - z) (fun i => -m i) = _
    simpa using (iteratedFDeriv ℝ 2 f (a - z)).map_smul_univ
      (fun _ : Fin 2 => (-1 : ℝ)) m
  rw [hneg, hneg]

end DifferentialGeometry.Analysis
