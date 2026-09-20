import Mathlib.Analysis.Calculus.ContDiff.Convolution

noncomputable section
open MeasureTheory
open scoped Convolution

variable {𝕜 E A B F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup A] [NormedSpace 𝕜 A]
  [NormedAddCommGroup B] [NormedSpace 𝕜 B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  {μ : Measure E} [SFinite μ] [μ.IsAddLeftInvariant]

theorem MeasureTheory.fderiv_convolution_right_apply
    (L : A →L[𝕜] B →L[𝕜] F) {k : E → A} {f : E → B}
    (hk : LocallyIntegrable k μ) (hc : HasCompactSupport f)
    (hf : ContDiff 𝕜 1 f) (x v : E) :
    fderiv 𝕜 (k ⋆[L, μ] f) x v =
      (k ⋆[L, μ] (fun y => fderiv 𝕜 f y v)) x := by
  rw [(hc.hasFDerivAt_convolution_right L hk hf x).fderiv]
  exact convolution_precompR_apply L hk (hc.fderiv 𝕜)
    (hf.continuous_fderiv (by norm_num)) x v

theorem MeasureTheory.fderiv_convolution_left_apply [μ.IsNegInvariant]
    (L : A →L[𝕜] B →L[𝕜] F) {k : E → A} {f : E → B}
    (hc : HasCompactSupport k) (hk : ContDiff 𝕜 1 k) (hf : LocallyIntegrable f μ) (x v : E) :
    fderiv 𝕜 (k ⋆[L, μ] f) x v =
      ((fun y => fderiv 𝕜 k y v) ⋆[L, μ] f) x := by
  simp +singlePass only [← convolution_flip]
  exact fderiv_convolution_right_apply L.flip hf hc hk x v

theorem MeasureTheory.fderiv_fderiv_convolution_right_apply
    (L : A →L[𝕜] B →L[𝕜] F) {k : E → A} {f : E → B}
    (hk : LocallyIntegrable k μ) (hc : HasCompactSupport f)
    (hf : ContDiff 𝕜 2 f) (x v w : E) :
    fderiv 𝕜 (fderiv 𝕜 (k ⋆[L, μ] f)) x v w =
      (k ⋆[L, μ] (fun y => fderiv 𝕜 (fderiv 𝕜 f) y v w)) x := by
  have hconv : ContDiff 𝕜 2 (k ⋆[L, μ] f) := hc.contDiff_convolution_right L hk hf
  have hdiff := (hconv.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have heq : (fun y => fderiv 𝕜 (k ⋆[L, μ] f) y w) =
      k ⋆[L, μ] (fun y => fderiv 𝕜 f y w) := by
    funext y
    exact fderiv_convolution_right_apply L hk hc (hf.of_le (by norm_num)) y w
  have hpartial : ContDiff 𝕜 1 (fun y => fderiv 𝕜 f y w) :=
    (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hderiv (y : E) : fderiv 𝕜 (fun z => fderiv 𝕜 f z w) y v =
      fderiv 𝕜 (fderiv 𝕜 f) y v w := by
    rw [fderiv_clm_apply ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) y)
      (differentiableAt_const w)]
    simp
  have hv : fderiv 𝕜 (fun y => fderiv 𝕜 (k ⋆[L, μ] f) y w) x v =
      fderiv 𝕜 (fderiv 𝕜 (k ⋆[L, μ] f)) x v w := by
    rw [fderiv_clm_apply (hdiff x) (differentiableAt_const w)]
    simp
  rw [← hv, heq, fderiv_convolution_right_apply L hk (hc.fderiv_apply 𝕜 w) hpartial]
  simp_rw [hderiv]

theorem MeasureTheory.fderiv_fderiv_convolution_left_apply [μ.IsNegInvariant]
    (L : A →L[𝕜] B →L[𝕜] F) {k : E → A} {f : E → B}
    (hc : HasCompactSupport k) (hk : ContDiff 𝕜 2 k) (hf : LocallyIntegrable f μ) (x v w : E) :
    fderiv 𝕜 (fderiv 𝕜 (k ⋆[L, μ] f)) x v w =
      ((fun y => fderiv 𝕜 (fderiv 𝕜 k) y v w) ⋆[L, μ] f) x := by
  simp +singlePass only [← convolution_flip]
  exact fderiv_fderiv_convolution_right_apply L.flip hf hc hk x v w
