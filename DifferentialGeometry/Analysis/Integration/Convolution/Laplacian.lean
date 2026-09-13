import DifferentialGeometry.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.ContDiff.Convolution

noncomputable section
open Set MeasureTheory InnerProductSpace DifferentialGeometry.Analysis
open scoped Topology ContDiff Convolution

variable {E A B F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [SFinite μ] [μ.IsAddLeftInvariant]

omit [FiniteDimensional ℝ E] in
private theorem fderiv_convolution_apply
    (L : A →L[ℝ] B →L[ℝ] F) {k : E → A} {f : E → B}
    (hk : LocallyIntegrable k μ) (hc : HasCompactSupport f)
    (hf : ContDiff ℝ 1 f) (z v : E) :
    fderiv ℝ (k ⋆[L, μ] f) z v =
      (k ⋆[L, μ] (fun q => fderiv ℝ f q v)) z := by
  rw [(hc.hasFDerivAt_convolution_right L hk hf z).fderiv]
  exact convolution_precompR_apply L hk (hc.fderiv ℝ)
    (hf.continuous_fderiv (by norm_num)) z v

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
private theorem second_partial {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {g : E → V} (hg : ContDiff ℝ 2 g) (x v : E) :
    fderiv ℝ (fderiv ℝ g) x v v =
      fderiv ℝ (fun q => fderiv ℝ g q v) x v := by
  rw [fderiv_clm_apply ((hg.fderiv_right (m := 1) (by norm_num)).differentiable
    (by norm_num) x) (differentiableAt_const v)]
  simp

theorem MeasureTheory.laplacian_convolution_right
    (L : A →L[ℝ] B →L[ℝ] F) {k : E → A} {f : E → B}
    (hk : LocallyIntegrable k μ) (hc : HasCompactSupport f)
    (hf : ContDiff ℝ 2 f) (z : E) :
    Laplacian.laplacian (k ⋆[L, μ] f) z =
      (k ⋆[L, μ] Laplacian.laplacian f) z := by
  have hconv : ContDiff ℝ 2 (k ⋆[L, μ] f) := hc.contDiff_convolution_right L hk hf
  have hpartial (v : E) : ContDiff ℝ 1 (fun q => fderiv ℝ f q v) :=
    (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have he (v : E) : (fun q => fderiv ℝ (k ⋆[L, μ] f) q v) =
      k ⋆[L, μ] (fun q => fderiv ℝ f q v) := by
    funext q
    exact fderiv_convolution_apply L hk hc (hf.of_le (by norm_num)) q v
  have hi (v : E) : Integrable (fun w : E => L (k w)
      (fderiv ℝ (fun q => fderiv ℝ f q v) (z - w) v)) μ :=
    ((hc.fderiv_apply ℝ v).fderiv_apply ℝ v).convolutionExists_right L hk
      (((hpartial v).continuous_fderiv (by norm_num)).clm_apply continuous_const) z
  simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, second_partial hconv, he,
    fderiv_convolution_apply L hk (hc.fderiv_apply ℝ _) (hpartial _), convolution_def,
    second_partial hf]
  rw [← integral_finsetSum Finset.univ (fun i _ => hi ((stdOrthonormalBasis ℝ E) i))]
  apply integral_congr_ae
  filter_upwards with w
  exact (map_sum (L (k w)) _ _).symm


theorem MeasureTheory.laplacian_convolution_left [μ.IsNegInvariant]
    (L : A →L[ℝ] B →L[ℝ] F) {k : E → A} {f : E → B}
    (hc : HasCompactSupport k) (hk : ContDiff ℝ 2 k) (hf : LocallyIntegrable f μ) (z : E) :
    Laplacian.laplacian (k ⋆[L, μ] f) z =
      (Laplacian.laplacian k ⋆[L, μ] f) z := by
  simp +singlePass only [← convolution_flip]
  exact MeasureTheory.laplacian_convolution_right L.flip hf hc hk z

theorem DifferentialGeometry.Analysis.laplacian_convolution_of_weak_laplacian [μ.IsNegInvariant]
    {u g : E → F} (hu : LocallyIntegrable u μ)
    (hw : ∀ φ : E → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      (∫ y, Laplacian.laplacian φ y • u y ∂μ) = ∫ y, φ y • g y ∂μ)
    {κ : E → ℝ} (hκ : ContDiff ℝ 2 κ) (hc : HasCompactSupport κ) (x : E) :
    Laplacian.laplacian (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u) x =
      (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g) x := by
  rw [laplacian_convolution_left _ hc hκ hu, ← convolution_flip, ← convolution_flip
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (f := κ) (g := g)]
  have ht : ContDiff ℝ 2 (fun y : E => κ (x - y)) := hκ.comp (contDiff_const.sub contDiff_id)
  have hct : HasCompactSupport (fun y : E => κ (x - y)) :=
    hc.comp_homeomorph (Homeomorph.subLeft x)
  have hh := hw (fun y => κ (x - y)) ht hct
  simpa only [convolution_def, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply, laplacian_comp_const_sub] using hh
