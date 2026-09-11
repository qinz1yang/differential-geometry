import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.GreenIdentity
import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariation.Minimizer



noncomputable section

open Filter Set InnerProductSpace
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis



theorem secondDirectional_nonneg_of_localMin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (hmin : IsLocalMin f z) (v : E) :
    0 ≤ fderiv ℝ (fun q => fderiv ℝ f q v) z v := by
  let line : ℝ → E := fun t => z + t • v
  let φ : ℝ → ℝ := f ∘ line
  have hl (t : ℝ) : HasDerivAt line v t := by
    simpa [line] using ((hasDerivAt_id t).smul_const v).const_add z
  have hl0 : line 0 = z := by simp [line]
  have hm : IsLocalMin φ 0 := by
    have h : IsLocalMin f (line 0) := by rwa [hl0]
    exact h.comp_continuous (hl 0).continuousAt
  have hfd := hf.differentiableAt (by norm_num)
  have hfirst : HasDerivAt φ 0 0 := by
    have h := hfd.hasFDerivAt.comp_hasDerivAt_of_eq (x := 0) (hl 0) hl0.symm
    simpa only [hmin.fderiv_eq_zero, _root_.zero_apply] using h
  have hpartial : DifferentiableAt ℝ (fun q => fderiv ℝ f q v) z :=
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  have hnear : deriv φ =ᶠ[𝓝 0] (fun t => fderiv ℝ f (line t) v) := by
    have hreg : ∀ᶠ t in 𝓝 (0 : ℝ), ContDiffAt ℝ 2 f (line t) := by
      have ht : Tendsto line (𝓝 0) (𝓝 z) := by
        have ht := (hl 0).continuousAt
        change Tendsto line (𝓝 0) (𝓝 (line 0)) at ht
        rwa [hl0] at ht
      exact ht.eventually (hf.eventually (by norm_num))
    filter_upwards [hreg] with t ht
    exact ((ht.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hl t)).deriv
  have hsecond : HasDerivAt (deriv φ)
      (fderiv ℝ (fun q => fderiv ℝ f q v) z v) 0 :=
    (hpartial.hasFDerivAt.comp_hasDerivAt_of_eq (x := 0) (hl 0) hl0.symm).congr_of_eventuallyEq hnear
  exact DifferentialGeometry.Geometry.Riemannian.Variation.second_deriv_nonneg_of_isLocalMin
    hm hfirst hsecond


theorem laplacian_nonneg_of_localMin {f : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) (hmin : IsLocalMin f z) :
    0 ≤ Laplacian.laplacian f z := by
  rw [← complexDivergence_gradient hf]
  exact add_nonneg (secondDirectional_nonneg_of_localMin hf hmin 1)
    (secondDirectional_nonneg_of_localMin hf hmin Complex.I)



theorem differential_laplacian_at_nonnegative_zero {f : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) (hn : ∀ᶠ q in 𝓝 z, 0 ≤ f q) (hz : f z = 0) :
    fderiv ℝ f z = 0 ∧ 0 ≤ Laplacian.laplacian f z := by
  have hm : IsLocalMin f z := by
    change ∀ᶠ q in 𝓝 z, f z ≤ f q
    simpa only [hz] using hn
  exact ⟨hm.fderiv_eq_zero, laplacian_nonneg_of_localMin hf hm⟩

end DifferentialGeometry.Analysis
