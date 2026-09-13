import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.NormNum

noncomputable section
open MeasureTheory Set InnerProductSpace
open scoped Topology BigOperators
namespace DifferentialGeometry.Analysis
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem integrable_smul_of_continuousOn_tsupport
    {φ : E → ℝ} {f : E → F} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hf : ContinuousOn f (tsupport φ)) : Integrable (fun x => φ x • f x) μ := by
  apply (integrableOn_iff_integrable_of_support_subset
    ((Function.support_smul_subset_left φ f).trans (subset_tsupport φ))).mp
  exact (hφ.continuousOn.smul hf).integrableOn_compact hc

private theorem integral_smul_fderiv_eq_of_contDiffAt
    {φ : E → ℝ} {f : E → F} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hf : ∀ x ∈ tsupport φ, ContDiffAt ℝ 1 f x) (v : E) :
    ∫ x, φ x • fderiv ℝ f x v ∂μ = -∫ x, fderiv ℝ φ x v • f x ∂μ := by
  have hf0 : ContinuousOn f (tsupport φ) :=
    fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hf1 : ContinuousOn (fun x => fderiv ℝ f x v) (tsupport φ) := by
    intro x hx
    exact (((hf x hx).fderiv_right (m := 0) (by norm_num)).continuousAt.clm_apply
      continuousAt_const).continuousWithinAt
  have hφ1 : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  apply integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
  · exact integrable_smul_of_continuousOn_tsupport hφ1 (hc.fderiv_apply ℝ v)
      (hf0.mono (tsupport_fderiv_apply_subset ℝ v))
  · exact integrable_smul_of_continuousOn_tsupport hφ.continuous hc hf1
  · exact integrable_smul_of_continuousOn_tsupport hφ.continuous hc hf0
  · intro x _
    exact hφ.differentiable (by norm_num) x
  · intro x hx
    exact (hf x hx).differentiableAt (by norm_num)

omit [MeasurableSpace E] [BorelSpace E] in
private theorem laplacian_eq_sum_fderiv_apply {f : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f x) :
    Laplacian.laplacian f x = ∑ i, fderiv ℝ
      (fun z => fderiv ℝ f z (stdOrthonormalBasis ℝ E i)) x (stdOrthonormalBasis ℝ E i) := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_clm_apply ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)) (differentiableAt_const _)]
  simp [iteratedFDeriv_two_apply]

theorem integral_smul_laplacian_eq_integral_laplacian_smul
    {φ : E → ℝ} {f : E → F} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hf : ∀ x ∈ tsupport φ, ContDiffAt ℝ 2 f x) :
    ∫ x, φ x • Laplacian.laplacian f x ∂μ =
      ∫ x, Laplacian.laplacian φ x • f x ∂μ := by
  let e := stdOrthonormalBasis ℝ E
  have hφ0 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hf0 : ContinuousOn f (tsupport φ) :=
    fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hφv (v : E) : ContDiff ℝ 1 (fun x => fderiv ℝ φ x v) :=
    (hφ.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hfv (v : E) (x : E) (hx : x ∈ tsupport φ) :
      ContDiffAt ℝ 1 (fun z => fderiv ℝ f z v) x :=
    ((hf x hx).fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  have hleftInt (v : E) : Integrable
      (fun x => φ x • fderiv ℝ (fun z => fderiv ℝ f z v) x v) μ := by
    apply integrable_smul_of_continuousOn_tsupport hφ.continuous hc
    intro x hx
    exact (((hfv v x hx).fderiv_right (m := 0) (by norm_num)).continuousAt.clm_apply
      continuousAt_const).continuousWithinAt
  have hrightInt (v : E) : Integrable
      (fun x => fderiv ℝ (fun z => fderiv ℝ φ z v) x v • f x) μ := by
    apply integrable_smul_of_continuousOn_tsupport
      ((hφv v).continuous_fderiv (by norm_num) |>.clm_apply continuous_const)
      ((hc.fderiv_apply ℝ v).fderiv_apply ℝ v)
    exact hf0.mono ((tsupport_fderiv_apply_subset ℝ v).trans
      (tsupport_fderiv_apply_subset ℝ v))
  have hparts (v : E) :
      (∫ x, φ x • fderiv ℝ (fun z => fderiv ℝ f z v) x v ∂μ) =
        ∫ x, fderiv ℝ (fun z => fderiv ℝ φ z v) x v • f x ∂μ := by
    rw [integral_smul_fderiv_eq_of_contDiffAt hφ0 hc (hfv v) v,
      integral_smul_fderiv_eq_of_contDiffAt (hφv v) (hc.fderiv_apply ℝ v)
        (fun x hx => (hf x (tsupport_fderiv_apply_subset ℝ v hx)).of_le (by norm_num)) v,
      neg_neg]
  have hleft : (fun x => φ x • Laplacian.laplacian f x) =
      fun x => ∑ i, φ x • fderiv ℝ (fun z => fderiv ℝ f z (e i)) x (e i) := by
    funext x
    by_cases hx : φ x = 0
    · simp [hx]
    · rw [laplacian_eq_sum_fderiv_apply (hf x (subset_tsupport φ hx)), Finset.smul_sum]
  have hright : (fun x => Laplacian.laplacian φ x • f x) =
      fun x => ∑ i, fderiv ℝ (fun z => fderiv ℝ φ z (e i)) x (e i) • f x := by
    funext x
    rw [laplacian_eq_sum_fderiv_apply hφ.contDiffAt, Finset.sum_smul]
  rw [hleft, hright, integral_finsetSum Finset.univ (fun i _ => hleftInt (e i)),
    integral_finsetSum Finset.univ (fun i _ => hrightInt (e i))]
  exact Finset.sum_congr rfl (fun i _ => hparts (e i))
end DifferentialGeometry.Analysis
