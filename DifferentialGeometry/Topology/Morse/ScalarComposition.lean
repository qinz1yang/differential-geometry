import DifferentialGeometry.Analysis.Schauder.Holder.SecondOrderComposition
import DifferentialGeometry.Tensor.QuadraticForm.Scaling
import DifferentialGeometry.Topology.Morse.Defs
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

open scoped Manifold

namespace DifferentialGeometry.Topology.Morse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open DifferentialGeometry.Analysis.Schauder in
theorem chartHessianAt_scalar_comp_of_fderiv_eq_zero
    {f : E → ℝ} {φ : ℝ → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hφ : ContDiffAt ℝ 2 φ (f x))
    (hcrit : fderiv ℝ f x = 0) :
    chartHessianAt (φ ∘ f) x = deriv φ (f x) • chartHessianAt f x := by
  have h := hessianCurryEquiv_iteratedFDeriv_two_comp hφ hf
  simp only [hessianCurryEquiv_iteratedFDeriv_two_eq_fderiv] at h
  ext v
  change fderiv ℝ (fderiv ℝ (φ ∘ f)) x v v =
    deriv φ (f x) * fderiv ℝ (fderiv ℝ f) x v v
  rw [h]
  simp [c2PullbackHessian, hcrit, fderiv_eq_smul_deriv, mul_comm]

variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem isCriticalPointAt_scalar_comp_iff
    {f : M → ℝ} {φ : ℝ → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hφ : DifferentiableAt ℝ φ (f x)) (hd : deriv φ (f x) ≠ 0) :
    IsCriticalPointAt I (φ ∘ f) x ↔ IsCriticalPointAt I f x := by
  unfold IsCriticalPointAt
  rw [mfderiv_comp x hφ.mdifferentiableAt hf]
  constructor
  · intro h
    have hinj : Function.Injective (fderiv ℝ φ (f x)) := by
      intro s t hst
      simpa only [fderiv_eq_deriv_mul, mul_right_inj' hd] using hst
    ext v
    apply hinj
    have hv := congrArg (fun L : E →L[ℝ] ℝ => L v) h
    change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ (f x) (mfderiv I 𝓘(ℝ, ℝ) f x v) = 0 at hv
    rw [mfderiv_eq_fderiv] at hv
    exact hv.trans (map_zero (fderiv ℝ φ (f x))).symm
  · intro h
    ext v
    change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ (f x) (mfderiv I 𝓘(ℝ, ℝ) f x v) = 0
    rw [h, zero_apply, map_zero]

variable [I.Boundaryless]

theorem chartHessianAt_scalar_comp
    {f : M → ℝ} {φ : ℝ → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x) (hφ : ContDiffAt ℝ 2 φ (f x))
    (hcrit : IsCriticalPointAt I f x) :
    chartHessianAt (fun z => φ (f ((extChartAt I x).symm z))) (extChartAt I x x) =
      deriv φ (f x) • chartHessianAt (fun z => f ((extChartAt I x).symm z))
        (extChartAt I x x) := by
  classical
  have hchart : ContDiffAt ℝ 2 (fun z => f ((extChartAt I x).symm z))
      (extChartAt I x x) := by
    simpa only [Function.comp_def, I.range_eq_univ, contDiffWithinAt_univ,
      extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp, id_eq]
      using (contMDiffAt_iff.mp hf).2
  have hc : fderiv ℝ (fun z => f ((extChartAt I x).symm z))
      (extChartAt I x x) = 0 := by
    have hmd : MDifferentiableAt I 𝓘(ℝ, ℝ) f x := hf.mdifferentiableAt (by norm_num)
    change (if MDifferentiableAt I 𝓘(ℝ, ℝ) f x then
      fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ, ℝ) x f) (Set.range I)
        (extChartAt I x x) else (0 : E →L[ℝ] ℝ)) = 0 at hcrit
    rw [if_pos hmd] at hcrit
    simp only [I.range_eq_univ, fderivWithin_univ,
      writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      Function.id_comp] at hcrit
    exact hcrit
  simpa only [Function.comp_def, extChartAt_to_inv] using
    chartHessianAt_scalar_comp_of_fderiv_eq_zero hchart
      (by simpa only [extChartAt_to_inv] using hφ) hc

theorem isNondegenerateCriticalPointAt_scalar_comp_iff
    {f : M → ℝ} {φ : ℝ → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x) (hφ : ContDiffAt ℝ 2 φ (f x))
    (hd : deriv φ (f x) ≠ 0) :
    IsNondegenerateCriticalPointAt I (φ ∘ f) x ↔
      IsNondegenerateCriticalPointAt I f x := by
  have hc := isCriticalPointAt_scalar_comp_iff (hf.mdifferentiableAt (by norm_num))
    (hφ.differentiableAt (by norm_num)) hd
  by_cases hcrit : IsCriticalPointAt I f x
  · simp only [IsNondegenerateCriticalPointAt, hc, hcrit, true_and, Function.comp_apply]
    rw [chartHessianAt_scalar_comp hf hφ hcrit, map_smul]
    simp only [LinearMap.SeparatingLeft, LinearMap.smul_apply, smul_eq_mul,
      mul_eq_zero, hd, false_or]
  · simp only [IsNondegenerateCriticalPointAt, hc, hcrit, false_and]

theorem sigNeg_chartHessianAt_scalar_comp
    {f : M → ℝ} {φ : ℝ → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x) (hφ : ContDiffAt ℝ 2 φ (f x))
    (hcrit : IsCriticalPointAt I f x) (hd : 0 < deriv φ (f x)) :
    _root_.sigNeg (chartHessianAt (fun z => φ (f ((extChartAt I x).symm z)))
      (extChartAt I x x)) =
      _root_.sigNeg (chartHessianAt (fun z => f ((extChartAt I x).symm z))
        (extChartAt I x x)) := by
  rw [chartHessianAt_scalar_comp hf hφ hcrit]
  exact (QuadraticForm.equivalent_smul_of_pos _ hd).sigNeg_eq

end DifferentialGeometry.Topology.Morse
