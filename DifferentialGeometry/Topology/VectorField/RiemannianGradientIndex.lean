import DifferentialGeometry.Topology.VectorField.RiemannianGradientLinearization
import DifferentialGeometry.Topology.VectorField.GradientLinearization
import DifferentialGeometry.Tensor.QuadraticForm.MetricSignature
import DifferentialGeometry.Topology.VectorField.InteriorIndexLinearization

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Filter InnerProductSpace
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Geometry.Operator
  DifferentialGeometry.Tensor.Coordinates
namespace Poincare.VectorField
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]


theorem rieszFlat_comp_fderiv_gradientInChart
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : M}
    (hx : I.IsInteriorPoint x) (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f x)
    (hcrit : mfderiv I 𝓘(ℝ, ℝ) f x = 0) :
    Poincare.QuadraticForm.rieszFlat (metricFlatContinuousEquiv g x).toContinuousLinearMap ∘L
        fderiv ℝ (gradientInChart g f x) (extChartAt I x x) =
      fderiv ℝ (gradient (fun z => f ((extChartAt I x).symm z))) (extChartAt I x x) := by
  rw [fderiv_gradient ((contDiffAt_scalarInChart hx hf).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))]
  exact congrArg
    (fun L => (toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L L)
    (metricFlat_comp_fderiv_gradientInChart g hx hf hcrit)


theorem det_fderiv_gradientInChart_ne_zero
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : M}
    (hx : I.IsInteriorPoint x) (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f x)
    (hcrit : mfderiv I 𝓘(ℝ, ℝ) f x = 0)
    (hnd : (QuadraticMap.associated
      (DifferentialGeometry.Topology.Morse.chartHessianAt
        (fun z => f ((extChartAt I x).symm z)) (extChartAt I x x))).SeparatingLeft) :
    LinearMap.det (fderiv ℝ (gradientInChart g f x) (extChartAt I x x)).toLinearMap ≠ 0 := by
  have hS := det_fderiv_gradient_ne_zero
    ((contDiffAt_scalarInChart hx hf).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) hnd
  rw [← rieszFlat_comp_fderiv_gradientInChart g hx hf hcrit] at hS
  intro h
  apply hS
  change LinearMap.det
    ((Poincare.QuadraticForm.rieszFlat (metricFlatContinuousEquiv g x).toContinuousLinearMap).toLinearMap.comp
      (fderiv ℝ (gradientInChart g f x) (extChartAt I x x)).toLinearMap) = 0
  rw [LinearMap.det_comp, h, mul_zero]


theorem sign_det_fderiv_gradientInChart
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : M}
    (hx : I.IsInteriorPoint x) (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f x)
    (hcrit : mfderiv I 𝓘(ℝ, ℝ) f x = 0)
    (hnd : (QuadraticMap.associated
      (DifferentialGeometry.Topology.Morse.chartHessianAt
        (fun z => f ((extChartAt I x).symm z)) (extChartAt I x x))).SeparatingLeft) :
    (SignType.sign (LinearMap.det
      (fderiv ℝ (gradientInChart g f x) (extChartAt I x x)).toLinearMap) : ℤ) =
      (-1 : ℤ) ^ sigNeg (DifferentialGeometry.Topology.Morse.chartHessianAt
        (fun z => f ((extChartAt I x).symm z)) (extChartAt I x x)) := by
  have hb : ∀ v w : E, metricFlatContinuousEquiv g x v w = metricFlatContinuousEquiv g x w v := by
    intro v w
    erw [metricFlatContinuousEquiv_apply_self, metricFlatContinuousEquiv_apply_self]
    exact g.symm x v w
  have hp : ∀ v : E, v ≠ 0 → 0 < metricFlatContinuousEquiv g x v v := by
    intro v hv
    erw [metricFlatContinuousEquiv_apply_self]
    exact g.pos x v hv
  have hs := Poincare.QuadraticForm.sign_det_rieszFlat_comp
    (metricFlatContinuousEquiv g x).toContinuousLinearMap hb hp
    (fderiv ℝ (gradientInChart g f x) (extChartAt I x x))
  rw [rieszFlat_comp_fderiv_gradientInChart g hx hf hcrit] at hs
  exact hs.symm.trans (sign_det_fderiv_gradient
    ((contDiffAt_scalarInChart hx hf).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) hnd)

end Poincare.VectorField

namespace Poincare.VectorField
variable {d : ℕ} {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (d + 1))) H)
  [IsManifold I ∞ M]


theorem hasContinuousIsolatedZero_gradientFun_of_hessian_nondegenerate
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : M}
    (hx : I.IsInteriorPoint x) (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f x)
    (hcrit : mfderiv I 𝓘(ℝ, ℝ) f x = 0)
    (hnd : (QuadraticMap.associated
      (DifferentialGeometry.Topology.Morse.chartHessianAt
        (fun z => f ((extChartAt I x).symm z)) (extChartAt I x x))).SeparatingLeft) :
    HasContinuousIsolatedZero I (gradientFun g f) x := by
  have hC : ContMDiffAt I I.tangent 1
      (fun y => (⟨y, gradientFun g f y⟩ : TangentBundle I M)) x :=
    (gradientFun_contMDiffAt g hf).of_le (by simp)
  apply hasContinuousIsolatedZero_of_isInteriorPoint_contMDiffAt_det_ne_zero I hx hC
    (gradientFun_eq_zero_of_mfderiv_eq_zero g f hcrit)
  erw [linearizationAtZero_eq_fderivWithin,
    fderivWithin_of_mem_nhds (range_mem_nhds_isInteriorPoint hx)]
  exact det_fderiv_gradientInChart_ne_zero g hx hf hcrit hnd


theorem interiorIndex_gradientFun_eq_neg_one_pow_sigNeg
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : M}
    (hx : I.IsInteriorPoint x) (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f x)
    (hnd : (QuadraticMap.associated
      (DifferentialGeometry.Topology.Morse.chartHessianAt
        (fun z => f ((extChartAt I x).symm z)) (extChartAt I x x))).SeparatingLeft)
    (hV : HasContinuousIsolatedZero I (gradientFun g f) x) :
    interiorIndex I (gradientFun g f) x hV hx =
      (-1 : ℤ) ^ sigNeg (DifferentialGeometry.Topology.Morse.chartHessianAt
        (fun z => f ((extChartAt I x).symm z)) (extChartAt I x x)) := by
  have hcrit : mfderiv I 𝓘(ℝ, ℝ) f x = 0 := by
    ext v
    have hh := inner_gradientFun g f x v
    rw [hV.zero, map_zero, zero_apply] at hh
    exact hh.symm
  have hd := (gradientFun_contMDiffAt g hf).mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hdet : LinearMap.det (linearizationAtZero hd hV.zero).toLinearMap ≠ 0 := by
    erw [linearizationAtZero_gradientFun_eq_fderivInChart g hx hf hcrit]
    exact det_fderiv_gradientInChart_ne_zero g hx hf hcrit hnd
  rw [interiorIndex_eq_sign_det_linearizationAtZero I hx hV hd hdet]
  erw [linearizationAtZero_gradientFun_eq_fderivInChart g hx hf hcrit]
  exact sign_det_fderiv_gradientInChart g hx hf hcrit hnd


theorem exists_interiorIndex_gradientFun_eq_neg_one_pow_sigNeg
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : M}
    (hx : I.IsInteriorPoint x) (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f x)
    (hcrit : mfderiv I 𝓘(ℝ, ℝ) f x = 0)
    (hnd : (QuadraticMap.associated
      (DifferentialGeometry.Topology.Morse.chartHessianAt
        (fun z => f ((extChartAt I x).symm z)) (extChartAt I x x))).SeparatingLeft) :
    ∃ hV : HasContinuousIsolatedZero I (gradientFun g f) x,
      interiorIndex I (gradientFun g f) x hV hx =
        (-1 : ℤ) ^ sigNeg (DifferentialGeometry.Topology.Morse.chartHessianAt
          (fun z => f ((extChartAt I x).symm z)) (extChartAt I x x)) :=
  ⟨hasContinuousIsolatedZero_gradientFun_of_hessian_nondegenerate I g hx hf hcrit hnd,
    interiorIndex_gradientFun_eq_neg_one_pow_sigNeg I g hx hf hnd _⟩

end Poincare.VectorField

namespace Poincare.VectorField

theorem exists_interiorIndex_gradientFun_of_isNondegenerateCriticalPointAt
    {d : ℕ} {H M : Type} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (d + 1))) H) [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : M}
    (hx : I.IsInteriorPoint x) (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f x)
    (hcrit : DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt I f x) :
    ∃ hV : HasContinuousIsolatedZero I (gradientFun g f) x,
      interiorIndex I (gradientFun g f) x hV hx =
        (-1 : ℤ) ^ sigNeg (DifferentialGeometry.Topology.Morse.chartHessianAt
          (fun z => f ((extChartAt I x).symm z)) (extChartAt I x x)) :=
  exists_interiorIndex_gradientFun_eq_neg_one_pow_sigNeg I g hx hf hcrit.1 hcrit.2
end Poincare.VectorField
