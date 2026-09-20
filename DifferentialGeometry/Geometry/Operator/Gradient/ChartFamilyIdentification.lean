import DifferentialGeometry.Geometry.Operator.Gradient.ChartPairing
import DifferentialGeometry.Analysis.Calculus.Derivative.LocallyLipschitz


noncomputable section

namespace DifferentialGeometry.Geometry.Operator

open Filter MeasureTheory Set
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.DivergenceTheorem
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {μ : Measure ℝ} [Measure.IsAddHaarMeasure μ]
  {ν : Measure E} [Measure.IsAddHaarMeasure ν]

theorem ae_chartGradientBilin_fderiv_eq_inner_gradientFun_family
    (g : ℝ → SmoothRiemannianMetric I M) (α : M)
    {f : ℝ → M → ℝ} {h : ℝ → M → ℝ} {S : Set ℝ} {W : Set E}
    (hS : IsOpen S) (hW : IsOpen W) (hWt : W ⊆ (extChartAt I α).target)
    (hf : LocallyLipschitzOn (S ×ˢ W)
      (fun z : ℝ × E => f z.1 ((extChartAt I α).symm z.2)))
    (hh : LocallyLipschitzOn (S ×ˢ W)
      (fun z : ℝ × E => h z.1 ((extChartAt I α).symm z.2))) :
    ∀ᵐ z ∂μ.prod ν, z ∈ S ×ˢ W →
      chartGradientBilin (g z.1) α ((extChartAt I α).symm z.2)
        (fderiv ℝ (fun y : E => f z.1 ((extChartAt I α).symm y)) z.2)
        (fderiv ℝ (fun y : E => h z.1 ((extChartAt I α).symm y)) z.2) =
      (g z.1).inner ((extChartAt I α).symm z.2)
        (gradientFun (g z.1) (f z.1) ((extChartAt I α).symm z.2))
        (gradientFun (g z.1) (h z.1) ((extChartAt I α).symm z.2)) := by
  have hdiff := hf.ae_differentiableAt_of_isOpen (μ := μ.prod ν) (hS.prod hW)
  have htest := hh.ae_differentiableAt_of_isOpen (μ := μ.prod ν) (hS.prod hW)
  filter_upwards [hdiff, htest] with z hfz hhz hz
  have hzt : z.2 ∈ (extChartAt I α).target := hWt hz.2
  have hzs : (extChartAt I α).symm z.2 ∈ (chartAt H α).source := by
    simpa only [extChartAt_source] using (extChartAt I α).map_target hzt
  have hd : DifferentiableAt ℝ
      (fun v : ℝ × E => f v.1 ((extChartAt I α).symm v.2)) z := hfz hz
  have hfspatial := hd.comp z.2
    (show DifferentiableAt ℝ (fun y : E => (z.1, y)) z.2 from
      (differentiableAt_const z.1).prodMk differentiableAt_id)
  have hfm : MDifferentiableAt I 𝓘(ℝ, ℝ) (f z.1) ((extChartAt I α).symm z.2) := by
    rw [mdifferentiableAt_iff_source_of_mem_source hzs,
      mdifferentiableWithinAt_iff_differentiableWithinAt, (extChartAt I α).right_inv hzt]
    exact hfspatial.differentiableWithinAt
  have hdψ : DifferentiableAt ℝ
      (fun v : ℝ × E => h v.1 ((extChartAt I α).symm v.2)) z := hhz hz
  have hψspatial := hdψ.comp z.2
    (show DifferentiableAt ℝ (fun y : E => (z.1, y)) z.2 from
      (differentiableAt_const z.1).prodMk differentiableAt_id)
  have hhm : MDifferentiableAt I 𝓘(ℝ, ℝ) (h z.1) ((extChartAt I α).symm z.2) := by
    rw [mdifferentiableAt_iff_source_of_mem_source hzs,
      mdifferentiableWithinAt_iff_differentiableWithinAt, (extChartAt I α).right_inv hzt]
    exact hψspatial.differentiableWithinAt
  have hid := (inner_gradientFun_eq_chartGradientBilin (g z.1) α hfm hhm hzs).symm
  rw [(extChartAt I α).right_inv hzt] at hid
  exact hid

end DifferentialGeometry.Geometry.Operator
