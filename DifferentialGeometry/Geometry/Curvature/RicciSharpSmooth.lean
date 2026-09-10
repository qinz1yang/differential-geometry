import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.Ricci
import DifferentialGeometry.Geometry.Operator.Gradient.MetricSharpSmoothness
import DifferentialGeometry.Bundle.ContinuousLinearMapSection.Basic

noncomputable section
open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Integral.Measure

namespace Poincare.Geometry.Curvature

theorem ricciSharp_contMDiff
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [BoundarylessManifold I M] (g : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) x (ricciSharp g x)) := by
  apply DifferentialGeometry.contMDiff_continuousLinearMap_section_of_apply (φ := ricciSharp g)
  intro Y
  change ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
    (fun x : M ↦ TotalSpace.mk' E x (metricSharp g x (ricciTensor g x (Y x)).toLinearMap))
  apply metricSharp_contMDiff_total g
  intro α j
  have hb := DifferentialGeometry.Tensor.Coordinates.chartBasisVec_contMDiffOn (I := I) α j
  rw [TangentBundle.trivializationAt_baseSet] at hb
  have ht : ContMDiffOn I (I.prod 𝓘(ℝ)) ∞
      (fun x : M ↦ TotalSpace.mk' ℝ (E := fun _ : M ↦ ℝ) x
        (ricciTensor g x (Y x)
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j x)))
        (chartAt H α).source :=
    ContMDiffOn.clm_bundle_apply₂ (E₁ := TangentSpace I) (E₂ := TangentSpace I)
      (E₃ := fun _ : M ↦ ℝ) (b := id) (ψ := ricciTensor g)
      (v := fun x ↦ Y x)
      (w := DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j)
      (ricciTensor_contMDiff g).contMDiffOn Y.contMDiff.contMDiffOn hb
  intro x hx
  exact (contMDiffWithinAt_totalSpace.mp (ht x hx)).2

end Poincare.Geometry.Curvature
