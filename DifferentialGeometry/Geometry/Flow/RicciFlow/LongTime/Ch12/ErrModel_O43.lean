import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HChart_O43
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PullbackModel_O43

/-!
# CH12-O43 G2b prep: chart model of the `ckErr_S45` error field in an atlas chart

For `y` in the chart target at `c` with `F (symm y)` in the chart source, the model
representative of the pullback-error field of `ckErr_S45 H H.metric 1 F` is
`pullbackErrorExpression_O43 H.metric H.metric c c (y, y + u y, D(ext ∘ F ∘ symm) y)`,
`u = chartDisplacement_CX3 c F`: the starting point of S80's `hmodel` (step (c)).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor.RSTensor DifferentialGeometry.TensorLieDeriv
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Manifold
open Bundle Set
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

theorem errModel_eq_O43 (H : FiniteVolumeHyperbolicModel.{u}) (c : H.Carrier)
    {F : H.Carrier → H.Carrier} {y : EuclideanSpace ℝ (Fin 3)}
    (hy : y ∈ (extChartAt (𝓡 3) c).target)
    (hF : MDifferentiableAt (𝓡 3) (𝓡 3) F ((extChartAt (𝓡 3) c).symm y))
    (hFy : F ((extChartAt (𝓡 3) c).symm y) ∈ (extChartAt (𝓡 3) c).source) :
    tensor0SModelInChart (I := 𝓡 3) 2 c (fun q : H.Carrier =>
        ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) q) ℝ).symm.toContinuousLinearMap.comp
          ((1 : ℝ) • localPullInner H.metric F q - H.metric.inner q)).uncurryLeft) y =
      pullbackErrorExpression_O43 H.metric H.metric c c
        (y, y + chartDisplacement_CX3 (I := 𝓡 3) c F y,
          fderiv ℝ (extChartAt (𝓡 3) c ∘ F ∘ (extChartAt (𝓡 3) c).symm) y) := by
  have hy' : y ∈ (interiorChart (𝓡 3) ∞ c).target := by
    rw [interiorChart_target, (isOpen_extChartAt_target c).interior_eq]
    exact hy
  have hFy' : F ((extChartAt (𝓡 3) c).symm y) ∈ (interiorChart (𝓡 3) ∞ c).source := by
    rw [interiorChart_source, (isOpen_extChartAt_target c).interior_eq]
    exact ⟨by rwa [extChartAt_source] at hFy, (extChartAt (𝓡 3) c).map_source hFy⟩
  have h := pullbackError_model_eq_O43 H.metric H.metric F c c hy' hF hFy'
  have hu : y + chartDisplacement_CX3 (I := 𝓡 3) c F y =
      (extChartAt (𝓡 3) c ∘ F ∘ (extChartAt (𝓡 3) c).symm) y := by
    simp only [chartDisplacement_CX3, Function.comp_apply]
    abel
  rw [hu, ← h]
  simp only [one_smul]

end GC.LongTime.Ch12
