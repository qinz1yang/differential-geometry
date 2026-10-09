import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OpenCoreGeometry

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u v

/-- The unscaled pullback has curvature `-1/4`, is complete, and has exactly
the volume of the original model. This is the metric before the Thurston
structure's conventional rescaling to curvature `-1`. -/
theorem hyperbolicMetric_pullback_CX1 (H : FiniteVolumeHyperbolicModel.{u})
    {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [SigmaCompactSpace M]
    (D : Diffeomorph (𝓡 3) (𝓡 3) M H.Carrier ∞) :
    let g := Diffeomorph.pullbackMetricCross H.metric D
    hasConstantSectionalCurvature g (-(1 / 4 : ℝ)) ∧
      RiemannianMetricComplete g ∧
      Integral.Measure.riemannianVolumeMeasure (𝓡 3) M g univ =
        Integral.Measure.riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric univ ∧
      Integral.Measure.riemannianVolumeMeasure (𝓡 3) M g univ < ⊤ := by
  dsimp only
  have hvol : Integral.Measure.riemannianVolumeMeasure (𝓡 3) M
      (Diffeomorph.pullbackMetricCross H.metric D) univ =
      Integral.Measure.riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric univ := by
    let : MeasurableSpace M := borel M
    let : MeasurableSpace H.Carrier := borel H.Carrier
    let : BorelSpace M := ⟨rfl⟩
    let : BorelSpace H.Carrier := ⟨rfl⟩
    rw [Integral.Measure.riemannianVolumeMeasure_pullback_cross,
      MeasureTheory.Measure.map_apply D.symm.continuous.measurable MeasurableSet.univ]
    rfl
  refine ⟨?_, DifferentialGeometry.Geometry.Metric.riemannianMetricComplete_pullbackMetricCross
    H.complete D, hvol, hvol.symm ▸ H.finite_volume⟩
  intro p v w hvw
  rw [Diffeomorph.pullbackMetricCross_eq_pullbackMetric,
    DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_pullback]
  apply H.curvature
  let A := D.mfderivToContinuousLinearEquiv (by decide) p
  have hm := hvw.map' A.toLinearMap (LinearMap.ker_eq_bot.mpr A.injective)
  convert hm using 1
  ext j
  fin_cases j <;> rfl

end GC.LongTime.Ch12
