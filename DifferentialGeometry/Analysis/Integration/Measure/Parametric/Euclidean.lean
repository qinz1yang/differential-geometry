import DifferentialGeometry.Analysis.Integration.Measure.Parametric.AreaFormula
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Euclidean
import DifferentialGeometry.Geometry.Coordinates.Frame.Chart

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Integral.Measure

open MeasureTheory Set Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

theorem riemannianVolumeMeasure_euclideanMetric_image_eq
    (Ψ : E → E) {U K : Set E} (hU : IsOpen U) (hK : MeasurableSet K) (hKU : K ⊆ U)
    (hΨ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) 1 Ψ U) (hinj : Set.InjOn Ψ K) :
    riemannianVolumeMeasure (I := 𝓘(ℝ, E)) (M := E) (euclideanMetric (E := E)) (Ψ '' K) =
      ∫⁻ x in K, ENNReal.ofReal |(fderiv ℝ Ψ x).det| ∂(volume : Measure E) := by
  set B : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ := Matrix.of fun i j =>
    inner ℝ (Tensor.Coordinates.chartModelBasis E i) (Tensor.Coordinates.chartModelBasis E j)
  have hvol : (volume : Measure E) = ENNReal.ofReal (Real.sqrt B.det) • modelHaar (E := E) := by
    have h := addHaar_withDensity_sqrt_det_gramMatrix_eq_volume
      (Tensor.Coordinates.chartModelBasis E)
    rw [← h, modelHaar, withDensity_const]
  have hpoint : ∀ x ∈ K,
      paramDensity (I := 𝓘(ℝ, E)) (euclideanMetric (E := E)) Ψ x =
        Real.sqrt B.det * |(fderiv ℝ Ψ x).det| := by
    intro x hx
    have hxU : x ∈ U := hKU hx
    have hmd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) Ψ x :=
      (hΨ.mdifferentiableOn (by norm_num)).mdifferentiableAt (hU.mem_nhds hxU)
    have hbase : Ψ x ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (Ψ x)).baseSet := by
      rw [DifferentialGeometry.Tensor.Coordinates.trivializationAt_baseSet_eq_chartAt_source]
      exact mem_chart_source E (Ψ x)
    have h1 := paramDensity_eq_abs_det_mul_chartDensity_of_mdifferentiableAt
      (I := 𝓘(ℝ, E)) (M := E) (euclideanMetric (E := E)) Ψ hmd (Ψ x) hbase
    rw [h1, chartDensity_euclideanMetric]
    have hchart : (fun z : E => extChartAt 𝓘(ℝ, E) (Ψ x) (Ψ z)) = Ψ := by
      funext z
      rw [extChartAt_modelWithCornersSelf]
      rfl
    rw [hchart, mul_comm]
  rw [riemannianVolumeMeasure_image_eq (I := 𝓘(ℝ, E)) (M := E)
    (euclideanMetric (E := E)) hU hK hKU hΨ hinj]
  calc ∫⁻ x in K, ENNReal.ofReal (paramDensity (I := 𝓘(ℝ, E))
        (euclideanMetric (E := E)) Ψ x) ∂modelHaar (E := E)
      = ∫⁻ x in K, ENNReal.ofReal (Real.sqrt B.det * |(fderiv ℝ Ψ x).det|)
          ∂modelHaar (E := E) := by
        refine setLIntegral_congr_fun hK fun x hx => ?_
        rw [hpoint x hx]
    _ = ∫⁻ x in K, ENNReal.ofReal (Real.sqrt B.det) *
          ENNReal.ofReal |(fderiv ℝ Ψ x).det| ∂modelHaar (E := E) := by
        refine setLIntegral_congr_fun hK fun x hx => ?_
        rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    _ = ENNReal.ofReal (Real.sqrt B.det) *
          ∫⁻ x in K, ENNReal.ofReal |(fderiv ℝ Ψ x).det| ∂modelHaar (E := E) := by
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ∫⁻ x in K, ENNReal.ofReal |(fderiv ℝ Ψ x).det| ∂(volume : Measure E) := by
        rw [hvol, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]

end DifferentialGeometry.Integral.Measure
