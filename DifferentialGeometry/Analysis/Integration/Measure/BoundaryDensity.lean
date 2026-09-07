import DifferentialGeometry.Analysis.Integration.Measure.BasisHaar
import DifferentialGeometry.Geometry.Boundary.BoundaryGramMatrix

open MeasureTheory

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

private noncomputable def boundaryChartBilinForm
    (g : SmoothRiemannianMetric I M) (alpha x : BoundaryManifold I M) :
    LinearMap.BilinForm Real hI.boundaryE :=
  (inducedMetricInner g x).toBilinForm.comp
    ((trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) alpha).symmL Real x).toLinearMap
    ((trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) alpha).symmL Real x).toLinearMap

private theorem boundaryChartBilinForm_toMatrix_chartModelBasis
    (g : SmoothRiemannianMetric I M) (alpha x : BoundaryManifold I M) :
    LinearMap.BilinForm.toMatrix (chartModelBasis hI.boundaryE) (boundaryChartBilinForm g alpha x) =
      chartGramMatrix (inducedMetric g) alpha x := by
  ext i j
  rw [LinearMap.BilinForm.toMatrix_apply, chartGramMatrix_apply]
  rfl

private theorem boundaryChartBilinForm_toMatrix_finBasis
    (g : SmoothRiemannianMetric I M) (alpha x : BoundaryManifold I M)
    (hx : x ∈ (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) alpha).baseSet) :
    LinearMap.BilinForm.toMatrix (Module.finBasis Real hI.boundaryE)
        (boundaryChartBilinForm g alpha x) = boundaryGramMatrix g alpha x := by
  ext i j
  rw [LinearMap.BilinForm.toMatrix_apply]
  change inducedMetricInner g x
      ((trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) alpha).symmL Real x
        (Module.finBasis Real hI.boundaryE i))
      ((trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) alpha).symmL Real x
        (Module.finBasis Real hI.boundaryE j)) = _
  simp only [Trivialization.symmL_apply _ hx, boundaryGramMatrix_apply,
    boundaryChartBasisVecFiber]

theorem chartDensity_inducedMetric_eq_abs_det_mul_sqrt_boundaryGramMatrix
    (g : SmoothRiemannianMetric I M) (alpha x : BoundaryManifold I M)
    (hx : x ∈ (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) alpha).baseSet) :
    chartDensity (inducedMetric g) alpha x =
      |(Module.finBasis Real hI.boundaryE).det (chartModelBasis hI.boundaryE)| *
        Real.sqrt (boundaryGramMatrix g alpha x).det := by
  have h := (boundaryChartBilinForm g alpha x).sqrt_det_toMatrix_basis_change
    (Module.finBasis Real hI.boundaryE) (chartModelBasis hI.boundaryE)
  rw [boundaryChartBilinForm_toMatrix_chartModelBasis,
    boundaryChartBilinForm_toMatrix_finBasis g alpha x hx] at h
  exact h

private local instance : MeasurableSpace hI.boundaryE := borel hI.boundaryE
private local instance : BorelSpace hI.boundaryE := ⟨rfl⟩

theorem chartDensity_inducedMetric_smul_modelHaar_eq_sqrt_boundaryGramMatrix_smul_addHaar
    (g : SmoothRiemannianMetric I M) (alpha x : BoundaryManifold I M)
    (hx : x ∈ (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) alpha).baseSet) :
    ENNReal.ofReal (chartDensity (inducedMetric g) alpha x) • modelHaar (E := hI.boundaryE) =
      ENNReal.ofReal (Real.sqrt (boundaryGramMatrix g alpha x).det) •
        (Module.finBasis Real hI.boundaryE).addHaar := by
  have h := (boundaryChartBilinForm g alpha x).sqrt_det_smul_addHaar_eq
    (chartModelBasis hI.boundaryE) (Module.finBasis Real hI.boundaryE)
  rw [boundaryChartBilinForm_toMatrix_chartModelBasis,
    boundaryChartBilinForm_toMatrix_finBasis g alpha x hx] at h
  exact h

private local instance : MeasurableSpace (BoundaryManifold I M) := borel (BoundaryManifold I M)
private local instance : BorelSpace (BoundaryManifold I M) := ⟨rfl⟩

theorem chartLocalMeasure_inducedMetric_eq_map_withDensity_boundaryGramMatrix
    (g : SmoothRiemannianMetric I M) (alpha : BoundaryManifold I M) :
    chartLocalMeasure (inducedMetric g) alpha =
      MeasureTheory.Measure.map (extChartAt hI.boundaryI alpha).symm
        (((Module.finBasis Real hI.boundaryE).addHaar.restrict
          (extChartAt hI.boundaryI alpha).target).withDensity
          (fun y => ENNReal.ofReal (Real.sqrt
            (boundaryGramMatrix g alpha ((extChartAt hI.boundaryI alpha).symm y)).det))) := by
  rw [chartLocalMeasure_def]
  congr 1
  rw [← (Module.finBasis Real hI.boundaryE).det_smul_addHaar (chartModelBasis hI.boundaryE),
    MeasureTheory.Measure.restrict_smul, MeasureTheory.withDensity_smul_measure,
    ← MeasureTheory.withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  apply MeasureTheory.withDensity_congr_ae
  filter_upwards [ae_restrict_mem (isOpen_extChartAt_target alpha).measurableSet] with y hy
  have hys : (extChartAt hI.boundaryI alpha).symm y ∈
      (trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) alpha).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    simpa only [extChartAt_source] using (extChartAt hI.boundaryI alpha).map_target hy
  rw [chartDensity_inducedMetric_eq_abs_det_mul_sqrt_boundaryGramMatrix g alpha _ hys,
    ENNReal.ofReal_mul (abs_nonneg _)]
  rfl

end DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

