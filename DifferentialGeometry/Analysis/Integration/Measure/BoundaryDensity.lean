import DifferentialGeometry.Analysis.Integration.Measure.Chart.HaarBasis
import DifferentialGeometry.Analysis.Integration.Measure.ModelHaar
import DifferentialGeometry.Geometry.Boundary.Metric.GramMatrix
import DifferentialGeometry.Geometry.Boundary.Model.EuclideanHalfSpace
import DifferentialGeometry.Geometry.Boundary.EuclideanHalfSpaceOrientation

open MeasureTheory

open Bundle Manifold
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff

namespace DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

open DifferentialGeometry.Integral.Measure

section

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

end

section

private local instance euclideanMeasurableSpace (i : Type*) :
    MeasurableSpace (EuclideanSpace Real i) := borel _
private local instance euclideanBorelSpace (i : Type*) :
    BorelSpace (EuclideanSpace Real i) := ⟨rfl⟩

variable {n : Nat} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) ∞ M]

local notation "J" => modelWithCornersEuclideanHalfSpace (n + 1)
local notation "K" => HasSmoothBoundary.boundaryModel J
local notation "EB" => HasSmoothBoundary.boundaryModelE J

theorem modelHaarScalarFactor_mul_chartDensity_chart_euclideanHalfSpace_eq_normal_mul_induced
    (g : SmoothRiemannianMetric J M) (alpha x : BoundaryManifold J M)
    (hx : (x : M) ∈ (chartAt (EuclideanHalfSpace (n + 1)) (alpha : M)).source) :
    (MeasureTheory.Measure.addHaarScalarFactor
        (modelHaar (E := EuclideanSpace Real (Fin (n + 1)))) volume : Real) *
        chartDensity g (alpha : M) (x : M) =
      Real.sqrt (g.inner (x : M) (outwardDirAt (M := M) g alpha x)
        (outwardDirAt (M := M) g alpha x)) *
        ((MeasureTheory.Measure.addHaarScalarFactor
          (modelHaar (E := EuclideanSpace Real (Fin n))) volume : Real) *
          chartDensity (inducedMetric g) alpha x) := by
  let : IsManifold K ∞ (BoundaryManifold J M) := BoundaryManifold.isManifold
  have hnonneg : 0 ≤ g.inner (x : M) (outwardDirAt (M := M) g alpha x)
      (outwardDirAt (M := M) g alpha x) := by
    by_cases h : outwardDirAt (M := M) g alpha x = 0
    · rw [h, map_zero]
    · exact (g.pos (x : M) _ h).le
  have ha := modelHaarScalarFactor_mul_chartDensity g (alpha : M) (x : M)
    (EuclideanSpace.basisFun (Fin (n + 1)) Real)
  have hb := modelHaarScalarFactor_mul_chartDensity (inducedMetric g) alpha x
    (EuclideanSpace.basisFun (Fin n) Real)
  simp only [EuclideanSpace.basisFun_apply] at ha hb
  rw [ha, hb, det_gram_chart_euclideanHalfSpace_eq_normal_sq_mul_det_induced g alpha x hx,
    Real.sqrt_mul hnonneg]
  congr 3
  ext i j
  simp only [Matrix.of_apply]
  congr 2
  · exact congrArg ((trivializationAt EB (TangentSpace K) alpha).symmL Real x)
      (EuclideanSpace.basisFun_apply (Fin n) Real i).symm
  · exact (EuclideanSpace.basisFun_apply (Fin n) Real j).symm

theorem modelHaarScalarFactor_mul_inducedDensity_mul_outwardNormal_inner_chart_euclideanHalfSpace
    (g : SmoothRiemannianMetric J M) (alpha x : BoundaryManifold J M)
    (hx : (x : M) ∈ (chartAt (EuclideanHalfSpace (n + 1)) (alpha : M)).source)
    (v : TangentSpace J (x : M)) :
    ((MeasureTheory.Measure.addHaarScalarFactor
        (modelHaar (E := EuclideanSpace Real (Fin n))) volume : Real) *
        chartDensity (inducedMetric g) alpha x) *
        g.inner (x : M) (outwardNormal (M := M) g x) v =
      -(((MeasureTheory.Measure.addHaarScalarFactor
          (modelHaar (E := EuclideanSpace Real (Fin (n + 1)))) volume : Real) *
          chartDensity g (alpha : M) (x : M)) *
        ((trivializationAt (EuclideanSpace Real (Fin (n + 1))) (TangentSpace J)
          (alpha : M)).continuousLinearMapAt Real (x : M) v) 0) := by
  rw [modelHaarScalarFactor_mul_chartDensity_chart_euclideanHalfSpace_eq_normal_mul_induced g alpha x hx,
    outwardNormal_inner_chart_euclideanHalfSpace_eq_neg_sqrt_mul_head g alpha x hx]
  ring

theorem modelHaarScalarFactor_mul_chartDensity_euclideanHalfSpace_eq_normal_mul_induced
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace (n + 1)) M)
    (x : BoundaryManifold (modelWithCornersEuclideanHalfSpace (n + 1)) M) :
    (MeasureTheory.Measure.addHaarScalarFactor
        (modelHaar (E := EuclideanSpace Real (Fin (n + 1)))) volume : Real) *
        chartDensity g (x : M) (x : M) =
      Real.sqrt (g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x)) *
        ((MeasureTheory.Measure.addHaarScalarFactor
          (modelHaar (E := EuclideanSpace Real (Fin n))) volume : Real) *
          chartDensity (inducedMetric g) x x) := by
  simpa only [outwardDirAt_self] using
    modelHaarScalarFactor_mul_chartDensity_chart_euclideanHalfSpace_eq_normal_mul_induced
      g x x (mem_chart_source _ _)

theorem modelHaarScalarFactor_mul_inducedDensity_mul_outwardNormal_inner_euclideanHalfSpace
    (g : SmoothRiemannianMetric (modelWithCornersEuclideanHalfSpace (n + 1)) M)
    (x : BoundaryManifold (modelWithCornersEuclideanHalfSpace (n + 1)) M)
    (v : TangentSpace (modelWithCornersEuclideanHalfSpace (n + 1)) (x : M)) :
    ((MeasureTheory.Measure.addHaarScalarFactor
        (modelHaar (E := EuclideanSpace Real (Fin n))) volume : Real) *
        chartDensity (inducedMetric g) x x) *
        g.inner (x : M) (outwardNormal (M := M) g x) v =
      -(((MeasureTheory.Measure.addHaarScalarFactor
          (modelHaar (E := EuclideanSpace Real (Fin (n + 1)))) volume : Real) *
          chartDensity g (x : M) (x : M)) *
        (tangentSpaceModelContinuousLinearEquiv
          (I := modelWithCornersEuclideanHalfSpace (n + 1)) (x : M) v) 0) := by
  have h := modelHaarScalarFactor_mul_inducedDensity_mul_outwardNormal_inner_chart_euclideanHalfSpace
    g x x (mem_chart_source _ _) v
  have hchart : (trivializationAt (EuclideanSpace Real (Fin (n + 1)))
      (TangentSpace J) (x : M)).continuousLinearMapAt Real (x : M) v =
      tangentSpaceModelContinuousLinearEquiv (I := J) (x : M) v := by
    rw [TangentBundle.continuousLinearMapAt_trivializationAt (mem_chart_source _ _),
      mfderiv_extChartAt_self]
    rfl
  rw [hchart] at h
  exact h

end

end DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
