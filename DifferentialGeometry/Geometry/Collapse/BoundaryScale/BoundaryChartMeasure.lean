import DifferentialGeometry.Geometry.Metric.EuclideanChart
import DifferentialGeometry.Analysis.Integration.Measure.Chart.HaarBasis
import DifferentialGeometry.Analysis.Integration.Measure.Chart.MeasureComparison

/-!
# Haar normalization in an actual metric chart

The metric-normalized chart sends its centre density times model Haar measure to
Euclidean volume. The identity uses the actual tangent metric and its chart basis.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set DifferentialGeometry
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff ENNReal InnerProductSpace

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem metricChartEuclideanEquiv_inner (g : SmoothRiemannianMetric I M) (p : M)
    (v w : E) :
    ⟪metricChartEuclideanEquiv g p v, metricChartEuclideanEquiv g p w⟫_ℝ =
      g.inner p ((trivializationAt E (TangentSpace I) p).symmL ℝ p v)
        ((trivializationAt E (TangentSpace I) p).symmL ℝ p w) := by
  have hf (z : E) : metricEuclideanFrame g p (metricChartEuclideanEquiv g p z) =
      (trivializationAt E (TangentSpace I) p).symmL ℝ p z := by
    rw [metricChartEuclideanEquiv, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.apply_symm_apply]
    exact congrFun ((trivializationAt E (TangentSpace I) p).symm_continuousLinearEquivAt_eq
      (R := ℝ) (FiberBundle.mem_baseSet_trivializationAt' p)) z
  rw [← metricEuclideanFrame_inner g p, hf, hf]

theorem map_metricChartEuclideanEquiv_density_haar
    (g : SmoothRiemannianMetric I M) (p : M) :
    Measure.map (metricChartEuclideanEquiv g p)
      (ENNReal.ofReal (chartDensity g p p) • modelHaar (E := E)) =
        (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
  classical
  let A := metricChartEuclideanEquiv g p
  let b := chartModelBasis E
  let c := b.map A.toLinearEquiv
  let e := (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis
  let B := (innerSL ℝ (E := EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toBilinForm
  have hc : LinearMap.BilinForm.toMatrix c B = chartGramMatrix g p p := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    simp only [c, Module.Basis.map_apply, B, ContinuousLinearMap.toBilinForm_apply]
    change ⟪A (b i), A (b j)⟫_ℝ = _
    rw [metricChartEuclideanEquiv_inner]
    rfl
  have he : LinearMap.BilinForm.toMatrix e B = 1 := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    simp only [B, ContinuousLinearMap.toBilinForm_apply]
    rw [innerSL_apply_apply]
    exact (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).inner_eq_ite i j
  rw [Measure.map_smul _ (metricChartEuclideanEquiv g p).continuous.measurable.aemeasurable,
    show modelHaar (E := E) = b.addHaar from rfl,
    Module.Basis.map_addHaar b A]
  have h := B.sqrt_det_smul_addHaar_eq c e
  rw [hc, he, Matrix.det_one, Real.sqrt_one, ENNReal.ofReal_one, one_smul,
    (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).addHaar_eq_volume] at h
  exact h

theorem volume_inverseChart_compact_image [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (p : M) {S : Set E}
    (hS : IsCompact S) (hSt : S ⊆ (extChartAt I p).target) :
    riemannianVolumeMeasure (I := I) (M := M) g ((extChartAt I p).symm '' S) =
      ∫⁻ y in S, ENNReal.ofReal (chartDensity g p ((extChartAt I p).symm y))
        ∂modelHaar (E := E) := by
  classical
  let e := extChartAt I p
  let A := e.symm '' S
  have hAs : A ⊆ (chartAt H p).source := by
    rintro x ⟨y, hy, rfl⟩
    have hh : e.symm y ∈ (extChartAt I p).source := e.map_target (hSt hy)
    rw [extChartAt_source] at hh
    exact hh
  have hA : MeasurableSet A :=
    (hS.image_of_continuousOn ((continuousOn_extChartAt_symm p).mono hSt)).measurableSet
  have hvol : riemannianVolumeMeasure (I := I) (M := M) g A = chartLocalMeasure g p A := by
    have h := congrArg (fun μ : Measure M => μ A)
      (DifferentialGeometry.Analysis.Sobolev.Chart.volume_restrict_eq g p)
    simpa only [Measure.restrict_apply hA, inter_eq_left.mpr hAs] using h
  rw [hvol, ← lintegral_indicator_one hA]
  change (∫⁻ x, A.indicator (fun x : M => (1 : ℝ≥0∞)) x ∂chartLocalMeasure g p) = _
  rw [chartLocalMeasure_lintegral g p (measurable_const.indicator hA)]
  calc
    _ = ∫⁻ y in (extChartAt I p).target,
        S.indicator (fun y => ENNReal.ofReal (chartDensity g p (e.symm y))) y
          ∂modelHaar (E := E) := by
      apply setLIntegral_congr_fun (measurableSet_extChartAt_target (I := I) p)
      intro y hy
      have hiff : e.symm y ∈ A ↔ y ∈ S := by
        constructor
        · rintro ⟨z, hz, heq⟩
          have hh := congrArg e heq
          rw [e.right_inv (hSt hz), e.right_inv hy] at hh
          exact hh ▸ hz
        · intro hz
          exact ⟨y, hz, rfl⟩
      change ENNReal.ofReal (chartDensity g p (e.symm y)) *
        A.indicator (fun x : M => (1 : ℝ≥0∞)) (e.symm y) =
          S.indicator (fun y => ENNReal.ofReal (chartDensity g p (e.symm y))) y
      by_cases hyS : y ∈ S
      · simp only [Set.indicator_of_mem hyS, Set.indicator_of_mem (hiff.mpr hyS), mul_one]
      · simp only [Set.indicator_of_notMem hyS,
          Set.indicator_of_notMem (fun h => hyS (hiff.mp h)), mul_zero]
    _ = _ := by
      rw [setLIntegral_indicator hS.measurableSet, inter_eq_left.mpr hSt]

end DifferentialGeometry.Geometry.Metric
