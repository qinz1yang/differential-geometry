import DifferentialGeometry.Geometry.Metric.Approximation.RiemannianHausdorffVolume
import DifferentialGeometry.Analysis.Integration.Measure.CubeMeasureBound

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Riemannian

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [MeasurableSpace M] [BorelSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- LC14 with its exact constant, for an ambient map restricted to an arbitrary set. -/
theorem volume_lower_of_local_image_cube
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hdim : Module.finrank ℝ E = 3) {U : Set M}
    {f : M → EuclideanSpace ℝ (Fin 3)}
    (hf : LipschitzOnWith (NNReal.sqrt 3) f U)
    {v : EuclideanSpace ℝ (Fin 3)} {e : ℝ} (he : 0 < e)
    (himage : {w : EuclideanSpace ℝ (Fin 3) | ∀ j, |w j - v j| ≤ e / 4} ⊆ f '' U) :
    ENNReal.ofReal ((e / 2) ^ 3 / (3 * Real.sqrt 3)) ≤
      DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g U ∧
      0 < (e / 2) ^ 3 / (3 * Real.sqrt 3) := by
  have h := cube_le_normalizedHausdorffMeasure_three hf he himage
  rw [normalizedHausdorffMeasure_three_apply_eq_riemannianVolumeMeasure_apply
    g hEnorm hdim U] at h
  exact h

/-- LC14 for the literal restricted ambient metric on `U`; no extension of `f` is assumed. -/
theorem volume_lower_of_subtype_image_cube
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hdim : Module.finrank ℝ E = 3) {U : Set M}
    {f : U → EuclideanSpace ℝ (Fin 3)} (hf : LipschitzWith (NNReal.sqrt 3) f)
    {v : EuclideanSpace ℝ (Fin 3)} {e : ℝ} (he : 0 < e)
    (himage : {w : EuclideanSpace ℝ (Fin 3) | ∀ j, |w j - v j| ≤ e / 4} ⊆ range f) :
    ENNReal.ofReal ((e / 2) ^ 3 / (3 * Real.sqrt 3)) ≤
      DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g U ∧
      0 < (e / 2) ^ 3 / (3 * Real.sqrt 3) := by
  have h := cube_le_normalizedHausdorffMeasure_three hf.lipschitzOnWith he
    (s := univ) (by simpa only [image_univ] using himage)
  have hsub : normalizedHausdorffMeasure 3 U =
      normalizedHausdorffMeasure 3 (univ : Set U) := by
    have hiso := (isometry_subtype_coe (s := U)).hausdorffMeasure_image
      (Or.inl (by norm_num : (0 : ℝ) ≤ 3)) (univ : Set U)
    simp only [image_univ, Subtype.range_coe] at hiso
    simp only [normalizedHausdorffMeasure, Measure.smul_apply]
    norm_num only [Nat.cast_ofNat]
    rw [hiso]
  rw [← hsub, normalizedHausdorffMeasure_three_apply_eq_riemannianVolumeMeasure_apply
    g hEnorm hdim U] at h
  exact h

end DifferentialGeometry.Geometry.Collapse
