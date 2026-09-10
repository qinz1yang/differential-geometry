import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CurvatureNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceEntropyMinimum

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open CanonicalNeighborhood
open scoped Manifold ContDiff ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)


def surfaceArea (g : SmoothRiemannianMetric I M) : ℝ :=
  (riemannianVolumeMeasure (I := I) (M := M) g).real Set.univ


def totalScalarCurvature (g : SmoothRiemannianMetric I M) : ℝ :=
  ∫ x, metricScalarAt (I := I) g x ∂(riemannianVolumeMeasure (I := I) (M := M) g)


def meanScalarCurvature (g : SmoothRiemannianMetric I M) : ℝ :=
  totalScalarCurvature g / surfaceArea g


def surfaceEntropy (g : SmoothRiemannianMetric I M) : ℝ :=
  ∫ x, metricScalarAt (I := I) g x *
    Real.log (metricScalarAt (I := I) g x * surfaceArea g)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)

omit [T2Space M] [CompactSpace M] in
theorem metricScalarAt_scaleMetric
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c) (x : M) :
    metricScalarAt (I := I) (scaleMetric c hc g) x = c⁻¹ * metricScalarAt (I := I) g x := by
  let S : SolutionOn (I := I) (M := M) ancientTimeInterval :=
    ⟨⟨fun _ => g⟩⟩
  have h := congrFun (congrFun (parabolicSolution_scalar (I := I) S 0 c hc
    (by change (0 : ℝ) ≤ 0; exact le_rfl)) 0) x
  change metricScalarAt (I := I) (scaleMetric c hc g) x =
    c⁻¹ * metricScalarAt (I := I) g x at h
  exact h

omit [CompleteSpace E] in
theorem surfaceVolume_scaleMetric
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 2)
    (c : ℝ) (hc : 0 < c) :
    riemannianVolumeMeasure (I := I) (M := M) (scaleMetric c hc g) =
      ENNReal.ofReal c • riemannianVolumeMeasure (I := I) (M := M) g := by
  have h := volume_scaleMetric (I := I) (M := M) c hc g
  rw [hdim, ← ENNReal.ofReal_pow (Real.sqrt_nonneg c), Real.sq_sqrt hc.le] at h
  exact h

omit [CompleteSpace E] in
theorem surfaceArea_scaleMetric
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 2)
    (c : ℝ) (hc : 0 < c) :
    surfaceArea (scaleMetric c hc g) = c * surfaceArea g := by
  unfold surfaceArea
  rw [surfaceVolume_scaleMetric g hdim c hc, measureReal_ennreal_smul_apply,
    ENNReal.toReal_ofReal hc.le]


theorem totalScalarCurvature_scaleMetric
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 2)
    (c : ℝ) (hc : 0 < c) :
    totalScalarCurvature (scaleMetric c hc g) = totalScalarCurvature g := by
  unfold totalScalarCurvature
  simp_rw [metricScalarAt_scaleMetric]
  rw [surfaceVolume_scaleMetric g hdim c hc, integral_smul_measure,
    ENNReal.toReal_ofReal hc.le, smul_eq_mul, integral_const_mul,
    ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]


theorem surfaceEntropy_scaleMetric
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 2)
    (c : ℝ) (hc : 0 < c) :
    surfaceEntropy (scaleMetric c hc g) = surfaceEntropy g := by
  have hproduct (x : M) :
      metricScalarAt (I := I) (scaleMetric c hc g) x * surfaceArea (scaleMetric c hc g) =
        metricScalarAt (I := I) g x * surfaceArea g := by
    rw [metricScalarAt_scaleMetric, surfaceArea_scaleMetric g hdim c hc]
    field_simp [hc.ne']
  unfold surfaceEntropy
  simp_rw [hproduct, metricScalarAt_scaleMetric]
  rw [surfaceVolume_scaleMetric g hdim c hc, integral_smul_measure,
    ENNReal.toReal_ofReal hc.le, smul_eq_mul]
  simp_rw [mul_assoc]
  rw [integral_const_mul, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]


theorem surfaceEntropy_lower_and_eq_iff_constant [Nonempty M]
    (g : SmoothRiemannianMetric I M)
    (hpositive : ∀ x : M, 0 < metricScalarAt (I := I) g x) :
    totalScalarCurvature g * Real.log (totalScalarCurvature g) ≤ surfaceEntropy g ∧
      (surfaceEntropy g = totalScalarCurvature g * Real.log (totalScalarCurvature g) ↔
        ∃ c : ℝ, ∀ x : M, metricScalarAt (I := I) g x = c) :=
  surfaceEntropy_minimum g hpositive

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
