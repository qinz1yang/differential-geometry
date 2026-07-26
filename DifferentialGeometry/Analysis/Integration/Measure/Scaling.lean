import DifferentialGeometry.Geometry.Metric.Scaling
import DifferentialGeometry.Analysis.Integration.Measure.Invariance

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Riemannian volume under constant metric scaling

This file proves the constant-scaling law for the canonical Riemannian volume
measure.  It proceeds through the chart Gram matrix, chart density, chart-local
measure, and partition-of-unity assembly.
-/

namespace DifferentialGeometry.Integral.Measure

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private theorem sqrt_pow (c : Real) (hc : 0 ≤ c) (n : Nat) :
    Real.sqrt (c ^ n) = Real.sqrt c ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Real.sqrt_mul (pow_nonneg hc n), ih, pow_succ]

/-- A constant positive scaling of the metric scales every chart Gram matrix
by the same constant. -/
theorem chartGram_scale (c : Real) (hc : 0 < c)
    (g : SmoothRiemannianMetric I M) (x₀ x : M) :
    chartGramMatrix (scaleMetric (I := I) c hc g) x₀ x =
      c • chartGramMatrix g x₀ x := by
  ext i j
  simp [chartGramMatrix_apply, scaleMetric_inner]

/-- A constant positive metric scaling multiplies the chart volume density by
the square root of the determinant scaling factor. -/
theorem chartDensity_scale (c : Real) (hc : 0 < c)
    (g : SmoothRiemannianMetric I M) (x₀ x : M) :
    chartDensity (scaleMetric (I := I) c hc g) x₀ x =
      Real.sqrt (c ^ Module.finrank Real E) * chartDensity g x₀ x := by
  unfold chartDensity
  rw [chartGram_scale (I := I) c hc g x₀ x, Matrix.det_smul]
  simp only [Fintype.card_fin]
  rw [Real.sqrt_mul (pow_nonneg hc.le _)]

/-- The chart-local Riemannian measure scales by the constant chart-density
factor. -/
theorem chartLocal_scale (c : Real) (hc : 0 < c)
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    chartLocalMeasure (I := I) (scaleMetric (I := I) c hc g) x₀ =
      ENNReal.ofReal (Real.sqrt (c ^ Module.finrank Real E)) •
        chartLocalMeasure (I := I) g x₀ := by
  let a : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt (c ^ Module.finrank Real E))
  have hdensity :
      (fun y : E =>
        ENNReal.ofReal
          (chartDensity (scaleMetric (I := I) c hc g) x₀
            ((extChartAt I x₀).symm y))) =
        a • fun y : E =>
          ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)) := by
    funext y
    rw [chartDensity_scale (I := I) c hc]
    simp only [a, Pi.smul_apply, smul_eq_mul]
    exact ENNReal.ofReal_mul (Real.sqrt_nonneg _)
  have ha : a ≠ (∞ : ℝ≥0∞) := by simp [a]
  unfold chartLocalMeasure
  rw [hdensity, withDensity_smul' a _ ha, Measure.map_smul]

/-- A constant positive metric scaling multiplies the partition-of-unity
Riemannian measure by the same dimension-dependent factor. -/
theorem riemMeasure_scale [T2Space M] [SigmaCompactSpace M]
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (rho : SmoothPartitionOfUnity M I M Set.univ) :
    riemannianMeasure (I := I) (scaleMetric (I := I) c hc g) rho =
      ENNReal.ofReal (Real.sqrt (c ^ Module.finrank Real E)) •
        riemannianMeasure (I := I) g rho := by
  let a : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt (c ^ Module.finrank Real E))
  unfold riemannianMeasure
  have hterm :
      (fun alpha : M =>
        (chartLocalMeasure (I := I) (scaleMetric (I := I) c hc g) alpha).withDensity
          (fun x : M => ENNReal.ofReal (rho alpha x))) =
        fun alpha : M => a •
          (chartLocalMeasure (I := I) g alpha).withDensity
            (fun x : M => ENNReal.ofReal (rho alpha x)) := by
    funext alpha
    rw [chartLocal_scale (I := I) c hc]
    exact withDensity_smul_measure _ _
  rw [hterm]
  refine Measure.ext fun s hs => ?_
  rw [Measure.sum_apply _ hs, Measure.smul_apply, Measure.sum_apply _ hs]
  exact ENNReal.tsum_const_smul a

/-- The canonical Riemannian volume measure of `c g` is
`sqrt(c)^n` times that of `g`, where `n` is the model dimension. -/
theorem volume_scaleMetric [T2Space M] [SigmaCompactSpace M]
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) :
    riemannianVolumeMeasure (I := I) (M := M)
        (scaleMetric (I := I) c hc g) =
      ENNReal.ofReal (Real.sqrt c) ^ Module.finrank Real E •
        riemannianVolumeMeasure (I := I) (M := M) g := by
  simpa only [sqrt_pow c hc.le,
    ENNReal.ofReal_pow (Real.sqrt_nonneg c)] using
    riemMeasure_scale (I := I) (M := M) c hc g (chartAtlasPOU I M)

/-- Setwise form of `volume_scaleMetric`, ready for metric-ball volume
calculations. -/
theorem volume_scale_apply [T2Space M] [SigmaCompactSpace M]
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (s : Set M) :
    riemannianVolumeMeasure (I := I) (M := M)
        (scaleMetric (I := I) c hc g) s =
      ENNReal.ofReal (Real.sqrt c) ^ Module.finrank Real E *
        riemannianVolumeMeasure (I := I) (M := M) g s := by
  have h := congrArg (fun mu : Measure M => mu s)
    (volume_scaleMetric (I := I) (M := M) c hc g)
  simpa only [Measure.smul_apply, smul_eq_mul] using h

end

end DifferentialGeometry.Integral.Measure
