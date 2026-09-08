import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Measure
import Mathlib.Tactic.Linarith

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open MeasureTheory
open Integral.Measure (riemannianVolumeMeasure)
open scoped ContDiff

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
variable {D : Geometry.Curvature.RealTimeInterval}

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem measure_mul_exp_le_redVolume
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M)
    (tau l₀ : ℝ) (A : Set M)
    (hl : ∀ᵐ y ∂(riemannianVolumeMeasure I M
        (S.base.metric (T - tau))).restrict A, redLength S T x y tau ≤ l₀) :
    riemannianVolumeMeasure I M (S.base.metric (T - tau)) A *
        ENNReal.ofReal (Real.exp (-l₀ -
          ((Module.finrank ℝ E : ℝ) / 2) * Real.log tau -
          ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))) ≤
      redVolume S T x tau := by
  let μ := riemannianVolumeMeasure I M (S.base.metric (T - tau))
  let c := ENNReal.ofReal (Real.exp (-l₀ -
    ((Module.finrank ℝ E : ℝ) / 2) * Real.log tau -
    ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)))
  have hc : ∀ᵐ y ∂μ.restrict A, c ≤ ENNReal.ofReal (redDensity S T x y tau) := by
    filter_upwards [hl] with y hy
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    linarith
  calc
    μ A * c = ∫⁻ _ in A, c ∂μ := by rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ y in A, ENNReal.ofReal (redDensity S T x y tau) ∂μ := lintegral_mono_ae hc
    _ ≤ redVolume S T x tau := lintegral_mono' Measure.restrict_le_self le_rfl

end DifferentialGeometry.PDE.RicciFlow.Perelman
