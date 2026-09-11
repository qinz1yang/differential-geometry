import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ReducedVolumeComplete
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory
open DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped ContDiff Manifold Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private theorem setVolume_density_factor (n : ℕ) (tau L : ℝ) (htau : 0 < tau) :
    Real.exp (-L - ((n : ℝ) / 2) * Real.log tau -
        ((n : ℝ) / 2) * Real.log (4 * Real.pi)) =
      (4 * Real.pi * tau) ^ (-(n : ℝ) / 2) * Real.exp (-L) := by
  have hpi : 0 < 4 * Real.pi := by positivity
  rw [Real.rpow_def_of_pos (mul_pos hpi htau), ← Real.exp_add,
    Real.log_mul hpi.ne' htau.ne']
  congr 1
  ring

private theorem setVolume_density_factor_pos (n : ℕ) (tau L : ℝ) (htau : 0 < tau) :
    0 < (4 * Real.pi * tau) ^ (-(n : ℝ) / 2) * Real.exp (-L) :=
  mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)

section General

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem redVolume_set_lower
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M)
    (tau L : ℝ) (htau : 0 < tau) {A : Set M} (hA : MeasurableSet A)
    (hL : ∀ y ∈ A, redLength S T x y tau ≤ L) :
    riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (T - tau)) A *
        ENNReal.ofReal ((4 * Real.pi * tau) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
          Real.exp (-L)) ≤
      DifferentialGeometry.PDE.RicciFlow.redVolume S T x tau := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (T - tau))
  let c := (4 * Real.pi * tau) ^ (-(Module.finrank ℝ E : ℝ) / 2) * Real.exp (-L)
  have hc : ∀ y ∈ A, ENNReal.ofReal c ≤ ENNReal.ofReal (redDensity S T x y tau) := by
    intro y hy
    apply ENNReal.ofReal_le_ofReal
    rw [show c = Real.exp (-L - ((Module.finrank ℝ E : ℝ) / 2) * Real.log tau -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) from
      (setVolume_density_factor (Module.finrank ℝ E) tau L htau).symm]
    unfold redDensity
    apply Real.exp_le_exp.mpr
    linarith [hL y hy]
  calc
    μ A * ENNReal.ofReal c = ENNReal.ofReal c * μ A := mul_comm _ _
    _ = ∫⁻ _y in A, ENNReal.ofReal c ∂μ := by rw [setLIntegral_const]
    _ ≤ ∫⁻ y in A, ENNReal.ofReal (redDensity S T x y tau) ∂μ :=
      setLIntegral_mono' hA hc
    _ ≤ ∫⁻ y, ENNReal.ofReal (redDensity S T x y tau) ∂μ := by
      simpa using lintegral_mono_set (subset_univ A)
    _ = DifferentialGeometry.PDE.RicciFlow.redVolume S T x tau := rfl

theorem redVolume_toReal_set_lower
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M)
    (tau L : ℝ) (htau : 0 < tau) {A : Set M} (hA : MeasurableSet A)
    (hL : ∀ y ∈ A, redLength S T x y tau ≤ L)
    (hfinite : DifferentialGeometry.PDE.RicciFlow.redVolume S T x tau ≠ ⊤) :
    riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (T - tau)) A ≠ ⊤ ∧
      (riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (T - tau)) A).toReal *
          ((4 * Real.pi * tau) ^ (-(Module.finrank ℝ E : ℝ) / 2) * Real.exp (-L)) ≤
        (DifferentialGeometry.PDE.RicciFlow.redVolume S T x tau).toReal := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (T - tau))
  let c := (4 * Real.pi * tau) ^ (-(Module.finrank ℝ E : ℝ) / 2) * Real.exp (-L)
  have hc : 0 < c := setVolume_density_factor_pos (Module.finrank ℝ E) tau L htau
  have hlow : μ A * ENNReal.ofReal c ≤ DifferentialGeometry.PDE.RicciFlow.redVolume S T x tau :=
    redVolume_set_lower S T x tau L htau hA hL
  have hprod : μ A * ENNReal.ofReal c ≠ ⊤ := ne_top_of_le_ne_top hfinite hlow
  have hAfinite : μ A ≠ ⊤ := by
    intro htop
    apply hprod
    rw [htop, ENNReal.top_mul (ne_of_gt (ENNReal.ofReal_pos.mpr hc))]
  have hreal := ENNReal.toReal_mono hfinite hlow
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le] at hreal
  exact ⟨hAfinite, hreal⟩

end General

end DifferentialGeometry.PDE.RicciFlow

end
