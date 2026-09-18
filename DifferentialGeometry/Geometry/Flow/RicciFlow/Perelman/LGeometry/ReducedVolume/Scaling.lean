import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedVolumeNormalization
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Scaling

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] {D : RealTimeInterval}
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem intrinsicReducedVolume_eq_normalizedShrinkerMass
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (p : M) {tau : ℝ} (htau : 0 < tau) :
    intrinsicReducedVolume S T p tau =
      normalizedShrinkerMass (scaleMetric tau⁻¹ (inv_pos.mpr htau) (S.base.metric (T - tau)))
        (fun q => redLength S T p q tau) := by
  have hcoeff : (Real.sqrt tau⁻¹) ^ Module.finrank ℝ E =
      Real.exp (-((Module.finrank ℝ E : ℝ) / 2) * Real.log tau) := by
    have hroot : Real.sqrt tau⁻¹ = Real.exp (-(1 / 2 : ℝ) * Real.log tau) := by
      calc
        _ = Real.exp (Real.log (Real.sqrt tau⁻¹)) :=
          (Real.exp_log (Real.sqrt_pos.mpr (inv_pos.mpr htau))).symm
        _ = _ := by
          rw [Real.log_sqrt (inv_pos.mpr htau).le, Real.log_inv]
          congr 1
          ring
    rw [hroot, ← Real.exp_nat_mul]
    congr 1
    ring
  unfold normalizedShrinkerMass
  rw [volume_scaleMetric, lintegral_smul_measure, smul_eq_mul,
    ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), hcoeff,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  unfold intrinsicReducedVolume
  apply lintegral_congr
  intro q
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  dsimp only [redLength]
  ring

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
