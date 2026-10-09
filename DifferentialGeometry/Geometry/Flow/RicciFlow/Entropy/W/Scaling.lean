import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Potential.Defs
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Scaling

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

open MeasureTheory
open DifferentialGeometry.Integral.Measure
open scoped ContDiff

private theorem prefactor_mul_sqrt_pow (n : ℕ) {c tau : ℝ} (hc : 0 < c) (htau : 0 < tau) :
    perelmanDensityPrefactor n (c * tau) * Real.sqrt c ^ n = perelmanDensityPrefactor n tau := by
  have heq : 4 * Real.pi * (c * tau) = c * (4 * Real.pi * tau) := by ring
  have hp : c ^ (-(n : ℝ) / 2) = (Real.sqrt c ^ n)⁻¹ := by
    rw [neg_div, Real.rpow_neg hc.le, Real.rpow_div_two_eq_sqrt _ hc.le, Real.rpow_natCast]
  change (4 * Real.pi * (c * tau)) ^ (-(n : ℝ) / 2) * Real.sqrt c ^ n =
    (4 * Real.pi * tau) ^ (-(n : ℝ) / 2)
  rw [heq, Real.mul_rpow hc.le (by positivity), hp]
  have hn : Real.sqrt c ^ n ≠ 0 := pow_ne_zero _ (Real.sqrt_pos.mpr hc).ne'
  calc
    _ = (Real.sqrt c ^ n)⁻¹ * Real.sqrt c ^ n * (4 * Real.pi * tau) ^ (-(n : ℝ) / 2) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hn, one_mul]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem setLIntegral_perelmanDensity_scaleMetric
    (g : SmoothRiemannianMetric I M) {c tau : ℝ} (hc : 0 < c) (htau : 0 < tau)
    (f : M → ℝ) (A : Set M) :
    ∫⁻ x in A, ENNReal.ofReal (perelmanDensity (Module.finrank ℝ E) (c * tau) f x)
      ∂riemannianVolumeMeasure (I := I) (M := M) (scaleMetric c hc g) =
    ∫⁻ x in A, ENNReal.ofReal (perelmanDensity (Module.finrank ℝ E) tau f x)
      ∂riemannianVolumeMeasure (I := I) (M := M) g := by
  rw [volume_scaleMetric, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul,
    ← lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
  apply lintegral_congr
  intro x
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg c),
    ← ENNReal.ofReal_mul (pow_nonneg (Real.sqrt_nonneg c) _)]
  congr 1
  dsimp only [perelmanDensity]
  rw [← mul_assoc, mul_comm (Real.sqrt c ^ Module.finrank ℝ E), prefactor_mul_sqrt_pow _ hc htau]

end DifferentialGeometry.PDE.RicciFlow.Entropy
