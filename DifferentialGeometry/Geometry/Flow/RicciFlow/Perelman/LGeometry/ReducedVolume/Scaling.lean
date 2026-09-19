import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedVolumeNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Scaling

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open MeasureTheory
open DifferentialGeometry.PDE.RicciFlow.Entropy
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

private theorem normalizedShrinkerMass_eq_density_one
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) :
    normalizedShrinkerMass g f = ∫⁻ x,
      ENNReal.ofReal (perelmanDensity (Module.finrank ℝ E) 1 f x)
      ∂riemannianVolumeMeasure (I := I) (M := M) g := by
  rw [normalizedShrinkerMass_eq_const_mul_lintegral,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro x
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 4 * Real.pi) _)]
  simp only [perelmanDensity, perelmanDensityPrefactor, mul_one]
  rfl

theorem intrinsicReducedVolume_eq_lintegral_perelmanDensity_scaled
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (p : M)
    {c tau : ℝ} (hc : 0 < c) (htau : 0 < tau) :
    intrinsicReducedVolume S T p (c * tau) =
      ∫⁻ x, ENNReal.ofReal (perelmanDensity (Module.finrank ℝ E) tau
        (fun y => redLength S T p y (c * tau)) x)
        ∂riemannianVolumeMeasure (I := I) (M := M)
          (scaleMetric c⁻¹ (inv_pos.mpr hc) (S.base.metric (T - c * tau))) := by
  let g := scaleMetric (c * tau)⁻¹ (inv_pos.mpr (mul_pos hc htau))
    (S.base.metric (T - c * tau))
  have hg : scaleMetric c⁻¹ (inv_pos.mpr hc) (S.base.metric (T - c * tau)) =
      scaleMetric tau htau g := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    simp only [g, scaleMetric_inner]
    field_simp
  rw [intrinsicReducedVolume_eq_normalizedShrinkerMass S T p (mul_pos hc htau),
    normalizedShrinkerMass_eq_density_one, hg]
  have h := setLIntegral_perelmanDensity_scaleMetric g htau zero_lt_one
    (fun y => redLength S T p y (c * tau)) Set.univ
  simpa only [mul_one, setLIntegral_univ] using h.symm

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
