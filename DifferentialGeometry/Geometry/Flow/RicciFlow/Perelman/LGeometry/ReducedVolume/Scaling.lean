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
  rw [normalizedShrinkerMass_scaleMetric_inv_eq_lintegral_perelmanDensity _ htau]
  apply lintegral_congr
  intro q
  apply congrArg ENNReal.ofReal
  rw [perelmanDensity, ← Real.exp_log (prefactor_pos (Module.finrank ℝ E) htau),
    log_prefactor (Module.finrank ℝ E) htau, ← Real.exp_add,
    Real.log_mul (show 4 * Real.pi ≠ 0 by positivity) htau.ne']
  congr 1
  dsimp only [redLength]
  ring

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
    normalizedShrinkerMass_eq_lintegral_perelmanDensity_one, hg]
  have h := setLIntegral_perelmanDensity_scaleMetric g htau zero_lt_one
    (fun y => redLength S T p y (c * tau)) Set.univ
  simpa only [mul_one, setLIntegral_univ] using h.symm

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
