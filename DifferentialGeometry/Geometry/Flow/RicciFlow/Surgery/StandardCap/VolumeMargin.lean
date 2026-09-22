import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitnessVolume
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties

noncomputable section
open MeasureTheory Set
open DifferentialGeometry DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev Cap := {x : E3 // ‖x‖ ≤ transitionEnd}
private instance : CompactSpace Cap :=
  (DifferentialGeometry.Topology.Manifold.closedBallUnitHomeomorph transitionEnd_pos).symm.compactSpace
private instance : MeasurableSpace E3 := borel E3
private instance : BorelSpace E3 := ⟨rfl⟩

private theorem cap_volume_ne_top :
    riemannianVolumeMeasure (𝓡 3) E3 metric {x | ‖x‖ ≤ transitionEnd} ≠ (∞ : ℝ≥0∞) := by
  let : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (𝓡 3) E3 metric) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts metric
  exact (isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace Cap)).measure_lt_top.ne

theorem cap_volume_margin_of_precision_le (δ Q : ℝ) (hδ : 0 < δ) (hQ : 0 < Q)
    (hsmall : δ ≤ Real.pi /
      (8 * (riemannianVolumeMeasure (𝓡 3) E3 metric {x | ‖x‖ ≤ transitionEnd}).toReal + 1)) :
    ENNReal.ofReal (8 * Q ^ (-3 / 2 : ℝ)) *
        riemannianVolumeMeasure (𝓡 3) E3 metric {x | ‖x‖ ≤ transitionEnd} +
      ENNReal.ofReal (Q ^ (-3 / 2 : ℝ)) ≤
      ENNReal.ofReal (2 * Real.pi / δ) * ENNReal.ofReal (Q ^ (-3 / 2 : ℝ)) := by
  let V := riemannianVolumeMeasure (𝓡 3) E3 metric {x | ‖x‖ ≤ transitionEnd}
  have hV : ENNReal.ofReal V.toReal = V := ENNReal.ofReal_toReal cap_volume_ne_top
  have hp : 0 < 8 * V.toReal + 1 := by positivity
  have hbound : 8 * V.toReal + 1 ≤ 2 * Real.pi / δ := by
    have hs := (le_div_iff₀ hp).mp hsmall
    exact (le_div_iff₀ hδ).mpr (by nlinarith [Real.pi_pos])
  have hqn : 0 ≤ Q ^ (-3 / 2 : ℝ) := Real.rpow_nonneg hQ.le _
  change ENNReal.ofReal (8 * Q ^ (-3 / 2 : ℝ)) * V + ENNReal.ofReal (Q ^ (-3 / 2 : ℝ)) ≤ _
  rw [← hV, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) hqn, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc
    8 * Q ^ (-3 / 2 : ℝ) * V.toReal + Q ^ (-3 / 2 : ℝ) =
      (8 * V.toReal + 1) * Q ^ (-3 / 2 : ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hbound hqn

end DifferentialGeometry.PDE.RicciFlow.StandardCap
