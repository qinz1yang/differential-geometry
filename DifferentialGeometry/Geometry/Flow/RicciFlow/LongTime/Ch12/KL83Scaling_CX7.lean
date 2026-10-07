import DifferentialGeometry.Geometry.Collapse.ScaleInvariance
import DifferentialGeometry.Geometry.Collapse.CurvatureScaleVolumeComparison
import DifferentialGeometry.Geometry.Collapse.InducedVolumeComparison

/-! # CH12-CX7: scale-invariant lower volume bounds for the blow-up sequence -/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped Manifold ContDiff ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Collapse

namespace GC.LongTime.Ch12

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [CompleteSpace M]

/-- Noncollapse of a unit ball persists at every smaller radius after rescaling. -/
theorem noncollapse_rescale_CX7 (hdim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (p : M) {w ρ : ℝ} (hρ : 0 < ρ) (hρ1 : 2 * ρ ≤ 1)
    (hsec : ∀ q ∈ riemannianBallOf g p 1, SectionalBoundedBelowAt g q (-1))
    (hvol : ENNReal.ofReal w ≤ ballVolume g p 1) :
    ENNReal.ofReal (Real.exp (-4) * w) ≤
      ballVolume (scaleMetric (ρ⁻¹ ^ 2) (pow_pos (inv_pos.mpr hρ) 2) g) p 2 := by
  have hg := (riemannianMetricComplete_iff_completeSpace hmetric).mpr inferInstance
  have hscale : ENNReal.ofReal 1 ≤ curvatureRadius g p := by
    unfold curvatureRadius
    apply le_iSup_of_le (1 : ℝ)
    apply le_iSup_of_le zero_lt_one
    exact le_iSup_of_le (by simpa using hsec) le_rfl
  have hb := ballVolume_ratio_at_curvature_scale g hdim hg p (by positivity : 0 < 2 * ρ) hρ1 hscale
  have hsmall : ENNReal.ofReal ((Real.exp (-4) * w / 8) * (2 * ρ) ^ 3) ≤ ballVolume g p (2 * ρ) := by
    calc ENNReal.ofReal ((Real.exp (-4) * w / 8) * (2 * ρ) ^ 3)
        = ENNReal.ofReal (Real.exp (-4) * ((2 * ρ) / (2 * 1)) ^ 3) * ENNReal.ofReal w := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
      _ ≤ ENNReal.ofReal (Real.exp (-4) * ((2 * ρ) / (2 * 1)) ^ 3) * ballVolume g p 1 := by
          gcongr
      _ ≤ ballVolume g p (2 * ρ) := hb
  have hscaled := (le_ballVolume_scaleMetric_iff hdim (ρ⁻¹ ^ 2)
    (pow_pos (inv_pos.mpr hρ) 2) (w := Real.exp (-4) * w / 8) (t := 2 * ρ)).mpr hsmall
  have hsqrt : Real.sqrt (ρ⁻¹ ^ 2) * (2 * ρ) = 2 := by
    rw [Real.sqrt_sq (inv_pos.mpr hρ).le]
    field_simp
  rw [hsqrt] at hscaled
  convert hscaled using 1
  congr 1
  ring

end GC.LongTime.Ch12
