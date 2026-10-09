import DifferentialGeometry.Geometry.Collapse.CurvatureScaleVolumeComparison
import DifferentialGeometry.Geometry.Comparison.Volume.InteriorBallLowerBound

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open Set
open scoped ContDiff ENNReal Manifold

namespace DifferentialGeometry.Geometry.Collapse

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

/-- Thick volume at a curvature scale gives a quantitative volume lower bound at nearby
centers. The comparison passes to half the curvature radius and does not assume that
the defining supremum is attained. -/
theorem ballVolume_lower_near_curvature_scale
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 3)
    (hg : RiemannianMetricComplete g) (p q : M) {R r w : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hrR : r ≤ R / 4)
    (hq : q ∈ riemannianBallOf g p (R / 8))
    (hscale : ENNReal.ofReal R ≤ curvatureRadius g p)
    (hvol : ENNReal.ofReal (w * R ^ 3) ≤ ballVolume g p R) :
    ENNReal.ofReal (w * Real.exp (-7) / 4096 * r ^ 3) ≤ ballVolume g q r := by
  let : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let c := Real.exp (-4) * ((R / 2) / (2 * R)) ^ 3
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hcoef : c * (w * R ^ 3) = (w * Real.exp (-4) / 8) * (R / 2) ^ 3 := by
    dsimp only [c]
    field_simp [hR.ne']
    ring
  have hhalf : ENNReal.ofReal ((w * Real.exp (-4) / 8) * (R / 2) ^ 3) ≤
      ballVolume g p (R / 2) := calc
    _ = ENNReal.ofReal c * ENNReal.ofReal (w * R ^ 3) := by
      rw [← ENNReal.ofReal_mul hc, hcoef]
    _ ≤ ENNReal.ofReal c * ballVolume g p R := mul_le_mul' le_rfl hvol
    _ ≤ ballVolume g p (R / 2) :=
      ballVolume_ratio_at_curvature_scale g hdim hg p (half_pos hR)
        (half_le_self hR.le) hscale
  have hsec : ∀ x ∈ riemannianBallOf g p (R / 2),
      SectionalBoundedBelowAt g x (-((R / 2) ^ 2)⁻¹) := by
    intro x hx
    exact sectional_lower_on_ball_of_le_curvatureRadius g p hR hscale
      (riemannianBallOf_mono g p (half_le_self hR.le) hx)
  have hnear := riemannianBallOf_volume_lower_of_nearby_center g hg p q
    (s := R / 2) (w := w * Real.exp (-4) / 8) (half_pos hR) hr
    (by linarith : r ≤ (R / 2) / 2)
    (by simpa only [show (R / 2) / 4 = R / 8 by ring] using hq) hsec
    (by simpa only [hdim, ballVolume] using hhalf)
  have hexp : Real.exp (-4) * Real.exp (-3) = Real.exp (-7) := by
    rw [← Real.exp_add]
    norm_num
  have hfactor : (w * Real.exp (-4) / 8) * Real.exp (-3) / (8 : ℝ) ^ 3 * r ^ 3 =
      w * Real.exp (-7) / 4096 * r ^ 3 := by
    calc
      _ = w * (Real.exp (-4) * Real.exp (-3)) / 4096 * r ^ 3 := by ring
      _ = _ := by rw [hexp]
  simpa only [hdim, Nat.reduceSub, Nat.cast_ofNat,
    show -3 * (2 : ℝ) / 2 = -3 by ring, hfactor, ballVolume] using hnear

end DifferentialGeometry.Geometry.Collapse
