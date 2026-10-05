import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.ParabolicScaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceMass
import DifferentialGeometry.Geometry.Metric.Basic

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] {D : RealTimeInterval}

theorem intrinsicReducedVolume_parabolic
    (S : SolutionOn (I := I) (M := M) D)
    (t0 R T tau : ℝ) (hR : 0 < R) (ht0 : t0 ∈ D.carrier)
    (htau : 0 < tau) (p : M) :
    intrinsicReducedVolume (parabolicSolution S t0 R hR ht0)
        (parabolicBackward t0 R T) p (R * tau) =
      intrinsicReducedVolume S T p tau := by
  rw [← normalizedShrinkerMass_backward_slice_eq_intrinsicReducedVolume
    _ _ _ (mul_pos hR htau),
    ← normalizedShrinkerMass_backward_slice_eq_intrinsicReducedVolume S T p htau]
  have htime : parabolicTime t0 R (parabolicBackward t0 R T - R * tau) = T - tau := by
    unfold parabolicTime parabolicBackward
    field_simp [hR.ne']
    ring
  have hmetric : scaleMetric (R * tau)⁻¹ (inv_pos.mpr (mul_pos hR htau))
      ((parabolicSolution S t0 R hR ht0).base.metric
        (parabolicBackward t0 R T - R * tau)) =
      scaleMetric tau⁻¹ (inv_pos.mpr htau) (S.base.metric (T - tau)) := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    change (scaleMetric (R * tau)⁻¹ _
      (scaleMetric R hR (S.base.metric
        (parabolicTime t0 R (parabolicBackward t0 R T - R * tau))))).inner x v w = _
    rw [htime]
    simp only [scaleMetric_inner]
    field_simp
  rw [hmetric]
  congr 1
  funext x
  exact redLength_parabolic S t0 R T tau hR ht0 htau.le p x

omit [T2Space M] [SigmaCompactSpace M] in
theorem redLength_curvatureNormalizedSolution
    (S : SolutionOn (I := I) (M := M) D)
    (tau theta : ℝ) (htau : 0 < tau) (hzero : 0 ∈ D.carrier)
    (htheta : 0 ≤ theta) (p x : M) :
    redLength (curvatureNormalizedSolution S 0 tau⁻¹ (inv_pos.mpr htau) hzero)
        0 p x theta = redLength S 0 p x (tau * theta) := by
  change redLength (parabolicSolution S 0 tau⁻¹ (inv_pos.mpr htau) hzero)
    0 p x theta = redLength S 0 p x (tau * theta)
  have h := redLength_parabolic S 0 tau⁻¹ 0 (tau * theta)
    (inv_pos.mpr htau) hzero (mul_nonneg htau.le htheta) p x
  simpa only [parabolicBackward, sub_self, mul_zero, inv_mul_cancel_left₀ htau.ne'] using h

theorem intrinsicReducedVolume_curvatureNormalizedSolution
    (S : SolutionOn (I := I) (M := M) D)
    (tau theta : ℝ) (htau : 0 < tau) (hzero : 0 ∈ D.carrier)
    (htheta : 0 < theta) (p : M) :
    intrinsicReducedVolume
        (curvatureNormalizedSolution S 0 tau⁻¹ (inv_pos.mpr htau) hzero)
        0 p theta = intrinsicReducedVolume S 0 p (tau * theta) := by
  change intrinsicReducedVolume (parabolicSolution S 0 tau⁻¹ (inv_pos.mpr htau) hzero)
    0 p theta = intrinsicReducedVolume S 0 p (tau * theta)
  have h := intrinsicReducedVolume_parabolic S 0 tau⁻¹ 0 (tau * theta)
    (inv_pos.mpr htau) hzero (mul_pos htau htheta) p
  simpa only [parabolicBackward, sub_self, mul_zero, inv_mul_cancel_left₀ htau.ne'] using h

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
