import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross

noncomputable section

open Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]

theorem mfderiv_metricScalarAt_localPull_scaleMetric
    (g : SmoothRiemannianMetric J N) (Phi : M → N)
    (hPhi : IsLocalDiffeomorph I J ∞ Phi) {Q : ℝ} (hQ : 0 < Q) (x : M)
    (v : TangentSpace I x) :
    (show ℝ from mfderiv I 𝓘(ℝ, ℝ) (metricScalarAt (localPullMetric (scaleMetric Q hQ g) Phi hPhi)) x v) =
      Q⁻¹ * (show ℝ from mfderiv J 𝓘(ℝ, ℝ) (metricScalarAt g) (Phi x) (mfderiv I J Phi x v)) := by
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  let _ : IsManifold J 1 N := IsManifold.of_le (n := ∞) (by decide)
  have hg : MDifferentiableAt J 𝓘(ℝ, ℝ) (metricScalarAt g) (Phi x) :=
    (metricScalar_smooth g).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp x hg (hPhi.mdifferentiable (by simp) x)
  have heq : metricScalarAt (localPullMetric (scaleMetric Q hQ g) Phi hPhi) =
      Q⁻¹ • ((metricScalarAt g) ∘ Phi) := by
    funext y
    change metricScalarAt (localPullMetric (scaleMetric Q hQ g) Phi hPhi) y =
      Q⁻¹ * metricScalarAt g (Phi y)
    rw [metricScalarAt_localPull, metricScalarAt_scaleMetric]
  rw [heq, const_smul_mfderiv (hg.comp x (hPhi.mdifferentiable (by simp) x)), hcomp]
  rfl

theorem scalar_gradient_bound_of_localPull_scaleMetric
    (g : SmoothRiemannianMetric J N) (Phi : M → N)
    (hPhi : IsLocalDiffeomorph I J ∞ Phi) {Q : ℝ} (hQ : 0 < Q) (x : M) {C : ℝ}
    (hbound : ∀ v : TangentSpace I x,
      |(show ℝ from mfderiv I 𝓘(ℝ, ℝ) (metricScalarAt (localPullMetric (scaleMetric Q hQ g) Phi hPhi)) x v)| ≤
        C * metricScalarAt (localPullMetric (scaleMetric Q hQ g) Phi hPhi) x *
          Real.sqrt (metricScalarAt (localPullMetric (scaleMetric Q hQ g) Phi hPhi) x) *
          Real.sqrt ((localPullMetric (scaleMetric Q hQ g) Phi hPhi).inner x v v)) :
    ∀ w : TangentSpace J (Phi x),
      |(show ℝ from mfderiv J 𝓘(ℝ, ℝ) (metricScalarAt g) (Phi x) w)| ≤
        C * metricScalarAt g (Phi x) * Real.sqrt (metricScalarAt g (Phi x)) *
          Real.sqrt (g.inner (Phi x) w w) := by
  intro w
  obtain ⟨v, hv⟩ := (hPhi.mfderivToContinuousLinearEquiv (by simp) x).surjective w
  change mfderiv I J Phi x v = w at hv
  have hb := hbound v
  rw [mfderiv_metricScalarAt_localPull_scaleMetric, hv, metricScalarAt_localPull,
    metricScalarAt_scaleMetric, localPullMetric_inner, scaleMetric_inner, hv,
    abs_mul, abs_of_pos (inv_pos.mpr hQ)] at hb
  have hs : Real.sqrt Q ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hQ)
  have hroot : Real.sqrt (Q⁻¹ * metricScalarAt g (Phi x)) *
      Real.sqrt (Q * g.inner (Phi x) w w) =
      Real.sqrt (metricScalarAt g (Phi x)) * Real.sqrt (g.inner (Phi x) w w) := by
    rw [inv_mul_eq_div, Real.sqrt_div' _ hQ.le, Real.sqrt_mul hQ.le]
    field_simp
  apply (div_le_div_iff_of_pos_right hQ).mp
  calc
    |(show ℝ from mfderiv J 𝓘(ℝ, ℝ) (metricScalarAt g) (Phi x) w)| / Q =
      Q⁻¹ * |(show ℝ from mfderiv J 𝓘(ℝ, ℝ) (metricScalarAt g) (Phi x) w)| := by ring
    _ ≤ C * (Q⁻¹ * metricScalarAt g (Phi x)) * Real.sqrt (Q⁻¹ * metricScalarAt g (Phi x)) *
          Real.sqrt (Q * g.inner (Phi x) w w) := hb
    _ = (C * metricScalarAt g (Phi x) * Real.sqrt (metricScalarAt g (Phi x)) *
        Real.sqrt (g.inner (Phi x) w w)) / Q := by
      rw [mul_assoc (C * (Q⁻¹ * metricScalarAt g (Phi x))), hroot]
      ring

end DifferentialGeometry.Geometry.Curvature
