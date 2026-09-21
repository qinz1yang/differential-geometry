import DifferentialGeometry.Geometry.Metric.Pullback.Local

section
set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry

variable {E F G H H' H'' M N P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'} {K : ModelWithCorners ℝ G H''}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
  [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold K ∞ P]

omit [FiniteDimensional ℝ G] in
theorem localPullMetric_comp
    (g : SmoothRiemannianMetric K P) (h : N → P) (f : M → N)
    (hh : IsLocalDiffeomorph J K ∞ h) (hf : IsLocalDiffeomorph I J ∞ f)
    (hhf : IsLocalDiffeomorph I K ∞ (h ∘ f)) :
    localPullMetric (localPullMetric g h hh) f hf = localPullMetric g (h ∘ f) hhf := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [localPullMetric_inner, localPullMetric_inner, localPullMetric_inner]
  have hd : mfderiv I K (h ∘ f) x = (mfderiv J K h (f x)).comp (mfderiv I J f x) :=
    mfderiv_comp x (hh.mdifferentiable (by decide) (f x)) (hf.mdifferentiable (by decide) x)
  rw [hd]
  rfl

end DifferentialGeometry

end

end
