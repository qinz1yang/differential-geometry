import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Curvature.Bounds.RiemannTensorOperator

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N] [BoundarylessManifold J N]

theorem inner_riemannOp_localPullMetric_le
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (x : M) {K : ℝ}
    (hRm : Real.sqrt (Tensor0SBundle.normSq0S g (f x) 4
      (metricRm04At g (f x))) ≤ K)
    (X Y : TangentSpace I x) :
    let gPull := localPullMetric g f hf
    gPull.inner x (riemannOp (LeviCivita gPull) x X Y Y) X ≤
      K * gPull.inner x X X * gPull.inner x Y Y := by
  obtain ⟨basis, hON⟩ := Tensor0SBundle.exists_orthonormal_basis g (f x)
  have hbound := riemann_quad_le g basis hON hRm
    (mfderiv I J f x X) (mfderiv I J f x Y)
  change (localPullMetric g f hf).inner x
    (riemannOp (LeviCivita (localPullMetric g f hf)) x X Y Y) X ≤ _
  calc
    _ = (localPullMetric g f hf).inner x X
        (riemannOp (LeviCivita (localPullMetric g f hf)) x X Y Y) :=
      (localPullMetric g f hf).symm x _ _
    _ = metricRm04StandardAt (localPullMetric g f hf) x X Y Y X :=
      (rm04_eq_inner (localPullMetric g f hf) x X Y X).symm
    _ = metricRm04StandardAt g (f x)
        (mfderiv I J f x X) (mfderiv I J f x Y)
        (mfderiv I J f x Y) (mfderiv I J f x X) :=
      metricRm04StandardAt_localPullMetric g f hf x X Y Y X
    _ = g.inner (f x)
        (riemannOp (LeviCivita g) (f x) (mfderiv I J f x X)
          (mfderiv I J f x Y) (mfderiv I J f x Y))
        (mfderiv I J f x X) := by
      rw [rm04_eq_inner]
      exact g.symm _ _ _
    _ ≤ K * g.inner (f x) (mfderiv I J f x X) (mfderiv I J f x X) *
        g.inner (f x) (mfderiv I J f x Y) (mfderiv I J f x Y) := hbound
    _ = _ := by rw [localPullMetric_inner, localPullMetric_inner]

end DifferentialGeometry.Geometry.Curvature
