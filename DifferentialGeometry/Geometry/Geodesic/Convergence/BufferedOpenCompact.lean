import DifferentialGeometry.Geometry.Geodesic.Convergence.BufferedOpenDistance
import DifferentialGeometry.Geometry.Metric.Distance.LocalPullCompactness

/-!
# Actual compact buffer on the original incomplete open limit source

Compactness follows from the actual injective metric pullback and the complete ambient buffer.
The original restricted metric and inherited tangent norm are retained throughout.
-/

set_option autoImplicit false

noncomputable section

open Set Bundle
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem bufferedOpen_native_closedBall_compact
    (g : SmoothRiemannianMetric I M) (hNorm : IsMetricNorm g)
    (U : TopologicalSpace.Opens M) (n : U)
    (hbuffer : Metric.closedBall (n : M) 10 ⊆ U) :
    IsCompact (riemannianClosedBallOf (g.restrictOpen U) n 10) := by
  let f : U → M := Subtype.val
  have hf := DifferentialGeometry.isLocalDiffeomorph_subtype_val (I := I) U
  have hpull : DifferentialGeometry.localPullMetric g f hf =
      g.restrictOpen U := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [DifferentialGeometry.localPullMetric_inner]
    change g.inner (x : M) (mfderiv I I (Subtype.val : U → M) x v)
      (mfderiv I I (Subtype.val : U → M) x w) = g.inner (x : M) v w
    rw [DifferentialGeometry.mfderiv_subtype_val_apply,
      DifferentialGeometry.mfderiv_subtype_val_apply]
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    hNorm.isContinuousRiemannianBundle
  let : ProperSpace M := Manifold.properSpace_of_isRiemannianManifold I
  have hball : riemannianClosedBallOf g (n : M) 10 = Metric.closedBall (n : M) 10 := by
    ext x
    change riemannianEDistOf g (n : M) x ≤ ENNReal.ofReal 10 ↔ dist x (n : M) ≤ 10
    rw [riemannianEDistOf_eq_riemannianEDist g hNorm,
      ← IsRiemannianManifold.out (I := I), edist_dist]
    simpa only [dist_comm] using
      (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 10))
  rw [← hpull]
  apply DifferentialGeometry.Geometry.Metric.isCompact_riemannianClosedBallOf_localPullMetric
    g f hf Subtype.val_injective n 10 (hball ▸ isCompact_closedBall (n : M) 10)
  intro x hx
  exact ⟨⟨x, hbuffer (hball ▸ hx)⟩, rfl⟩

theorem bufferedOpen_native_near
    (g : SmoothRiemannianMetric I M) (hNorm : IsMetricNorm g)
    (U : TopologicalSpace.Opens M) (n q : U)
    (hbuffer : Metric.closedBall (n : M) 10 ⊆ U)
    (hq : (q : M) ∈ Metric.ball (n : M) 3) :
    q ∈ riemannianBallOf (g.restrictOpen U) n 3 := by
  change riemannianEDistOf (g.restrictOpen U) n q < ENNReal.ofReal 3
  rw [bufferedOpen_restricted_edist_eq g hNorm U n q hbuffer hq, edist_dist]
  apply ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg |>.2
  simpa only [Metric.mem_ball, dist_comm] using hq

private theorem realMetricNorm : IsMetricNorm (euclideanMetric (E := ℝ)) := by
  intro x v
  rw [← ofReal_norm, euclideanMetric_inner, real_inner_self_eq_norm_sq,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg v)]

theorem realOpen_native_closedBall_compact :
    let U : TopologicalSpace.Opens ℝ := ⟨Ioo (-11) 11, isOpen_Ioo⟩
    let n : U := ⟨0, by constructor <;> norm_num⟩
    IsCompact (riemannianClosedBallOf ((euclideanMetric (E := ℝ)).restrictOpen U) n 10) := by
  let U : TopologicalSpace.Opens ℝ := ⟨Ioo (-11) 11, isOpen_Ioo⟩
  let n : U := ⟨0, by constructor <;> norm_num⟩
  apply bufferedOpen_native_closedBall_compact (euclideanMetric (E := ℝ)) realMetricNorm U n
  intro x hx
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le] at hx
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

end DifferentialGeometry.Geometry.Riemannian.Geodesic
