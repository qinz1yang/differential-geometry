import DifferentialGeometry.Geometry.Comparison.Soul.SoulConvexCore
import DifferentialGeometry.Geometry.Curvature.Nonnegative

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem exists_radius_busemann_ray_gt (g : SmoothRiemannianMetric I M)
    (hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm g)
    (hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature g)
    (p : M) (A : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : M, R < dist p x →
      ∃ c : ℝ≥0 → M, Isometry c ∧ c 0 = p ∧ A < busemann c x := by
  obtain ⟨R, hR, hbound⟩ :=
    (isCompact_rayBusemannSublevel g hEnorm hsec p A).isBounded.subset_closedBall_lt 0 p
  refine ⟨R, hR, ?_⟩
  intro x hx
  have hnot : x ∉ rayBusemannSublevel p A := by
    intro hmem
    have hdist := hbound hmem
    rw [Metric.mem_closedBall, dist_comm] at hdist
    exact hx.not_ge hdist
  change ¬ (∀ c : ℝ≥0 → M, Isometry c → c 0 = p → busemann c x ≤ A) at hnot
  push Not at hnot
  exact hnot

end DifferentialGeometry.Geometry.Topology
