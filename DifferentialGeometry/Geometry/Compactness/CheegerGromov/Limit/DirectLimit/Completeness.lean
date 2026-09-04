import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.DirectLimit.Defs
import DifferentialGeometry.Geometry.Metric.DirectLimit.Properness

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Bundle
open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {A : ℕ → Type u} [∀ k, TopologicalSpace (A k)] [∀ k, ChartedSpace H (A k)]
  [∀ k, IsManifold I ∞ (A k)] [∀ k, Nonempty (A k)]
  [∀ k, SigmaCompactSpace (A k)] [∀ k, T2Space (A k)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] in
theorem limit_complete_of_compact_ball_cover
    (S : SmoothSeqSystem I A) (O₀ : A 0)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g)
    [∀ k, PreconnectedSpace (A k)]
    (hcover : S.hasCompactBallCover g hg) :
    MetricComplete (I := I) (pointedDirectLimitOfMetricCocycle S O₀ g hg) := by
  unfold MetricComplete
  let : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric g hg).toRiemannianMetric⟩
  let : IsManifold I 1 S.toSeqSystem.Lim :=
    IsManifold.of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  let : TopologicalSpace.MetrizableSpace S.toSeqSystem.Lim :=
    Manifold.metrizableSpace I S.toSeqSystem.Lim
  let : T3Space S.toSeqSystem.Lim := inferInstance
  let : IsContinuousRiemannianBundle E
      (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨⟨(S.limitMetric g hg).inner, (S.limitMetric g hg).contMDiff.continuous,
      by intro x v w; rfl⟩⟩
  let : EMetricSpace S.toSeqSystem.Lim :=
    EMetricSpace.ofRiemannianMetric I S.toSeqSystem.Lim
  let : MetricSpace S.toSeqSystem.Lim :=
    EMetricSpace.toMetricSpace
      (fun x y => Geometry.Riemannian.Exponential.riemannianEDist_ne_top (I := I) x y)
  have : ProperSpace S.toSeqSystem.Lim := by
    refine ProperSpace.of_isCompact_closedBall_of_le 0 (fun z r hr => ?_)
    have h := S.isCompact_limit_closedBall_of_cover g hg hcover z (ENNReal.ofReal r) ENNReal.ofReal_ne_top
    have hset : Metric.closedBall z r =
        {w : S.toSeqSystem.Lim |
          Manifold.riemannianEDist I z w ≤ ENNReal.ofReal r} := by
      rw [← Metric.closedEBall_ofReal hr]
      ext w
      exact Metric.mem_closedEBall'
    rw [hset]
    exact h
  exact (complete_of_proper : CompleteSpace S.toSeqSystem.Lim)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] in
theorem limit_complete_of_compact_stage_balls
    (S : SmoothSeqSystem I A) (O₀ : A 0)
    (g : ∀ k, SmoothRiemannianMetric I (A k)) (hg : S.MetricCocycle g)
    [∀ k, PreconnectedSpace (A k)]
    (hexh : ∀ (z : S.toSeqSystem.Lim) (r : ENNReal),
      letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
        ⟨(S.limitMetric g hg).toRiemannianMetric⟩
      ∃ k, ∀ w : S.toSeqSystem.Lim,
        Manifold.riemannianEDist I z w ≤ r → w ∈ Set.range (S.toSeqSystem.incl k))
    (hcpt : ∀ (k : ℕ) (a : A k) (r : ENNReal),
      letI : RiemannianBundle (fun x : A k => TangentSpace I x) :=
        ⟨(g k).toRiemannianMetric⟩
      IsCompact {b : A k | Manifold.riemannianEDist I a b ≤ r}) :
    MetricComplete (I := I) (pointedDirectLimitOfMetricCocycle S O₀ g hg) := by
  unfold MetricComplete
  let : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨(S.limitMetric g hg).toRiemannianMetric⟩
  let : IsManifold I 1 S.toSeqSystem.Lim :=
    IsManifold.of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  let : TopologicalSpace.MetrizableSpace S.toSeqSystem.Lim :=
    Manifold.metrizableSpace I S.toSeqSystem.Lim
  let : T3Space S.toSeqSystem.Lim := inferInstance
  let : IsContinuousRiemannianBundle E (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨⟨(S.limitMetric g hg).inner, (S.limitMetric g hg).contMDiff.continuous,
      by intro x v w; rfl⟩⟩
  let : EMetricSpace S.toSeqSystem.Lim :=
    EMetricSpace.ofRiemannianMetric I S.toSeqSystem.Lim
  let : MetricSpace S.toSeqSystem.Lim :=
    EMetricSpace.toMetricSpace
      (fun x y => Geometry.Riemannian.Exponential.riemannianEDist_ne_top (I := I) x y)
  have : ProperSpace S.toSeqSystem.Lim := by
    refine ProperSpace.of_isCompact_closedBall_of_le 0 (fun z r hr => ?_)
    have h := S.isCompact_limit_closedBall g hg hexh hcpt z (ENNReal.ofReal r) ENNReal.ofReal_ne_top
    have hset : Metric.closedBall z r
        = {w : S.toSeqSystem.Lim |
            Manifold.riemannianEDist I z w ≤ ENNReal.ofReal r} := by
      rw [← Metric.closedEBall_ofReal hr]
      ext w
      exact Metric.mem_closedEBall'
    rw [hset]
    exact h
  exact (complete_of_proper : CompleteSpace S.toSeqSystem.Lim)

end CheegerGromovCompactness
end DifferentialGeometry
