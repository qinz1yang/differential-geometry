import DifferentialGeometry.Geometry.Collapse.SublevelCore.BufferedMapsAtScale
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Arity
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Composition

/-!
# Consumer of GAP A2: the identity maps of a model satisfy LC56 item (2)

For the constant sequence `M i = N`, `g_i = g` with the identity partial diffeomorphisms, the A1
hypothesis holds with `i₀ = 0` (the pullback of `g` on `B(n, r)` is `g|_{B(n, r)}`), and
`exists_shifted_buffered_maps_at_scale` gives at every scale `R > 0` the buffered data on
`U = B(n, 11R)`: restricted maps with source everything and `closedBall(n, 10R) ⊆ U`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

/-- The pullback of `g` by the identity on an open set is the restriction of `g`. -/
theorem pullbackMetricOn_refl {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold I ∞ N] [T2Space N] (g : SmoothRiemannianMetric I N)
    (U : TopologicalSpace.Opens N) :
    PartialDiffeomorph.pullbackMetricOn (DifferentialGeometry.PartialDiffeomorph.refl (I := I) N)
      U (subset_univ _) g = g.restrictOpen U := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  refine (PartialDiffeomorph.pullbackMetricOn_inner
    (DifferentialGeometry.PartialDiffeomorph.refl (I := I) N) U (subset_univ _) g x v w).trans ?_
  change g.inner (x : N) (mfderiv I I (id : N → N) (x : N) v)
    (mfderiv I I (id : N → N) (x : N) w) = _
  rw [mfderiv_id]
  rfl

/-- **Consumer of `exists_shifted_buffered_maps_at_scale`.** The identity maps of `N` satisfy the
A1 encoding of LC56 item (2); at every scale `R > 0` the restricted maps on `B(n, 11R)` have
source everything and `closedBall(n, 10R) ⊆ B(n, 11R)`. -/
theorem identity_buffered_maps_at_scale {N : Type*} [MetricSpace N] [ChartedSpace H N]
    [IsManifold I ∞ N] (g : SmoothRiemannianMetric I N) (n : N) {R : ℝ} (hR : 0 < R) :
    ∃ hU : Nonempty (⟨Metric.ball n (11 * R), Metric.isOpen_ball⟩ : TopologicalSpace.Opens N),
      ((openSubtypePartialDiffeomorph I _ hU).trans
        (DifferentialGeometry.PartialDiffeomorph.refl (I := I) N)).source = univ ∧
      Metric.closedBall n (10 * R) ⊆ Metric.ball n (11 * R) := by
  obtain ⟨i₀, -, hU, hsrc, -, -, hball⟩ := exists_shifted_buffered_maps_at_scale (M := fun _ => N)
    g (fun _ => g) n (fun _ => DifferentialGeometry.PartialDiffeomorph.refl (I := I) N)
    (fun r _ => ⟨0, fun _ => subset_univ _, fun C _ => by
      intro ε hε
      refine ⟨0, fun k _ => ?_⟩
      simp only [pullbackMetricOn_refl]
      rw [metricDerivNormSupOn_self]
      exact hε⟩) hR
  exact ⟨hU, hsrc i₀, hball⟩

end DifferentialGeometry.Geometry.Collapse
