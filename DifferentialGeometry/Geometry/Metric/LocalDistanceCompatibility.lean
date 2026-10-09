import DifferentialGeometry.Geometry.Metric.Path.Variation
import DifferentialGeometry.Topology.MetricSpace.IntrinsicLipschitz

set_option autoImplicit false

noncomputable section
open Bundle Manifold Set
open scoped ContDiff Topology ENNReal NNReal

namespace Manifold

theorem isRiemannianManifold_of_local_edist_eq
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]
    (hintrinsic : ∀ x y : M, Metric.intrinsicEDist x y = edist x y)
    (hlocal : ∀ p : M, ∃ V ∈ 𝓝 p, ∀ x ∈ V, ∀ y ∈ V,
      riemannianEDist I x y = edist x y) : IsRiemannianManifold I M := by
  let original := ‹PseudoEMetricSpace M›
  let native : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace M := original
  have hforward (x y : M) : riemannianEDist I x y ≤ edist x y := by
    have h := @Metric.edist_map_le_intrinsicEDist_of_locally_nonexpanding
      M M original native id (by
        intro p
        obtain ⟨V, hV, heq⟩ := hlocal p
        refine ⟨V, hV, ?_⟩
        intro a ha b hb
        change riemannianEDist I a b ≤ (1 : ℝ≥0∞) * edist a b
        rw [one_mul, heq a ha b hb]) x y
    change riemannianEDist I x y ≤ @Metric.intrinsicEDist M original x y at h
    exact h.trans_eq (hintrinsic x y)
  have hbackward (x y : M) : edist x y ≤ riemannianEDist I x y := by
    have h := @Metric.edist_map_le_intrinsicEDist_of_locally_nonexpanding
      M M native original id (by
        intro p
        obtain ⟨V, hV, heq⟩ := hlocal p
        refine ⟨V, hV, ?_⟩
        intro a ha b hb
        change edist a b ≤ (1 : ℝ≥0∞) * riemannianEDist I a b
        rw [one_mul, heq a ha b hb]) x y
    have hnative : @Metric.intrinsicEDist M native x y = riemannianEDist I x y := by
      let : PseudoEMetricSpace M := native
      let : IsRiemannianManifold I M := ⟨fun _ _ => rfl⟩
      exact intrinsicEDist_eq_riemannianEDist (I := I) x y
    simpa only [id_eq, hnative] using h
  exact ⟨fun x y => le_antisymm (hbackward x y) (hforward x y)⟩

end Manifold
