import DifferentialGeometry.Geometry.Metric.Comparison.BallImage


open Bundle Filter Manifold Set
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.PartialDiffeomorph

theorem edist_map_le_mul_of_quad_le_on_closedEBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
    [PseudoEMetricSpace N] [RiemannianBundle (fun y : N => TangentSpace J y)]
    [IsRiemannianManifold J N]
    {n : WithTop ℕ∞} (Φ : PartialDiffeomorph I J M N n) (hn : 1 ≤ n)
    {x y : M} {rho C : ℝ}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric J N}
    (hgnorm : ∀ (z : M) (v : TangentSpace I z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner z v v)))
    (hhnorm : ∀ (z : N) (w : TangentSpace J z),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (h.inner z w w)))
    (hC : 0 ≤ C)
    (hsub : Metric.closedEBall x (ENNReal.ofReal rho) ⊆ Φ.source)
    (hquad : ∀ z ∈ Metric.closedEBall x (ENNReal.ofReal rho),
      ∀ v : TangentSpace I z,
        h.inner ((Φ : M → N) z)
          (mfderiv I J (Φ : M → N) z v) (mfderiv I J (Φ : M → N) z v) ≤
          C * g.inner z v v)
    (hxy : edist x y < ENNReal.ofReal rho) :
    edist ((Φ : M → N) x) ((Φ : M → N) y) ≤
      ENNReal.ofReal (Real.sqrt C) * edist x y := by
  have hfinite : edist x y ≠ ⊤ := ne_top_of_lt hxy
  have hrho : 0 < rho := ENNReal.ofReal_pos.mp (bot_le.trans_lt hxy)
  have hd : (edist x y).toReal < rho := by
    apply (ENNReal.ofReal_lt_ofReal_iff hrho).mp
    rwa [ENNReal.ofReal_toReal hfinite]
  have htend : Tendsto (fun r : ℝ => ENNReal.ofReal (Real.sqrt C * r))
      (𝓝[>] (edist x y).toReal)
      (𝓝 (ENNReal.ofReal (Real.sqrt C * (edist x y).toReal))) :=
    ((ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_id)).tendsto
      (edist x y).toReal).mono_left nhdsWithin_le_nhds
  have hbound : ∀ᶠ r : ℝ in 𝓝[>] (edist x y).toReal,
      edist ((Φ : M → N) x) ((Φ : M → N) y) ≤
        ENNReal.ofReal (Real.sqrt C * r) := by
    apply eventually_nhdsWithin_iff.mpr
    filter_upwards [eventually_lt_nhds hd] with r hrrho hdr
    have hr : 0 < r := ENNReal.toReal_nonneg.trans_lt hdr
    have hy : y ∈ Metric.eball x (ENNReal.ofReal r) := by
      rw [Metric.mem_eball, edist_comm, ← ENNReal.ofReal_toReal hfinite]
      exact (ENNReal.ofReal_lt_ofReal_iff hr).mpr hdr
    have himage := image_eball_subset_closedEBall_of_quad_le Φ hn
      hgnorm hhnorm hrrho.le hC hsub hquad (mem_image_of_mem (Φ : M → N) hy)
    simpa only [Metric.mem_closedEBall, edist_comm] using himage
  have hle := ge_of_tendsto htend hbound
  simpa only [ENNReal.ofReal_mul (Real.sqrt_nonneg C), ENNReal.ofReal_toReal hfinite]
    using hle

end DifferentialGeometry.PartialDiffeomorph
