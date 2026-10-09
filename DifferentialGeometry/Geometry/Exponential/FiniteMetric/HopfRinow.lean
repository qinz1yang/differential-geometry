import DifferentialGeometry.Geometry.Exponential.FiniteMetric.Segments
import DifferentialGeometry.Geometry.Metric.Path.RiemannianHopfRinow
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.Completeness

/-!
# Hopf–Rinow for a complete finite metric (CM2.b)

For a complete `C^{r+1}` metric, `r ≥ 2`: any two points are joined by a radial geodesic which is a
metric segment (`exists_unit_segment_expMap`), and `hopfRinow_finite` (properness, completeness of
the geodesic flow, minimizing radial geodesics). The metric-space form lives in
`Topology/MetricSpace/HopfRinow.lean`, the smooth form in `Geometry/Comparison/HopfRinow/`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Manifold Metric
open scoped Manifold ContDiff Topology ENNReal

namespace Bundle.ContMDiffRiemannianMetric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}
  (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))

/-! ## CM2.b: Hopf–Rinow for a complete finite metric -/

section HopfRinow

variable [NeZero (Module.finrank ℝ E)]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]

/-- **CM2.b (minimizing geodesics), segment form.** Any two points of a complete finite metric are
joined by the radial geodesic `t ↦ exp_x (t u)`, `u` a unit vector, which is a segment on
`[0, d(x, y)]`. -/
theorem exists_unit_segment_expMap (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (x y : M) :
    ∃ u : E, g.inner x u u = 1 ∧
      (∀ s ∈ Icc 0 (dist x y), ∀ t ∈ Icc 0 (dist x y),
        dist (g.expMap (⟨x, s • u⟩ : TangentBundle I M))
          (g.expMap (⟨x, t • u⟩ : TangentBundle I M)) = |s - t|) ∧
      g.expMap (⟨x, dist x y • u⟩ : TangentBundle I M) = y := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  obtain ⟨c, hc0, hcd, hseg⟩ := Manifold.exists_unit_speed_segment_of_isRiemannianManifold I x y
  obtain ⟨u, hu, hflow⟩ := exists_geodesicFlow_eq_of_segment g hr hnorm hseg
  subst hc0
  have hexp : ∀ t ∈ Icc 0 (dist (c 0) y), g.expMap (⟨c 0, t • u⟩ : TangentBundle I M) = c t :=
    fun t ht => (g.expMap_smul_eq_proj_geodesicFlow hr1 (c 0) u t (hflow t ht).1).trans
      (hflow t ht).2.symm
  refine ⟨u, hu, fun s hs t ht => ?_, ?_⟩
  · rw [hexp s hs, hexp t ht]
    exact hseg s hs t ht
  · rw [hexp _ ⟨dist_nonneg, le_rfl⟩]
    exact hcd

/-- **CM2.b, Hopf–Rinow for a complete finite metric** (frozen statement). -/
theorem hopfRinow_finite (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))) :
    ProperSpace M ∧ g.geodesicFlowDomain = univ ∧
      ∀ x y : M, ∃ u : E, g.inner x u u = 1 ∧
        ∀ t ∈ Icc 0 (dist x y), dist x (g.expMap (⟨x, t • u⟩ : TangentBundle I M)) = t ∧
          g.expMap (⟨x, dist x y • u⟩ : TangentBundle I M) = y := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  refine ⟨Manifold.properSpace_of_isRiemannianManifold I,
    geodesicFlowDomain_eq_univ g hr hnorm, fun x y => ?_⟩
  obtain ⟨u, hu, hseg, hy⟩ := exists_unit_segment_expMap g hr hnorm x y
  have h0 : g.expMap (⟨x, (0 : ℝ) • u⟩ : TangentBundle I M) = x := by
    rw [zero_smul]
    exact g.expMap_zero hr1 x
  refine ⟨u, hu, fun t ht => ⟨?_, hy⟩⟩
  have h := hseg 0 ⟨le_rfl, dist_nonneg⟩ t ht
  rw [h0, zero_sub, abs_neg, abs_of_nonneg ht.1] at h
  exact h

end HopfRinow

end Bundle.ContMDiffRiemannianMetric
