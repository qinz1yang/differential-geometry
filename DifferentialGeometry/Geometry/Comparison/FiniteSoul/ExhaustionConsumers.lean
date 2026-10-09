import DifferentialGeometry.Geometry.Comparison.FiniteSoul.RayExhaustionConvex
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.TotallyConvexSegments

/-!
# Consumers of the convex exhaustion (S-DEF / S-BUS)

* `exists_isCompact_isTotallyConvexFinite_superset`: in a complete finite metric with `sec ≥ 0`,
  every compact set lies in a compact totally convex set (a sublevel of `rayExhaustion`).
* `exists_isCompact_isTotallyConvexFinite_superset_of_C3`: the same for a `C³` metric (`r = 2`).
* `IsTotallyConvexFinite.isPreconnected_of_finite`: a totally convex set of a complete finite
  metric is preconnected (segments stay inside).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.FiniteSoul

open DifferentialGeometry.Geometry.Topology (rayExhaustion lipschitzWith_rayExhaustion)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- Every compact set lies in a compact totally convex set (a sublevel of the convex
exhaustion). -/
theorem exists_isCompact_isTotallyConvexFinite_superset
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {K : Set M} (hK : IsCompact K) :
    ∃ C : Set M, IsCompact C ∧ IsTotallyConvexFinite g C ∧ K ⊆ C := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨o, -⟩
  · exact ⟨∅, isCompact_empty, isTotallyConvexFinite_empty g, subset_rfl⟩
  obtain ⟨t, ht⟩ := hK.bddAbove_image (lipschitzWith_rayExhaustion o).continuous.continuousOn
  refine ⟨{x | rayExhaustion o x ≤ t},
    (isCompact_isTotallyConvexFinite_rayExhaustion_sublevel g hr hnorm hsec o t).1,
    (isCompact_isTotallyConvexFinite_rayExhaustion_sublevel g hr hnorm hsec o t).2,
    fun x hx => ht (mem_image_of_mem _ hx)⟩

/-- The `C³` case (`r = 2`). -/
theorem exists_isCompact_isTotallyConvexFinite_superset_of_C3
    (g : ContMDiffRiemannianMetric I (((2 : ℕ∞) : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {K : Set M} (hK : IsCompact K) :
    ∃ C : Set M, IsCompact C ∧ IsTotallyConvexFinite g C ∧ K ⊆ C :=
  exists_isCompact_isTotallyConvexFinite_superset g le_rfl hnorm hsec hK

omit [SigmaCompactSpace M] in
/-- A totally convex set of a complete finite metric is preconnected. -/
theorem IsTotallyConvexFinite.isPreconnected_of_finite
    {g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _)}
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hC : IsTotallyConvexFinite g C) : IsPreconnected C := by
  refine isPreconnected_of_forall_pair fun x hx y hy => ?_
  obtain ⟨u, -, hseg, hend, hmem⟩ := hC.exists_unit_segment_mem hr hnorm hx hy
  refine ⟨(fun s => g.expMap (⟨x, s • u⟩ : TangentBundle I M)) '' Icc 0 (dist x y), ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact hmem s hs
  · refine ⟨0, left_mem_Icc.2 dist_nonneg, ?_⟩
    change g.expMap (⟨x, (0 : ℝ) • u⟩ : TangentBundle I M) = x
    rw [zero_smul]
    exact g.expMap_zero (one_le_two.trans hr) x
  · exact ⟨dist x y, right_mem_Icc.2 dist_nonneg, hend⟩
  · refine (isPreconnected_Icc).image _ ?_
    refine Metric.continuousOn_iff.2 fun b hb ε hε => ⟨ε, hε, fun a ha hab => ?_⟩
    exact (hseg a ha b hb).trans_lt (by rw [← Real.dist_eq]; exact hab)

end DifferentialGeometry.Geometry.FiniteSoul
