import DifferentialGeometry.Geometry.Comparison.FiniteSoul.TotallyConvex
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.HopfRinow

/-!
# Segments inside totally convex sets of a complete finite metric

* `IsTotallyConvexFinite.expMap_mem`: a radial arc `s ↦ exp_x (s u)`, `s ∈ [0, ℓ]`, with both
  endpoints in a totally convex `C` stays in `C` (any `u`).
* `IsTotallyConvexFinite.exists_unit_segment_mem`: two points of `C` are joined by a unit-speed
  segment (CM-H's Hopf–Rinow segment) lying in `C`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

omit [NeZero (Module.finrank ℝ E)] in
/-- A radial arc with both endpoints in a totally convex set stays in it. -/
theorem IsTotallyConvexFinite.expMap_mem
    {g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _)}
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hC : IsTotallyConvexFinite g C) {x : M} {u : E} {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hx : x ∈ C) (hy : g.expMap (⟨x, ℓ • u⟩ : TangentBundle I M) ∈ C) :
    ∀ s ∈ Icc 0 ℓ, g.expMap (⟨x, s • u⟩ : TangentBundle I M) ∈ C := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ :=
    Bundle.ContMDiffRiemannianMetric.geodesicFlowDomain_eq_univ g hr hnorm
  have hflow : ∀ τ : ℝ, g.expMap (⟨x, τ • u⟩ : TangentBundle I M) =
      (g.geodesicFlow (⟨x, u⟩ : TangentBundle I M) τ).proj := fun τ =>
    g.expMap_smul_eq_proj_geodesicFlow hr1 x u τ (by rw [hD]; exact mem_univ _)
  intro s hs
  rw [hflow]
  exact hC _ ℓ hℓ hx (by rw [← hflow]; exact hy) s hs

/-- Two points of a totally convex set are joined by a unit-speed segment lying in it. -/
theorem IsTotallyConvexFinite.exists_unit_segment_mem
    {g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _)}
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hC : IsTotallyConvexFinite g C) {x y : M} (hx : x ∈ C) (hy : y ∈ C) :
    ∃ u : E, g.inner x u u = 1 ∧
      (∀ s ∈ Icc 0 (dist x y), ∀ t ∈ Icc 0 (dist x y),
        dist (g.expMap (⟨x, s • u⟩ : TangentBundle I M))
          (g.expMap (⟨x, t • u⟩ : TangentBundle I M)) = |s - t|) ∧
      g.expMap (⟨x, dist x y • u⟩ : TangentBundle I M) = y ∧
      ∀ s ∈ Icc 0 (dist x y), g.expMap (⟨x, s • u⟩ : TangentBundle I M) ∈ C := by
  obtain ⟨u, hu, hseg, hend⟩ :=
    Bundle.ContMDiffRiemannianMetric.exists_unit_segment_expMap g hr hnorm x y
  exact ⟨u, hu, hseg, hend, hC.expMap_mem hr hnorm dist_nonneg hx (by rw [hend]; exact hy)⟩

end DifferentialGeometry.Geometry.FiniteSoul
