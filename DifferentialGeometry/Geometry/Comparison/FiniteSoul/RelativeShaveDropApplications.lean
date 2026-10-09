import DifferentialGeometry.Geometry.Comparison.FiniteSoul.RelativeShaveDrop

/-!
# Consumers of DROP (CMS3-REL, G3)

* `one_le_maxSliceDimOfOrder_of_relBoundary_nonempty`: a compact totally convex set with nonempty
  relative boundary has relative dimension `≥ 1` (so points have empty relative boundary).
* `maxSliceDimOfOrder_argmax_add_one_le_finrank`: the argmax set of one shaving step has relative
  dimension at most `dim - 1`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- Nonempty relative boundary forces relative dimension `≥ 1`. -/
theorem one_le_maxSliceDimOfOrder_of_relBoundary_nonempty [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {C : Set M} (hCc : IsCompact C) (hconv : IsTotallyConvexFinite g C)
    (hB : (relBoundaryOfOrder I (r : ℕ∞ω) C).Nonempty) :
    1 ≤ maxSliceDimOfOrder I (r : ℕ∞ω) C := by
  obtain ⟨-, -, -, -, hlt⟩ := maxSliceDimOfOrder_argmax_lt g hr hnorm hsec hCc hconv hB
  omega

/-- One shaving step lands in relative dimension at most `dim - 1`. -/
theorem maxSliceDimOfOrder_argmax_add_one_le_finrank [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {C : Set M} (hCc : IsCompact C) (hconv : IsTotallyConvexFinite g C)
    (hB : (relBoundaryOfOrder I (r : ℕ∞ω) C).Nonempty) :
    maxSliceDimOfOrder I (r : ℕ∞ω)
        {x ∈ C | ∀ y ∈ C, infDist y (relBoundaryOfOrder I (r : ℕ∞ω) C) ≤
          infDist x (relBoundaryOfOrder I (r : ℕ∞ω) C)} + 1 ≤ Module.finrank ℝ E := by
  obtain ⟨-, -, -, -, hlt⟩ := maxSliceDimOfOrder_argmax_lt g hr hnorm hsec hCc hconv hB
  have hle : maxSliceDimOfOrder I (r : ℕ∞ω) C ≤ Module.finrank ℝ E := maxSliceDimOfOrder_le C
  omega

end DifferentialGeometry.Geometry.FiniteSoul

end
