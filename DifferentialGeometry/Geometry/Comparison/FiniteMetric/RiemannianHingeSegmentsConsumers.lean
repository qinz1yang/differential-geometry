import DifferentialGeometry.Geometry.Comparison.FiniteMetric.RiemannianHingeSegments

/-!
# Consumer of the segment-input hinge (CM5.b, LFR21 G3)

The three-point hinge for a complete `C³` metric (`r = 2`, the lowest covered order) with
`sec ≥ 0`, and its cosine form: `g_o(u, v) ≤ cos θ̃`, `θ̃` the comparison angle at `o`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.FiniteComparison

open DifferentialGeometry.Geometry.Comparison.Toponogov

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

/-- Three-point hinge for a complete `C³` metric with `sec ≥ 0`, cosine form: the unit directions
`u, v` of minimizing geodesics from `o` to `y, z` satisfy `g_o(u, v) ≤ cos θ̃(o; y, z)`. -/
theorem inner_le_cos_comparisonAngle_of_points_C3
    (g : ContMDiffRiemannianMetric I 3 E (TangentSpace I : M → Type _))
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {o y z : M} (hy : y ≠ o) (hz : z ≠ o) :
    ∃ u v : E, g.inner o u u = 1 ∧ g.inner o v v = 1 ∧
      g.expMap (⟨o, dist o y • u⟩ : TangentBundle I M) = y ∧
      g.expMap (⟨o, dist o z • v⟩ : TangentBundle I M) = z ∧
      g.inner o u v ≤ Real.cos (comparisonAngle (dist o y) (dist o z) (dist y z)) := by
  obtain ⟨u, v, hu, hv, hyu, hzv, h⟩ :=
    comparisonAngle_le_arccos_of_points_finite (r := 2) g le_rfl hnorm hsec hy hz
  refine ⟨u, v, hu, hv, hyu, hzv, ?_⟩
  have hcs := DifferentialGeometry.Geometry.Collapse.abs_finite_inner_le g o u v
  rw [hu, hv, Real.sqrt_one, mul_one] at hcs
  obtain ⟨hlo, hhi⟩ := abs_le.mp hcs
  calc g.inner o u v = Real.cos (Real.arccos (g.inner o u v)) := (Real.cos_arccos hlo hhi).symm
    _ ≤ Real.cos (comparisonAngle (dist o y) (dist o z) (dist y z)) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (comparisonAngle_mem_Icc _ _ _).1
        (Real.arccos_le_pi _) h

end DifferentialGeometry.Geometry.FiniteComparison
