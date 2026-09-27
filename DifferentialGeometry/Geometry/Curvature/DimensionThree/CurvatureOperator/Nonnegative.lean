import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Positivity

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff_sectional
    (g : SmoothRiemannianMetric I M) (x : M) (hdim : Module.finrank ℝ E = 3) :
    metricAlgebraicCurvatureTensorAt g x ∈ algebraicCurvatureOperatorNonnegativeCone (I := I) ↔
      ∀ v w : TangentSpace I x, 0 ≤ metricRm04StandardAt g x v w w v := by
  constructor
  · intro h v w
    have hq := mem_algebraicCurvatureOperatorNonnegativeCone.mp h 1
      (fun _ => 1) (fun _ => v) (fun _ => w)
    simpa only [algebraicCurvatureOperatorQuadraticEval, Fin.sum_univ_one, one_mul,
      metricAlgebraicCurvatureTensorAt_coe, metricRm04StandardAt] using hq
  · intro h
    apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
    intro n c v w
    obtain ⟨a, b, _hgram, hvalue⟩ :=
      DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.three_bivector_quadratic_realized
        g x hdim (metricAlgebraicCurvatureTensorAt g x) c v w
    rw [← hvalue]
    simpa only [metricAlgebraicCurvatureTensorAt_coe, metricRm04StandardAt] using h a b

end DifferentialGeometry.Geometry.Curvature
