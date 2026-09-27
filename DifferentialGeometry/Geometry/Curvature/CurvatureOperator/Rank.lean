import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Endomorphism

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance (x : M) :
    FiniteDimensional ℝ (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) :=
  (ContinuousAlternatingMap.elementaryCovectorBasis (k := 2)
    (Module.finBasis ℝ (TangentSpace I x))).finiteDimensional_of_finite

theorem curvatureOperatorImageAt_finrank_eq_of_pos
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (hpos : ∀ w : TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ,
      w ≠ 0 → 0 < (twoFormMetricData g x).inner
        (curvatureOperatorEndomorphismAt g x A w) w) :
    Module.finrank ℝ (curvatureOperatorImageAt g x A) =
      (Module.finrank ℝ E).choose 2 := by
  have hzero (w : TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ)
      (hw : curvatureOperatorEndomorphismAt g x A w = 0) : w = 0 := by
    by_contra hne
    have h := hpos w hne
    rw [hw] at h
    simp only [MetricFiberData.inner, map_zero, LinearMap.zero_apply] at h
    exact (lt_irrefl 0) h
  have hinj : Function.Injective (curvatureOperatorEndomorphismAt g x A) := by
    intro u v huv
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, huv, sub_self]
  rw [curvatureOperatorImageAt_eq_range, LinearMap.finrank_range_of_inj hinj,
    ContinuousAlternatingMap.finrank_continuousAlternatingMap]
  rfl

end DifferentialGeometry.Geometry.Curvature
