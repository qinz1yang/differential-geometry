import DifferentialGeometry.Geometry.Curvature.Positive



noncomputable section
open Bundle Manifold
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature

namespace Poincare.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


theorem sectional_contraction_smul_pair (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) (a b : ℝ) :
    metricRm04StandardAt g x (a • v) (b • w) (b • w) (a • v) =
      a ^ 2 * b ^ 2 * metricRm04StandardAt g x v w w v := by
  have h := (metricRm04At g x).map_smul_univ ![a, b, b, a] (vec4 v w w v)
  have hv : (fun i : Fin 4 => ![a, b, b, a] i • vec4 v w w v i) =
      vec4 (a • v) (b • w) (b • w) (a • v) := by
    funext i
    fin_cases i <;> rfl
  rw [hv] at h
  change metricRm04StandardAt g x (a • v) (b • w) (b • w) (a • v) = _ at h
  rw [h]
  simp only [Fin.prod_univ_four]
  change (a * b * b * a) * metricRm04StandardAt g x v w w v = _
  ring

end Poincare.Geometry
