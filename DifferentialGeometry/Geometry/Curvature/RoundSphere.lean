import DifferentialGeometry.Geometry.Curvature.Sphere.ConstCurvature
import DifferentialGeometry.Geometry.Curvature.Metric.ConstantRicci
import DifferentialGeometry.Geometry.Curvature.MetricScaling

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature

namespace Poincare.Geometry.Curvature

theorem ricciTensor_roundSphere
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    (x : Metric.sphere (0 : E) 1) (v w : TangentSpace (𝓡 n) x) :
    ricciTensor (roundMetric (E := E) (n := n)) x v w =
      ((n : ℝ) - 1) * (roundMetric (E := E) (n := n)).inner x v w := by
  by_cases hn : n = 0
  · subst n
    have hv : v = 0 := by
      let : Subsingleton (TangentSpace (𝓡 0) x) :=
        inferInstanceAs (Subsingleton (EuclideanSpace ℝ (Fin 0)))
      exact Subsingleton.elim _ _
    simp [hv]
  · let : NeZero n := ⟨hn⟩
    let : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
      rw [finrank_euclideanSpace_fin]
      infer_instance
    have h := ricci_of_op (roundMetric (E := E) (n := n)) x 1
      (fun X Y Z ↦ by simpa only [one_smul] using round_riemann_one x X Y Z) v w
    simpa only [finrank_euclideanSpace_fin, mul_one] using h

theorem ricciTensor_scaledRoundSphere
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    (c : ℝ) (hc : 0 < c) (x : Metric.sphere (0 : E) 1)
    (v w : TangentSpace (𝓡 n) x) :
    ricciTensor (scaleMetric c hc (roundMetric (E := E) (n := n))) x v w =
      (((n : ℝ) - 1) / c) *
        (scaleMetric c hc (roundMetric (E := E) (n := n))).inner x v w := by
  rw [ricciTensor_scaleMetric, ricciTensor_roundSphere, scaleMetric_inner]
  field_simp

end Poincare.Geometry.Curvature
