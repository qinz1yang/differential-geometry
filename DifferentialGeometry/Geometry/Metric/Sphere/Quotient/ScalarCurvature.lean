import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.Descent
import DifferentialGeometry.Geometry.Curvature.Metric.ConstantRicci
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross

noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.RoundSphereQuotient

open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)] [NeZero n]

theorem gQuot_scalar (D : RoundSphereQuotient E n) (x : D.Q) :
    metricScalarAt (I := 𝓡 n) D.gQuot x = (n : ℝ) * ((n : ℝ) - 1) := by
  let _ : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :=
    ⟨by simpa only [finrank_euclideanSpace_fin] using (NeZero.ne n)⟩
  obtain ⟨b, hb⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis D.gQuot x
  rw [metricScalarAt_eq_orthonormal_trace D.gQuot x b hb]
  have hRic := ricci_of_sec D.gQuot 1
    (fun y v w => by simpa only [one_mul] using D.gQuot_sectional_one y v w)
  simp only [hRic, hb, if_true, finrank_euclideanSpace_fin, mul_one]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    exact finrank_euclideanSpace_fin
  rw [hdim]

end DifferentialGeometry.Geometry.RoundSphereQuotient
