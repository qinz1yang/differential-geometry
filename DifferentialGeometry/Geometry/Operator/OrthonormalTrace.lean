import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Laplacian
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm

set_option autoImplicit false
noncomputable section
open Bundle Set DifferentialGeometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Operator

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] in
theorem inner_self_eq_sum_sq_of_orthonormalBasis
    (g : SmoothRiemannianMetric I M) (x : M) {n : ℕ}
    (B : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hB : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0)
    (u : TangentSpace I x) :
    g.inner x u u = ∑ i, (g.inner x u (B i)) ^ 2 := by
  classical
  have hinv := metricInverseInBasis_of_orthonormal g B hB
  have hr (i : Fin n) : B.repr u i = g.inner x u (B i) := by
    rw [basis_repr_eq_sum_inv_inner g x B _ hinv u i]
    simp [identityInvMetric, diagonalInvMetric]
  calc
    _ = g.inner x u (∑ i, B.repr u i • B i) := by rw [B.sum_repr u]
    _ = ∑ i, B.repr u i * g.inner x u (B i) := by
      rw [map_sum]
      simp_rw [map_smul, smul_eq_mul]
    _ = _ := by simp only [hr, pow_two]

theorem inner_gradFun_self_eq_sum_sq
    (g : SmoothRiemannianMetric I M) (F : M → ℝ) (x : M) {n : ℕ}
    (B : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hB : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    g.inner x (gradFun g F x) (gradFun g F x) =
      ∑ i, (mvfderiv I F x (B i)) ^ 2 := by
  rw [inner_self_eq_sum_sq_of_orthonormalBasis g x B hB]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun r : ℝ => r ^ 2) (inner_gradFun g F x (B i))

variable [I.Boundaryless] [T2Space M]

theorem laplacian_eq_sum_hessFun
    (g : SmoothRiemannianMetric I M) (F : M → ℝ) (hF : ContMDiff I 𝓘(ℝ) ∞ F)
    (x : M) {n : ℕ} (B : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hB : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    laplacian (LeviCivita g) g F x = ∑ i, hessFun g F x (B i) (B i) := by
  classical
  have hinv := metricInverseInBasis_of_orthonormal g B hB
  rw [lap_eq_hess_on g isOpen_univ hF.contMDiffOn (mem_univ x),
    metricTracePair0SAt_eq_sum_basis g B _ hinv (hessTensorAt g F x)]
  simp [identityInvMetric, diagonalInvMetric, hessTensorAt_apply]

end DifferentialGeometry.Geometry.Operator
