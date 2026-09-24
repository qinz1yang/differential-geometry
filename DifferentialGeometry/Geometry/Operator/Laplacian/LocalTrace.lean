import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Laplacian


noncomputable section

namespace DifferentialGeometry.Geometry.Operator

open Set
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem laplacian_eq_sum_hessFun_of_contMDiffOn
    (g : SmoothRiemannianMetric I M) {f : M → Real} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn I 𝓘(Real, Real) ∞ f U)
    {x : M} (hx : x ∈ U) {n : Nat}
    (B : Module.Basis (Fin n) Real (TangentSpace I x))
    (hB : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : Real) else 0) :
    laplacian (I := I) (LeviCivita (I := I) g) g f x =
      ∑ i : Fin n, hessFun (I := I) g f x (B i) (B i) := by
  classical
  have hinv := metricInverseInBasis_of_orthonormal (I := I) g B hB
  rw [lap_eq_hess_on (I := I) g hU hf hx,
    metricTracePair0SAt_eq_sum_basis (I := I) g B _ hinv (hessTensorAt (I := I) g f x)]
  simp [identityInvMetric, diagonalInvMetric, hessTensorAt_apply]

end DifferentialGeometry.Geometry.Operator
