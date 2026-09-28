import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricCongr
import DifferentialGeometry.Tensor.RSTensor.Functoriality.Pullback

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Tensor0SBundle

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

theorem tensor0SPullbackCLE_product
    {r s : Nat} {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor0SSpace r I y) (B : Tensor0SSpace s I y) :
    tensor0SPullbackCLE (I := I) (M := M) (r + s) e
        (Tensor0SSpace.product A B) =
      Tensor0SSpace.product
        (tensor0SPullbackCLE (I := I) (M := M) r e A)
        (tensor0SPullbackCLE (I := I) (M := M) s e B) := by
  apply tensor0SSpace_ext (r + s) x
  intro v
  simp only [tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply,
    Tensor0SSpace.product_apply]
  rfl

theorem inner0S_tensor0SPullbackCLE
    (gSource gTarget : SmoothRiemannianMetric I M) (x y : M) (s : Nat)
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (hiso : ∀ u v, gTarget.inner y (e u) (e v) =
      gSource.inner x u v)
    (A B : Tensor0SSpace s I y) :
    inner0S (I := I) gSource x s
        (tensor0SPullbackCLE (I := I) (M := M) s e A)
        (tensor0SPullbackCLE (I := I) (M := M) s e B) =
      inner0S (I := I) gTarget y s A B := by
  classical
  obtain ⟨basis, horth⟩ := exists_orthonormal_basis (I := I) gSource x
  let targetBasis := basis.map e
  have htarget : ∀ i j, gTarget.inner y (targetBasis i) (targetBasis j) =
      if i = j then (1 : Real) else 0 := by
    intro i j
    change gTarget.inner y (e (basis i)) (e (basis j)) = _
    rw [hiso, horth]
  rw [inner0S_identity_eq_sum (I := I) gSource x s basis
      (metricInverseInBasis_of_orthonormal (I := I) gSource basis horth),
    inner0S_identity_eq_sum (I := I) gTarget y s targetBasis
      (metricInverseInBasis_of_orthonormal (I := I) gTarget targetBasis htarget)]
  apply Finset.sum_congr rfl
  intro slots _
  simp only [component0S_apply, tensor0SPullbackCLE_apply,
    tensor0SPullbackCLM_apply]
  congr 2

end DifferentialGeometry.Tensor0SBundle
