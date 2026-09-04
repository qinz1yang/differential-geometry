import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Tensor.Multilinear.Bundle.TensorProduct

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Tensor0SBundle.Tensor0SSpace

open Bundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

noncomputable def product {r s : ℕ} {x : M}
    (A : Tensor0SSpace r I x) (B : Tensor0SSpace s I x) :
    Tensor0SSpace (r + s) I x :=
  (tensor0SSpaceFiberContinuousLinearEquiv (I := I) (r + s) x).symm
    ((((tensor0SSpaceFiberContinuousLinearEquiv (I := I) r x A).smulRight
      (tensor0SSpaceFiberContinuousLinearEquiv (I := I) s x B)).uncurrySum).domDomCongr
        finSumFinEquiv)

@[simp]
theorem product_apply {r s : ℕ} {x : M}
    (A : Tensor0SSpace r I x) (B : Tensor0SSpace s I x)
    (v : Fin (r + s) → TangentSpace I x) :
    product A B v = A (v ∘ Fin.castAdd s) * B (v ∘ Fin.natAdd r) := by
  change
    ((((tensor0SSpaceFiberContinuousLinearEquiv (I := I) r x A).smulRight
      (tensor0SSpaceFiberContinuousLinearEquiv (I := I) s x B)).uncurrySum).domDomCongr
        finSumFinEquiv) v = _
  simp only [ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.smulRight_apply,
    tensor0SSpaceFiberContinuousLinearEquiv_apply_apply]
  rfl

end DifferentialGeometry.Tensor0SBundle.Tensor0SSpace
