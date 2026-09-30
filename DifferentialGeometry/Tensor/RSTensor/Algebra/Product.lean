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

namespace DifferentialGeometry.Tensor0SBundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

namespace Tensor0SModel

noncomputable def productContinuousLinearMap (p q : ℕ) :
    Tensor0SModel p 𝕜 E →L[𝕜]
      Tensor0SModel q 𝕜 E →L[𝕜] Tensor0SModel (p + q) 𝕜 E :=
  let uncurry :
      ContinuousMultilinearMap 𝕜 (fun _ : Fin p => E) (Tensor0SModel q 𝕜 E) →L[𝕜]
        Tensor0SModel (p + q) 𝕜 E :=
    ((ContinuousMultilinearMap.domDomCongrₗᵢ 𝕜 E 𝕜
        (finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q))).toContinuousLinearEquiv.toContinuousLinearMap).comp
      (ContinuousMultilinearMap.currySumEquiv 𝕜 (Fin p) (Fin q) E 𝕜).symm.toContinuousLinearEquiv.toContinuousLinearMap
  (ContinuousLinearMap.compL 𝕜 (Tensor0SModel q 𝕜 E)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin p => E) (Tensor0SModel q 𝕜 E))
      (Tensor0SModel (p + q) 𝕜 E) uncurry).comp
    (ContinuousMultilinearMap.smulRightL 𝕜 (fun _ : Fin p => E) (Tensor0SModel q 𝕜 E))

theorem productContinuousLinearMap_apply (p q : ℕ)
    (A : Tensor0SBundle.Tensor0SModel p 𝕜 E) (B : Tensor0SBundle.Tensor0SModel q 𝕜 E) :
    productContinuousLinearMap (E := E) p q A B =
      Bundle.continuousMultilinearMap.modelProduct (𝕜 := 𝕜) (F := E) p q A B := by
  rw [productContinuousLinearMap]
  rfl

end Tensor0SModel

namespace Tensor0SSpace

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

noncomputable def rightProductContinuousLinearMap {p q : ℕ} (x : M)
    (κ : Tensor0SBundle.Tensor0SSpace q I x) :
    Tensor0SBundle.Tensor0SSpace p I x →L[𝕜] Tensor0SBundle.Tensor0SSpace (p + q) I x :=
  (Tensor0SBundle.tensor0SSpaceContinuousLinearEquiv (I := I) (p + q)
      x).symm.toContinuousLinearMap.comp
    (((Tensor0SModel.productContinuousLinearMap (E := E) p q).flip
        (Tensor0SBundle.Tensor0SSpace.toModel κ)).comp
      (Tensor0SBundle.tensor0SSpaceContinuousLinearEquiv (I := I) p x).toContinuousLinearMap)

theorem rightProductContinuousLinearMap_apply {p q : ℕ} (x : M)
    (κ : Tensor0SBundle.Tensor0SSpace q I x) (D : Tensor0SBundle.Tensor0SSpace p I x) :
    rightProductContinuousLinearMap (I := I) x κ D =
      Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := 𝕜) (I := I) (x := x)
        (Bundle.continuousMultilinearMap.modelProduct (𝕜 := 𝕜) (F := E) p q
          (Tensor0SBundle.Tensor0SSpace.toModel D) (Tensor0SBundle.Tensor0SSpace.toModel κ)) := by
  rw [rightProductContinuousLinearMap]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.flip_apply]
  rw [Tensor0SModel.productContinuousLinearMap_apply]
  rfl

end Tensor0SSpace

end DifferentialGeometry.Tensor0SBundle
