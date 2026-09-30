import DifferentialGeometry.Tensor.RSTensor.Defs

noncomputable section

namespace DifferentialGeometry.Tensor0SBundle.Tensor0SSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

noncomputable def reindexContinuousLinearMap (d : ℕ) (σ : Equiv.Perm (Fin d)) (x : M) :
    Tensor0SBundle.Tensor0SSpace d I x →L[𝕜] Tensor0SBundle.Tensor0SSpace d I x :=
  (Tensor0SBundle.tensor0SSpaceContinuousLinearEquiv (I := I) d x).symm.toContinuousLinearMap.comp
    (((ContinuousMultilinearMap.domDomCongrₗᵢ 𝕜 E 𝕜
          σ).toContinuousLinearEquiv.toContinuousLinearMap).comp
      (Tensor0SBundle.tensor0SSpaceContinuousLinearEquiv (I := I) d x).toContinuousLinearMap)

theorem reindexContinuousLinearMap_apply (d : ℕ) (σ : Equiv.Perm (Fin d)) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace d I x) :
    reindexContinuousLinearMap (I := I) d σ x D =
      Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := 𝕜) (I := I) (x := x)
        (ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SBundle.Tensor0SSpace.toModel D)) := by
  rw [reindexContinuousLinearMap]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rfl

end DifferentialGeometry.Tensor0SBundle.Tensor0SSpace
