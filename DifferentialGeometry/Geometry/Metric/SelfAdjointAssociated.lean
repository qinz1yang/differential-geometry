import DifferentialGeometry.Geometry.LieGroup.Representation.SelfAdjoint
import DifferentialGeometry.Bundle.Associated.Topology

noncomputable section

namespace LinearIsometryEquiv

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

private local instance selfAdjointNormedAddCommGroupV :
    NormedAddCommGroup (selfAdjoint.submodule ℝ (V →L[ℝ] V)) :=
  (selfAdjoint.submodule ℝ (V →L[ℝ] V)).normedAddCommGroup
private local instance selfAdjointNormedSpaceV :
    NormedSpace ℝ (selfAdjoint.submodule ℝ (V →L[ℝ] V)) :=
  (selfAdjoint.submodule ℝ (V →L[ℝ] V)).normedSpace
private local instance selfAdjointNormedAddCommGroupW :
    NormedAddCommGroup (selfAdjoint.submodule ℝ (W →L[ℝ] W)) :=
  (selfAdjoint.submodule ℝ (W →L[ℝ] W)).normedAddCommGroup
private local instance selfAdjointNormedSpaceW :
    NormedSpace ℝ (selfAdjoint.submodule ℝ (W →L[ℝ] W)) :=
  (selfAdjoint.submodule ℝ (W →L[ℝ] W)).normedSpace

private def selfAdjointAssociated : (selfAdjoint.submodule ℝ (V →L[ℝ] V)) →L[ℝ]
    ((V ≃ₗᵢ[ℝ] W) →ₑ[(ContRepresentation.selfAdjointConjugation (W := W)).toRepresentation]
      selfAdjoint.submodule ℝ (W →L[ℝ] W)) where
  toFun A :=
    { toFun := fun p => ⟨p.conjStarAlgEquiv (A : V →L[ℝ] V), A.property.map p.conjStarAlgEquiv⟩
      map_smul' := by intro g p; ext w; rfl }
  map_add' A B := by
    ext p w
    change p ((A : V →L[ℝ] V) (p.symm w) + (B : V →L[ℝ] V) (p.symm w)) = _
    exact p.map_add _ _
  map_smul' c A := by
    ext p w
    change p (c • (A : V →L[ℝ] V) (p.symm w)) = _
    exact p.map_smul c _
  cont := by
    apply MulActionHom.continuous_iff.mpr
    intro p
    apply continuous_induced_rng.mpr
    exact p.toContinuousLinearEquiv.conjContinuousAlgEquiv.continuous.comp continuous_subtype_val

def selfAdjointAssociatedEquiv [Nonempty (V ≃ₗᵢ[ℝ] W)] :
    (selfAdjoint.submodule ℝ (V →L[ℝ] V)) ≃L[ℝ]
      ((V ≃ₗᵢ[ℝ] W) →ₑ[(ContRepresentation.selfAdjointConjugation (W := W)).toRepresentation]
        selfAdjoint.submodule ℝ (W →L[ℝ] W)) where
  __ := selfAdjointAssociated
  continuous_toFun := selfAdjointAssociated.continuous
  invFun f :=
    let p := Classical.choice (inferInstance : Nonempty (V ≃ₗᵢ[ℝ] W))
    ⟨p.symm.conjStarAlgEquiv (f p), (f p).property.map p.symm.conjStarAlgEquiv⟩
  left_inv A := by
    apply Subtype.ext
    ext v
    let p := Classical.choice (inferInstance : Nonempty (V ≃ₗᵢ[ℝ] W))
    change p.symm (p ((A : V →L[ℝ] V) (p.symm (p v)))) = (A : V →L[ℝ] V) v
    rw [p.symm_apply_apply, p.symm_apply_apply]
  right_inv f := by
    ext q w
    let p := Classical.choice (inferInstance : Nonempty (V ≃ₗᵢ[ℝ] W))
    have h := MulActionSemiHomClass.map_smulₛₗ f (q /ₛ p) p
    simp only [sdiv_smul] at h
    have hv := congrArg (fun A : selfAdjoint.submodule ℝ (W →L[ℝ] W) =>
      (A : W →L[ℝ] W) w) h
    exact hv.symm
  continuous_invFun := by
    let p := Classical.choice (inferInstance : Nonempty (V ≃ₗᵢ[ℝ] W))
    apply continuous_induced_rng.mpr
    exact p.symm.toContinuousLinearEquiv.conjContinuousAlgEquiv.continuous.comp
      (continuous_subtype_val.comp (MulActionHom.continuous_eval p))

theorem selfAdjointAssociatedEquiv_apply [Nonempty (V ≃ₗᵢ[ℝ] W)]
    (A : selfAdjoint.submodule ℝ (V →L[ℝ] V)) (p : V ≃ₗᵢ[ℝ] W) :
    selfAdjointAssociatedEquiv A p =
      ⟨p.conjStarAlgEquiv (A : V →L[ℝ] V), A.property.map p.conjStarAlgEquiv⟩ := rfl

theorem selfAdjointAssociatedEquiv_symm_apply [Nonempty (V ≃ₗᵢ[ℝ] W)]
    (f : (V ≃ₗᵢ[ℝ] W) →ₑ[(ContRepresentation.selfAdjointConjugation (W := W)).toRepresentation]
      selfAdjoint.submodule ℝ (W →L[ℝ] W)) (p : V ≃ₗᵢ[ℝ] W) :
    selfAdjointAssociatedEquiv.symm f =
      ⟨p.symm.conjStarAlgEquiv (f p : W →L[ℝ] W), (f p).property.map p.symm.conjStarAlgEquiv⟩ := by
  have h := congrArg (fun q => q p)
    ((selfAdjointAssociatedEquiv (V := V) (W := W)).apply_symm_apply f)
  apply Subtype.ext
  ext v
  have hv := congrArg (fun A : selfAdjoint.submodule ℝ (W →L[ℝ] W) =>
    p.symm ((A : W →L[ℝ] W) (p v))) h
  simpa only [selfAdjointAssociatedEquiv_apply, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_symm] using hv

end LinearIsometryEquiv
