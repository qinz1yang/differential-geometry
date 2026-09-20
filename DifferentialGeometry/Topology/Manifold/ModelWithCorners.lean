import Mathlib.Geometry.Manifold.Diffeomorph
namespace ModelWithCorners

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H : Type*} [TopologicalSpace H]

@[simp] theorem transContinuousLinearEquiv_trans (I : ModelWithCorners 𝕜 E H) (e : E ≃L[𝕜] F) (f : F ≃L[𝕜] G) :
    (I.transContinuousLinearEquiv e).transContinuousLinearEquiv f =
      I.transContinuousLinearEquiv (e.trans f) := by
  ext x <;> simp [transContinuousLinearEquiv, PartialEquiv.trans]

@[simp] theorem transContinuousLinearEquiv_refl (I : ModelWithCorners 𝕜 E H) :
    I.transContinuousLinearEquiv (ContinuousLinearEquiv.refl 𝕜 E) = I := by
  ext x <;> simp [transContinuousLinearEquiv, PartialEquiv.trans]

theorem transContinuousLinearEquiv_symm (I : ModelWithCorners 𝕜 E H) (e : E ≃L[𝕜] F) :
    (I.transContinuousLinearEquiv e).transContinuousLinearEquiv e.symm = I := by
  ext x <;> simp

theorem isManifold_transContinuousLinearEquiv_iff
    (I : ModelWithCorners 𝕜 E H) (e : E ≃L[𝕜] F)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] (n : WithTop ℕ∞) :
    IsManifold (I.transContinuousLinearEquiv e) n M ↔ IsManifold I n M := by
  constructor
  · intro h
    let _ := h
    have h' : IsManifold ((I.transContinuousLinearEquiv e).transContinuousLinearEquiv e.symm) n M :=
      inferInstance
    simpa only [transContinuousLinearEquiv_symm] using h'
  · intro h
    let _ := h
    infer_instance

instance boundaryless_transContinuousLinearEquiv
    (I : ModelWithCorners 𝕜 E H) [I.Boundaryless] (e : E ≃L[𝕜] F) :
    (I.transContinuousLinearEquiv e).Boundaryless where
  range_eq_univ := by
    rw [I.transContinuousLinearEquiv_range, I.range_eq_univ, Set.image_univ]
    exact e.surjective.range_eq

end ModelWithCorners
