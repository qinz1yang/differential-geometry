import Mathlib.Geometry.Manifold.Diffeomorph

open scoped ContDiff

namespace ModelWithCorners

variable {𝕜 E F H : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace H]

@[simp] theorem transContinuousLinearEquiv_symm
    (I : ModelWithCorners 𝕜 E H) (e : E ≃L[𝕜] F) :
    (I.transContinuousLinearEquiv e).transContinuousLinearEquiv e.symm = I := by
  ext x <;> simp [transContinuousLinearEquiv, PartialEquiv.trans_source]

end ModelWithCorners

namespace ContinuousLinearEquiv

variable {𝕜 E F H M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}

theorem isManifold_transContinuousLinearEquiv_iff (e : E ≃L[𝕜] F) :
    IsManifold (I.transContinuousLinearEquiv e) n M ↔ IsManifold I n M := by
  constructor
  · intro h
    let _ := h
    have hback : IsManifold
        ((I.transContinuousLinearEquiv e).transContinuousLinearEquiv e.symm) n M :=
      inferInstance
    simpa only [ModelWithCorners.transContinuousLinearEquiv_symm] using hback
  · intro h
    let _ := h
    infer_instance

end ContinuousLinearEquiv
