import Mathlib.Analysis.Convex.Cone.InnerDual

open Set
open scoped RealInnerProductSpace

namespace DifferentialGeometry.Analysis.InnerProductSpace

section

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem ProperCone.coe_map_continuousLinearEquiv
    (C : ProperCone ℝ E) (e : E ≃L[ℝ] F) :
    (C.map e.toContinuousLinearMap : Set F) = e '' C := by
  change closure (e '' (C : Set E)) = e '' C
  exact (e.toHomeomorph.isClosedMap (C : Set E) C.isClosed).closure_eq

theorem ProperCone.mem_map_continuousLinearEquiv_iff
    (C : ProperCone ℝ E) (e : E ≃L[ℝ] F) (y : F) :
    y ∈ C.map e.toContinuousLinearMap ↔ e.symm y ∈ C := by
  change y ∈ (C.map e.toContinuousLinearMap : Set F) ↔ e.symm y ∈ C
  rw [show (C.map e.toContinuousLinearMap : Set F) = e '' C from
    ProperCone.coe_map_continuousLinearEquiv C e]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hy
    exact ⟨e.symm y, hy, e.apply_symm_apply y⟩

@[simp]
theorem ProperCone.map_continuousLinearEquiv_symm
    (C : ProperCone ℝ E) (e : E ≃L[ℝ] F) :
    (C.map e.toContinuousLinearMap).map e.symm.toContinuousLinearMap = C := by
  apply ProperCone.ext
  intro x
  rw [ProperCone.mem_map_continuousLinearEquiv_iff]
  rw [ProperCone.mem_map_continuousLinearEquiv_iff]
  simp

end

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem LinearIsometryEquiv.mapsTo_innerDual
    (e : E ≃ₗᵢ[ℝ] F) {C : Set E} :
    MapsTo e (ProperCone.innerDual C) (ProperCone.innerDual (e '' C)) := by
  intro y hy
  change ∀ ⦃x : F⦄, x ∈ e '' C → 0 ≤ ⟪x, e y⟫
  rintro _ ⟨x, hx, rfl⟩
  simpa only [e.inner_map_map] using hy hx

theorem LinearIsometryEquiv.image_innerDual
    (e : E ≃ₗᵢ[ℝ] F) (C : Set E) :
    e '' ProperCone.innerDual C = ProperCone.innerDual (e '' C) := by
  apply Set.Subset.antisymm
  · exact (LinearIsometryEquiv.mapsTo_innerDual e).image_subset
  intro y hy
  have hmap := LinearIsometryEquiv.mapsTo_innerDual e.symm hy
  refine ⟨e.symm y, ?_, by simp⟩
  simpa using hmap

theorem ProperCone.innerDual_map_linearIsometryEquiv
    (C : ProperCone ℝ E) (e : E ≃ₗᵢ[ℝ] F) :
    ProperCone.innerDual
        (C.map e.toContinuousLinearEquiv.toContinuousLinearMap : Set F) =
      (ProperCone.innerDual (C : Set E)).map
        e.toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ProperCone.ext
  intro y
  have hC :
      (C.map e.toContinuousLinearEquiv.toContinuousLinearMap : Set F) =
        e '' (C : Set E) :=
    ProperCone.coe_map_continuousLinearEquiv C e.toContinuousLinearEquiv
  have hdual :
      ((ProperCone.innerDual (C : Set E)).map
          e.toContinuousLinearEquiv.toContinuousLinearMap : Set F) =
        e '' ProperCone.innerDual (C : Set E) :=
    ProperCone.coe_map_continuousLinearEquiv
      (ProperCone.innerDual (C : Set E)) e.toContinuousLinearEquiv
  change y ∈ ProperCone.innerDual
      (C.map e.toContinuousLinearEquiv.toContinuousLinearMap : Set F) ↔
    y ∈ ((ProperCone.innerDual (C : Set E)).map
      e.toContinuousLinearEquiv.toContinuousLinearMap : Set F)
  rw [hC, hdual, LinearIsometryEquiv.image_innerDual]
  rfl

end DifferentialGeometry.Analysis.InnerProductSpace
