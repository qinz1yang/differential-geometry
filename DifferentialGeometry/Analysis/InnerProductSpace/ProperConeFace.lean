import DifferentialGeometry.Analysis.Convex.ProperConeFace

set_option autoImplicit false

open Set
open scoped RealInnerProductSpace

namespace DifferentialGeometry.Analysis.InnerProductSpace

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

noncomputable def ProperCone.innerDualZeroFace
    (C : ProperCone ℝ E) (y : E) : ProperCone ℝ E :=
  DifferentialGeometry.Analysis.Convex.ProperCone.dualZeroFace C (innerSL ℝ y)

theorem ProperCone.innerDualZeroFace_eq_dualZeroFace
    (C : ProperCone ℝ E) (y : E) :
    ProperCone.innerDualZeroFace C y =
      DifferentialGeometry.Analysis.Convex.ProperCone.dualZeroFace C (innerSL ℝ y) :=
  rfl

@[simp]
theorem ProperCone.mem_innerDualZeroFace
    {C : ProperCone ℝ E} {x y : E} :
    x ∈ ProperCone.innerDualZeroFace C y ↔ x ∈ C ∧ ⟪x, y⟫ = 0 := by
  simp [ProperCone.innerDualZeroFace, real_inner_comm]

@[simp]
theorem ProperCone.innerDualZeroFace_zero (C : ProperCone ℝ E) :
    ProperCone.innerDualZeroFace C 0 = C := by
  ext x
  simp

theorem ProperCone.innerDualZeroFace_le
    (C : ProperCone ℝ E) (y : E) :
    ProperCone.innerDualZeroFace C y ≤ C := by
  intro x hx
  exact (ProperCone.mem_innerDualZeroFace.mp hx).1

theorem ProperCone.innerDualZeroFace_isExposed
    [CompleteSpace E]
    (C : ProperCone ℝ E) {y : E}
    (hy : y ∈ ProperCone.innerDual (C : Set E)) :
    IsExposed ℝ (C : Set E) (ProperCone.innerDualZeroFace C y : Set E) := by
  intro _
  refine ⟨-(innerSL ℝ y), Set.ext fun x ↦ ?_⟩
  constructor
  · intro hx
    obtain ⟨hxC, hxy⟩ := ProperCone.mem_innerDualZeroFace.mp hx
    refine ⟨hxC, fun z hz ↦ ?_⟩
    have hznonneg : 0 ≤ ⟪z, y⟫ := hy hz
    simp only [ContinuousLinearMap.neg_apply, innerSL_apply_apply]
    rw [real_inner_comm z y, real_inner_comm x y, hxy]
    simpa using neg_nonpos.mpr hznonneg
  · rintro ⟨hxC, hxmax⟩
    have hxnonneg : 0 ≤ ⟪x, y⟫ := hy hxC
    have hxmax0 := hxmax 0 C.zero_mem
    have hxnonpos : ⟪x, y⟫ ≤ 0 := by
      simpa [real_inner_comm] using hxmax0
    exact ProperCone.mem_innerDualZeroFace.mpr
      ⟨hxC, le_antisymm hxnonpos hxnonneg⟩

theorem ProperCone.innerDualZeroFace_isExtreme
    [CompleteSpace E]
    (C : ProperCone ℝ E) {y : E}
    (hy : y ∈ ProperCone.innerDual (C : Set E)) :
    IsExtreme ℝ (C : Set E) (ProperCone.innerDualZeroFace C y : Set E) :=
  (ProperCone.innerDualZeroFace_isExposed C hy).isExtreme

@[simp]
theorem ProperCone.innerDualZeroFace_map_linearIsometryEquiv
    (C : ProperCone ℝ E) (e : E ≃ₗᵢ[ℝ] F) (y : E) :
    (ProperCone.innerDualZeroFace C y).map
        e.toContinuousLinearEquiv.toContinuousLinearMap =
      ProperCone.innerDualZeroFace
        (C.map e.toContinuousLinearEquiv.toContinuousLinearMap) (e y) := by
  apply ProperCone.ext
  intro z
  rw [ProperCone.mem_map_continuousLinearEquiv_iff]
  rw [ProperCone.mem_innerDualZeroFace]
  rw [ProperCone.mem_innerDualZeroFace]
  rw [ProperCone.mem_map_continuousLinearEquiv_iff]
  constructor
  · rintro ⟨hzC, hzy⟩
    refine ⟨hzC, ?_⟩
    have hinner : ⟪z, e y⟫ = ⟪e.symm z, y⟫ := by
      simpa using e.inner_map_map (e.symm z) y
    exact hinner.trans hzy
  · rintro ⟨hzC, hzy⟩
    refine ⟨hzC, ?_⟩
    have hinner : ⟪z, e y⟫ = ⟪e.symm z, y⟫ := by
      simpa using e.inner_map_map (e.symm z) y
    exact hinner.symm.trans hzy

end

end DifferentialGeometry.Analysis.InnerProductSpace
