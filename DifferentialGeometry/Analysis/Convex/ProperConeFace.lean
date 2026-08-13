import DifferentialGeometry.Analysis.InnerProductSpace.ProperConeIsometry
import Mathlib.Analysis.Convex.Exposed

set_option autoImplicit false

open Set

namespace DifferentialGeometry.Analysis.Convex

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def ProperCone.IsDualElement
    (C : ProperCone ℝ E) (phi : StrongDual ℝ E) : Prop :=
  ∀ x ∈ C, 0 ≤ phi x

@[simp]
theorem ProperCone.isDualElement_iff
    {C : ProperCone ℝ E} {phi : StrongDual ℝ E} :
    ProperCone.IsDualElement C phi ↔ ∀ x ∈ C, 0 ≤ phi x :=
  Iff.rfl

noncomputable def ProperCone.dualZeroFace
    (C : ProperCone ℝ E) (phi : StrongDual ℝ E) : ProperCone ℝ E :=
  C ⊓ (⊥ : ProperCone ℝ ℝ).comap phi

@[simp]
theorem ProperCone.mem_dualZeroFace
    {C : ProperCone ℝ E} {phi : StrongDual ℝ E} {x : E} :
    x ∈ ProperCone.dualZeroFace C phi ↔ x ∈ C ∧ phi x = 0 := by
  simp [ProperCone.dualZeroFace]

@[simp]
theorem ProperCone.dualZeroFace_zero (C : ProperCone ℝ E) :
    ProperCone.dualZeroFace C 0 = C := by
  ext x
  simp

theorem ProperCone.dualZeroFace_le
    (C : ProperCone ℝ E) (phi : StrongDual ℝ E) :
    ProperCone.dualZeroFace C phi ≤ C := by
  intro x hx
  exact (ProperCone.mem_dualZeroFace.mp hx).1

theorem ProperCone.dualZeroFace_isExposed
    (C : ProperCone ℝ E) {phi : StrongDual ℝ E}
    (hphi : ProperCone.IsDualElement C phi) :
    IsExposed ℝ (C : Set E) (ProperCone.dualZeroFace C phi : Set E) := by
  intro _
  refine ⟨-phi, Set.ext fun x ↦ ?_⟩
  constructor
  · intro hx
    obtain ⟨hxC, hphix⟩ := ProperCone.mem_dualZeroFace.mp hx
    refine ⟨hxC, fun z hz ↦ ?_⟩
    have hznonneg : 0 ≤ phi z := hphi z hz
    simp only [ContinuousLinearMap.neg_apply]
    rw [hphix]
    simpa using neg_nonpos.mpr hznonneg
  · rintro ⟨hxC, hxmax⟩
    have hxnonneg : 0 ≤ phi x := hphi x hxC
    have hxmax0 := hxmax 0 C.zero_mem
    have hxnonpos : phi x ≤ 0 := by
      simpa using hxmax0
    exact ProperCone.mem_dualZeroFace.mpr
      ⟨hxC, le_antisymm hxnonpos hxnonneg⟩

theorem ProperCone.dualZeroFace_isExtreme
    (C : ProperCone ℝ E) {phi : StrongDual ℝ E}
    (hphi : ProperCone.IsDualElement C phi) :
    IsExtreme ℝ (C : Set E) (ProperCone.dualZeroFace C phi : Set E) :=
  (ProperCone.dualZeroFace_isExposed C hphi).isExtreme

theorem ProperCone.IsDualElement.comp_symm
    {C : ProperCone ℝ E} {phi : StrongDual ℝ E}
    (hphi : ProperCone.IsDualElement C phi) (e : E ≃L[ℝ] F) :
    ProperCone.IsDualElement (C.map e.toContinuousLinearMap)
      (phi.comp e.symm.toContinuousLinearMap) := by
  intro y hy
  exact hphi (e.symm y)
    ((DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.mem_map_continuousLinearEquiv_iff
      C e y).mp hy)

@[simp]
theorem ProperCone.dualZeroFace_map_continuousLinearEquiv
    (C : ProperCone ℝ E) (e : E ≃L[ℝ] F) (phi : StrongDual ℝ E) :
    (ProperCone.dualZeroFace C phi).map e.toContinuousLinearMap =
      ProperCone.dualZeroFace (C.map e.toContinuousLinearMap)
        (phi.comp e.symm.toContinuousLinearMap) := by
  apply ProperCone.ext
  intro y
  simp only [
    DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.mem_map_continuousLinearEquiv_iff,
    ProperCone.mem_dualZeroFace, ContinuousLinearMap.comp_apply]
  rfl

end DifferentialGeometry.Analysis.Convex
