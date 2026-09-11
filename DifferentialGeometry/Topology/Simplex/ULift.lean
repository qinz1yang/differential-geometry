import DifferentialGeometry.Topology.Simplex.BoundaryRetraction
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false

noncomputable section

universe u v

namespace DifferentialGeometry.Simplex

variable (I : Type v) [Fintype I]

def uliftHomeomorph : ULift.{u} (stdSimplex ℝ I) ≃ₜ stdSimplex ℝ (ULift.{u} I) where
  toFun p := ⟨fun i ↦ p.down.val i.down, ⟨fun i ↦ p.down.property.1 i.down, by
    exact (Equiv.ulift.sum_comp p.down.val).trans p.down.property.2⟩⟩
  invFun q := ULift.up ⟨fun i ↦ q.val (ULift.up i), ⟨fun i ↦ q.property.1 (ULift.up i), by
    exact (Equiv.ulift.symm.sum_comp q.val).trans q.property.2⟩⟩
  left_inv p := rfl
  right_inv q := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (continuous_apply i.down).comp (continuous_subtype_val.comp continuous_uliftDown)
  continuous_invFun := by
    apply continuous_uliftUp.comp
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (continuous_apply (ULift.up i)).comp continuous_subtype_val


@[simp]
theorem uliftHomeomorph_apply (p : ULift.{u} (stdSimplex ℝ I)) (i : ULift.{u} I) :
    (uliftHomeomorph I p).val i = p.down.val i.down := rfl


@[simp]
theorem uliftHomeomorph_symm_apply (q : stdSimplex ℝ (ULift.{u} I)) (i : I) :
    ((uliftHomeomorph I).symm q).down.val i = q.val (ULift.up i) := rfl


theorem uliftHomeomorph_mem_boundary (p : ULift.{u} (stdSimplex ℝ I)) :
    p.down ∈ boundary I ↔ uliftHomeomorph I p ∈ boundary (ULift.{u} I) := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨ULift.up i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i.down, hi⟩


def boundaryUliftHomeomorph :
    {p : ULift.{u} (stdSimplex ℝ I) // p.down ∈ boundary I} ≃ₜ boundary (ULift.{u} I) :=
  (uliftHomeomorph I).subtype (uliftHomeomorph_mem_boundary I)


@[simp]
theorem boundaryUliftHomeomorph_val
    (p : {p : ULift.{u} (stdSimplex ℝ I) // p.down ∈ boundary I}) :
    (boundaryUliftHomeomorph I p).val = uliftHomeomorph I p.val := rfl

end DifferentialGeometry.Simplex
