/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.LieGroup.ProjectiveOrthogonal.Defs
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Tactic.Ext

open MeasureTheory DifferentialGeometry.ProjectiveOrthogonalGroup

namespace DifferentialGeometry.ProjectiveOrthogonalGroup.Lattices

section Instances

variable (p q : ℕ)

instance : SecondCountableTopology (MatrixSum (Fin p) (Fin q) ℝ) :=
  inferInstanceAs (SecondCountableTopology ((Fin p ⊕ Fin q) → (Fin p ⊕ Fin q) → ℝ))

instance : SecondCountableTopology ↥(unitary (MatrixSum (Fin p) (Fin q) ℝ)) :=
  inferInstanceAs (SecondCountableTopology
    ↥(SetLike.coe (unitary (MatrixSum (Fin p) (Fin q) ℝ)) : Set (MatrixSum (Fin p) (Fin q) ℝ)))

instance isHaarMeasureVolumePO : Measure.IsHaarMeasure (volume : Measure (PO p q)) := by
  rw [show (volume : Measure (PO p q)) = Measure.haar from rfl]
  infer_instance

end Instances

variable {n : ℕ}

theorem countable_of_isDiscrete (Γ : Subgroup (PO n 1))
    (disc : IsDiscrete (SetLike.coe Γ)) : Countable ↥Γ := by
  have dT : DiscreteTopology ↥Γ := SetLike.isDiscrete_iff_discreteTopology.mp disc
  have sep : TopologicalSpace.SeparableSpace ↥Γ := inferInstance
  exact TopologicalSpace.separableSpace_iff_countable.mp sep

theorem covolume_ne_zero (Γ : Subgroup (PO n 1))
    (disc : IsDiscrete (SetLike.coe Γ)) [hfd : HasFundamentalDomain Γ (PO n 1)] :
    covolume Γ (PO n 1) ≠ 0 := by
  have : Countable ↥Γ := countable_of_isDiscrete Γ disc
  have hμ : (volume : Measure (PO n 1)) ≠ 0 := NeZero.ne _
  unfold MeasureTheory.covolume
  rw [dite_eq_left hfd]
  exact hfd.ExistsIsFundamentalDomain.choose_spec.measure_ne_zero hμ

theorem inv_mul_mem_centralizer_of_forall_conj_eq {Γ Λ : Subgroup (PO n 1)} (f : Γ ≃* Λ)
    {g₁ g₂ : PO n 1} (h₁ : ∀ γ : Γ, (f γ : PO n 1) = g₁ * γ * g₁⁻¹)
    (h₂ : ∀ γ : Γ, (f γ : PO n 1) = g₂ * γ * g₂⁻¹) :
    g₂⁻¹ * g₁ ∈ Subgroup.centralizer (SetLike.coe Γ) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h : g₁ * x * g₁⁻¹ = g₂ * x * g₂⁻¹ := by
    have e₁ := h₁ ⟨x, hx⟩
    have e₂ := h₂ ⟨x, hx⟩
    rw [← e₁, ← e₂]
  calc x * (g₂⁻¹ * g₁) = g₂⁻¹ * (g₂ * x * g₂⁻¹) * g₁ := by group
    _ = g₂⁻¹ * (g₁ * x * g₁⁻¹) * g₁ := by rw [← h]
    _ = g₂⁻¹ * g₁ * x := by group

theorem eq_map_conj_of_forall_conj_eq {Γ Λ : Subgroup (PO n 1)} (f : Γ ≃* Λ) {g : PO n 1}
    (h : ∀ γ : Γ, (f γ : PO n 1) = g * γ * g⁻¹) :
    Λ = Subgroup.map (MulAut.conj g).toMonoidHom Γ := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · intro hx
    refine ⟨f.symm ⟨x, hx⟩, (f.symm ⟨x, hx⟩).prop, ?_⟩
    have hx' := h (f.symm ⟨x, hx⟩)
    rw [MulEquiv.apply_symm_apply] at hx'
    exact hx'.symm
  · rintro ⟨y, hy, rfl⟩
    have hy' := h ⟨y, hy⟩
    rw [← hy']
    exact (f ⟨y, hy⟩).prop

theorem isDiscrete_map_conj {Γ : Subgroup (PO n 1)} (g : PO n 1)
    (disc : IsDiscrete (SetLike.coe Γ)) :
    IsDiscrete (SetLike.coe (Subgroup.map (MulAut.conj g).toMonoidHom Γ)) := by
  have hφ : (⇑(MulAut.conj g).toMonoidHom) =
      ⇑((Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹)) := by
    funext x
    simp [MulAut.conj_apply, Homeomorph.trans_apply,
      Homeomorph.coe_mulLeft, Homeomorph.coe_mulRight]
  rw [Subgroup.coe_map, hφ]
  have dT : DiscreteTopology ↥(SetLike.coe Γ) := SetLike.isDiscrete_iff_discreteTopology.mp disc
  exact isDiscrete_iff_discreteTopology.mpr
    (Homeomorph.image ((Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹))
      (SetLike.coe Γ)).symm.isEmbedding.discreteTopology

end DifferentialGeometry.ProjectiveOrthogonalGroup.Lattices
