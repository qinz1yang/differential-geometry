import DifferentialGeometry.Bundle.Associated.FiberBundle
import Mathlib.RepresentationTheory.Continuous.Basic

noncomputable section

open Set Bundle

namespace ContRepresentation

variable {k G B W : Type*} [NontriviallyNormedField k] [Group G]
  [TopologicalSpace G] [TopologicalSpace B] [NormedAddCommGroup W] [NormedSpace k W]
  {P : B → Type*} [∀ x, Torsor G (P x)] [∀ x, TopologicalSpace (P x)]
  [TopologicalSpace (TotalSpace G P)] [FiberBundle G P] [IsPrincipalBundle P]

def associatedVectorPrebundle (ρ : ContRepresentation k G W)
    (hρ : Continuous (fun g => ρ g)) :
    VectorPrebundle k W (fun x => P x →ₑ[ρ.toRepresentation] W) where
  __ := ρ.toRepresentation.associatedFiberPrebundle
    ((hρ.comp continuous_fst).clm_apply continuous_snd)
  pretrivialization_linear' := by
    rintro _ ⟨e, he, rfl⟩
    infer_instance
  exists_coordChange := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    let := he
    let := he'
    refine ⟨fun x => ρ (e'.principalSection x /ₛ e.principalSection x),
      hρ.comp_continuousOn (e.continuousOn_principalSection_sdiv e'), ?_⟩
    intro x hx w
    have h := congrArg Prod.snd
      (Pretrivialization.associated_coordChange ρ.toRepresentation e' e (x, w))
    rw [← (Pretrivialization.associated ρ.toRepresentation e).mk_symm hx.1 w] at h
    exact h.symm

theorem associatedVectorPrebundle_toFiberPrebundle (ρ : ContRepresentation k G W)
    (hρ : Continuous (fun g => ρ g)) :
    (ρ.associatedVectorPrebundle (P := P) hρ).toFiberPrebundle =
      ρ.toRepresentation.associatedFiberPrebundle
        ((hρ.comp continuous_fst).clm_apply continuous_snd) := rfl

end ContRepresentation
