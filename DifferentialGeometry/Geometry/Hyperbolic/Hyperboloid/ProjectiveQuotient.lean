import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.ProjectiveOrthogonalGroup
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.EquivariantMaps.Existence
import Mathlib.Topology.Homeomorph.Quotient

noncomputable section

namespace DifferentialGeometry.Hyperboloid

variable (n : ℕ)

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

def projectiveQuotientHomeomorph {G : Type*} [Group G]
    (ρ : G →* (Hyperboloid E ≃ᵢ Hyperboloid E)) :
    let σ := (projectiveOrthogonalGroupEquiv n : (Hyperboloid E ≃ᵢ Hyperboloid E) →*
      ProjectiveOrthogonalGroup.PO (n + 1) 1).comp ρ
    letI := EquivariantMap.subAction (by omega : 1 ≤ n + 1) σ.range
    MulAction.orbitRel.Quotient σ.range (DifferentialGeometry.Hyperbolic.HUpper (n + 1)) ≃ₜ
      MulAction.orbitRel.Quotient ρ.range (Hyperboloid E) := by
  let σ := (projectiveOrthogonalGroupEquiv n : (Hyperboloid E ≃ᵢ Hyperboloid E) →*
      ProjectiveOrthogonalGroup.PO (n + 1) 1).comp ρ
  letI := EquivariantMap.subAction (by omega : 1 ≤ n + 1) σ.range
  let J := hUpperIsometryEquiv (n + 1)
  apply Homeomorph.Quotient.congr J.toHomeomorph
  intro x y
  constructor
  · rintro ⟨γ, hγ⟩
    obtain ⟨δ, hδ⟩ := γ.property
    refine ⟨⟨ρ δ, ⟨δ, rfl⟩⟩, ?_⟩
    change ρ δ (J y) = J x
    have he := projectiveOrthogonalGroupEquiv_smul n (ρ δ) y
    change J ((DifferentialGeometry.HyperbolicAction.poMulAction (by omega : 1 ≤ n + 1)).smul
      (σ δ) y) = ρ δ (J y) at he
    rw [hδ] at he
    exact he.symm.trans (congrArg J hγ)
  · rintro ⟨γ, hγ⟩
    obtain ⟨δ, hδ⟩ := γ.property
    refine ⟨⟨σ δ, ⟨δ, rfl⟩⟩, ?_⟩
    apply J.injective
    have he := projectiveOrthogonalGroupEquiv_smul n (ρ δ) y
    change J ((DifferentialGeometry.HyperbolicAction.poMulAction (by omega : 1 ≤ n + 1)).smul
      (σ δ) y) = ρ δ (J y) at he
    exact he.trans ((congrArg (fun F : Hyperboloid E ≃ᵢ Hyperboloid E => F (J y)) hδ).trans hγ)

@[simp] theorem projectiveQuotientHomeomorph_apply_mk {G : Type*} [Group G]
    (ρ : G →* (Hyperboloid E ≃ᵢ Hyperboloid E)) :
    let σ := (projectiveOrthogonalGroupEquiv n : (Hyperboloid E ≃ᵢ Hyperboloid E) →*
      ProjectiveOrthogonalGroup.PO (n + 1) 1).comp ρ
    letI := EquivariantMap.subAction (by omega : 1 ≤ n + 1) σ.range
    ∀ x : DifferentialGeometry.Hyperbolic.HUpper (n + 1),
      projectiveQuotientHomeomorph n ρ
        (Quotient.mk (MulAction.orbitRel σ.range (DifferentialGeometry.Hyperbolic.HUpper (n + 1))) x) =
          Quotient.mk (MulAction.orbitRel ρ.range (Hyperboloid E)) (hUpperIsometryEquiv (n + 1) x) := by
  dsimp only
  intro x
  rfl

@[simp] theorem projectiveQuotientHomeomorph_symm_apply_mk {G : Type*} [Group G]
    (ρ : G →* (Hyperboloid E ≃ᵢ Hyperboloid E)) :
    let σ := (projectiveOrthogonalGroupEquiv n : (Hyperboloid E ≃ᵢ Hyperboloid E) →*
      ProjectiveOrthogonalGroup.PO (n + 1) 1).comp ρ
    letI := EquivariantMap.subAction (by omega : 1 ≤ n + 1) σ.range
    ∀ x : Hyperboloid E,
      (projectiveQuotientHomeomorph n ρ).symm (Quotient.mk (MulAction.orbitRel ρ.range (Hyperboloid E)) x) =
        Quotient.mk (MulAction.orbitRel σ.range (DifferentialGeometry.Hyperbolic.HUpper (n + 1)))
          ((hUpperIsometryEquiv (n + 1)).symm x) := by
  dsimp only
  intro x
  rfl

end DifferentialGeometry.Hyperboloid
