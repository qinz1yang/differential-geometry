import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.Terminal

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def HasInitialSphericalFrontier (τ : ℝ) : Prop :=
  ∃ ε Λ : ℝ, 0 < ε ∧ ε < 1 ∧ 1 ≤ Λ ∧
    ∀ D : OneStepIncoming.{u}, τ ≤ D.endTime →
      Nonempty (TerminalCorePresentation.{u} D ε Λ)

theorem hasInitialSphericalFrontier_iff_exists_terminalCorePresentationInput :
    (∃ τ : ℝ, 0 < τ ∧ HasInitialSphericalFrontier.{u} τ) ↔
      ∃ τ ε : ℝ, 0 < τ ∧ 0 < ε ∧ ε < 1 ∧
        Nonempty (TerminalCorePresentationInput.{u} τ ε) := by
  constructor
  · rintro ⟨τ, hτ, ε, Λ, hε, hεone, hΛ, h⟩
    exact ⟨τ, ε, hτ, hε, hεone,
      ⟨{ tau_pos := hτ
         epsilon_pos := hε
         epsilon_lt_one := hεone
         lambda := Λ
         one_le_lambda := hΛ
         presentation := fun D hD => h D hD }⟩⟩
  · rintro ⟨τ, ε, hτ, hε, hεone, ⟨P⟩⟩
    exact ⟨τ, hτ, ε, P.lambda, hε, hεone, P.one_le_lambda,
      fun D hD => P.presentation D hD⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
