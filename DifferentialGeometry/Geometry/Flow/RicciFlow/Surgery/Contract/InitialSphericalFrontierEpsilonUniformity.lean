import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.InitialSphericalFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.EndNeckFields

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def HasUniformEpsilonSphericalFrontier (τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ Λ : ℝ, 1 ≤ Λ ∧
    ∀ D : OneStepIncoming.{u}, τ ≤ D.endTime →
      Nonempty (TerminalCorePresentation.{u} D ε Λ)

theorem hasInitialSphericalFrontier_of_uniformEpsilon {τ : ℝ}
    (U : HasUniformEpsilonSphericalFrontier.{u} τ) :
    HasInitialSphericalFrontier.{u} τ := by
  obtain ⟨Λ, hΛ, h⟩ := U (1 / 2) (by norm_num) (by norm_num)
  exact ⟨1 / 2, Λ, by norm_num, by norm_num, hΛ, h⟩

theorem hasUniformEpsilonSphericalFrontier_of_no_terminal_event {τ : ℝ}
    (h : ∀ D : OneStepIncoming.{u}, ¬ τ ≤ D.endTime) :
    HasUniformEpsilonSphericalFrontier.{u} τ := by
  intro ε _ _
  exact ⟨1, le_refl 1, fun D hD => absurd hD (h D)⟩

theorem hasInitialSphericalFrontier_epsilon_step {τ ε ε' Λ : ℝ} (hε : ε ≤ ε')
    (h : ∀ D : OneStepIncoming.{u}, τ ≤ D.endTime →
      Nonempty (TerminalCorePresentation.{u} D ε Λ)) :
    ∀ D : OneStepIncoming.{u}, τ ≤ D.endTime →
      Nonempty (TerminalCorePresentation.{u} D ε' Λ) :=
  fun D hD => (h D hD).map (fun P => P.monoEpsilon hε)

theorem exists_epsilon_upwardMonotoneFamily_not_forall :
    ∃ F : ℝ → Prop, (∀ ⦃ε ε' : ℝ⦄, ε ≤ ε' → F ε → F ε') ∧
      (∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ F ε) ∧
        ¬ (∀ ε : ℝ, 0 < ε → ε < 1 → F ε) := by
  refine ⟨fun ε => (1 / 2 : ℝ) ≤ ε, ?_, ?_, ?_⟩
  · intro ε ε' hle h
    exact h.trans hle
  · exact ⟨1 / 2, by norm_num, by norm_num, le_refl _⟩
  · intro h
    have h14 : (1 / 2 : ℝ) ≤ 1 / 4 := h (1 / 4) (by norm_num) (by norm_num)
    norm_num at h14


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
