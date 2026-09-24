import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.InitialSphericalFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.EndNeckFields

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem hasInitialSphericalFrontier_of_le {τ τ' : ℝ} (hτ : τ ≤ τ')
    (H : HasInitialSphericalFrontier.{u} τ) :
    HasInitialSphericalFrontier.{u} τ' := by
  obtain ⟨ε, Λ, hε, hε1, hΛ, h⟩ := H
  exact ⟨ε, Λ, hε, hε1, hΛ, fun D hD => h D (hτ.trans hD)⟩

theorem hasInitialSphericalFrontier_of_presentation {τ ε Λ : ℝ} (hε : 0 < ε)
    (hε1 : ε < 1) (hΛ : 1 ≤ Λ)
    (h : ∀ D : OneStepIncoming.{u}, τ ≤ D.endTime →
      Nonempty (TerminalCorePresentation.{u} D ε Λ)) :
    HasInitialSphericalFrontier.{u} τ :=
  ⟨ε, Λ, hε, hε1, hΛ, h⟩

theorem exists_hasInitialSphericalFrontier_iff_eventually :
    (∃ τ : ℝ, 0 < τ ∧ HasInitialSphericalFrontier.{u} τ) ↔
      ∃ T : ℝ, 0 < T ∧ ∀ τ : ℝ, T ≤ τ → HasInitialSphericalFrontier.{u} τ := by
  constructor
  · rintro ⟨τ, hτ, H⟩
    exact ⟨τ, hτ, fun τ' hτ' => hasInitialSphericalFrontier_of_le hτ' H⟩
  · rintro ⟨T, hT, h⟩
    exact ⟨T, hT, h T le_rfl⟩

theorem hasInitialSphericalFrontier_of_no_terminal_event {τ : ℝ}
    (h : ∀ D : OneStepIncoming.{u}, ¬ τ ≤ D.endTime) :
    HasInitialSphericalFrontier.{u} τ :=
  ⟨1 / 2, 1, by norm_num, by norm_num, le_refl 1, fun D hD => absurd hD (h D)⟩

theorem exists_terminalCorePresentation_of_hasInitialSphericalFrontier {τ : ℝ}
    (H : HasInitialSphericalFrontier.{u} τ) (D : OneStepIncoming.{u})
    (hD : τ ≤ D.endTime) :
    ∃ ε Λ : ℝ, 0 < ε ∧ ε < 1 ∧ 1 ≤ Λ ∧
      Nonempty (TerminalCorePresentation.{u} D ε Λ) := by
  obtain ⟨ε, Λ, hε, hε1, hΛ, h⟩ := H
  exact ⟨ε, Λ, hε, hε1, hΛ, h D hD⟩

theorem hasInitialSphericalFrontier_witness_window {τ : ℝ}
    (H : HasInitialSphericalFrontier.{u} τ) :
    ∃ ε₀ Λ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧ 1 ≤ Λ ∧
      (∀ D : OneStepIncoming.{u}, τ ≤ D.endTime →
        Nonempty (TerminalCorePresentation.{u} D ε₀ Λ)) ∧
      (∀ ε : ℝ, ε₀ ≤ ε → ε < 1 → ∀ D : OneStepIncoming.{u}, τ ≤ D.endTime →
        Nonempty (TerminalCorePresentation.{u} D ε Λ)) := by
  obtain ⟨ε, Λ, hε, hε1, hΛ, h⟩ := H
  exact ⟨ε, Λ, hε, hε1, hΛ, h,
    fun ε' hε' _ D hD => (h D hD).map (fun P => P.monoEpsilon hε')⟩

def TerminalCorePresentationInput.monoTau {τ τ' ε : ℝ}
    (P : TerminalCorePresentationInput.{u} τ ε) (hτ : τ ≤ τ') (hτ' : 0 < τ') :
    TerminalCorePresentationInput.{u} τ' ε where
  tau_pos := hτ'
  epsilon_pos := P.epsilon_pos
  epsilon_lt_one := P.epsilon_lt_one
  lambda := P.lambda
  one_le_lambda := P.one_le_lambda
  presentation := fun D hD => P.presentation D (hτ.trans hD)

theorem exists_terminalCorePresentationInput_iff_eventually :
    (∃ τ ε : ℝ, 0 < τ ∧ 0 < ε ∧ ε < 1 ∧
      Nonempty (TerminalCorePresentationInput.{u} τ ε)) ↔
      ∃ T ε : ℝ, 0 < T ∧ 0 < ε ∧ ε < 1 ∧
        ∀ τ : ℝ, T ≤ τ → Nonempty (TerminalCorePresentationInput.{u} τ ε) := by
  constructor
  · rintro ⟨τ, ε, hτ, hε, hε1, ⟨P⟩⟩
    exact ⟨τ, ε, hτ, hε, hε1,
      fun τ' hτ' => ⟨P.monoTau hτ' (lt_of_lt_of_le hτ hτ')⟩⟩
  · rintro ⟨T, ε, hT, hε, hε1, h⟩
    exact ⟨T, ε, hT, hε, hε1, h T le_rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
