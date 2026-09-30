import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Terminal.CorePresentation.Basic

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Function Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_terminalCorePresentation_family_of_le {τ τ' : ℝ} (hτ : τ ≤ τ')
    (H : ∃ ε Λ : ℝ, 0 < ε ∧ ε < 1 ∧ 1 ≤ Λ ∧
      ∀ D : OneStepIncoming.{u}, τ ≤ D.endTime →
        Nonempty (TerminalCorePresentation D ε Λ)) :
    ∃ ε Λ : ℝ, 0 < ε ∧ ε < 1 ∧ 1 ≤ Λ ∧
      ∀ D : OneStepIncoming.{u}, τ' ≤ D.endTime →
        Nonempty (TerminalCorePresentation D ε Λ) := by
  obtain ⟨ε, Λ, hε, hε1, hΛ, h⟩ := H
  exact ⟨ε, Λ, hε, hε1, hΛ, fun D hD => h D (hτ.trans hD)⟩

theorem exists_terminalCorePresentation_family_iff_eventually :
    (∃ τ ε Λ : ℝ, 0 < τ ∧ 0 < ε ∧ ε < 1 ∧ 1 ≤ Λ ∧
      ∀ D : OneStepIncoming.{u}, τ ≤ D.endTime →
        Nonempty (TerminalCorePresentation D ε Λ)) ↔
      ∃ T : ℝ, 0 < T ∧ ∀ τ : ℝ, T ≤ τ →
        ∃ ε Λ : ℝ, 0 < ε ∧ ε < 1 ∧ 1 ≤ Λ ∧
          ∀ D : OneStepIncoming.{u}, τ ≤ D.endTime →
            Nonempty (TerminalCorePresentation D ε Λ) := by
  constructor
  · rintro ⟨τ, ε, Λ, hτ, hε, hε1, hΛ, h⟩
    exact ⟨τ, hτ, fun τ' hτ' =>
      exists_terminalCorePresentation_family_of_le hτ' ⟨ε, Λ, hε, hε1, hΛ, h⟩⟩
  · rintro ⟨T, hT, h⟩
    obtain ⟨ε, Λ, hε, hε1, hΛ, hP⟩ := h T le_rfl
    exact ⟨T, ε, Λ, hT, hε, hε1, hΛ, hP⟩

theorem exists_terminalCorePresentation_of_family {τ : ℝ}
    (H : ∃ ε Λ : ℝ, 0 < ε ∧ ε < 1 ∧ 1 ≤ Λ ∧
      ∀ D : OneStepIncoming.{u}, τ ≤ D.endTime →
        Nonempty (TerminalCorePresentation D ε Λ))
    (D : OneStepIncoming.{u}) (hD : τ ≤ D.endTime) :
    ∃ ε Λ : ℝ, 0 < ε ∧ ε < 1 ∧ 1 ≤ Λ ∧
      Nonempty (TerminalCorePresentation D ε Λ) := by
  obtain ⟨ε, Λ, hε, hε1, hΛ, h⟩ := H
  exact ⟨ε, Λ, hε, hε1, hΛ, h D hD⟩

theorem terminalCorePresentation_family_mono_epsilon {τ ε ε' Λ : ℝ} (hε : ε ≤ ε')
    (h : ∀ D : OneStepIncoming.{u}, τ ≤ D.endTime →
      Nonempty (TerminalCorePresentation D ε Λ)) :
    ∀ D : OneStepIncoming.{u}, τ ≤ D.endTime →
      Nonempty (TerminalCorePresentation D ε' Λ) :=
  fun D hD => (h D hD).map (fun P => P.monoEpsilon hε)

theorem terminalCorePresentation_family_mono_lambda {τ ε Λ Λ' : ℝ} (hΛ : Λ ≤ Λ')
    (h : ∀ D : OneStepIncoming.{u}, τ ≤ D.endTime →
      Nonempty (TerminalCorePresentation D ε Λ)) :
    ∀ D : OneStepIncoming.{u}, τ ≤ D.endTime →
      Nonempty (TerminalCorePresentation D ε Λ') :=
  fun D hD => (h D hD).map (fun P => P.monoLambda hΛ)

theorem terminalCorePresentation_family_mono_parameters {τ τ' ε ε' Λ Λ' : ℝ}
    (hτ : τ ≤ τ') (hε : ε ≤ ε') (hΛ : Λ ≤ Λ')
    (h : ∀ D : OneStepIncoming.{u}, τ ≤ D.endTime →
      Nonempty (TerminalCorePresentation D ε Λ)) :
    ∀ D : OneStepIncoming.{u}, τ' ≤ D.endTime →
      Nonempty (TerminalCorePresentation D ε' Λ') :=
  fun D hD => (h D (hτ.trans hD)).map (fun P => (P.monoEpsilon hε).monoLambda hΛ)

theorem exists_terminalCorePresentation_family_window {τ : ℝ}
    (H : ∃ ε Λ : ℝ, 0 < ε ∧ ε < 1 ∧ 1 ≤ Λ ∧
      ∀ D : OneStepIncoming.{u}, τ ≤ D.endTime →
        Nonempty (TerminalCorePresentation D ε Λ)) :
    ∃ ε₀ Λ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧ 1 ≤ Λ ∧
      (∀ D : OneStepIncoming.{u}, τ ≤ D.endTime →
        Nonempty (TerminalCorePresentation D ε₀ Λ)) ∧
      (∀ ε : ℝ, ε₀ ≤ ε → ε < 1 → ∀ D : OneStepIncoming.{u}, τ ≤ D.endTime →
        Nonempty (TerminalCorePresentation D ε Λ)) := by
  obtain ⟨ε, Λ, hε, hε1, hΛ, h⟩ := H
  exact ⟨ε, Λ, hε, hε1, hΛ, h,
    fun ε' hε' _ D hD => (h D hD).map (fun P => P.monoEpsilon hε')⟩

theorem exists_terminalCorePresentation_family_of_all_precisions {τ : ℝ}
    (U : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ Λ : ℝ, 1 ≤ Λ ∧
      ∀ D : OneStepIncoming.{u}, τ ≤ D.endTime →
        Nonempty (TerminalCorePresentation D ε Λ)) :
    ∃ ε Λ : ℝ, 0 < ε ∧ ε < 1 ∧ 1 ≤ Λ ∧
      ∀ D : OneStepIncoming.{u}, τ ≤ D.endTime →
        Nonempty (TerminalCorePresentation D ε Λ) := by
  obtain ⟨Λ, hΛ, h⟩ := U (1 / 2) (by norm_num) (by norm_num)
  exact ⟨1 / 2, Λ, by norm_num, by norm_num, hΛ, h⟩

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
