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

theorem nonempty_globalStepInputs_of_uniformEpsilon {p : CutoffParameters} {τ ε d : ℝ}
    {k : ℕ} {DiscardedCutOpen : Type u → Prop} (hτ : 0 < τ) (hε : 0 < ε)
    (hε1 : ε < 1) (U : HasUniformEpsilonSphericalFrontier.{u} τ)
    (hneck : ∀ Λ : ℝ, 1 ≤ Λ →
      (∀ D : OneStepIncoming.{u}, τ ≤ D.endTime →
        Nonempty (TerminalCorePresentation.{u} D ε Λ)) →
      historicalNeckRecognition.{u} τ ε d k Λ)
    (hcylinder : ∀ Λ : ℝ, 1 ≤ Λ →
      (∀ D : OneStepIncoming.{u}, τ ≤ D.endTime →
        Nonempty (TerminalCorePresentation.{u} D ε Λ)) →
      hornCylinderLimit.{u} ε Λ)
    (hprotect : ∀ Λ : ℝ, 1 ≤ Λ →
      (∀ D : OneStepIncoming.{u}, τ ≤ D.endTime →
        Nonempty (TerminalCorePresentation.{u} D ε Λ)) →
      protectionInput.{u} τ ε Λ)
    (hpiece : ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount),
      GeometricCutoffRecord H i p → DiscardedCutOpen (H.event i).discarded.Carrier →
      (H.event i).discarded.toClosedOrientedManifold.componentwiseConnectedSumStandardFactor) :
    Nonempty (GlobalStepInputs.{u} p τ ε d k DiscardedCutOpen) := by
  obtain ⟨Λ, hΛ, hΛpres⟩ := U ε hε hε1
  exact Nonempty.intro
    { endInput :=
        { tau_pos := hτ,
          epsilon_pos := hε,
          epsilon_lt_one := hε1,
          lambda := Λ,
          one_le_lambda := hΛ,
          presentation := hΛpres },
      neckInput := hneck Λ hΛ hΛpres,
      pieceInput := hpiece,
      cylinderInput := hcylinder Λ hΛ hΛpres,
      protectInput := hprotect Λ hΛ hΛpres }

theorem exists_pair_and_globalStepInputs_of_hasInitialSphericalFrontier
    {p : CutoffParameters} {τ d : ℝ} {k : ℕ} {DiscardedCutOpen : Type u → Prop}
    (hτ : 0 < τ) (H : HasInitialSphericalFrontier.{u} τ)
    (hneck : ∀ (ε Λ : ℝ), 0 < ε → ε < 1 → 1 ≤ Λ →
      (∀ D : OneStepIncoming.{u}, τ ≤ D.endTime →
        Nonempty (TerminalCorePresentation.{u} D ε Λ)) →
      historicalNeckRecognition.{u} τ ε d k Λ)
    (hcylinder : ∀ (ε Λ : ℝ), 0 < ε → ε < 1 → 1 ≤ Λ →
      (∀ D : OneStepIncoming.{u}, τ ≤ D.endTime →
        Nonempty (TerminalCorePresentation.{u} D ε Λ)) →
      hornCylinderLimit.{u} ε Λ)
    (hprotect : ∀ (ε Λ : ℝ), 0 < ε → ε < 1 → 1 ≤ Λ →
      (∀ D : OneStepIncoming.{u}, τ ≤ D.endTime →
        Nonempty (TerminalCorePresentation.{u} D ε Λ)) →
      protectionInput.{u} τ ε Λ)
    (hpiece : ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount),
      GeometricCutoffRecord H i p → DiscardedCutOpen (H.event i).discarded.Carrier →
      (H.event i).discarded.toClosedOrientedManifold.componentwiseConnectedSumStandardFactor) :
    ∃ ε Λ : ℝ, 0 < ε ∧ ε < 1 ∧ 1 ≤ Λ ∧
      Nonempty (GlobalStepInputs.{u} p τ ε d k DiscardedCutOpen) := by
  obtain ⟨ε, Λ, hε, hε1, hΛ, hΛpres⟩ := H
  exact ⟨ε, Λ, hε, hε1, hΛ,
    Nonempty.intro
      { endInput :=
          { tau_pos := hτ,
            epsilon_pos := hε,
            epsilon_lt_one := hε1,
            lambda := Λ,
            one_le_lambda := hΛ,
            presentation := hΛpres },
        neckInput := hneck ε Λ hε hε1 hΛ hΛpres,
        pieceInput := hpiece,
        cylinderInput := hcylinder ε Λ hε hε1 hΛ hΛpres,
        protectInput := hprotect ε Λ hε hε1 hΛ hΛpres }⟩


open DifferentialGeometry.Topology
  (componentwiseConnectedSumStandardFactor_of_componentwiseStandardFactor) in
theorem nonempty_globalStepInputs_of_uniformEpsilon_of_standardDiscard
    {p : CutoffParameters} {τ d : ℝ} {k : ℕ} {DiscardedCutOpen : Type u → Prop}
    (hτ : 0 < τ) (huniform : HasUniformEpsilonSphericalFrontier.{u} τ)
    (hmodels : ∀ (H : ObservedHistory.{u}) (i : Fin H.eventCount),
      GeometricCutoffRecord H i p → DiscardedCutOpen (H.event i).discarded.Carrier →
      (H.event i).discarded.toClosedOrientedManifold.componentwiseStandardFactor)
    (hneck : ∀ Λ : ℝ, 1 ≤ Λ →
      (∀ D : OneStepIncoming.{u}, τ ≤ D.endTime →
        Nonempty (TerminalCorePresentation.{u} D (1 / 2) Λ)) →
      historicalNeckRecognition.{u} τ (1 / 2) d k Λ)
    (hcylinder : ∀ Λ : ℝ, 1 ≤ Λ →
      (∀ D : OneStepIncoming.{u}, τ ≤ D.endTime →
        Nonempty (TerminalCorePresentation.{u} D (1 / 2) Λ)) →
      hornCylinderLimit.{u} (1 / 2) Λ)
    (hprotect : ∀ Λ : ℝ, 1 ≤ Λ →
      (∀ D : OneStepIncoming.{u}, τ ≤ D.endTime →
        Nonempty (TerminalCorePresentation.{u} D (1 / 2) Λ)) →
      protectionInput.{u} τ (1 / 2) Λ) :
    Nonempty (GlobalStepInputs.{u} p τ (1 / 2) d k DiscardedCutOpen) :=
  nonempty_globalStepInputs_of_uniformEpsilon hτ (by norm_num) (by norm_num) huniform hneck
    hcylinder hprotect (fun H i R hD =>
      componentwiseConnectedSumStandardFactor_of_componentwiseStandardFactor
        (H.event i).discarded.toClosedOrientedManifold (hmodels H i R hD))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
