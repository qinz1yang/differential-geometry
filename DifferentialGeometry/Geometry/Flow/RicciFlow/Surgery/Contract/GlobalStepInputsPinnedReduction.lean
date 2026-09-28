import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.MetricStripPinning
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.Terminal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.InitialSphericalFrontierEpsilonUniformity

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def HasNontrivialPositiveHorizonHistory : Prop :=
  ∃ H : ObservedHistory.{u}, 0 < H.horizon ∧ ∃ p q : (H.stage 0).Carrier, p ≠ q

noncomputable def poleAvoidingVariationalStrip (H : ObservedHistory.{u})
    (hpos : 0 < H.horizon) (p q : (H.stage 0).Carrier) : VariationalStrip H where
  pole := p
  start := 0
  finish := H.horizon
  start_nonneg := le_rfl
  finish_le_horizon := le_rfl
  start_lt_finish := hpos
  radius := 1
  radius_pos := one_pos
  metricAt := H.stageMetric 0
  admissible := fun gamma => gamma = fun _ => q
  regular := fun _ => False
  regular_admissible := fun _ h => h.elim

theorem hasAdmissibleCurve_poleAvoidingVariationalStrip (H : ObservedHistory.{u})
    (hpos : 0 < H.horizon) (p q : (H.stage 0).Carrier) :
    HasAdmissibleCurve (poleAvoidingVariationalStrip H hpos p q) :=
  ⟨fun _ => q, rfl⟩

theorem admissible_poleAvoidingVariationalStrip {H : ObservedHistory.{u}}
    {hpos : 0 < H.horizon} {p q : (H.stage 0).Carrier}
    {gamma : ℝ → (H.stage 0).Carrier}
    (hgamma : (poleAvoidingVariationalStrip H hpos p q).admissible gamma) :
    gamma = fun _ => q :=
  hgamma

theorem reducedLength_poleAvoidingVariationalStrip (H : ObservedHistory.{u})
    (hpos : 0 < H.horizon) (p q : (H.stage 0).Carrier) (hpq : q ≠ p)
    (u : ℝ) (x : (H.stage 0).Carrier) :
    (poleAvoidingVariationalStrip H hpos p q).reducedLength u x = 0 := by
  simp [poleAvoidingVariationalStrip, VariationalStrip.reducedLength, reducedLength, hpq]

theorem not_isReducedLengthRealization_poleAvoidingVariationalStrip
    (H : ObservedHistory.{u}) (hpos : 0 < H.horizon) (p q : (H.stage 0).Carrier)
    (hpq : q ≠ p) :
    ¬ IsReducedLengthRealization (poleAvoidingVariationalStrip H hpos p q) := by
  intro hreal
  obtain ⟨-, -, hattain, -, -⟩ := hreal
  have hu : H.horizon / 2 ∈ Ioo (0 : ℝ) H.horizon :=
    ⟨half_pos hpos, half_lt_self hpos⟩
  obtain ⟨x, -, gamma, hgamma, hgamma0, -⟩ := hattain (H.horizon / 2) hu
  have h0 : gamma 0 = q := congrFun (admissible_poleAvoidingVariationalStrip hgamma) 0
  have h1 : gamma 0 = p := by simpa [poleAvoidingVariationalStrip] using hgamma0
  exact hpq (h0.symm.trans h1)

theorem not_isTowerPinnedStrip_poleAvoidingVariationalStrip (H : ObservedHistory.{u})
    (hpos : 0 < H.horizon) (p q : (H.stage 0).Carrier) (hpq : p ≠ q) :
    ¬ IsTowerPinnedStrip (poleAvoidingVariationalStrip H hpos p q) := by
  intro hpinned
  have hadmis : (poleAvoidingVariationalStrip H hpos p q).admissible (fun _ => q) := rfl
  rw [hpinned.2] at hadmis
  exact hpq (by simpa [poleAvoidingVariationalStrip] using hadmis.2.symm)

theorem
    exists_isTowerPinnedStrip_hasAdmissibleCurve_of_hasNontrivialPositiveHorizonHistory
    (h : HasNontrivialPositiveHorizonHistory.{u}) :
    ∃ (H : ObservedHistory.{u}) (S : VariationalStrip H),
      0 < H.horizon ∧ IsTowerPinnedStrip S ∧ HasAdmissibleCurve S := by
  obtain ⟨H, hpos, p, -, -⟩ := h
  exact ⟨H, towerVariationalStrip H hpos p, hpos,
    isTowerPinnedStrip_towerVariationalStrip H hpos p,
    hasAdmissibleCurve_towerVariationalStrip H hpos p⟩

theorem nonempty_globalStepInputs_falseDiscard_iff (p : CutoffParameters) (τ ε d : ℝ)
    (k : ℕ) :
    Nonempty (GlobalStepInputs.{u} p τ ε d k fun _ => False) ↔
      ∃ endInput : TerminalCorePresentationInput.{u} τ ε,
        historicalNeckRecognition.{u} τ ε d k endInput.lambda ∧
          hornCylinderLimit.{u} ε endInput.lambda ∧
            protectionInput.{u} τ ε endInput.lambda := by
  constructor
  · rintro ⟨G⟩
    exact ⟨G.endInput, G.neckInput, G.cylinderInput, G.protectInput⟩
  · rintro ⟨endInput, hneck, hcylinder, hprotect⟩
    exact ⟨{ endInput := endInput
             neckInput := hneck
             pieceInput := fun _ _ _ h => h.elim
             cylinderInput := hcylinder
             protectInput := hprotect }⟩

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
