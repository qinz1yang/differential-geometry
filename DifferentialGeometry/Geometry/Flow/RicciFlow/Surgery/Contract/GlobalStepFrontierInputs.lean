import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PoincareStandardControl
import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.SpaceFormCovering

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

structure GlobalStepFrontierInputs (p : CutoffParameters) (τ ε d : ℝ) (k : ℕ)
    (DiscardedCutOpen : Type u → Prop) where
  endInput : TerminalCorePresentationInput.{u} τ ε
  neckInput : historicalNeckRecognition.{u} τ ε d k endInput.lambda
  pieceInput : ∀ (C : Type u) [TopologicalSpace C] [ChartedSpace ThreeSpace C]
    [IsManifold ThreeModel ∞ C] [T2Space C] [CompactSpace C],
    DiscardedCutOpen C → HasElementaryDiscardDecomposition C
  cylinderInput : hornCylinderLimit.{u} ε endInput.lambda
  protectInput : protectionInput.{u} τ ε endInput.lambda

theorem sphericalSpaceFormCovering_holds' : sphericalSpaceFormCovering.{u} :=
  sphericalSpaceFormCovering_holds

namespace GlobalStepFrontierInputs

variable {p : CutoffParameters} {τ ε d : ℝ} {k : ℕ} {DiscardedCutOpen : Type u → Prop}

def toGlobalStepInputs (G : GlobalStepFrontierInputs.{u} p τ ε d k DiscardedCutOpen) :
    GlobalStepInputs.{u} p τ ε d k DiscardedCutOpen where
  endInput := G.endInput
  neckInput := G.neckInput
  pieceInput := G.pieceInput
  roundInput := sphericalSpaceFormCovering_holds
  cylinderInput := G.cylinderInput
  protectInput := G.protectInput

def ofGlobalStepInputs (G : GlobalStepInputs.{u} p τ ε d k DiscardedCutOpen) :
    GlobalStepFrontierInputs.{u} p τ ε d k DiscardedCutOpen where
  endInput := G.endInput
  neckInput := G.neckInput
  pieceInput := G.pieceInput
  cylinderInput := G.cylinderInput
  protectInput := G.protectInput

@[simp]
theorem toGlobalStepInputs_endInput
    (G : GlobalStepFrontierInputs.{u} p τ ε d k DiscardedCutOpen) :
    (toGlobalStepInputs G).endInput = G.endInput := rfl

@[simp]
theorem toGlobalStepInputs_neckInput
    (G : GlobalStepFrontierInputs.{u} p τ ε d k DiscardedCutOpen) :
    (toGlobalStepInputs G).neckInput = G.neckInput := rfl

@[simp]
theorem toGlobalStepInputs_pieceInput
    (G : GlobalStepFrontierInputs.{u} p τ ε d k DiscardedCutOpen) :
    (toGlobalStepInputs G).pieceInput = G.pieceInput := rfl

@[simp]
theorem toGlobalStepInputs_cylinderInput
    (G : GlobalStepFrontierInputs.{u} p τ ε d k DiscardedCutOpen) :
    (toGlobalStepInputs G).cylinderInput = G.cylinderInput := rfl

@[simp]
theorem toGlobalStepInputs_protectInput
    (G : GlobalStepFrontierInputs.{u} p τ ε d k DiscardedCutOpen) :
    (toGlobalStepInputs G).protectInput = G.protectInput := rfl

@[simp]
theorem ofGlobalStepInputs_roundInput
    (G : GlobalStepInputs.{u} p τ ε d k DiscardedCutOpen) :
    (ofGlobalStepInputs G).endInput = G.endInput := rfl

theorem of_to (G : GlobalStepFrontierInputs.{u} p τ ε d k DiscardedCutOpen) :
    ofGlobalStepInputs (toGlobalStepInputs G) = G := by
  cases G
  rfl

theorem to_of (G : GlobalStepInputs.{u} p τ ε d k DiscardedCutOpen) :
    toGlobalStepInputs (ofGlobalStepInputs G) = G := by
  cases G
  rfl

end GlobalStepFrontierInputs

theorem nonempty_globalStepInputs_iff_frontierInputs
    (p : CutoffParameters) (τ ε d : ℝ) (k : ℕ) (DiscardedCutOpen : Type u → Prop) :
    Nonempty (GlobalStepInputs.{u} p τ ε d k DiscardedCutOpen) ↔
      Nonempty (GlobalStepFrontierInputs.{u} p τ ε d k DiscardedCutOpen) :=
  ⟨fun ⟨G⟩ => ⟨GlobalStepFrontierInputs.ofGlobalStepInputs G⟩,
    fun ⟨G⟩ => ⟨GlobalStepFrontierInputs.toGlobalStepInputs G⟩⟩

theorem nonempty_globalStepInputs_iff_exists_endInput
    (p : CutoffParameters) (τ ε d : ℝ) (k : ℕ) (DiscardedCutOpen : Type u → Prop) :
    Nonempty (GlobalStepFrontierInputs.{u} p τ ε d k DiscardedCutOpen) ↔
      ∃ (Λ : ℝ) (endInput : TerminalCorePresentationInput.{u} τ ε),
        endInput.lambda = Λ ∧
        Nonempty {G : GlobalStepFrontierInputs.{u} p τ ε d k DiscardedCutOpen //
          G.endInput = endInput} := by
  constructor
  · rintro ⟨G⟩
    exact ⟨G.endInput.lambda, G.endInput, rfl, ⟨G, rfl⟩⟩
  · rintro ⟨Λ, endInput, _hΛ, ⟨G, _hG⟩⟩
    exact ⟨G⟩

theorem nonempty_globalStepInputs_of_endInput
    (p : CutoffParameters) (τ ε d : ℝ) (k : ℕ) (DiscardedCutOpen : Type u → Prop)
    (endInput : TerminalCorePresentationInput.{u} τ ε)
    (neckInput : historicalNeckRecognition.{u} τ ε d k endInput.lambda)
    (pieceInput : ∀ (C : Type u) [TopologicalSpace C] [ChartedSpace ThreeSpace C]
      [IsManifold ThreeModel ∞ C] [T2Space C] [CompactSpace C],
      DiscardedCutOpen C → HasElementaryDiscardDecomposition C)
    (cylinderInput : hornCylinderLimit.{u} ε endInput.lambda)
    (protectInput : protectionInput.{u} τ ε endInput.lambda) :
    Nonempty (GlobalStepInputs.{u} p τ ε d k DiscardedCutOpen) :=
  ⟨GlobalStepFrontierInputs.toGlobalStepInputs
    { endInput := endInput
      neckInput := neckInput
      pieceInput := pieceInput
      cylinderInput := cylinderInput
      protectInput := protectInput }⟩

theorem not_frontierInputs_of_not_endInput
    (p : CutoffParameters) (τ ε : ℝ)
    (h : ¬ Nonempty (TerminalCorePresentationInput.{u} τ ε)) :
    ∀ (d : ℝ) (k : ℕ) (DiscardedCutOpen : Type u → Prop),
      ¬ Nonempty (GlobalStepFrontierInputs.{u} p τ ε d k DiscardedCutOpen) := by
  intro d k DiscardedCutOpen hF
  obtain ⟨G⟩ := hF
  exact h ⟨G.endInput⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
