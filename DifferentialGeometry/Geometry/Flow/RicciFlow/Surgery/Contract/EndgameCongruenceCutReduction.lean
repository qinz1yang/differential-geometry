import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.ExtinctionContractReduction
import DifferentialGeometry.Topology.ThreeManifold.CutCapIncidenceCycleRank

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem nonempty_poincareExtinctionContracts_of_geometricInput
    (DiscardedCutOpen : Type u → Prop)
    (hgeometric : geometricReconstructionBackground.{u})
    (hterminal : ∃ (p : CutoffParameters) (τ ε d : ℝ) (k : ℕ),
      Nonempty (GlobalStepInputs.{u} p τ ε d k DiscardedCutOpen))
    (hmetric : isCommonLocalRealizationOnAdmissibleStrips.{u})
    (hcomponentSum : ∀ (H : DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.{u})
      (i : Fin H.eventCount), (H.cutCapTrace.transition i).componentConnectedSumDecomposition) :
    Nonempty (PoincareExtinctionContracts DiscardedCutOpen) :=
  ⟨{ geometric := hgeometric
     terminalStep := hterminal
     metricStep := hmetric
     componentSumInput := hcomponentSum
     sumInput := DifferentialGeometry.Topology.poincareStandardSumClosed_holds
     congruenceInput := finiteConnectedSum_orientedDiffeomorph_of_forall₂ }⟩

theorem nonempty_poincareExtinctionContracts_of_geometricInput_of_isCommonLocalRealization
    (DiscardedCutOpen : Type u → Prop)
    (hgeometric : geometricReconstructionBackground.{u})
    (hterminal : ∃ (p : CutoffParameters) (τ ε d : ℝ) (k : ℕ),
      Nonempty (GlobalStepInputs.{u} p τ ε d k DiscardedCutOpen))
    (hmetric : isCommonLocalRealization.{u})
    (hcomponentSum : ∀ (H : DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.{u})
      (i : Fin H.eventCount), (H.cutCapTrace.transition i).componentConnectedSumDecomposition) :
    Nonempty (PoincareExtinctionContracts DiscardedCutOpen) :=
  nonempty_poincareExtinctionContracts_of_geometricInput DiscardedCutOpen hgeometric hterminal
    (isCommonLocalRealizationOnAdmissibleStrips_of_isCommonLocalRealization hmetric) hcomponentSum

theorem nonempty_poincareExtinctionContracts_of_localReconstruction
    (DiscardedCutOpen : Type u → Prop)
    (hgeometric : geometricReconstructionBackground.{u})
    (hterminal : ∃ (p : CutoffParameters) (τ ε d : ℝ) (k : ℕ),
      Nonempty (GlobalStepInputs.{u} p τ ε d k DiscardedCutOpen))
    (hmetric : isCommonLocalRealizationOnAdmissibleStrips.{u})
    (hlocal : ∀ (H : DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.{u})
      (i : Fin H.eventCount), (H.cutCapTrace.transition i).localReconstruction) :
    Nonempty (PoincareExtinctionContracts DiscardedCutOpen) :=
  nonempty_poincareExtinctionContracts_of_geometricInput DiscardedCutOpen hgeometric hterminal
    hmetric fun H i =>
      ((H.cutCapTrace.transition i).localReconstruction_iff_componentConnectedSumDecomposition).mp
        (hlocal H i)

theorem nonempty_poincareExtinctionContracts_of_localReconstruction_of_isCommonLocalRealization
    (DiscardedCutOpen : Type u → Prop)
    (hgeometric : geometricReconstructionBackground.{u})
    (hterminal : ∃ (p : CutoffParameters) (τ ε d : ℝ) (k : ℕ),
      Nonempty (GlobalStepInputs.{u} p τ ε d k DiscardedCutOpen))
    (hmetric : isCommonLocalRealization.{u})
    (hlocal : ∀ (H : DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.{u})
      (i : Fin H.eventCount), (H.cutCapTrace.transition i).localReconstruction) :
    Nonempty (PoincareExtinctionContracts DiscardedCutOpen) :=
  nonempty_poincareExtinctionContracts_of_localReconstruction DiscardedCutOpen hgeometric hterminal
    (isCommonLocalRealizationOnAdmissibleStrips_of_isCommonLocalRealization hmetric) hlocal

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
