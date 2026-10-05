import DifferentialGeometry.Topology.ThreeManifold.Surgery.CutCap.SmoothTransition
import DifferentialGeometry.Topology.Manifold.ClosedOriented.Empty

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

abbrev emptyOrientedThreeStage : OrientedThreeStage.{0} :=
  DifferentialGeometry.Topology.ClosedOrientedManifold.empty 3

theorem SmoothCutCapTransition.nonempty_output {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) : Nonempty N.Carrier := by
  by_cases hI : Nonempty X.trace.tubes.Index
  · obtain ⟨a⟩ := hI
    exact ⟨X.trace.capping.cap (a, false) ⟨0, by simp [ThreeBall]⟩⟩
  · have hEmpty : IsEmpty X.trace.tubes.Index := ⟨fun a => hI ⟨a⟩⟩
    have hcore : X.trace.tubes.core = Set.univ :=
      @TubeSystem.core_eq_univ_of_isEmpty _ _ X.trace.tubes hEmpty
    obtain ⟨p⟩ := X.source_nonempty
    exact ⟨X.trace.capping.coreInclusion ⟨p, by rw [hcore]; exact Set.mem_univ p⟩⟩

theorem SmoothCutCapTransition.nonempty_output_piece {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) : Nonempty Q.Carrier ∨ Nonempty D.Carrier := by
  obtain ⟨n⟩ := X.nonempty_output
  cases h : X.presentation n with
  | inl q => exact Or.inl ⟨q⟩
  | inr d => exact Or.inr ⟨d⟩

theorem not_nonempty_smoothCutCapTransition_of_isEmpty_pieces
    {P Q D N : OrientedThreeStage.{u}} (hQ : IsEmpty Q.Carrier) (hD : IsEmpty D.Carrier) :
    ¬ Nonempty (SmoothCutCapTransition P Q D N) := by
  rintro ⟨X⟩
  rcases X.nonempty_output_piece with h | h
  · exact hQ.false h.some
  · exact hD.false h.some

theorem not_nonempty_smoothCutCapTransition_empty_output (P N : OrientedThreeStage.{0}) :
    ¬ Nonempty (SmoothCutCapTransition P emptyOrientedThreeStage emptyOrientedThreeStage N) :=
  not_nonempty_smoothCutCapTransition_of_isEmpty_pieces PEmpty.instIsEmpty PEmpty.instIsEmpty

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
