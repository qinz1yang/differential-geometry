import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Poincare
import DifferentialGeometry.Topology.ThreeManifold.CutCapGluing

noncomputable section

open Manifold
open DifferentialGeometry.Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

universe u

namespace PoincareControlledExtinction

variable {M : ClosedOrientedManifold.{u} 3}
  {g : SmoothRiemannianMetric (𝓡 3) M.Carrier}

theorem isPoincareStandard_of_localReconstruction [ConnectedSpace M.Carrier]
    (W : PoincareControlledExtinction M g)
    (hrec : ∀ i : Fin W.history.eventCount,
      (W.history.cutCapTrace.transition i).localReconstruction) :
    Topology.isPoincareStandard M.Carrier :=
  W.history.cutCapTrace.isPoincareStandard_of_initialIdentification
    hrec W.controlled (W.history.extinct_trace W.extinct)
    poincareStandardSumClosed_holds M
    W.initial.cutCapIdentification

end PoincareControlledExtinction

theorem exists_diffeomorph_standardThreeSphere_of_localReconstruction
    {M : Topology.ClosedOrientedManifold.{u} 3} {g : SmoothRiemannianMetric (𝓡 3) M.Carrier}
    (W : PoincareControlledExtinction M g)
    (hrec : ∀ i : Fin W.history.eventCount,
      (W.history.cutCapTrace.transition i).localReconstruction)
    [ConnectedSpace M.Carrier] [SimplyConnectedSpace M.Carrier] :
    Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ Topology.standardThreeSphereLift.{u}.Carrier) :=
  Topology.exists_diffeomorph_standardThreeSphere_of_isPoincareStandard
    (W.isPoincareStandard_of_localReconstruction hrec)

theorem smoothPoincareConjecture_of_localReconstruction
    (hrec : ∀ (H : FiniteSurgeryHistory.{u}) (i : Fin H.eventCount),
      (H.cutCapTrace.transition i).localReconstruction)
    (hext : ∀ (M : Topology.ConnectedClosedOrientedManifold.{u} 3)
      [SimplyConnectedSpace M.Carrier]
      (g : SmoothRiemannianMetric (𝓡 3) M.Carrier),
      Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g)) :
    smoothPoincareConjecture.{u} := by
  intro M _ _ _ _ _ _ _
  obtain ⟨g⟩ := Geometry.nonempty_smoothRiemannianMetric (I := 𝓡 3) (M := M)
  obtain ⟨o⟩ := Topology.Manifold.exists_manifoldOrientation_of_simply_connected
    (E := EuclideanSpace ℝ (Fin 3)) (M := M) (n := 3) (by simp)
  exact exists_diffeomorph_standardThreeSphere_of_localReconstruction
    (W := (hext { Carrier := M, orientation := o } g).some) (hrec := fun i => hrec _ i)

end DifferentialGeometry.PDE.RicciFlow.Surgery
