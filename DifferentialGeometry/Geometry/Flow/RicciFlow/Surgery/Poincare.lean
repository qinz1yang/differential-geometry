import DifferentialGeometry.Topology.ThreeManifold.CutCapGluing
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardClassification
import DifferentialGeometry.Topology.VanKampen.FiniteConnectedSumFreeProduct
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ExtinctionReconstruction

noncomputable section

open Manifold
open DifferentialGeometry.Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

universe u

theorem exists_diffeomorph_standardThreeSphere_of_poincareControlledExtinction
    {M : Topology.ClosedOrientedManifold.{u} 3} {g : SmoothRiemannianMetric (𝓡 3) M.Carrier}
    (W : PoincareControlledExtinction M g)
    (hunitR : ∀ X : Topology.ConnectedClosedOrientedManifold.{u} 3,
      Nonempty ((Topology.connectedSum X
        Topology.standardThreeSphereLift.{u}).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯ X.toClosedOrientedManifold.Carrier))
    (hunitL : ∀ X : Topology.ConnectedClosedOrientedManifold.{u} 3,
      Nonempty ((Topology.connectedSum Topology.standardThreeSphereLift.{u} X
        ).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯ X.toClosedOrientedManifold.Carrier))
    (hassoc : ∀ X Y Z : Topology.ConnectedClosedOrientedManifold.{u} 3,
      Nonempty ((Topology.connectedSum (Topology.connectedSum X Y) Z
        ).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯
        (Topology.connectedSum X (Topology.connectedSum Y Z)).toClosedOrientedManifold.Carrier))
    (htransportL : ∀ X X' Y : Topology.ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (X.toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        X'.toClosedOrientedManifold.Carrier) →
      Nonempty ((Topology.connectedSum X Y).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯ (Topology.connectedSum X' Y).toClosedOrientedManifold.Carrier))
    (htransportR : ∀ X Y Y' : Topology.ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (Y.toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        Y'.toClosedOrientedManifold.Carrier) →
      Nonempty ((Topology.connectedSum X Y).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯ (Topology.connectedSum X Y').toClosedOrientedManifold.Carrier))
    (hsum : ∀ i : Fin W.history.eventCount,
      (W.history.cutCapTrace.transition i).componentConnectedSumDecomposition)
    [ConnectedSpace M.Carrier] [SimplyConnectedSpace M.Carrier] :
    Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ Topology.standardThreeSphereLift.{u}.Carrier) :=
  Topology.exists_diffeomorph_standardThreeSphere_of_isPoincareStandard
    Topology.fundamentalGroup_finiteConnectedSum_freeProduct
    (fun G p => Topology.SphericalSpaceFormGroup.nonempty_fundamentalGroupManifoldEquiv G p)
    Topology.exists_orientedDiffeomorph_standardThreeSphere_of_subsingleton_group
    (fun p => Topology.exists_fundamentalGroupMulEquivInt_sphereTwoTimesCircle p)
    hunitR
    (fun _ _ hf => Topology.finiteConnectedSum_congr_of_transport htransportL htransportR hf)
    (W.isPoincareStandard hsum
      (Topology.poincareStandardSumClosed_of_unit_assoc_transport
        hunitR hunitL hassoc htransportL htransportR))

def smoothPoincareConjecture : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [SimplyConnectedSpace M],
    Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ Topology.standardThreeSphereLift.{u}.Carrier)

theorem smoothPoincareConjecture_of_poincareControlledExtinction
    (hunitR : ∀ X : Topology.ConnectedClosedOrientedManifold.{u} 3,
      Nonempty ((Topology.connectedSum X
        Topology.standardThreeSphereLift.{u}).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯ X.toClosedOrientedManifold.Carrier))
    (hunitL : ∀ X : Topology.ConnectedClosedOrientedManifold.{u} 3,
      Nonempty ((Topology.connectedSum Topology.standardThreeSphereLift.{u} X
        ).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯ X.toClosedOrientedManifold.Carrier))
    (hassoc : ∀ X Y Z : Topology.ConnectedClosedOrientedManifold.{u} 3,
      Nonempty ((Topology.connectedSum (Topology.connectedSum X Y) Z
        ).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯
        (Topology.connectedSum X (Topology.connectedSum Y Z)).toClosedOrientedManifold.Carrier))
    (htransportL : ∀ X X' Y : Topology.ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (X.toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        X'.toClosedOrientedManifold.Carrier) →
      Nonempty ((Topology.connectedSum X Y).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯ (Topology.connectedSum X' Y).toClosedOrientedManifold.Carrier))
    (htransportR : ∀ X Y Y' : Topology.ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (Y.toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        Y'.toClosedOrientedManifold.Carrier) →
      Nonempty ((Topology.connectedSum X Y).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯ (Topology.connectedSum X Y').toClosedOrientedManifold.Carrier))
    (hsum : ∀ (H : FiniteSurgeryHistory.{u}) (i : Fin H.eventCount),
      (H.cutCapTrace.transition i).componentConnectedSumDecomposition)
    (hext : ∀ (M : Topology.ConnectedClosedOrientedManifold.{u} 3) [SimplyConnectedSpace M.Carrier]
      (g : SmoothRiemannianMetric (𝓡 3) M.Carrier),
      Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g)) :
    smoothPoincareConjecture.{u} := by
  intro M _ _ _ _ _ _ _
  obtain ⟨g⟩ := Geometry.nonempty_smoothRiemannianMetric (I := 𝓡 3) (M := M)
  obtain ⟨o⟩ := Topology.Manifold.exists_manifoldOrientation_of_simply_connected
    (E := EuclideanSpace ℝ (Fin 3)) (M := M) (n := 3) (by simp)
  exact exists_diffeomorph_standardThreeSphere_of_poincareControlledExtinction
    (W := (hext { Carrier := M, orientation := o } g).some)
    (hunitR := hunitR) (hunitL := hunitL) (hassoc := hassoc)
    (htransportL := htransportL) (htransportR := htransportR)
    (hsum := fun i => hsum _ i)

def topologicalPoincareConjecture : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M],
    Nonempty (M ≃ₜ Topology.standardThreeSphereLift.{u}.Carrier)

theorem topologicalPoincareConjecture_of_smoothStructureInput
    (hsm : ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [CompactSpace M]
      [ConnectedSpace M] [SimplyConnectedSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M],
      ∃ inst : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
        letI := inst
        Nonempty (IsManifold (𝓡 3) ∞ M))
    (hsmooth : smoothPoincareConjecture.{u}) :
    topologicalPoincareConjecture.{u} := by
  intro M _ _ _ _ _ _
  obtain ⟨inst, hman⟩ := hsm M
  let inst := inst
  let smooth : IsManifold (𝓡 3) ∞ M := hman.some
  exact ⟨(hsmooth M).some.toHomeomorph⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery
