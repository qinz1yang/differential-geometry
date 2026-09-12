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
    (hunit : ∀ N : Topology.ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (Topology.ClosedOrientedManifold.OrientedDiffeomorph
        (Topology.connectedSum N Topology.standardThreeSphereLift.{u}).toClosedOrientedManifold
        N.toClosedOrientedManifold))
    (hcongr : ∀ (L K : List (Topology.ConnectedClosedOrientedManifold.{u} 3)),
      List.Forall₂ (fun (M N : Topology.ConnectedClosedOrientedManifold.{u} 3) =>
        Nonempty (Topology.ClosedOrientedManifold.OrientedDiffeomorph
          M.toClosedOrientedManifold N.toClosedOrientedManifold)) L K →
      Nonempty (Topology.ClosedOrientedManifold.OrientedDiffeomorph
        (Topology.finiteConnectedSum L).toClosedOrientedManifold
        (Topology.finiteConnectedSum K).toClosedOrientedManifold))
    (hconn : ∀ i : Fin W.history.eventCount,
      ∀ C : ConnectedComponents (W.history.stage i.castSucc).Carrier,
        ((W.history.cutCapTrace.transition i).cutIncidenceGraph C).Connected)
    (hsum : ∀ i : Fin W.history.eventCount,
      (W.history.cutCapTrace.transition i).componentConnectedSumDecomposition)
    (hsumClosed : Topology.poincareStandardSumClosed.{u})
    [ConnectedSpace M.Carrier] [SimplyConnectedSpace M.Carrier] :
    Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ Topology.standardThreeSphereLift.{u}.Carrier) :=
  Topology.exists_diffeomorph_standardThreeSphere_of_isPoincareStandard
    Topology.fundamentalGroup_finiteConnectedSum_freeProduct
    (fun G p => Topology.SphericalSpaceFormGroup.nonempty_fundamentalGroupManifoldEquiv G p)
    Topology.exists_orientedDiffeomorph_standardThreeSphere_of_subsingleton_group
    (fun p => Topology.exists_fundamentalGroupMulEquivInt_sphereTwoTimesCircle p)
    hunit hcongr (W.isPoincareStandard hconn hsum hsumClosed)

def smoothPoincareConjecture : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [SimplyConnectedSpace M],
    Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ Topology.standardThreeSphereLift.{u}.Carrier)

theorem smoothPoincareConjecture_of_poincareControlledExtinction
    (hunit : ∀ N : Topology.ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (Topology.ClosedOrientedManifold.OrientedDiffeomorph
        (Topology.connectedSum N Topology.standardThreeSphereLift.{u}).toClosedOrientedManifold
        N.toClosedOrientedManifold))
    (hcongr : ∀ (L K : List (Topology.ConnectedClosedOrientedManifold.{u} 3)),
      List.Forall₂ (fun (M N : Topology.ConnectedClosedOrientedManifold.{u} 3) =>
        Nonempty (Topology.ClosedOrientedManifold.OrientedDiffeomorph
          M.toClosedOrientedManifold N.toClosedOrientedManifold)) L K →
      Nonempty (Topology.ClosedOrientedManifold.OrientedDiffeomorph
        (Topology.finiteConnectedSum L).toClosedOrientedManifold
        (Topology.finiteConnectedSum K).toClosedOrientedManifold))
    (hconn : ∀ (H : FiniteSurgeryHistory.{u}) (i : Fin H.eventCount)
      (C : ConnectedComponents (H.stage i.castSucc).Carrier),
      ((H.cutCapTrace.transition i).cutIncidenceGraph C).Connected)
    (hsum : ∀ (H : FiniteSurgeryHistory.{u}) (i : Fin H.eventCount),
      (H.cutCapTrace.transition i).componentConnectedSumDecomposition)
    (hsumClosed : Topology.poincareStandardSumClosed.{u})
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
    (hunit := hunit) (hcongr := hcongr)
    (hconn := fun i C => hconn _ i C) (hsum := fun i => hsum _ i)
    (hsumClosed := hsumClosed)

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
