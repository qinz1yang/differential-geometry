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
    (hclass : ∀ (N : Type u) [TopologicalSpace N]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
      [T2Space N] [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
      Topology.isPoincareStandard N →
        Nonempty (N ≃ₘ⟮𝓡 3, 𝓡 3⟯ Topology.standardThreeSphereLift.{u}.Carrier))
    (hcut : ∀ i : Fin W.history.eventCount,
      (W.history.cutCapTrace.transition i).localReconstruction)
    (hsum : Topology.poincareStandardSumClosed.{u})
    [ConnectedSpace M.Carrier] [SimplyConnectedSpace M.Carrier] :
    Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ Topology.standardThreeSphereLift.{u}.Carrier) :=
  hclass M.Carrier (W.isPoincareStandard hcut hsum)

def smoothPoincareConjecture : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [SimplyConnectedSpace M],
    Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ Topology.standardThreeSphereLift.{u}.Carrier)

theorem smoothPoincareConjecture_of_poincareControlledExtinction
    (hclass : ∀ (N : Type u) [TopologicalSpace N]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
      [T2Space N] [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
      Topology.isPoincareStandard N →
        Nonempty (N ≃ₘ⟮𝓡 3, 𝓡 3⟯ Topology.standardThreeSphereLift.{u}.Carrier))
    (hcut : ∀ (H : FiniteSurgeryHistory.{u}) (i : Fin H.eventCount),
      (H.cutCapTrace.transition i).localReconstruction)
    (hsum : Topology.poincareStandardSumClosed.{u})
    (hmet : ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
      [SimplyConnectedSpace M], Nonempty (SmoothRiemannianMetric (𝓡 3) M))
    (hor : ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
      [SimplyConnectedSpace M], Nonempty (ManifoldOrientation (𝓡 3) M 3))
    (hext : ∀ (M : Topology.ConnectedClosedOrientedManifold.{u} 3) [SimplyConnectedSpace M.Carrier]
      (g : SmoothRiemannianMetric (𝓡 3) M.Carrier),
      Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g)) :
    smoothPoincareConjecture.{u} := by
  intro M _ _ _ _ _ _ _
  obtain ⟨g⟩ := hmet M
  obtain ⟨o⟩ := hor M
  exact exists_diffeomorph_standardThreeSphere_of_poincareControlledExtinction
    (W := (hext { Carrier := M, orientation := o } g).some)
    (hclass := hclass) (hcut := fun i => hcut _ i) (hsum := hsum)

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
