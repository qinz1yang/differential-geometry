import DifferentialGeometry.Topology.ThreeManifold.CutCapGluing
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardClassification
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardFactorOrientationReduction
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardOrientationRefinement
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
    (hstd : Topology.factorOrientationClosure.{u})
    (hsum : ∀ i : Fin W.history.eventCount,
      (W.history.cutCapTrace.transition i).componentConnectedSumDecomposition)
    [ConnectedSpace M.Carrier] [SimplyConnectedSpace M.Carrier] :
    Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ Topology.standardThreeSphereLift.{u}.Carrier) :=
  Topology.exists_diffeomorph_standardThreeSphere_of_isPoincareStandard
    (W.isPoincareStandard hsum
      (Topology.poincareStandardSumClosed_of_factorOrientationClosure hstd))

def smoothPoincareConjecture : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [SimplyConnectedSpace M],
    Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ Topology.standardThreeSphereLift.{u}.Carrier)

theorem smoothPoincareConjecture_of_poincareControlledExtinction
    (hstd : Topology.factorOrientationClosure.{u})
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
    (hstd := hstd)
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
