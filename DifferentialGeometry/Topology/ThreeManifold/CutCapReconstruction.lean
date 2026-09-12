import DifferentialGeometry.Topology.ThreeManifold.PoincareStandard

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

def poincareStandardSumClosed : Prop :=
  ∀ L : List (ConnectedClosedOrientedManifold.{u} 3),
    (∀ F ∈ L, isPoincareStandard F.Carrier) → isPoincareStandard (finiteConnectedSum L).Carrier

namespace ClosedOrientedManifold

variable (M : ClosedOrientedManifold.{u} 3) [ConnectedSpace M.Carrier]

theorem isPoincareStandard_of_component (C : ConnectedComponents M.Carrier)
    (h : isPoincareStandard (M.component C).Carrier) : isPoincareStandard M.Carrier :=
  isPoincareStandard_of_diffeomorph (componentDiffeomorph M C) h

end ClosedOrientedManifold

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

def cutIndices (C : ConnectedComponents M.Carrier) : Finset E.tubes.Index := by
  classical
  exact Finset.univ.filter fun a =>
    ∀ z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Set.Icc (-2 : ℝ) 2,
      (E.tubes.tube a) z ∈ ClosedOrientedManifold.componentSet M C

def localReconstruction : Prop :=
  ∀ C : ConnectedComponents M.Carrier,
    ∃ L : List (ConnectedClosedOrientedManifold.{u} 3),
      L.length = (E.cutIndices C).card + 1 ∧
      (∀ F ∈ L,
        (∃ D : ConnectedComponents Q.Carrier,
          Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
            F.toClosedOrientedManifold (Q.component D).toClosedOrientedManifold)) ∨
        (∃ D : ConnectedComponents E.discarded.Carrier,
          Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
            F.toClosedOrientedManifold (E.discarded.component D).toClosedOrientedManifold)) ∨
        (∃ f : F.Carrier ≃ₘ⟮𝓡 3, (𝓡 2).prod (𝓡 1)⟯ SphereTwoTimesCircle,
          f.preservesOrientation F.orientation sphereTwoTimesCircleOrientation)) ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (M.component C).toClosedOrientedManifold (finiteConnectedSum L).toClosedOrientedManifold)

theorem componentwise_isPoincareStandard (h : E.localReconstruction)
    (hctrl : E.poincareControlled)
    (hnext : ∀ C : ConnectedComponents Q.Carrier, isPoincareStandard (Q.component C).Carrier)
    (hsum : poincareStandardSumClosed.{u}) :
    ∀ C : ConnectedComponents M.Carrier, isPoincareStandard (M.component C).Carrier := by
  intro C
  obtain ⟨L, -, hfactors, ⟨ρ⟩⟩ := h C
  refine isPoincareStandard_of_diffeomorph ρ (hsum L ?_)
  intro F hF
  rcases hfactors F hF with ⟨D, ⟨e⟩⟩ | ⟨D, ⟨e⟩⟩ | ⟨f, hf⟩
  · exact isPoincareStandard_of_diffeomorph e (hnext D)
  · exact isPoincareStandard_of_diffeomorph e (hctrl D)
  · exact isPoincareStandard_of_standard_factor F (Or.inr ⟨f, hf⟩)

end SphericalCutCapTransition

namespace FiniteCutCapTrace

variable (T : FiniteCutCapTrace.{u})

theorem componentwise_isPoincareStandard
    (h : ∀ i : Fin T.eventCount, (T.transition i).localReconstruction)
    (hctrl : T.poincareControlled) (hext : T.extinct) (hsum : poincareStandardSumClosed.{u}) :
    ∀ i : Fin (T.eventCount + 1), ∀ C : ConnectedComponents (T.stage i).Carrier,
      isPoincareStandard ((T.stage i).component C).Carrier := by
  have hbase : ∀ C : ConnectedComponents (T.stage (Fin.last T.eventCount)).Carrier,
      isPoincareStandard ((T.stage (Fin.last T.eventCount)).component C).Carrier := by
    have hEmpty : IsEmpty (ConnectedComponents (T.stage (Fin.last T.eventCount)).Carrier) :=
      ConnectedComponents.isEmpty_iff_isEmpty.mpr hext
    intro C
    exact hEmpty.elim C
  refine Fin.reverseInduction (motive := fun j => ∀ C : ConnectedComponents (T.stage j).Carrier,
    isPoincareStandard ((T.stage j).component C).Carrier) hbase ?_
  intro j ih
  exact (T.transition j).componentwise_isPoincareStandard (h j) (hctrl j) ih hsum

theorem isPoincareStandard_of_initialIdentification
    (h : ∀ i : Fin T.eventCount, (T.transition i).localReconstruction)
    (hctrl : T.poincareControlled) (hext : T.extinct) (hsum : poincareStandardSumClosed.{u})
    (M : ClosedOrientedManifold.{u} 3) [ConnectedSpace M.Carrier]
    (Φ : T.InitialIdentification M) : isPoincareStandard M.Carrier := by
  have hcomp := T.componentwise_isPoincareStandard h hctrl hext hsum 0
  have : ConnectedSpace (T.stage 0).Carrier :=
    Φ.1.toHomeomorph.connectedSpace_iff.mp inferInstance
  let C : ConnectedComponents (T.stage 0).Carrier :=
    ConnectedComponents.mk (Φ.1 (Classical.choice inferInstance))
  exact isPoincareStandard_of_diffeomorph Φ.1
    ((T.stage 0).isPoincareStandard_of_component C (hcomp C))

end FiniteCutCapTrace

end DifferentialGeometry.Topology
