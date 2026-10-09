import DifferentialGeometry.Topology.ThreeManifold.CutCapConnectedSumSmooth
import DifferentialGeometry.Topology.ThreeManifold.CappedPoincareStandard
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardUnion
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardComponentTransport
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardComponentwise

noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphericalCutCapTransition

universe u
variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem componentwise_isPoincareStandard_of_poincareControlled
    (hctrl : E.poincareControlled)
    (hnext : ∀ C : ConnectedComponents Q.Carrier, isPoincareStandard (Q.component C).Carrier) :
    ∀ C : ConnectedComponents M.Carrier, isPoincareStandard (M.component C).Carrier := by
  classical
  obtain ⟨W,hW,assign,L,k,hm,hn,hne,⟨D⟩⟩ := E.exists_diffeomorph_finiteConnectedSum_capComponents
  let := hW
  let := Fintype.ofFinite W
  let N := fun w => (finiteConnectedSum ((L w).map E.capped.component ++
    List.replicate (k w) (sphereTwoTimesCircleLift.ulift.{0, u}))).toClosedOrientedManifold
  have hN (w : W) : isOrientedPoincareStandard (N w) :=
    E.isOrientedPoincareStandard_capComponent_finiteConnectedSum
      (fun K => poincareStandardOrientationRefinement_holds (Q.component K) (hnext K))
      (fun K => poincareStandardOrientationRefinement_holds (E.discarded.component K) (hctrl K))
      (L w) (k w)
  have hcomponents : ∀ C : ConnectedComponents (closedOrientedUnion N).Carrier,
      isPoincareStandard ((closedOrientedUnion N).component C).Carrier := by
    intro C
    apply isPoincareStandard_of_isOrientedPoincareStandard
    apply componentwise_isOrientedPoincareStandard_closedOrientedUnion N _ C
    intro w K
    exact isOrientedPoincareStandard_of_orientedDiffeomorph
      ((N w).componentOrientedDiffeomorph K) (hN w)
  exact (ClosedOrientedManifold.componentwise_isPoincareStandard_iff_of_diffeomorph
    (M := M) (N := closedOrientedUnion N) D).mpr hcomponents

end DifferentialGeometry.Topology.SphericalCutCapTransition

namespace DifferentialGeometry.Topology.FiniteCutCapTrace

universe u

theorem componentwise_isPoincareStandard_of_poincareControlled_extinct
    (T : FiniteCutCapTrace.{u}) (hctrl : T.poincareControlled) (hext : T.extinct) :
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
  exact (T.transition j).componentwise_isPoincareStandard_of_poincareControlled (hctrl j) ih

theorem isPoincareStandard_of_initialIdentification_of_poincareControlled_extinct
    (T : FiniteCutCapTrace.{u}) (hctrl : T.poincareControlled) (hext : T.extinct)
    (M : ClosedOrientedManifold.{u} 3) [ConnectedSpace M.Carrier]
    (Φ : T.InitialIdentification M) : isPoincareStandard M.Carrier := by
  have hcomp := T.componentwise_isPoincareStandard_of_poincareControlled_extinct hctrl hext 0
  have : ConnectedSpace (T.stage 0).Carrier :=
    Φ.val.toHomeomorph.connectedSpace_iff.mp inferInstance
  let C := ConnectedComponents.mk (Φ.val (Classical.choice (inferInstance : Nonempty M.Carrier)))
  exact isPoincareStandard_of_diffeomorph Φ.val
    ((T.stage 0).isPoincareStandard_of_component C (hcomp C))

end DifferentialGeometry.Topology.FiniteCutCapTrace
