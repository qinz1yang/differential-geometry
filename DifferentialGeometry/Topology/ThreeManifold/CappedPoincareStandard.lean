import DifferentialGeometry.Topology.ThreeManifold.CutCapCappedPresentationRealization
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardSumClosure
import DifferentialGeometry.Topology.ThreeManifold.SphericalSpaceFormOrientationClosure

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphericalCutCapTransition

universe u
variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem isOrientedPoincareStandard_capComponent
    (hnext : ∀ K : ConnectedComponents Q.Carrier,
      isOrientedPoincareStandard (Q.component K).toClosedOrientedManifold)
    (hdiscard : ∀ K : ConnectedComponents E.discarded.Carrier,
      isOrientedPoincareStandard (E.discarded.component K).toClosedOrientedManifold)
    (K : ConnectedComponents E.capped.Carrier) :
    isOrientedPoincareStandard (E.capped.component K).toClosedOrientedManifold := by
  let e : ClosedOrientedManifold.OrientedDiffeomorph E.capped
      (ClosedOrientedManifold.sum Q E.discarded) :=
    ⟨E.presentation, E.presentation_preservesOrientation⟩
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe K
  let F := e.component (ConnectedComponents.mk x)
  apply isOrientedPoincareStandard_of_orientedDiffeomorph F
  have hcomponent : e.val.continuous.connectedComponentsMap (ConnectedComponents.mk x) =
      ConnectedComponents.mk (E.presentation x) := Continuous.connectedComponentsMap_mk _ _
  rw [hcomponent]
  cases hy : E.presentation x with
  | inl q =>
    exact isOrientedPoincareStandard_of_orientedDiffeomorph
      (ClosedOrientedManifold.sumComponentInlOrientedDiffeomorph (X := Q) (Y := E.discarded) q)
      (hnext (ConnectedComponents.mk q))
  | inr d =>
    exact isOrientedPoincareStandard_of_orientedDiffeomorph
      (ClosedOrientedManifold.sumComponentInrOrientedDiffeomorph (X := Q) (Y := E.discarded) d)
      (hdiscard (ConnectedComponents.mk d))

theorem isOrientedPoincareStandard_capComponent_of_poincareControlled
    (hctrl : E.poincareControlled)
    (hnext : ∀ K : ConnectedComponents Q.Carrier,
      isPoincareStandard (Q.component K).Carrier)
    (K : ConnectedComponents E.capped.Carrier) :
    isOrientedPoincareStandard (E.capped.component K).toClosedOrientedManifold :=
  E.isOrientedPoincareStandard_capComponent
    (fun K => poincareStandardOrientationRefinement_holds (Q.component K) (hnext K))
    (fun K => poincareStandardOrientationRefinement_holds (E.discarded.component K) (hctrl K)) K

theorem isOrientedPoincareStandard_capComponent_finiteConnectedSum
    (hnext : ∀ K : ConnectedComponents Q.Carrier,
      isOrientedPoincareStandard (Q.component K).toClosedOrientedManifold)
    (hdiscard : ∀ K : ConnectedComponents E.discarded.Carrier,
      isOrientedPoincareStandard (E.discarded.component K).toClosedOrientedManifold)
    (L : List (ConnectedComponents E.capped.Carrier)) (k : ℕ) :
    isOrientedPoincareStandard
      (finiteConnectedSum (L.map E.capped.component ++
        List.replicate k (sphereTwoTimesCircleLift.ulift.{0, u}))).toClosedOrientedManifold := by
  apply isOrientedPoincareStandardSumClosed_holds
  intro F hF
  rcases List.mem_append.mp hF with hF | hF
  · obtain ⟨K, _, rfl⟩ := List.mem_map.mp hF
    exact E.isOrientedPoincareStandard_capComponent hnext hdiscard K
  · obtain ⟨_, rfl⟩ := List.mem_replicate.mp hF
    apply isOrientedPoincareStandard_of_standard_factor
    apply isStandardFactor_of_isSphereTwoTimesCircleFactor
    obtain ⟨f, hf⟩ := isSphereTwoTimesCircleFactor_sphereTwoTimesCircleLift
    let U := (ClosedOrientedManifold.uliftOrientedDiffeomorph.{0, u}
      sphereTwoTimesCircleLift.toClosedOrientedManifold).symm
    exact ⟨U.val.trans f, Diffeomorph.preservesOrientation_trans U.property hf⟩

end DifferentialGeometry.Topology.SphericalCutCapTransition
