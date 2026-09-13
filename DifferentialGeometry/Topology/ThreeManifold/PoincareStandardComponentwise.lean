import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardDiscarded
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardOriented
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardOrientationRefinement
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardModels

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

theorem isStandardFactor_of_orientedDiffeomorph
    {M N : ConnectedClosedOrientedManifold.{u} 3}
    (f : ClosedOrientedManifold.OrientedDiffeomorph
      M.toClosedOrientedManifold N.toClosedOrientedManifold)
    (h : isStandardFactor M) : isStandardFactor N := by
  rcases h with ⟨G, ⟨e⟩⟩ | ⟨φ, hφ⟩
  · exact Or.inl ⟨G, ⟨f.symm.trans e⟩⟩
  · exact Or.inr ⟨f.symm.1.trans φ,
      Diffeomorph.preservesOrientation_trans f.symm.2 hφ⟩

theorem isStandardFactor_iff_of_orientedDiffeomorph
    {M N : ConnectedClosedOrientedManifold.{u} 3}
    (f : ClosedOrientedManifold.OrientedDiffeomorph
      M.toClosedOrientedManifold N.toClosedOrientedManifold) :
    isStandardFactor M ↔ isStandardFactor N :=
  ⟨isStandardFactor_of_orientedDiffeomorph f,
    isStandardFactor_of_orientedDiffeomorph f.symm⟩

namespace ClosedOrientedManifold

variable (D : ClosedOrientedManifold.{u} 3)

noncomputable def componentInclusionDiffeomorph [PreconnectedSpace D.Carrier]
    (C : ConnectedComponents D.Carrier) :
    ↥(D.componentOpen C) ≃ₘ⟮𝓡 3, 𝓡 3⟯ D.Carrier where
  toFun := Subtype.val
  invFun := fun x => ⟨x, by rw [componentOpen_eq_top_of_preconnectedSpace D C]; trivial⟩
  left_inv := fun x => Subtype.ext rfl
  right_inv := fun _ => rfl
  contMDiff_toFun := contMDiff_subtype_val
  contMDiff_invFun := by
    intro x
    exact codRestr_contMDiffAt (V := D.componentOpen C) (f := id)
      (fun _ => by rw [componentOpen_eq_top_of_preconnectedSpace D C]; trivial) contMDiffAt_id

theorem componentInclusionDiffeomorph_preservesOrientation [PreconnectedSpace D.Carrier]
    (C : ConnectedComponents D.Carrier) :
    (D.componentInclusionDiffeomorph C).preservesOrientation
      (D.component C).toClosedOrientedManifold.orientation D.orientation := by
  intro x
  have htangent : ((D.componentInclusionDiffeomorph C).mfderivToContinuousLinearEquiv
        (by simp) x).toLinearEquiv = D.componentInclusionTangentEquiv C x := by
    ext v
    rfl
  rw [htangent]
  exact D.componentInclusion_preservesOrientation C x

noncomputable def componentOrientedDiffeomorph [PreconnectedSpace D.Carrier]
    (C : ConnectedComponents D.Carrier) :
    ClosedOrientedManifold.OrientedDiffeomorph (D.component C).toClosedOrientedManifold D :=
  ⟨D.componentInclusionDiffeomorph C, D.componentInclusionDiffeomorph_preservesOrientation C⟩

theorem componentwiseStandardFactor_iff :
    D.componentwiseStandardFactor ↔ ∀ C : ConnectedComponents D.Carrier,
      isStandardFactor (D.component C) := by
  constructor
  · intro h C
    obtain ⟨N, hN, ⟨e⟩⟩ := h C
    exact isStandardFactor_of_orientedDiffeomorph e.symm hN
  · intro h C
    exact ⟨D.component C, h C, ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩⟩

theorem componentwiseConnectedSumStandardFactor_iff_isOrientedPoincareStandard :
    D.componentwiseConnectedSumStandardFactor ↔
      ∀ C : ConnectedComponents D.Carrier,
        isOrientedPoincareStandard (D.component C).toClosedOrientedManifold := by
  constructor
  · intro h C
    obtain ⟨L, hL, ⟨e⟩⟩ := h C
    exact ⟨⟨L, hL, e⟩⟩
  · intro h C
    obtain ⟨p⟩ := h C
    exact ⟨p.factors, p.standard, ⟨p.diffeomorph⟩⟩

theorem componentwiseConnectedSumStandardFactor_of_orientationRefinement
    (h : poincareStandardOrientationRefinement.{u})
    (hD : ∀ C : ConnectedComponents D.Carrier,
      isPoincareStandard (D.component C).Carrier) :
    D.componentwiseConnectedSumStandardFactor :=
  (D.componentwiseConnectedSumStandardFactor_iff_isOrientedPoincareStandard).mpr fun C =>
    h (D.component C) (hD C)

end ClosedOrientedManifold

namespace ConnectedClosedOrientedManifold

theorem componentwiseStandardFactor_of_isStandardFactor
    (M : ConnectedClosedOrientedManifold.{u} 3) (h : isStandardFactor M) :
    M.toClosedOrientedManifold.componentwiseStandardFactor := fun C =>
  ⟨M, h, ⟨M.toClosedOrientedManifold.componentOrientedDiffeomorph C⟩⟩

end ConnectedClosedOrientedManifold

theorem sphereTwoTimesCircleLift_componentwiseStandardFactor :
    sphereTwoTimesCircleLift.toClosedOrientedManifold.componentwiseStandardFactor :=
  sphereTwoTimesCircleLift.componentwiseStandardFactor_of_isStandardFactor
    isStandardFactor_sphereTwoTimesCircleLift

theorem exists_componentwiseStandardFactor_nonemptyComponent :
    ∃ D : ClosedOrientedManifold.{u} 3, D.componentwiseStandardFactor ∧
      Nonempty (ConnectedComponents D.Carrier) :=
  ⟨standardThreeSphereLift.{u}.toClosedOrientedManifold,
    standardThreeSphereLift.componentwiseStandardFactor_of_isStandardFactor
      isStandardFactor_standardThreeSphereLift,
    ⟨ConnectedComponents.mk (standardThreeSphereLiftDiffeomorph.{u}
      ⟨EuclideanSpace.single 0 1, by simp⟩)⟩⟩

end DifferentialGeometry.Topology
