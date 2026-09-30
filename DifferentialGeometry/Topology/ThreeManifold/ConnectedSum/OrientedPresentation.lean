import DifferentialGeometry.Topology.ThreeManifold.SphericalSpaceFormOrientationClosure
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.FiniteLawInstances

namespace GC.Topology
open DifferentialGeometry.Topology
open scoped Manifold ContDiff
set_option autoImplicit false
universe u

theorem oriented_presentation_with_original_list
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (P : PoincareStandardPresentation M.Carrier) :
    ∃ Q : OrientedPoincareStandardPresentation M.toClosedOrientedManifold,
      Q.factors = P.factors ∨
      Q.factors = P.factors.map ConnectedClosedOrientedManifold.opposite := by
  classical
  rcases Diffeomorph.preservesOrientation_or_preservesOrientation_opposite P.diffeomorph
    M.orientation (finiteConnectedSum P.factors).orientation with h | h
  · exact ⟨⟨P.factors, P.standard, ⟨P.diffeomorph, h⟩⟩, Or.inl rfl⟩
  · obtain ⟨e⟩ := finiteConnectedSum_opposite P.factors
    let f : ClosedOrientedManifold.OrientedDiffeomorph M.toClosedOrientedManifold
        (finiteConnectedSum P.factors).toClosedOrientedManifold.opposite :=
      ⟨P.diffeomorph, h⟩
    refine ⟨⟨P.factors.map ConnectedClosedOrientedManifold.opposite, ?_, f.trans e⟩,
      Or.inr rfl⟩
    intro X hX
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hX
    exact factorOrientationClosure_holds Y (P.standard Y hY)

theorem oriented_presentation_same_number_of_factors
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (P : PoincareStandardPresentation M.Carrier) :
    ∃ Q : OrientedPoincareStandardPresentation M.toClosedOrientedManifold,
      Q.factors.length = P.factors.length := by
  obtain ⟨Q, h | h⟩ := oriented_presentation_with_original_list M P
  · exact ⟨Q, congrArg List.length h⟩
  · exact ⟨Q, by simp only [h, List.length_map]⟩

theorem oriented_presentation_carrier_indices
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (P : PoincareStandardPresentation M.Carrier) :
    ∃ (Q : OrientedPoincareStandardPresentation M.toClosedOrientedManifold)
      (hlen : Q.factors.length = P.factors.length),
      ∀ i : Fin P.factors.length,
        (Q.factors.get (Fin.cast hlen.symm i)).Carrier = (P.factors.get i).Carrier := by
  obtain ⟨Q, h | h⟩ := oriented_presentation_with_original_list M P
  · refine ⟨Q, by rw [h], ?_⟩
    intro i
    simp only [h, List.get_eq_getElem, Fin.val_cast]
  · refine ⟨Q, by rw [h, List.length_map], ?_⟩
    intro i
    simp only [h, List.get_eq_getElem, Fin.val_cast, List.getElem_map,
      ConnectedClosedOrientedManifold.opposite_carrier]

end GC.Topology
