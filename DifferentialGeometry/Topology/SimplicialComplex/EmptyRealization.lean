import DifferentialGeometry.Topology.SimplicialComplex.OrderedSimplicialSet
import DifferentialGeometry.Topology.SimplicialSet.FiniteCellInduction
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace Poincare.Topology.SimplicialComplex
universe u
variable {ι : Type u} [LinearOrder ι]


theorem isEmpty_orderedRealization (K : PreAbstractSimplicialComplex ι) (hK : K.faces = ∅) :
    IsEmpty (SSet.toTop.obj (orderedSimplicialSet K)) := by
  let : IsEmpty (orderedSimplicialSet K).N := ⟨fun a => by
    have ha := a.simplex.prop
    change Finset.univ.image a.simplex.val.obj ∈ K.faces at ha
    rw [hK] at ha
    exact ha⟩
  have hI := (Poincare.SSet.isInitial_of_isEmpty_nondegenerate (orderedSimplicialSet K)).isInitialObj
    SSet.toTop
  exact ⟨fun x => PEmpty.elim (hI.to (TopCat.of PEmpty.{u + 1}) x)⟩

end Poincare.Topology.SimplicialComplex
