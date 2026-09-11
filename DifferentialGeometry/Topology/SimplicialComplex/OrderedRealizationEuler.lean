import DifferentialGeometry.Topology.SimplicialComplex.OrderedSimplicialSet
import DifferentialGeometry.Topology.SimplicialComplex.EulerCharacteristic
import DifferentialGeometry.Topology.SimplicialSet.RealizationEulerCharacteristic

set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace DifferentialGeometry.Topology.SimplicialComplex
universe u
variable {ι : Type u} [LinearOrder ι] (K : PreAbstractSimplicialComplex ι) [Finite K.faces]


theorem card_orderedSimplicialSet_nonDegenerate (n : ℕ) :
    Nat.card ((orderedSimplicialSet K).nonDegenerate n) = (facesOfCard K (n + 1)).card := by
  let e : {s : Finset ι // s ∈ K ∧ s.card = n + 1} ≃ (facesOfCard K (n + 1)) :=
    Equiv.subtypeEquivRight (fun _ => (mem_facesOfCard K).symm)
  rw [Nat.card_congr ((orderedNondegenerateFaceEquiv K n).trans e), Nat.card_eq_fintype_card]
  exact Fintype.card_coe _

theorem eulerChar_orderedRealization_eq_faceEulerChar (k : Type u) [Field k] :
    DifferentialGeometry.Homology.eulerChar k (SSet.toTop.obj (orderedSimplicialSet K)) = faceEulerChar K := by
  classical
  let d := (Set.toFinite K.faces).toFinset.sup Finset.card
  have hd : ∀ s ∈ K, s.card ≤ d := by
    intro s hs
    exact Finset.le_sup (f := Finset.card) ((Set.toFinite K.faces).mem_toFinset.mpr hs)
  have : (orderedSimplicialSet K).HasDimensionLT d := orderedSimplicialSet_hasDimensionLT K d hd
  rw [DifferentialGeometry.SSet.eulerChar_realization_eq_sum_card_nonDegenerate k _ d,
    faceEulerChar_eq_sum K d hd, Finset.sum_range_succ']
  simp only [pow_zero, facesOfCard_zero, Finset.card_empty, Nat.cast_zero, mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro n _
  rw [card_orderedSimplicialSet_nonDegenerate, pow_succ]
  ring

theorem finiteHomologyType_orderedRealization (k : Type u) [Field k] :
    DifferentialGeometry.Homology.finiteHomologyType k (SSet.toTop.obj (orderedSimplicialSet K)) :=
  DifferentialGeometry.SSet.finiteHomologyType_realization k (orderedSimplicialSet K)

end DifferentialGeometry.Topology.SimplicialComplex
