import DifferentialGeometry.Topology.SimplicialComplex.OrderedSimplicialSet

set_option autoImplicit false
noncomputable section
open CategoryTheory Simplicial
namespace DifferentialGeometry.Topology.SimplicialComplex
universe u
variable {ι : Type u} [LinearOrder ι] {K L Q : PreAbstractSimplicialComplex ι}


theorem orderedNerveSubcomplex_mono (h : K ≤ L) : orderedNerveSubcomplex K ≤ orderedNerveSubcomplex L :=
  fun _ _ hx => h hx


def orderedInclusion (h : K ≤ L) : orderedSimplicialSet K ⟶ orderedSimplicialSet L :=
  SSet.Subcomplex.homOfLE (orderedNerveSubcomplex_mono h)


@[simp]
theorem orderedInclusion_app_val (h : K ≤ L) (n : SimplexCategoryᵒᵖ)
    (s : (orderedSimplicialSet K).obj n) :
    ((orderedInclusion h).app n s).val = s.val := rfl


instance mono_orderedInclusion (h : K ≤ L) : Mono (orderedInclusion h) :=
  inferInstanceAs (Mono (SSet.Subcomplex.homOfLE (orderedNerveSubcomplex_mono h)))


@[simp]
theorem orderedInclusion_comp (h : K ≤ L) (h' : L ≤ Q) :
    orderedInclusion h ≫ orderedInclusion h' = orderedInclusion (h.trans h') := rfl


@[simp]
theorem orderedInclusion_refl : orderedInclusion (le_rfl : K ≤ K) = 𝟙 (orderedSimplicialSet K) := rfl

end DifferentialGeometry.Topology.SimplicialComplex
