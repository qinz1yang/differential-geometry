import DifferentialGeometry.Topology.SimplicialComplex.OrderedGeometricCell
import DifferentialGeometry.Topology.SimplicialComplex.GeometricInclusion
import DifferentialGeometry.Topology.SimplicialComplex.FiniteFaceInduction
import DifferentialGeometry.Topology.SimplicialComplex.EmptyRealization
import DifferentialGeometry.Topology.SimplicialSet.Compactness
import DifferentialGeometry.Topology.Category.TopCat.PushoutInjectivity

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits Simplicial
namespace Poincare.Topology.SimplicialComplex
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]

theorem geometricRealizationMap_injective (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] :
    Function.Injective (geometricRealizationMap K) := by
  apply finite_geometricFace_induction
    (fun L : Geometry.SimplicialComplex ℝ E => Function.Injective (geometricRealizationMap L)) ?_ ?_ K
  · intro L hL
    let : IsEmpty (SSet.toTop.obj (orderedSimplicialSet L.toPreAbstractSimplicialComplex)) :=
      isEmpty_orderedRealization _ hL
    exact Function.injective_of_subsingleton _
  · intro L _ s hs hOld
    let n := s.card - 1
    have hn : s.card = n + 1 :=
      (Nat.sub_add_cancel (Finset.card_pos.mpr (L.nonempty_of_mem_faces hs.1))).symm
    have hmax : IsMax (⟨s, hs.1⟩ : L.faces) := by
      intro t ht
      exact (hs.2 t.prop ht).symm.le
    have hP := (orderedFaceAttachment_isPushout L.toPreAbstractSimplicialComplex s hs.1 hn hmax).map
      SSet.toTop
    apply Poincare.TopCat.Pushout.injective_of_cell_overlap hP (geometricRealizationMap L)
    · intro x y hxy
      apply (orderedFaceRealizationHomeomorph L s hs.1 hn).injective
      apply Subtype.ext
      have he (z : SSet.toTop.obj (Δ[n] : SSet.{u})) :=
        congrArg Subtype.val (ConcreteCategory.congr_hom
          (orderedFaceCellMap_geometricRealizationMap L s hs.1 hn) z)
      exact (he x).symm.trans ((congrArg Subtype.val hxy).trans (he y))
    · intro x y hxy
      apply hOld
      apply Subtype.ext
      have he (z : SSet.toTop.obj
          (orderedSimplicialSet (geometricFaceCostar L s).toPreAbstractSimplicialComplex)) :=
        congrArg Subtype.val (ConcreteCategory.congr_hom
          (geometricRealizationMap_inclusion (geometricFaceCostar_le L s)) z)
      exact (he x).symm.trans ((congrArg Subtype.val hxy).trans (he y))
    · intro x y hxy
      apply (orderedFaceCellMap_geometricRealizationMap_mem_costar_iff L s hs.1 hn x).mp
      have he := congrArg Subtype.val (ConcreteCategory.congr_hom
        (geometricRealizationMap_inclusion (geometricFaceCostar_le L s)) y)
      have hval := (congrArg Subtype.val hxy).trans he
      exact hval.symm ▸ (geometricRealizationMap (geometricFaceCostar L s) y).prop

def geometricRealizationHomeomorphism (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] :
    SSet.toTop.obj (orderedSimplicialSet K.toPreAbstractSimplicialComplex) ≃ₜ K.space :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (geometricRealizationMap K)
      ⟨geometricRealizationMap_injective K, geometricRealizationMap_surjective K⟩)
    (geometricRealizationMap K).hom.continuous


@[simp]
theorem geometricRealizationHomeomorphism_apply (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (x : SSet.toTop.obj (orderedSimplicialSet K.toPreAbstractSimplicialComplex)) :
    geometricRealizationHomeomorphism K x = geometricRealizationMap K x := rfl

@[reassoc]
theorem geometricRealizationHomeomorphism_inclusion
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces] (h : K ≤ L) :
    SSet.toTop.map (orderedInclusion h) ≫
        (TopCat.isoOfHomeo (geometricRealizationHomeomorphism L)).hom =
      (TopCat.isoOfHomeo (geometricRealizationHomeomorphism K)).hom ≫ geometricInclusion h :=
  geometricRealizationMap_inclusion h

end Poincare.Topology.SimplicialComplex
