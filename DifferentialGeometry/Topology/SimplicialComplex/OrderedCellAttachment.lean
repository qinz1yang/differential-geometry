import DifferentialGeometry.Topology.SimplicialComplex.MaximalFace
import DifferentialGeometry.Topology.SimplicialComplex.OrderedMaps
import DifferentialGeometry.Topology.SimplicialSet.MaximalCell

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Poincare.Topology.SimplicialComplex
universe u
variable {ι : Type u} [LinearOrder ι]


@[reassoc (attr := simp)]
theorem orderedInclusion_ι {K L : PreAbstractSimplicialComplex ι} (h : K ≤ L) :
    orderedInclusion h ≫ (orderedNerveSubcomplex L).ι =
      (orderedNerveSubcomplex K).ι := rfl

variable (K : PreAbstractSimplicialComplex ι) (s : Finset ι) (hs : s ∈ K)
  {n : ℕ} (hn : s.card = n + 1)

theorem orderedFace_subcomplex_le_iff {m : SimplexCategoryᵒᵖ}
    (x : (orderedSimplicialSet K).obj m) :
    Subfunctor.ofSection (orderedSimplexOfFace K s hs hn).val ≤ Subfunctor.ofSection x ↔
      s ⊆ Finset.univ.image x.val.obj := by
  rw [Subfunctor.ofSection_le_iff, Subfunctor.ofSection_obj]
  constructor
  · rintro ⟨f, hf⟩ a ha
    have ha' : a ∈ Finset.univ.image (orderedSimplexOfFace K s hs hn).val.val.obj := by
      simpa only [vertices_orderedSimplexOfFace] using ha
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha'
    refine Finset.mem_image.mpr ⟨f.unop.toOrderHom i, Finset.mem_univ _, ?_⟩
    have hv := congrArg (fun y ↦ y.val.obj i) hf
    exact hv.trans hi
  · intro hsub
    have hpre (i : Fin (n + 1)) : ∃ j : Fin (m.unop.len + 1),
        x.val.obj j = (s.orderEmbOfFin hn) i := by
      have hi : (s.orderEmbOfFin hn) i ∈ s := by
        have hi' : (s.orderEmbOfFin hn) i ∈ Finset.univ.image (s.orderEmbOfFin hn) :=
          Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
        simpa only [Finset.image_orderEmbOfFin_univ] using hi'
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (hsub hi)
      exact ⟨j, hj⟩
    let f : Fin (n + 1) → Fin (m.unop.len + 1) := fun i ↦ (hpre i).choose
    have hf (i : Fin (n + 1)) : x.val.obj (f i) = (s.orderEmbOfFin hn) i :=
      (hpre i).choose_spec
    have hfmono : StrictMono f := by
      intro i j hij
      by_contra h
      have hji := x.val.monotone (le_of_not_gt h)
      rw [hf, hf] at hji
      exact ((s.orderEmbOfFin hn).strictMono hij).not_ge hji
    let φ : ⦋n⦌ ⟶ m.unop := SimplexCategory.Hom.mk ⟨f, hfmono.monotone⟩
    refine ⟨φ.op, ?_⟩
    apply Subtype.ext
    apply nerve.ext_of_isThin
    funext i
    exact hf i

def orderedFaceN : (orderedSimplicialSet K).N :=
  _root_.SSet.N.mk (orderedSimplexOfFace K s hs hn).val (orderedSimplexOfFace K s hs hn).prop


@[simp]
theorem orderedFaceN_dim : (orderedFaceN K s hs hn).dim = n := rfl

theorem orderedFaceN_le_iff (t : (orderedSimplicialSet K).N) :
    orderedFaceN K s hs hn ≤ t ↔ s ⊆ Finset.univ.image t.simplex.val.obj :=
  orderedFace_subcomplex_le_iff K s hs hn t.simplex


theorem isMax_orderedFaceN (hmax : IsMax (⟨s, hs⟩ : K.faces)) :
    IsMax (orderedFaceN K s hs hn) := by
  intro t hst
  have hst' := (orderedFaceN_le_iff K s hs hn t).mp hst
  have hts' : Finset.univ.image t.simplex.val.obj ⊆ s :=
    hmax (show (⟨s, hs⟩ : K.faces) ≤ ⟨_, t.simplex.prop⟩ from hst')
  let a : (orderedSimplicialSet K).nonDegenerate t.dim := ⟨t.simplex, t.nonDegenerate⟩
  have he := congrArg Subtype.val ((orderedNondegenerateFaceEquiv K t.dim).left_inv a)
  change (orderedSimplexOfFace K (Finset.univ.image t.simplex.val.obj) t.simplex.prop
    (card_vertices_nondegenerate K a)).val = t.simplex at he
  change Subfunctor.ofSection t.simplex ≤
    Subfunctor.ofSection (orderedSimplexOfFace K s hs hn).val
  rw [← he]
  apply (orderedFace_subcomplex_le_iff K _ t.simplex.prop
    (card_vertices_nondegenerate K a) (orderedSimplexOfFace K s hs hn).val).mpr
  simpa only [vertices_orderedSimplexOfFace] using hts'

theorem mem_orderedFaceN_costar_iff {m : SimplexCategoryᵒᵖ}
    (x : (orderedSimplicialSet K).obj m) :
    x ∈ (Poincare.SSet.costar (orderedFaceN K s hs hn)).obj m ↔
      ¬s ⊆ Finset.univ.image x.val.obj :=
  not_congr (orderedFace_subcomplex_le_iff K s hs hn x)

def orderedFaceCostarIso :
    orderedSimplicialSet (faceCostar K s) ≅ Poincare.SSet.costar (orderedFaceN K s hs hn) :=
  NatIso.ofComponents (fun _ ↦ Equiv.toIso {
    toFun := fun x ↦ ⟨⟨x.val, x.prop.1⟩,
      (mem_orderedFaceN_costar_iff K s hs hn _).mpr x.prop.2⟩
    invFun := fun x ↦ ⟨x.val.val, x.val.prop,
      (mem_orderedFaceN_costar_iff K s hs hn x.val).mp x.prop⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }) (fun _ ↦ rfl)


@[reassoc (attr := simp)]
theorem orderedFaceCostarIso_hom_inclusion :
    (orderedFaceCostarIso K s hs hn).hom ≫ (Poincare.SSet.costar (orderedFaceN K s hs hn)).ι =
      orderedInclusion (faceCostar_le K s) := rfl

def orderedFaceCellMap : (Δ[n] : _root_.SSet.{u}) ⟶ orderedSimplicialSet K :=
  Poincare.SSet.nondegenerateCellMap (orderedFaceN K s hs hn)

theorem orderedFaceCellMap_app {m : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) :
    ((orderedFaceCellMap K s hs hn).app (op ⦋m⦌)
      (_root_.SSet.stdSimplex.objEquiv.symm f)).val.obj =
        fun i ↦ (s.orderEmbOfFin hn) (f.toOrderHom i) := rfl


def orderedFaceAttachingMap : (_root_.SSet.boundary n : _root_.SSet.{u}) ⟶
    orderedSimplicialSet (faceCostar K s) :=
  Poincare.SSet.costarAttachingMap (orderedFaceN K s hs hn) ≫ (orderedFaceCostarIso K s hs hn).inv

@[reassoc (attr := simp)]
theorem orderedFaceAttachingMap_inclusion :
    orderedFaceAttachingMap K s hs hn ≫ orderedInclusion (faceCostar_le K s) =
      (_root_.SSet.boundary n).ι ≫ orderedFaceCellMap K s hs hn := by
  ext x
  rfl

theorem orderedFaceAttachment_isPushout (hmax : IsMax (⟨s, hs⟩ : K.faces)) :
    IsPushout (_root_.SSet.boundary n).ι (orderedFaceAttachingMap K s hs hn)
      (orderedFaceCellMap K s hs hn) (orderedInclusion (faceCostar_le K s)) := by
  apply (Poincare.SSet.costar_cell_isPushout (orderedFaceN K s hs hn)
    (isMax_orderedFaceN K s hs hn hmax)).of_iso'
    (Iso.refl _) (Iso.refl _) (orderedFaceCostarIso K s hs hn) (Iso.refl _)
  · change (𝟙 (_root_.SSet.boundary n : _root_.SSet)) ≫ (_root_.SSet.boundary n).ι =
      (_root_.SSet.boundary n).ι ≫ (𝟙 (Δ[n] : _root_.SSet))
    simp
  · ext x
    rfl
  · ext x
    rfl
  · simp

end Poincare.Topology.SimplicialComplex
