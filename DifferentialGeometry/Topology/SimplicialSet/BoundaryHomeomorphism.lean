import DifferentialGeometry.Topology.SimplicialSet.BoundaryRealization
import DifferentialGeometry.Topology.Simplex.Face
import Mathlib.Topology.LocallyFinite

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Simplicial

universe u

namespace DifferentialGeometry.SSet


def boundaryFaceMap {n : ℕ} (i : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)),
      _root_.SSet.toTop.obj (_root_.SSet.boundary (n + 1) : _root_.SSet.{u})) :=
  (_root_.SSet.toTop.map (_root_.SSet.boundary.ι i)).hom.comp
    ⟨(SimplexCategory.toTopHomeo ⦋n⦌).symm,
      (SimplexCategory.toTopHomeo ⦋n⦌).symm.continuous⟩


theorem boundaryFaceMap_ambient {n : ℕ} (i : Fin (n + 2))
    (p : stdSimplex ℝ (Fin (n + 1))) :
    boundaryRealizationMap (n + 1) (boundaryFaceMap.{u} i p) =
      ULift.up (stdSimplex.map i.succAbove p) := by
  have h := ConcreteCategory.congr_hom (boundaryRealizationMap_face.{u} i)
    ((SimplexCategory.toTopHomeo ⦋n⦌).symm p)
  change boundaryRealizationMap (n + 1) (boundaryFaceMap i p) =
    (SimplexCategory.toTop.map (SimplexCategory.δ i)).hom
      ((_root_.SSet.toTopSimplex.hom.app ⦋n⦌).hom
        ((SimplexCategory.toTopHomeo ⦋n⦌).symm p)) at h
  have hp : (_root_.SSet.toTopSimplex.hom.app ⦋n⦌).hom
      ((SimplexCategory.toTopHomeo ⦋n⦌).symm p) = ULift.up p := by
    apply ULift.ext
    exact (SimplexCategory.toTopHomeo ⦋n⦌).apply_symm_apply p
  rw [hp] at h
  exact h

private theorem boundary_face_overlap_morphism {n : ℕ}
    (i : Fin (n + 3)) (j : Fin (n + 2)) :
    _root_.SSet.stdSimplex.map (SimplexCategory.δ j) ≫ _root_.SSet.boundary.ι.{u} i =
      _root_.SSet.stdSimplex.map (SimplexCategory.δ (j.predAbove i)) ≫
        _root_.SSet.boundary.ι (i.succAbove j) := by
  apply (cancel_mono (_root_.SSet.boundary (n + 2)).ι).mp
  rw [Category.assoc, Category.assoc, _root_.SSet.boundary.ι_ι, _root_.SSet.boundary.ι_ι]
  change _root_.SSet.stdSimplex.map (SimplexCategory.δ j) ≫
      _root_.SSet.stdSimplex.map (SimplexCategory.δ i) =
    _root_.SSet.stdSimplex.map (SimplexCategory.δ (j.predAbove i)) ≫
      _root_.SSet.stdSimplex.map (SimplexCategory.δ (i.succAbove j))
  have hc : SimplexCategory.δ j ≫ SimplexCategory.δ i =
      SimplexCategory.δ (j.predAbove i) ≫ SimplexCategory.δ (i.succAbove j) := by
    ext k
    exact congrArg Fin.val (Fin.succAbove_succAbove_succAbove_predAbove i j k).symm
  exact (_root_.SSet.stdSimplex.map_comp _ _).symm.trans
    ((congrArg (fun f ↦ _root_.SSet.stdSimplex.map f) hc).trans
      (_root_.SSet.stdSimplex.map_comp _ _))


theorem boundaryFaceMap_overlap {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2))
    (p : stdSimplex ℝ (Fin (n + 1))) :
    boundaryFaceMap.{u} i (stdSimplex.map j.succAbove p) =
      boundaryFaceMap (i.succAbove j) (stdSimplex.map (j.predAbove i).succAbove p) := by
  change (_root_.SSet.toTop.map (_root_.SSet.boundary.ι i)).hom
      ((SimplexCategory.toTopHomeo ⦋n + 1⦌).symm (stdSimplex.map j.succAbove p)) =
    (_root_.SSet.toTop.map (_root_.SSet.boundary.ι (i.succAbove j))).hom
      ((SimplexCategory.toTopHomeo ⦋n + 1⦌).symm
        (stdSimplex.map (j.predAbove i).succAbove p))
  have hl := SimplexCategory.toTopHomeo_symm_naturality_apply.{u} (SimplexCategory.δ j) p
  have hr := SimplexCategory.toTopHomeo_symm_naturality_apply.{u}
    (SimplexCategory.δ (j.predAbove i)) p
  change (SimplexCategory.toTopHomeo ⦋n + 1⦌).symm (stdSimplex.map j.succAbove p) = _ at hl
  change (SimplexCategory.toTopHomeo ⦋n + 1⦌).symm
    (stdSimplex.map (j.predAbove i).succAbove p) = _ at hr
  rw [hl, hr]
  have h := congrArg (fun f ↦ _root_.SSet.toTop.map f) (boundary_face_overlap_morphism.{u} i j)
  rw [Functor.map_comp, Functor.map_comp] at h
  exact ConcreteCategory.congr_hom h ((SimplexCategory.toTopHomeo ⦋n⦌).symm p)

private theorem coordinate_faceDelete_map {n : ℕ} (i : Fin (n + 2))
    (p : stdSimplex ℝ (Fin (n + 2))) (hi : p.val i = 0) :
    stdSimplex.map i.succAbove (DifferentialGeometry.Simplex.faceDelete i ⟨p, hi⟩) = p :=
  congrArg Subtype.val (DifferentialGeometry.Simplex.faceInsert_faceDelete i ⟨p, hi⟩)


theorem boundaryFaceMap_delete_eq {n : ℕ} (i j : Fin (n + 2))
    (p : stdSimplex ℝ (Fin (n + 2))) (hi : p.val i = 0) (hj : p.val j = 0) :
    boundaryFaceMap.{u} i (DifferentialGeometry.Simplex.faceDelete i ⟨p, hi⟩) =
      boundaryFaceMap j (DifferentialGeometry.Simplex.faceDelete j ⟨p, hj⟩) := by
  by_cases hji : j = i
  · subst j
    rfl
  obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hji
  let q := DifferentialGeometry.Simplex.faceDelete i ⟨p, hi⟩
  have hq : q.val j = 0 := hj
  cases n with
  | zero =>
    have he : q.val j = 1 := by
      have hs := q.property.2
      change (∑ k : Fin 1, q.val k) = 1 at hs
      simpa only [Fin.sum_univ_one, Subsingleton.elim (0 : Fin 1) j] using hs
    exact False.elim (zero_ne_one (hq.symm.trans he))
  | succ n =>
    let z := DifferentialGeometry.Simplex.faceDelete j ⟨q, hq⟩
    have hz : stdSimplex.map j.succAbove z = q := coordinate_faceDelete_map j q hq
    have hother : DifferentialGeometry.Simplex.faceDelete (i.succAbove j) ⟨p, hj⟩ =
        stdSimplex.map (j.predAbove i).succAbove z := by
      apply (DifferentialGeometry.Simplex.faceHomeomorph (i.succAbove j)).injective
      apply Subtype.ext
      change stdSimplex.map (i.succAbove j).succAbove
        (DifferentialGeometry.Simplex.faceDelete (i.succAbove j) ⟨p, hj⟩) =
          stdSimplex.map (i.succAbove j).succAbove (stdSimplex.map (j.predAbove i).succAbove z)
      rw [coordinate_faceDelete_map]
      calc
        p = stdSimplex.map i.succAbove q := (coordinate_faceDelete_map i p hi).symm
        _ = stdSimplex.map i.succAbove (stdSimplex.map j.succAbove z) := congrArg _ hz.symm
        _ = _ := by
          rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply]
          congr 1
          funext k
          exact (Fin.succAbove_succAbove_succAbove_predAbove i j k).symm
    rw [hother]
    change boundaryFaceMap i q = _
    rw [← hz]
    exact boundaryFaceMap_overlap i j z

instance isEmpty_simplexBoundarySet_zero : IsEmpty (simplexBoundarySet.{u} 0) :=
  ⟨fun p ↦ by
    obtain ⟨i, hi⟩ := p.property
    have hs := p.val.down.property.2
    change (∑ j : Fin 1, p.val.down.val j) = 1 at hs
    have he : p.val.down.val i = 1 := by
      simpa only [Fin.sum_univ_one, Subsingleton.elim (0 : Fin 1) i] using hs
    exact zero_ne_one (hi.symm.trans he)⟩

instance isEmpty_realization_boundary_zero :
    IsEmpty (_root_.SSet.toTop.obj (_root_.SSet.boundary 0 : _root_.SSet.{u})) :=
  ⟨fun x ↦ isEmptyElim (boundaryRealizationLift 0 x)⟩

private def boundaryInverseSuccPoint (n : ℕ) (p : simplexBoundarySet.{u} (n + 1)) :
    _root_.SSet.toTop.obj (_root_.SSet.boundary (n + 1) : _root_.SSet.{u}) :=
  boundaryFaceMap p.property.choose
    (DifferentialGeometry.Simplex.faceDelete p.property.choose ⟨p.val.down, p.property.choose_spec⟩)

private theorem boundaryInverseSuccPoint_face (n : ℕ) (p : simplexBoundarySet.{u} (n + 1))
    (i : Fin (n + 2)) (hi : p.val.down.val i = 0) :
    boundaryInverseSuccPoint n p = boundaryFaceMap i (DifferentialGeometry.Simplex.faceDelete i ⟨p.val.down, hi⟩) :=
  boundaryFaceMap_delete_eq _ _ _ _ _

private theorem continuous_boundaryInverseSuccPoint (n : ℕ) :
    Continuous (boundaryInverseSuccPoint.{u} n) := by
  let F (i : Fin (n + 2)) : Set (simplexBoundarySet.{u} (n + 1)) :=
    {p | p.val.down.val i = 0}
  have hcover : ⋃ i, F i = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    exact Set.mem_iUnion.mpr p.property
  have hclosed (i : Fin (n + 2)) : IsClosed (F i) := by
    have hc : Continuous (fun p : simplexBoundarySet.{u} (n + 1) ↦ p.val.down.val i) := by
      have hv : Continuous (fun p : simplexBoundarySet.{u} (n + 1) ↦
          (p.val.down : stdSimplex ℝ (Fin (n + 2)))) := by fun_prop
      exact (continuous_apply i).comp (continuous_subtype_val.comp hv)
    exact isClosed_eq hc continuous_const
  apply (locallyFinite_of_finite F).continuous hcover hclosed
  intro i
  rw [continuousOn_iff_continuous_domRestrict]
  have he : (fun p : F i ↦ boundaryInverseSuccPoint n p.val) =
      fun p : F i ↦ boundaryFaceMap i
        (DifferentialGeometry.Simplex.faceDelete i ⟨p.val.val.down, p.property⟩) := by
    funext p
    exact boundaryInverseSuccPoint_face n p.val i p.property
  change Continuous (fun p : F i ↦ boundaryInverseSuccPoint n p.val)
  rw [he]
  apply (boundaryFaceMap i).continuous.comp
  apply (DifferentialGeometry.Simplex.faceDelete i).continuous.comp
  have hv : Continuous (fun p : F i ↦ (p.val.val.down : stdSimplex ℝ (Fin (n + 2)))) := by
    fun_prop
  exact hv.subtype_mk _


def boundaryRealizationInverse (n : ℕ) :
    C(simplexBoundarySet.{u} n,
      _root_.SSet.toTop.obj (_root_.SSet.boundary n : _root_.SSet.{u})) :=
  match n with
  | 0 => ⟨fun p ↦ isEmptyElim p,
      continuous_iff_continuousAt.mpr (fun p ↦ isEmptyElim p)⟩
  | n + 1 => ⟨boundaryInverseSuccPoint n, continuous_boundaryInverseSuccPoint n⟩


theorem boundaryRealizationInverse_face {n : ℕ} (p : simplexBoundarySet.{u} (n + 1))
    (i : Fin (n + 2)) (hi : p.val.down.val i = 0) :
    boundaryRealizationInverse (n + 1) p =
      boundaryFaceMap i (DifferentialGeometry.Simplex.faceDelete i ⟨p.val.down, hi⟩) :=
  boundaryInverseSuccPoint_face n p i hi


@[simp]
theorem boundaryRealizationLift_inverse (n : ℕ) (p : simplexBoundarySet.{u} n) :
    boundaryRealizationLift n (boundaryRealizationInverse n p) = p := by
  cases n with
  | zero => exact isEmptyElim p
  | succ n =>
    obtain ⟨i, hi⟩ := p.property
    rw [boundaryRealizationInverse_face p i hi]
    apply Subtype.ext
    have h := ConcreteCategory.congr_hom (boundaryRealizationLift_inclusion (n + 1))
      (boundaryFaceMap i (DifferentialGeometry.Simplex.faceDelete i ⟨p.val.down, hi⟩))
    refine h.trans ((boundaryFaceMap_ambient i _).trans ?_)
    exact congrArg ULift.up (coordinate_faceDelete_map i p.val.down hi)


theorem boundaryRealizationInverse_boundaryFaceMap {n : ℕ} (i : Fin (n + 2))
    (q : stdSimplex ℝ (Fin (n + 1))) :
    boundaryRealizationInverse (n + 1)
        (boundaryRealizationLift (n + 1) (boundaryFaceMap.{u} i q)) = boundaryFaceMap i q := by
  let p := boundaryRealizationLift (n + 1) (boundaryFaceMap.{u} i q)
  have hp : p.val.down = stdSimplex.map i.succAbove q :=
    congrArg ULift.down ((ConcreteCategory.congr_hom
      (boundaryRealizationLift_inclusion (n + 1)) (boundaryFaceMap i q)).trans
        (boundaryFaceMap_ambient i q))
  have hpi : p.val.down.val i = 0 := hp ▸ DifferentialGeometry.Simplex.map_succAbove_apply_pivot i q
  rw [boundaryRealizationInverse_face p i hpi]
  have hface : (⟨p.val.down, hpi⟩ : DifferentialGeometry.Simplex.face i) = DifferentialGeometry.Simplex.faceInsert i q :=
    Subtype.ext hp
  rw [hface, DifferentialGeometry.Simplex.faceDelete_faceInsert]

theorem boundaryRealization_hom_ext {n : ℕ} {X : TopCat.{u}}
    {f g : _root_.SSet.toTop.obj (_root_.SSet.boundary (n + 1) : _root_.SSet.{u}) ⟶ X}
    (h : ∀ i : Fin (n + 2), _root_.SSet.toTop.map (_root_.SSet.boundary.ι i) ≫ f =
      _root_.SSet.toTop.map (_root_.SSet.boundary.ι i) ≫ g) : f = g := by
  apply (sSetTopAdj.homEquiv _ _).injective
  apply _root_.SSet.boundary.hom_ext
  intro i
  have he := congrArg (sSetTopAdj.homEquiv Δ[n] X) (h i)
  simpa only [sSetTopAdj.homEquiv_naturality_left] using he


@[simp]
theorem boundaryRealizationInverse_lift (n : ℕ)
    (x : _root_.SSet.toTop.obj (_root_.SSet.boundary n : _root_.SSet.{u})) :
    boundaryRealizationInverse n (boundaryRealizationLift n x) = x := by
  cases n with
  | zero => exact isEmptyElim x
  | succ n =>
    have he : boundaryRealizationLift (n + 1) ≫
        TopCat.ofHom (boundaryRealizationInverse (n + 1)) = 𝟙 _ := by
      apply boundaryRealization_hom_ext
      intro i
      apply TopCat.ext
      intro y
      have h := boundaryRealizationInverse_boundaryFaceMap i
        ((SimplexCategory.toTopHomeo ⦋n⦌) y)
      change boundaryRealizationInverse (n + 1)
          (boundaryRealizationLift (n + 1)
            ((_root_.SSet.toTop.map (_root_.SSet.boundary.ι i)).hom
              ((SimplexCategory.toTopHomeo ⦋n⦌).symm ((SimplexCategory.toTopHomeo ⦋n⦌) y)))) =
        (_root_.SSet.toTop.map (_root_.SSet.boundary.ι i)).hom
          ((SimplexCategory.toTopHomeo ⦋n⦌).symm ((SimplexCategory.toTopHomeo ⦋n⦌) y)) at h
      rw [Homeomorph.symm_apply_apply] at h
      exact h
    exact ConcreteCategory.congr_hom he x


theorem injective_boundaryRealizationLift (n : ℕ) :
    Function.Injective (boundaryRealizationLift.{u} n) :=
  Function.LeftInverse.injective (boundaryRealizationInverse_lift n)

def boundaryRealizationHomeomorph (n : ℕ) :
    _root_.SSet.toTop.obj (_root_.SSet.boundary n : _root_.SSet.{u}) ≃ₜ simplexBoundarySet n where
  toFun := boundaryRealizationLift n
  invFun := boundaryRealizationInverse n
  left_inv := boundaryRealizationInverse_lift n
  right_inv := boundaryRealizationLift_inverse n
  continuous_toFun := (boundaryRealizationLift n).hom.continuous
  continuous_invFun := (boundaryRealizationInverse n).continuous


@[simp]
theorem boundaryRealizationHomeomorph_apply (n : ℕ)
    (x : _root_.SSet.toTop.obj (_root_.SSet.boundary n : _root_.SSet.{u})) :
    boundaryRealizationHomeomorph n x = boundaryRealizationLift n x := rfl


theorem boundaryRealizationHomeomorph_symm_face {n : ℕ} (p : simplexBoundarySet.{u} (n + 1))
    (i : Fin (n + 2)) (hi : p.val.down.val i = 0) :
    (boundaryRealizationHomeomorph (n + 1)).symm p =
      boundaryFaceMap i (DifferentialGeometry.Simplex.faceDelete i ⟨p.val.down, hi⟩) :=
  boundaryRealizationInverse_face p i hi


theorem boundaryRealizationHomeomorph_ambient (n : ℕ)
    (x : _root_.SSet.toTop.obj (_root_.SSet.boundary n : _root_.SSet.{u})) :
    (boundaryRealizationHomeomorph n x).val = boundaryRealizationMap n x :=
  ConcreteCategory.congr_hom (boundaryRealizationLift_inclusion n) x


theorem isClosedEmbedding_boundaryRealizationMap (n : ℕ) :
    Topology.IsClosedEmbedding (boundaryRealizationMap.{u} n) := by
  have h := (isClosed_simplexBoundarySet n).isClosedEmbedding_subtypeVal.comp
    (boundaryRealizationHomeomorph.{u} n).isClosedEmbedding
  simpa only [Function.comp_def, boundaryRealizationHomeomorph_ambient] using h

end DifferentialGeometry.SSet
