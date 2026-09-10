import DifferentialGeometry.Topology.Simplex.Attachment
import DifferentialGeometry.Topology.Simplex.RelativeHomology

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology AlgebraicTopology

universe u

namespace Poincare.Simplex.Attachment

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)

private def singularChainHomotopyEquiv {Y Z : TopCat.{u}}
    (e : ContinuousMap.HomotopyEquiv Y Z) :
    HomotopyEquiv
      (((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).obj Y)
      (((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).obj Z) := by
  let F := (singularChainComplexFunctor (ModuleCat.{u} k)).obj R
  refine {
    hom := F.map (TopCat.ofHom e.toFun)
    inv := F.map (TopCat.ofHom e.invFun)
    homotopyHomInvId := ?_
    homotopyInvHomId := ?_ }
  · have H : TopCat.Homotopy (TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun) (𝟙 Y) :=
      e.left_inv.some
    have hh := H.singularChainComplexFunctorObjMap R
    rwa [F.map_comp, F.map_id] at hh
  · have H : TopCat.Homotopy (TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun) (𝟙 Z) :=
      e.right_inv.some
    have hh := H.singularChainComplexFunctorObjMap R
    rwa [F.map_comp, F.map_id] at hh

private theorem quasiIso_relativeChainMap_openEmbedding {Y Z : TopCat.{u}}
    (j : Y ⟶ Z) (hj : IsOpenEmbedding j) (s : Set Y) (t : Set Z)
    (he : ∀ x, x ∈ s ↔ j x ∈ t) (ht : IsOpen t) (hcover : Set.range j ∪ t = Set.univ) :
    QuasiIso (Poincare.Homology.relativeChainMap R j (fun x hx ↦ (he x).mp hx)) := by
  let e := hj.isEmbedding.toHomeomorph
  let q := Poincare.Homology.relativeChainIso (X := Y) (Y := TopCat.of (Set.range j))
    (s := s) (t := {x : Set.range j | x.val ∈ t}) R e (fun x ↦ he x)
  let i : TopCat.of (Set.range j) ⟶ Z :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let q' := Poincare.Homology.relativeChainMap R i
    (show Set.MapsTo i {x : Set.range j | x.val ∈ t} t from fun _ hx ↦ hx)
  have : QuasiIso q' := Poincare.Homology.quasiIso_relativeChainMap_of_openCover
    Z (Set.range j) t R hj.isOpen_range ht hcover
  have heq : Poincare.Homology.relativeChainMap R j (fun x hx ↦ (he x).mp hx) = q.hom ≫ q' := by
    exact Poincare.Homology.relativeChainMap_comp R
      (TopCat.ofHom (⟨e, e.continuous⟩ : C(Y, Set.range j)))
      (fun x hx ↦ (he x).mp hx) i (fun _ hx ↦ hx)
  rw [heq]
  exact quasiIso_comp _ _

variable {I : Type u} [Fintype I] [Nonempty I]
  {X P : TopCat.{u}} {g : TopCat.of (boundary I) ⟶ X}
  {r : TopCat.of (stdSimplex ℝ I) ⟶ P} {b : X ⟶ P}
  (h : IsPushout boundaryι g r b)

include h

omit [Nonempty I] in
theorem mapsTo_boundary_range_inr : Set.MapsTo r (boundary I) (Set.range b) := by
  intro d hd
  exact ⟨g ⟨d, hd⟩, (ConcreteCategory.congr_hom h.w ⟨d, hd⟩).symm⟩


def cellRelativeChainMap :
    Poincare.Homology.relativeChainComplex (TopCat.of (stdSimplex ℝ I)) (boundary I) R ⟶
      Poincare.Homology.relativeChainComplex P (Set.range b) R :=
  Poincare.Homology.relativeChainMap R r (mapsTo_boundary_range_inr h)


def openCellMap : TopCat.of (openCell I) ⟶ P :=
  TopCat.ofHom ⟨fun d ↦ r d.val, r.hom.continuous.comp continuous_subtype_val⟩

omit h [Nonempty I] in
private theorem range_boundaryι : Set.range (boundaryι (I := I)) = boundary I := by
  ext d
  constructor
  · rintro ⟨a, rfl⟩
    exact a.property
  · intro hd
    exact ⟨⟨d, hd⟩, rfl⟩

omit [Nonempty I] in
theorem isOpenEmbedding_openCellMap : IsOpenEmbedding (openCellMap (r := r)) := by
  let e : openCell I ≃ₜ {d : stdSimplex ℝ I // d ∉ Set.range (boundaryι (I := I))} :=
    Homeomorph.setCongr (by rw [range_boundaryι, openCell_eq_compl_boundary]; rfl)
  exact (Poincare.TopCat.Pushout.isOpenEmbedding_inlComplement h
    isClosedEmbedding_boundaryι).comp e.isOpenEmbedding

omit h in
theorem openCellMap_range_union_neighborhood :
    Set.range (openCellMap (r := r)) ∪ puncturedNeighborhood (r := r) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  by_cases hp : p = r stdSimplex.barycenter
  · exact Or.inl ⟨⟨stdSimplex.barycenter, barycenter_mem_openCell⟩, hp.symm⟩
  · exact Or.inr hp


theorem mapsTo_punctured_neighborhood :
    Set.MapsTo r (punctured I) (puncturedNeighborhood (r := r)) := by
  intro d hd he
  exact hd ((inl_eq_barycenter_iff h d).mp he)


def puncturedCellRelativeChainMap :
    Poincare.Homology.relativeChainComplex (TopCat.of (stdSimplex ℝ I)) (punctured I) R ⟶
      Poincare.Homology.relativeChainComplex P (puncturedNeighborhood (r := r)) R :=
  Poincare.Homology.relativeChainMap R r (mapsTo_punctured_neighborhood h)


theorem quasiIso_puncturedCellRelativeChainMap :
    QuasiIso (puncturedCellRelativeChainMap R h) := by
  let j : TopCat.of (openCell I) ⟶ TopCat.of (stdSimplex ℝ I) :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have hlocal : ∀ d : openCell I, d.val ∈ punctured I ↔
      openCellMap (r := r) d ∈ puncturedNeighborhood (r := r) :=
    fun d ↦ (not_congr (inl_eq_barycenter_iff h d.val)).symm
  have hq := quasiIso_relativeChainMap_openEmbedding R (openCellMap (r := r))
    (isOpenEmbedding_openCellMap h) {d : openCell I | d.val ∈ punctured I}
    (puncturedNeighborhood (r := r)) hlocal (isOpen_puncturedNeighborhood h)
    openCellMap_range_union_neighborhood
  have heq : openCellExcisionChainMap (I := I) R ≫ puncturedCellRelativeChainMap R h =
      Poincare.Homology.relativeChainMap R (openCellMap (r := r))
        (fun d hd ↦ (hlocal d).mp hd) :=
    (Poincare.Homology.relativeChainMap_comp R j (fun _ hx ↦ hx) r
      (mapsTo_punctured_neighborhood h)).symm
  have : QuasiIso (openCellExcisionChainMap (I := I) R) := quasiIso_openCellExcisionChainMap R
  have : QuasiIso (openCellExcisionChainMap (I := I) R ≫ puncturedCellRelativeChainMap R h) := by
    rw [heq]
    exact hq
  exact quasiIso_of_comp_left (openCellExcisionChainMap R) _


theorem mapsTo_range_inr_neighborhood :
    Set.MapsTo (𝟙 P) (Set.range b) (puncturedNeighborhood (r := r)) := by
  rintro p ⟨x, rfl⟩
  exact inr_ne_barycenter h x

def neighborhoodRelativeChainMap :
    Poincare.Homology.relativeChainComplex P (Set.range b) R ⟶
      Poincare.Homology.relativeChainComplex P (puncturedNeighborhood (r := r)) R :=
  Poincare.Homology.relativeChainMap R (𝟙 P) (mapsTo_range_inr_neighborhood h)

theorem quasiIso_neighborhoodRelativeChainMap :
    QuasiIso (neighborhoodRelativeChainMap R h) := by
  let F := (singularChainComplexFunctor (ModuleCat.{u} k)).obj R
  let a := Poincare.Homology.relativeSubspaceMap (𝟙 P) (mapsTo_range_inr_neighborhood h)
  let e : X ≃ₜ Set.range b :=
    (Poincare.TopCat.Pushout.isClosedEmbedding_inr h
      isClosedEmbedding_boundaryι).isEmbedding.toHomeomorph
  let i : X ⟶ TopCat.of (Set.range b) := (TopCat.isoOfHomeo e).hom
  have hia : i ≫ a = TopCat.ofHom (oldToNeighborhood h) := by
    ext x
    rfl
  have : IsIso i := by dsimp [i]; infer_instance
  have : QuasiIso (F.map i ≫ F.map a) := by
    rw [← F.map_comp, hia]
    exact (singularChainHomotopyEquiv (Y := TopCat.of (puncturedNeighborhood (r := r)))
      (Z := X) R (neighborhoodHomotopyEquiv h)).quasiIso_inv
  have ha : QuasiIso (F.map a) := quasiIso_of_comp_left (F.map i) (F.map a)
  unfold neighborhoodRelativeChainMap Poincare.Homology.relativeChainMap
  exact Poincare.HomologicalComplex.quasiIso_cokernel_map _ _ _ _ _ ha (quasiIso_of_isIso _)


theorem cellRelativeChainMap_neighborhood :
    cellRelativeChainMap R h ≫ neighborhoodRelativeChainMap R h =
      boundaryToPuncturedChainMap R ≫ puncturedCellRelativeChainMap R h := by
  unfold cellRelativeChainMap neighborhoodRelativeChainMap boundaryToPuncturedChainMap
    puncturedCellRelativeChainMap
  erw [← Poincare.Homology.relativeChainMap_comp, ← Poincare.Homology.relativeChainMap_comp]
  exact Poincare.Homology.relativeChainMap_congr R _ _ (by simp)

theorem quasiIso_cellRelativeChainMap : QuasiIso (cellRelativeChainMap R h) := by
  have : QuasiIso (neighborhoodRelativeChainMap R h) := quasiIso_neighborhoodRelativeChainMap R h
  have : QuasiIso (cellRelativeChainMap R h ≫ neighborhoodRelativeChainMap R h) := by
    rw [cellRelativeChainMap_neighborhood]
    have : QuasiIso (boundaryToPuncturedChainMap (I := I) R) :=
      quasiIso_boundaryToPuncturedChainMap R
    have : QuasiIso (puncturedCellRelativeChainMap R h) := quasiIso_puncturedCellRelativeChainMap R h
    infer_instance
  exact quasiIso_of_comp_right (cellRelativeChainMap R h) (neighborhoodRelativeChainMap R h)

omit [Nonempty I] in
@[reassoc (attr := simp)]
theorem relativeProjection_cellRelativeChainMap :
    Poincare.Homology.relativeProjection (TopCat.of (stdSimplex ℝ I)) (boundary I) R ≫
        cellRelativeChainMap R h =
      ((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map r ≫
        Poincare.Homology.relativeProjection P (Set.range b) R :=
  Poincare.Homology.relativeProjection_chainMap R r (mapsTo_boundary_range_inr h)

def cellRelativeHomologyIso (n : ℕ) :
    Poincare.Homology.relativeHomology (TopCat.of (stdSimplex ℝ I)) (boundary I) R n ≅
      Poincare.Homology.relativeHomology P (Set.range b) R n := by
  have : QuasiIso (cellRelativeChainMap R h) := quasiIso_cellRelativeChainMap R h
  exact isoOfQuasiIsoAt (cellRelativeChainMap R h) n


@[simp]
theorem cellRelativeHomologyIso_hom (n : ℕ) :
    (cellRelativeHomologyIso R h n).hom =
      _root_.HomologicalComplex.homologyMap (cellRelativeChainMap R h) n := rfl

end Poincare.Simplex.Attachment
