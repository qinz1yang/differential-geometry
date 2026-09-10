import DifferentialGeometry.Topology.Simplex.BoundaryRetraction
import DifferentialGeometry.Topology.Homology.Relative.Excision
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

universe u

namespace Poincare.Simplex

variable {I : Type u} [Fintype I] [Nonempty I]
  {k : Type u} [Ring k] (R : ModuleCat.{u} k)

def boundaryInclusionChainHomotopyEquiv :
    HomotopyEquiv
      (((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).obj
        (TopCat.of (boundary I)))
      (((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).obj
        (TopCat.of (punctured I))) := by
  let F := (singularChainComplexFunctor (ModuleCat.{u} k)).obj R
  let e := (radialHomotopyEquiv (I := I)).symm
  refine {
    hom := F.map (TopCat.ofHom boundaryInclusion)
    inv := F.map (TopCat.ofHom radialRetraction)
    homotopyHomInvId := ?_
    homotopyInvHomId := ?_ }
  · have H : TopCat.Homotopy
        (TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun) (𝟙 (TopCat.of (boundary I))) :=
      e.left_inv.some
    have h := H.singularChainComplexFunctorObjMap R
    rwa [F.map_comp, F.map_id] at h
  · have H : TopCat.Homotopy
        (TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun) (𝟙 (TopCat.of (punctured I))) :=
      e.right_inv.some
    have h := H.singularChainComplexFunctorObjMap R
    rwa [F.map_comp, F.map_id] at h

def boundaryToPuncturedChainMap :
    Poincare.Homology.relativeChainComplex (TopCat.of (stdSimplex ℝ I)) (boundary I) R ⟶
      Poincare.Homology.relativeChainComplex (TopCat.of (stdSimplex ℝ I)) (punctured I) R :=
  Poincare.Homology.relativeChainMap R (𝟙 (TopCat.of (stdSimplex ℝ I)))
    (fun _ hx ↦ boundary_subset_punctured hx)


@[reassoc (attr := simp)]
theorem relativeProjection_boundaryToPuncturedChainMap :
    Poincare.Homology.relativeProjection (TopCat.of (stdSimplex ℝ I)) (boundary I) R ≫
        boundaryToPuncturedChainMap R =
      Poincare.Homology.relativeProjection (TopCat.of (stdSimplex ℝ I)) (punctured I) R := by
  have h := Poincare.Homology.relativeProjection_chainMap R (𝟙 (TopCat.of (stdSimplex ℝ I)))
      (show Set.MapsTo (𝟙 (TopCat.of (stdSimplex ℝ I))) (boundary I) (punctured I) from
        fun _ hx ↦ boundary_subset_punctured hx)
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact h

theorem quasiIso_boundaryToPuncturedChainMap :
    QuasiIso (boundaryToPuncturedChainMap (I := I) R) := by
  unfold boundaryToPuncturedChainMap Poincare.Homology.relativeChainMap
  exact Poincare.HomologicalComplex.quasiIso_cokernel_map _ _ _ _ _
    (boundaryInclusionChainHomotopyEquiv (I := I) R).quasiIso_hom
    (quasiIso_of_isIso _)

def boundaryToPuncturedHomologyIso (n : ℕ) :
    Poincare.Homology.relativeHomology (TopCat.of (stdSimplex ℝ I)) (boundary I) R n ≅
      Poincare.Homology.relativeHomology (TopCat.of (stdSimplex ℝ I)) (punctured I) R n := by
  letI := quasiIso_boundaryToPuncturedChainMap (I := I) R
  exact isoOfQuasiIsoAt (boundaryToPuncturedChainMap R) n


@[simp]
theorem boundaryToPuncturedHomologyIso_hom (n : ℕ) :
    (boundaryToPuncturedHomologyIso (I := I) R n).hom =
      _root_.HomologicalComplex.homologyMap (boundaryToPuncturedChainMap R) n := rfl

def openCell (I : Type*) [Fintype I] : Set (stdSimplex ℝ I) :=
  {x | ∀ i, 0 < x.val i}

omit [Nonempty I] in
theorem isOpen_openCell : IsOpen (openCell I) := by
  change IsOpen (Set.ofPred (fun x : stdSimplex ℝ I ↦ ∀ i, 0 < x.val i))
  rw [Set.ofPred_forall]
  exact isOpen_iInter_of_finite (fun i ↦
    isOpen_lt continuous_const ((continuous_apply i).comp continuous_subtype_val))

omit [Nonempty I] in
theorem openCell_eq_compl_boundary : openCell I = (boundary I)ᶜ := by
  ext x
  change (∀ i, 0 < x.val i) ↔ ¬ ∃ i, x.val i = 0
  constructor
  · rintro hx ⟨i, hi⟩
    exact (ne_of_gt (hx i)) hi
  · intro hx i
    exact lt_of_le_of_ne (x.property.1 i) (Ne.symm (fun hi ↦ hx ⟨i, hi⟩))


theorem barycenter_mem_openCell : stdSimplex.barycenter ∈ openCell I := by
  intro i
  exact inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)


theorem openCell_union_punctured : openCell I ∪ punctured I = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases h : x = stdSimplex.barycenter
  · exact Or.inl (h ▸ barycenter_mem_openCell)
  · exact Or.inr h

def openCellExcisionChainMap :
    Poincare.Homology.relativeChainComplex (TopCat.of (openCell I))
      {x : openCell I | x.val ∈ punctured I} R ⟶
      Poincare.Homology.relativeChainComplex (TopCat.of (stdSimplex ℝ I)) (punctured I) R :=
  Poincare.Homology.relativeChainMap R
    (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(openCell I, stdSimplex ℝ I)))
    (fun _ hx ↦ hx)


@[reassoc (attr := simp)]
theorem relativeProjection_openCellExcisionChainMap :
    Poincare.Homology.relativeProjection (TopCat.of (openCell I))
        {x : openCell I | x.val ∈ punctured I} R ≫ openCellExcisionChainMap R =
      Poincare.Homology.relativeInclusion (TopCat.of (stdSimplex ℝ I)) (openCell I) R ≫
        Poincare.Homology.relativeProjection (TopCat.of (stdSimplex ℝ I)) (punctured I) R :=
  Poincare.Homology.relativeProjection_chainMap R _ _


theorem quasiIso_openCellExcisionChainMap :
    QuasiIso (openCellExcisionChainMap (I := I) R) :=
  Poincare.Homology.quasiIso_relativeChainMap_of_openCover
    (TopCat.of (stdSimplex ℝ I)) (openCell I) (punctured I) R
    isOpen_openCell isOpen_punctured openCell_union_punctured

def openCellRelativeHomologyIso (n : ℕ) :
    Poincare.Homology.relativeHomology (TopCat.of (openCell I))
      {x : openCell I | x.val ∈ punctured I} R n ≅
      Poincare.Homology.relativeHomology (TopCat.of (stdSimplex ℝ I)) (boundary I) R n :=
  Poincare.Homology.relativeExcisionIso (TopCat.of (stdSimplex ℝ I))
    (openCell I) (punctured I) R isOpen_openCell isOpen_punctured openCell_union_punctured n ≪≫
      (boundaryToPuncturedHomologyIso R n).symm

@[reassoc]
theorem openCellRelativeHomologyIso_hom_boundaryToPunctured (n : ℕ) :
    (openCellRelativeHomologyIso (I := I) R n).hom ≫
        _root_.HomologicalComplex.homologyMap (boundaryToPuncturedChainMap R) n =
      _root_.HomologicalComplex.homologyMap (openCellExcisionChainMap R) n := by
  change (_ ≫ (boundaryToPuncturedHomologyIso R n).inv) ≫
    (boundaryToPuncturedHomologyIso R n).hom = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

end Poincare.Simplex
