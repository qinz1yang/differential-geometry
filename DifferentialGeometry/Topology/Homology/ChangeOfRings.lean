import DifferentialGeometry.Topology.Homology.Reduced
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

universe u

namespace DifferentialGeometry.Homology

variable {k l : Type u} [Ring k] [Ring l] (φ : k →+* l)
  (A : ModuleCat.{u} l) (X : TopCat.{u})

private instance restrictScalarsPreservesHomology :
    (ModuleCat.restrictScalars φ).PreservesHomology where
  preservesKernels _ := inferInstance
  preservesCokernels _ := inferInstance

private def singularChainRestrictScalarsXIso (n : ℕ) :
    ((TopCat.toSSet.obj X).chainComplex ((ModuleCat.restrictScalars φ).obj A)).X n ≅
      (ModuleCat.restrictScalars φ).obj (((TopCat.toSSet.obj X).chainComplex A).X n) :=
  (PreservesCoproduct.iso (ModuleCat.restrictScalars φ)
    (fun _ : TopCat.toSSet.obj X _⦋n⦌ => A)).symm

@[reassoc]
private theorem ι_singularChainRestrictScalarsXIso_hom {n : ℕ}
    (σ : TopCat.toSSet.obj X _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ (singularChainRestrictScalarsXIso φ A X n).hom =
      (ModuleCat.restrictScalars φ).map ((TopCat.toSSet.obj X).ιChainComplex σ) :=
  ι_comp_sigmaComparison _ _ σ

private theorem singularChainRestrictScalarsXIso_comm (n : ℕ) :
    ((TopCat.toSSet.obj X).chainComplex ((ModuleCat.restrictScalars φ).obj A)).d (n + 1) n ≫
      (singularChainRestrictScalarsXIso φ A X n).hom =
    (singularChainRestrictScalarsXIso φ A X (n + 1)).hom ≫
      (ModuleCat.restrictScalars φ).map (((TopCat.toSSet.obj X).chainComplex A).d (n + 1) n) := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, SSet.ιChainComplex_d]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp,
    ι_singularChainRestrictScalarsXIso_hom, ι_singularChainRestrictScalarsXIso_hom_assoc,
    ← Functor.map_comp, SSet.ιChainComplex_d, Functor.map_sum, Functor.map_zsmul]

private theorem singularAugmentation_restrictScalars :
    singularAugmentation ((ModuleCat.restrictScalars φ).obj A) X =
      (singularChainRestrictScalarsXIso φ A X 0).hom ≫
        (ModuleCat.restrictScalars φ).map (singularAugmentation A X) := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [ι_singularAugmentation, ι_singularChainRestrictScalarsXIso_hom_assoc,
    ← Functor.map_comp, ι_singularAugmentation, CategoryTheory.Functor.map_id]

private def augmentedSingularChainRestrictScalarsXIso (n : ℕ) :
    (augmentedSingularChainComplex ((ModuleCat.restrictScalars φ).obj A) X).X n ≅
      (ModuleCat.restrictScalars φ).obj ((augmentedSingularChainComplex A X).X n) := by
  cases n with
  | zero => exact Iso.refl _
  | succ n => exact singularChainRestrictScalarsXIso φ A X n

def augmentedSingularChainRestrictScalarsIso :
    augmentedSingularChainComplex ((ModuleCat.restrictScalars φ).obj A) X ≅
      ((ModuleCat.restrictScalars φ).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (augmentedSingularChainComplex A X) :=
  _root_.HomologicalComplex.Hom.isoOfComponents
    (augmentedSingularChainRestrictScalarsXIso φ A X) (by
      intro i j hij
      obtain rfl : j + 1 = i := hij
      symm
      cases j with
      | zero =>
        change singularAugmentation ((ModuleCat.restrictScalars φ).obj A) X ≫ 𝟙 _ = _
        rw [Category.comp_id]
        exact singularAugmentation_restrictScalars φ A X
      | succ n =>
        exact singularChainRestrictScalarsXIso_comm φ A X n)

@[simp]
theorem augmentedSingularChainRestrictScalarsIso_hom_f_zero :
    (augmentedSingularChainRestrictScalarsIso φ A X).hom.f 0 = 𝟙 _ := rfl

@[simp]
theorem augmentedSingularChainRestrictScalarsIso_inv_f_zero :
    (augmentedSingularChainRestrictScalarsIso φ A X).inv.f 0 = 𝟙 _ := rfl

@[reassoc]
theorem ι_augmentedSingularChainRestrictScalarsIso_hom_f_succ {n : ℕ}
    (σ : TopCat.toSSet.obj X _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫
        (augmentedSingularChainRestrictScalarsIso φ A X).hom.f (n + 1) =
      (ModuleCat.restrictScalars φ).map ((TopCat.toSSet.obj X).ιChainComplex σ) :=
  ι_singularChainRestrictScalarsXIso_hom φ A X σ

variable {X} {Y : TopCat.{u}}

@[reassoc]
theorem augmentedSingularChainRestrictScalarsIso_naturality (f : X ⟶ Y) :
    augmentedSingularChainMap ((ModuleCat.restrictScalars φ).obj A) f ≫
        (augmentedSingularChainRestrictScalarsIso φ A Y).hom =
      (augmentedSingularChainRestrictScalarsIso φ A X).hom ≫
        ((ModuleCat.restrictScalars φ).mapHomologicalComplex (ComplexShape.down ℕ)).map
          (augmentedSingularChainMap A f) := by
  apply _root_.HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ (ModuleCat.restrictScalars φ).map (𝟙 A)
    simp
  | succ n =>
    apply SSet.chainComplex_hom_ext
    intro σ
    change (TopCat.toSSet.obj X).ιChainComplex σ ≫
        ((SSet.chainComplexMap (TopCat.toSSet.map f)
          ((ModuleCat.restrictScalars φ).obj A)).f n ≫
            (singularChainRestrictScalarsXIso φ A Y n).hom) =
      (TopCat.toSSet.obj X).ιChainComplex σ ≫
        ((singularChainRestrictScalarsXIso φ A X n).hom ≫
          (ModuleCat.restrictScalars φ).map
            ((SSet.chainComplexMap (TopCat.toSSet.map f) A).f n))
    rw [← Category.assoc, SSet.ι_chainComplexMap_f,
      ι_singularChainRestrictScalarsXIso_hom,
      ι_singularChainRestrictScalarsXIso_hom_assoc,
      ← Functor.map_comp, SSet.ι_chainComplexMap_f]

variable (X)

def reducedSingularHomologyRestrictScalarsIso (n : ℕ) :
    reducedSingularHomology ((ModuleCat.restrictScalars φ).obj A) X n ≅
      (ModuleCat.restrictScalars φ).obj (reducedSingularHomology A X n) :=
  _root_.HomologicalComplex.homologyMapIso
      (augmentedSingularChainRestrictScalarsIso φ A X) (n + 1) ≪≫
    ((augmentedSingularChainComplex A X).sc (n + 1)).mapHomologyIso
      (ModuleCat.restrictScalars φ)

variable {X}

@[reassoc]
theorem reducedSingularHomologyRestrictScalarsIso_naturality (f : X ⟶ Y) (n : ℕ) :
    reducedSingularHomologyMap ((ModuleCat.restrictScalars φ).obj A) f n ≫
        (reducedSingularHomologyRestrictScalarsIso φ A Y n).hom =
      (reducedSingularHomologyRestrictScalarsIso φ A X n).hom ≫
        (ModuleCat.restrictScalars φ).map (reducedSingularHomologyMap A f n) := by
  have hchain := congrArg (fun f => _root_.HomologicalComplex.homologyMap f (n + 1))
    (augmentedSingularChainRestrictScalarsIso_naturality φ A f)
  simp only [_root_.HomologicalComplex.homologyMap_comp] at hchain
  have hrestrict := ShortComplex.mapHomologyIso_hom_naturality
    ((_root_.HomologicalComplex.shortComplexFunctor _ _ (n + 1)).map
      (augmentedSingularChainMap A f)) (ModuleCat.restrictScalars φ)
  have hleft := congrArg (fun f => f ≫
    (((augmentedSingularChainComplex A Y).sc (n + 1)).mapHomologyIso
      (ModuleCat.restrictScalars φ)).hom) hchain
  have hright := congrArg (fun f => _root_.HomologicalComplex.homologyMap
    (augmentedSingularChainRestrictScalarsIso φ A X).hom (n + 1) ≫ f) hrestrict
  exact ((Category.assoc _ _ _).symm.trans hleft).trans
    ((Category.assoc _ _ _).trans (hright.trans (Category.assoc _ _ _).symm))

end DifferentialGeometry.Homology
