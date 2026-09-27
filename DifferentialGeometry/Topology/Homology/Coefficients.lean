import DifferentialGeometry.Topology.Homology.Algebra.Augment
import DifferentialGeometry.Topology.Homology.Reduced

open CategoryTheory AlgebraicTopology
open scoped Simplicial

noncomputable section

namespace DifferentialGeometry.Homology

universe u

variable {k : Type u} [Ring k] {R S T : ModuleCat.{u} k}
  (φ : R ⟶ S) (X : TopCat.{u})

@[reassoc]
theorem singularAugmentation_coefficient_naturality :
    (((singularChainComplexFunctor (ModuleCat.{u} k)).map φ).app X).f 0 ≫
      singularAugmentation S X = singularAugmentation R X ≫ φ := by
  change CategoryTheory.Limits.Sigma.map
      (fun _ : TopCat.toSSet.obj X _⦋0⦌ => φ) ≫
    CategoryTheory.Limits.Sigma.desc (fun _ : TopCat.toSSet.obj X _⦋0⦌ => 𝟙 S) =
    CategoryTheory.Limits.Sigma.desc (fun _ : TopCat.toSSet.obj X _⦋0⦌ => 𝟙 R) ≫ φ
  apply CategoryTheory.Limits.Sigma.hom_ext
  intro σ
  simp

def augmentedSingularChainCoefficientMap :
    augmentedSingularChainComplex R X ⟶ augmentedSingularChainComplex S X :=
  DifferentialGeometry.ChainComplex.augmentMap
    (d_singularAugmentation R X) (d_singularAugmentation S X)
    (((singularChainComplexFunctor (ModuleCat.{u} k)).map φ).app X) φ
    (singularAugmentation_coefficient_naturality φ X)

@[simp]
theorem augmentedSingularChainCoefficientMap_f_zero :
    (augmentedSingularChainCoefficientMap φ X).f 0 = φ := rfl

@[simp]
theorem augmentedSingularChainCoefficientMap_f_succ (n : ℕ) :
    (augmentedSingularChainCoefficientMap φ X).f (n + 1) =
      (((singularChainComplexFunctor (ModuleCat.{u} k)).map φ).app X).f n := rfl

@[simp]
theorem augmentedSingularChainCoefficientMap_id :
    augmentedSingularChainCoefficientMap (𝟙 R) X = 𝟙 _ := by
  apply _root_.HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    exact congrArg (fun f => (f.app X).f n)
      (CategoryTheory.Functor.map_id (singularChainComplexFunctor (ModuleCat.{u} k)) R)

theorem augmentedSingularChainCoefficientMap_comp (ψ : S ⟶ T) :
    augmentedSingularChainCoefficientMap (φ ≫ ψ) X =
      augmentedSingularChainCoefficientMap φ X ≫ augmentedSingularChainCoefficientMap ψ X := by
  apply _root_.HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    exact congrArg (fun f => (f.app X).f n)
      (Functor.map_comp (singularChainComplexFunctor (ModuleCat.{u} k)) φ ψ)

variable {X} {Y : TopCat.{u}}

@[reassoc]
theorem augmentedSingularChainCoefficientMap_naturality (f : X ⟶ Y) :
    augmentedSingularChainMap R f ≫ augmentedSingularChainCoefficientMap φ Y =
      augmentedSingularChainCoefficientMap φ X ≫ augmentedSingularChainMap S f := by
  apply _root_.HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero => exact (Category.id_comp φ).trans (Category.comp_id φ).symm
  | succ n =>
    exact congrArg (fun f => f.f n)
      (((singularChainComplexFunctor (ModuleCat.{u} k)).map φ).naturality f)

variable (X)

def reducedSingularHomologyCoefficientMap (n : ℕ) :
    reducedSingularHomology R X n ⟶ reducedSingularHomology S X n :=
  _root_.HomologicalComplex.homologyMap (augmentedSingularChainCoefficientMap φ X) (n + 1)

@[simp]
theorem reducedSingularHomologyCoefficientMap_id (n : ℕ) :
    reducedSingularHomologyCoefficientMap (𝟙 R) X n = 𝟙 _ := by
  simp [reducedSingularHomologyCoefficientMap]

theorem reducedSingularHomologyCoefficientMap_comp (ψ : S ⟶ T) (n : ℕ) :
    reducedSingularHomologyCoefficientMap (φ ≫ ψ) X n =
      reducedSingularHomologyCoefficientMap φ X n ≫ reducedSingularHomologyCoefficientMap ψ X n := by
  simp only [reducedSingularHomologyCoefficientMap, augmentedSingularChainCoefficientMap_comp,
    _root_.HomologicalComplex.homologyMap_comp]

variable {X}

@[reassoc]
theorem reducedSingularHomologyCoefficientMap_naturality (f : X ⟶ Y) (n : ℕ) :
    reducedSingularHomologyMap R f n ≫ reducedSingularHomologyCoefficientMap φ Y n =
      reducedSingularHomologyCoefficientMap φ X n ≫ reducedSingularHomologyMap S f n := by
  have h := congrArg (fun f => _root_.HomologicalComplex.homologyMap f (n + 1))
    (augmentedSingularChainCoefficientMap_naturality φ f)
  simpa only [_root_.HomologicalComplex.homologyMap_comp, reducedSingularHomologyMap,
    reducedSingularHomologyCoefficientMap] using h

end DifferentialGeometry.Homology
