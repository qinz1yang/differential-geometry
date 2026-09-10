import DifferentialGeometry.Topology.Homology.Algebra.Augment
import DifferentialGeometry.Topology.Homology.Algebra.Biproduct
import DifferentialGeometry.Topology.Homology.Reduced
import DifferentialGeometry.Topology.Homology.SmallChains.Union
import DifferentialGeometry.Topology.Homology.SmallChains.QuasiIso
import Mathlib.Algebra.Homology.HomologySequence

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial ContinuousMap
noncomputable section
universe u v
namespace Poincare.Homology
variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)
  (X : TopCat.{u}) {ι : Type v} (U : ι → Set X)


def smallChainAugmentation :
    ((smallSingularSimplices X U : SSet).chainComplex R).X 0 ⟶ R :=
  (SSet.chainComplexMap (smallSingularSimplices X U).ι R).f 0 ≫ singularAugmentation R X


theorem d_smallChainAugmentation :
    ((smallSingularSimplices X U : SSet).chainComplex R).d 1 0 ≫
      smallChainAugmentation R X U = 0 := by
  change _ ≫ (SSet.chainComplexMap (smallSingularSimplices X U).ι R).f 0 ≫
    singularAugmentation R X = 0
  rw [← Category.assoc,
    ← (SSet.chainComplexMap (smallSingularSimplices X U).ι R).comm 1 0,
    Category.assoc, d_singularAugmentation, comp_zero]


def augmentedSmallChainComplex : ChainComplex (ModuleCat.{u} k) ℕ :=
  ChainComplex.augment ((smallSingularSimplices X U : SSet).chainComplex R)
    (smallChainAugmentation R X U) (d_smallChainAugmentation R X U)


def augmentedSmallChainMap :
    augmentedSmallChainComplex R X U ⟶ augmentedSingularChainComplex R X :=
  Poincare.ChainComplex.augmentMap (d_smallChainAugmentation R X U)
    (d_singularAugmentation R X) (smallChainMap X U R) (𝟙 R)
    (Category.comp_id (smallChainAugmentation R X U)).symm


@[simp]
theorem augmentedSmallChainMap_f_zero : (augmentedSmallChainMap R X U).f 0 = 𝟙 R := rfl


@[simp]
theorem augmentedSmallChainMap_f_succ (n : ℕ) :
    (augmentedSmallChainMap R X U).f (n + 1) = (smallChainMap X U R).f n := rfl

theorem quasiIso_augmentedSmallChainMap
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) :
    QuasiIso (augmentedSmallChainMap R X U) := by
  have hf := quasiIso_smallChainMap X U R hopen hcover
  have hf' : QuasiIso (SSet.chainComplexMap (smallSingularSimplices X U).ι R) := hf
  exact Poincare.ChainComplex.quasiIso_augmentMap
    (d_smallChainAugmentation R X U) (d_singularAugmentation R X)
    (SSet.chainComplexMap (smallSingularSimplices X U).ι R) (𝟙 R) _

def augmentedSmallChainHomologyIso
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    (augmentedSmallChainComplex R X U).homology (n + 1) ≅
      reducedSingularHomology R X n := by
  have := quasiIso_augmentedSmallChainMap R X U hopen hcover
  exact isoOfQuasiIsoAt (augmentedSmallChainMap R X U) (n + 1)


@[simp]
theorem augmentedSmallChainHomologyIso_hom
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    (augmentedSmallChainHomologyIso R X U hopen hcover n).hom =
      HomologicalComplex.homologyMap (augmentedSmallChainMap R X U) (n + 1) := rfl

variable (s t : Set X)

private theorem firstSubspace_augmentation :
    (SSet.chainComplexMap (firstSubspaceToSmall X s t) R).f 0 ≫
      smallChainAugmentation R X (twoSetFamily X s t) =
      singularAugmentation R (TopCat.of s) := by
  change (SSet.chainComplexMap (firstSubspaceToSmall X s t) R).f 0 ≫
    (SSet.chainComplexMap (smallSingularSimplices X (twoSetFamily X s t)).ι R).f 0 ≫
      singularAugmentation R X = _
  rw [← Category.assoc, ← HomologicalComplex.comp_f]
  rw [← Functor.map_comp, firstSubspaceToSmall_ι]
  exact singularAugmentation_naturality R _

private theorem secondSubspace_augmentation :
    (SSet.chainComplexMap (secondSubspaceToSmall X s t) R).f 0 ≫
      smallChainAugmentation R X (twoSetFamily X s t) =
      singularAugmentation R (TopCat.of t) := by
  change (SSet.chainComplexMap (secondSubspaceToSmall X s t) R).f 0 ≫
    (SSet.chainComplexMap (smallSingularSimplices X (twoSetFamily X s t)).ι R).f 0 ≫
      singularAugmentation R X = _
  rw [← Category.assoc, ← HomologicalComplex.comp_f]
  rw [← Functor.map_comp, secondSubspaceToSmall_ι]
  exact singularAugmentation_naturality R _


def augmentedFirstSubspaceToSmall : augmentedSingularChainComplex R (TopCat.of s) ⟶
    augmentedSmallChainComplex R X (twoSetFamily X s t) :=
  Poincare.ChainComplex.augmentMap (d_singularAugmentation R (TopCat.of s))
    (d_smallChainAugmentation R X (twoSetFamily X s t))
    (SSet.chainComplexMap (firstSubspaceToSmall X s t) R) (𝟙 R)
    (by simpa using! firstSubspace_augmentation R X s t)


def augmentedSecondSubspaceToSmall : augmentedSingularChainComplex R (TopCat.of t) ⟶
    augmentedSmallChainComplex R X (twoSetFamily X s t) :=
  Poincare.ChainComplex.augmentMap (d_singularAugmentation R (TopCat.of t))
    (d_smallChainAugmentation R X (twoSetFamily X s t))
    (SSet.chainComplexMap (secondSubspaceToSmall X s t) R) (𝟙 R)
    (by simpa using! secondSubspace_augmentation R X s t)


@[simp]
theorem augmentedFirstSubspaceToSmall_f_zero :
    (augmentedFirstSubspaceToSmall R X s t).f 0 = 𝟙 R := rfl


@[simp]
theorem augmentedSecondSubspaceToSmall_f_zero :
    (augmentedSecondSubspaceToSmall R X s t).f 0 = 𝟙 R := rfl


@[simp]
theorem augmentedFirstSubspaceToSmall_f_succ (n : ℕ) :
    (augmentedFirstSubspaceToSmall R X s t).f (n + 1) =
      (SSet.chainComplexMap (firstSubspaceToSmall X s t) R).f n := rfl


@[simp]
theorem augmentedSecondSubspaceToSmall_f_succ (n : ℕ) :
    (augmentedSecondSubspaceToSmall R X s t).f (n + 1) =
      (SSet.chainComplexMap (secondSubspaceToSmall X s t) R).f n := rfl

theorem augmentedSubspaceSmallSquare :
    IsPushout
      (augmentedSingularChainMap R
        (subspaceInclusion X (show s ∩ t ⊆ s from Set.inter_subset_left)))
      (augmentedSingularChainMap R
        (subspaceInclusion X (show s ∩ t ⊆ t from Set.inter_subset_right)))
      (augmentedFirstSubspaceToSmall R X s t) (augmentedSecondSubspaceToSmall R X s t) := by
  have hn : ∀ n, IsPushout
      ((augmentedSingularChainMap R
        (subspaceInclusion X (show s ∩ t ⊆ s from Set.inter_subset_left))).f n)
      ((augmentedSingularChainMap R
        (subspaceInclusion X (show s ∩ t ⊆ t from Set.inter_subset_right))).f n)
      ((augmentedFirstSubspaceToSmall R X s t).f n)
      ((augmentedSecondSubspaceToSmall R X s t).f n) := by
    intro n
    cases n with
    | zero => exact IsPushout.of_id_fst
    | succ n =>
      exact (HomologicalComplex.eval (ModuleCat.{u} k) (ComplexShape.down ℕ) n).map_isPushout
        (subspaceSmallChainSquare X s t R)
  refine ⟨⟨?w⟩, ⟨HomologicalComplex.isColimitOfEval _ _ (fun n => ?_)⟩⟩
  · apply HomologicalComplex.Hom.ext
    funext n
    exact (hn n).w
  · exact (PushoutCocone.isColimitMapCoconeEquiv _ _).symm (hn n).isColimit


abbrev augmentedSubspaceSmallShortComplex : ShortComplex (ChainComplex (ModuleCat.{u} k) ℕ) :=
  Poincare.ShortComplex.pushoutShortComplex (augmentedSubspaceSmallSquare R X s t)

theorem augmentedSubspaceSmallShortExact :
    (augmentedSubspaceSmallShortComplex R X s t).ShortExact := by
  have : Mono (subspaceInclusion X (show s ∩ t ⊆ s from Set.inter_subset_left)) :=
    (TopCat.mono_iff_injective _).mpr (Set.inclusion_injective Set.inter_subset_left)
  have : Mono (augmentedSingularChainMap R
      (subspaceInclusion X (show s ∩ t ⊆ s from Set.inter_subset_left))) := by
    apply HomologicalComplex.mono_of_mono_f
    intro n
    cases n with
    | zero => change Mono (𝟙 R); infer_instance
    | succ n =>
      change Mono ((SSet.chainComplexMap (TopCat.toSSet.map
        (subspaceInclusion X (show s ∩ t ⊆ s from Set.inter_subset_left))) R).f n)
      unfold SSet.chainComplexMap
      infer_instance
  exact Poincare.ShortComplex.pushoutShortExact (augmentedSubspaceSmallSquare R X s t)


def augmentedSmallConnectingMap (n : ℕ) :
    (augmentedSmallChainComplex R X (twoSetFamily X s t)).homology (n + 2) ⟶
      reducedSingularHomology R (TopCat.of ↥(s ∩ t)) n :=
  (augmentedSubspaceSmallShortExact R X s t).δ (n + 2) (n + 1) rfl

private theorem isZero_middle_homology [ContractibleSpace s] [ContractibleSpace t] (n : ℕ) :
    IsZero ((augmentedSubspaceSmallShortComplex R X s t).X₂.homology (n + 1)) :=
  IsZero.of_iso ((biprod_isZero_iff _ _).mpr
    ⟨isZero_reducedSingularHomology_of_contractible R (TopCat.of s) n,
      isZero_reducedSingularHomology_of_contractible R (TopCat.of t) n⟩)
    (Poincare.HomologicalComplex.homologyBiprodIso
      (augmentedSingularChainComplex R (TopCat.of s))
      (augmentedSingularChainComplex R (TopCat.of t)) (n + 1))

def augmentedSmallConnectingIso [ContractibleSpace s] [ContractibleSpace t] (n : ℕ) :
    (augmentedSmallChainComplex R X (twoSetFamily X s t)).homology (n + 2) ≅
      reducedSingularHomology R (TopCat.of ↥(s ∩ t)) n :=
  (augmentedSubspaceSmallShortExact R X s t).δIso (n + 2) (n + 1) rfl
    (isZero_middle_homology R X s t (n + 1)) (isZero_middle_homology R X s t n)


@[simp]
theorem augmentedSmallConnectingIso_hom [ContractibleSpace s] [ContractibleSpace t] (n : ℕ) :
    (augmentedSmallConnectingIso R X s t n).hom = augmentedSmallConnectingMap R X s t n := rfl

private theorem twoSetFamily_open (hs : IsOpen s) (ht : IsOpen t) :
    ∀ b, IsOpen (twoSetFamily X s t b) := by
  intro b
  cases b
  · exact ht
  · exact hs

private theorem twoSetFamily_cover (hcover : ∀ x : X, x ∈ s ∨ x ∈ t) :
    ∀ x : X, ∃ b, x ∈ twoSetFamily X s t b := by
  intro x
  rcases hcover x with h | h
  · exact ⟨true, h⟩
  · exact ⟨false, h⟩

def reducedMayerVietorisConnectingIso [ContractibleSpace s] [ContractibleSpace t]
    (hs : IsOpen s) (ht : IsOpen t) (hcover : ∀ x : X, x ∈ s ∨ x ∈ t) (n : ℕ) :
    reducedSingularHomology R X (n + 1) ≅
      reducedSingularHomology R (TopCat.of ↥(s ∩ t)) n :=
  (augmentedSmallChainHomologyIso R X (twoSetFamily X s t)
    (twoSetFamily_open X s t hs ht) (twoSetFamily_cover X s t hcover) (n + 1)).symm ≪≫
      augmentedSmallConnectingIso R X s t n

@[reassoc (attr := simp)]
theorem small_inclusion_reducedMayerVietorisConnectingIso
    [ContractibleSpace s] [ContractibleSpace t]
    (hs : IsOpen s) (ht : IsOpen t) (hcover : ∀ x : X, x ∈ s ∨ x ∈ t) (n : ℕ) :
    HomologicalComplex.homologyMap
      (augmentedSmallChainMap R X (twoSetFamily X s t)) (n + 2) ≫
        (reducedMayerVietorisConnectingIso R X s t hs ht hcover n).hom =
          augmentedSmallConnectingMap R X s t n := by
  change (augmentedSmallChainHomologyIso R X (twoSetFamily X s t)
    (twoSetFamily_open X s t hs ht) (twoSetFamily_cover X s t hcover) (n + 1)).hom ≫
      ((augmentedSmallChainHomologyIso R X (twoSetFamily X s t)
        (twoSetFamily_open X s t hs ht) (twoSetFamily_cover X s t hcover) (n + 1)).inv ≫ _) = _
  rw [Iso.hom_inv_id_assoc]
  rfl

end Poincare.Homology
