import DifferentialGeometry.Topology.Homology.Coefficients
import DifferentialGeometry.Topology.Homology.Reduced.MayerVietorisNaturality

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace DifferentialGeometry.Homology

variable {k : Type u} [Ring k] {R S : ModuleCat.{u} k}
  (φ : R ⟶ S) (X : TopCat.{u}) {ι : Type v} (U : ι → Set X)

private theorem smallChainAugmentation_coefficient_naturality :
    (((SSet.chainComplexFunctor (ModuleCat.{u} k)).map φ).app
      (smallSingularSimplices X U : SSet)).f 0 ≫ smallChainAugmentation S X U =
    smallChainAugmentation R X U ≫ φ := by
  have h := congrArg (fun f => f.f 0)
    (((SSet.chainComplexFunctor (ModuleCat.{u} k)).map φ).naturality
      (smallSingularSimplices X U).ι)
  simp only [_root_.HomologicalComplex.comp_f] at h
  change _ ≫ ((SSet.chainComplexMap (smallSingularSimplices X U).ι S).f 0 ≫
    singularAugmentation S X) =
    ((SSet.chainComplexMap (smallSingularSimplices X U).ι R).f 0 ≫
      singularAugmentation R X) ≫ φ
  rw [← Category.assoc, ← h, Category.assoc]
  simpa only [Category.assoc] using! congrArg
    (fun f => (SSet.chainComplexMap (smallSingularSimplices X U).ι R).f 0 ≫ f)
    (singularAugmentation_coefficient_naturality φ X)

def augmentedSmallChainCoefficientMap :
    augmentedSmallChainComplex R X U ⟶ augmentedSmallChainComplex S X U :=
  DifferentialGeometry.ChainComplex.augmentMap
    (d_smallChainAugmentation R X U) (d_smallChainAugmentation S X U)
    (((SSet.chainComplexFunctor (ModuleCat.{u} k)).map φ).app
      (smallSingularSimplices X U : SSet)) φ
    (smallChainAugmentation_coefficient_naturality φ X U)

@[simp]
theorem augmentedSmallChainCoefficientMap_f_zero :
    (augmentedSmallChainCoefficientMap φ X U).f 0 = φ := rfl

@[simp]
theorem augmentedSmallChainCoefficientMap_f_succ (n : ℕ) :
    (augmentedSmallChainCoefficientMap φ X U).f (n + 1) =
      (((SSet.chainComplexFunctor (ModuleCat.{u} k)).map φ).app
        (smallSingularSimplices X U : SSet)).f n := rfl

@[reassoc]
theorem augmentedSmallChainMap_coefficient_naturality :
    augmentedSmallChainMap R X U ≫ augmentedSingularChainCoefficientMap φ X =
      augmentedSmallChainCoefficientMap φ X U ≫ augmentedSmallChainMap S X U := by
  apply _root_.HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero => exact (Category.id_comp φ).trans (Category.comp_id φ).symm
  | succ n =>
    exact congrArg (fun f => f.f n)
      (((SSet.chainComplexFunctor (ModuleCat.{u} k)).map φ).naturality
        (smallSingularSimplices X U).ι)

variable (s t : Set X)

@[reassoc]
theorem augmentedFirstSubspaceToSmall_coefficient_naturality :
    augmentedFirstSubspaceToSmall R X s t ≫
        augmentedSmallChainCoefficientMap φ X (twoSetFamily X s t) =
      augmentedSingularChainCoefficientMap φ (TopCat.of s) ≫
        augmentedFirstSubspaceToSmall S X s t := by
  apply _root_.HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero => exact (Category.id_comp φ).trans (Category.comp_id φ).symm
  | succ n =>
    exact congrArg (fun f => f.f n)
      (((SSet.chainComplexFunctor (ModuleCat.{u} k)).map φ).naturality
        (firstSubspaceToSmall X s t))

@[reassoc]
theorem augmentedSecondSubspaceToSmall_coefficient_naturality :
    augmentedSecondSubspaceToSmall R X s t ≫
        augmentedSmallChainCoefficientMap φ X (twoSetFamily X s t) =
      augmentedSingularChainCoefficientMap φ (TopCat.of t) ≫
        augmentedSecondSubspaceToSmall S X s t := by
  apply _root_.HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero => exact (Category.id_comp φ).trans (Category.comp_id φ).symm
  | succ n =>
    exact congrArg (fun f => f.f n)
      (((SSet.chainComplexFunctor (ModuleCat.{u} k)).map φ).naturality
        (secondSubspaceToSmall X s t))

def augmentedSubspaceSmallCoefficientMap :
    augmentedSubspaceSmallShortComplex R X s t ⟶ augmentedSubspaceSmallShortComplex S X s t where
  τ₁ := augmentedSingularChainCoefficientMap φ (TopCat.of ↥(s ∩ t))
  τ₂ := biprod.map (augmentedSingularChainCoefficientMap φ (TopCat.of s))
    (augmentedSingularChainCoefficientMap φ (TopCat.of t))
  τ₃ := augmentedSmallChainCoefficientMap φ X (twoSetFamily X s t)
  comm₁₂ := by
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst, biprod.map_fst, biprod.lift_fst_assoc]
      exact (augmentedSingularChainCoefficientMap_naturality φ
        (subspaceInclusion X Set.inter_subset_left)).symm
    · simp only [Category.assoc, biprod.lift_snd, biprod.map_snd,
        biprod.lift_snd_assoc, Preadditive.comp_neg, Preadditive.neg_comp]
      exact congrArg Neg.neg (augmentedSingularChainCoefficientMap_naturality φ
        (subspaceInclusion X Set.inter_subset_right)).symm
  comm₂₃ := by
    apply biprod.hom_ext'
    · simp only [biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc_assoc]
      exact (augmentedFirstSubspaceToSmall_coefficient_naturality φ X s t).symm
    · simp only [biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc_assoc]
      exact (augmentedSecondSubspaceToSmall_coefficient_naturality φ X s t).symm

@[reassoc]
theorem augmentedSmallConnectingMap_coefficient_naturality (n : ℕ) :
    augmentedSmallConnectingMap R X s t n ≫
      reducedSingularHomologyCoefficientMap φ (TopCat.of ↥(s ∩ t)) n =
    _root_.HomologicalComplex.homologyMap
        (augmentedSmallChainCoefficientMap φ X (twoSetFamily X s t)) (n + 2) ≫
      augmentedSmallConnectingMap S X s t n :=
  _root_.HomologicalComplex.HomologySequence.δ_naturality
    (augmentedSubspaceSmallCoefficientMap φ X s t)
    (augmentedSubspaceSmallShortExact R X s t) (augmentedSubspaceSmallShortExact S X s t)
    (n + 2) (n + 1) rfl

@[reassoc]
theorem reducedMayerVietorisConnectingMap_coefficient_naturality
    (hs : IsOpen s) (ht : IsOpen t) (hcover : ∀ x : X, x ∈ s ∨ x ∈ t) (n : ℕ) :
    reducedSingularHomologyCoefficientMap φ X (n + 1) ≫
        reducedMayerVietorisConnectingMap S X s t hs ht hcover n =
      reducedMayerVietorisConnectingMap R X s t hs ht hcover n ≫
        reducedSingularHomologyCoefficientMap φ (TopCat.of ↥(s ∩ t)) n := by
  have := quasiIso_augmentedSmallChainMap R X (twoSetFamily X s t)
    (by
      intro b
      cases b with
      | false => exact ht
      | true => exact hs)
    (by
      intro x
      rcases hcover x with hx | hx
      · exact ⟨true, hx⟩
      · exact ⟨false, hx⟩)
  apply (cancel_epi (_root_.HomologicalComplex.homologyMap
    (augmentedSmallChainMap R X (twoSetFamily X s t)) (n + 2))).mp
  have h := congrArg (fun f => _root_.HomologicalComplex.homologyMap f (n + 2))
    (augmentedSmallChainMap_coefficient_naturality φ X (twoSetFamily X s t))
  simp only [_root_.HomologicalComplex.homologyMap_comp] at h
  change _root_.HomologicalComplex.homologyMap
      (augmentedSmallChainMap R X (twoSetFamily X s t)) (n + 2) ≫
      (_root_.HomologicalComplex.homologyMap (augmentedSingularChainCoefficientMap φ X) (n + 2) ≫
        reducedMayerVietorisConnectingMap S X s t hs ht hcover n) = _
  rw [← Category.assoc, h, Category.assoc,
    small_inclusion_reducedMayerVietorisConnectingMap, ← Category.assoc,
    small_inclusion_reducedMayerVietorisConnectingMap]
  exact (augmentedSmallConnectingMap_coefficient_naturality φ X s t n).symm

@[reassoc]
theorem reducedMayerVietorisConnectingIso_coefficient_naturality
    [ContractibleSpace s] [ContractibleSpace t]
    (hs : IsOpen s) (ht : IsOpen t) (hcover : ∀ x : X, x ∈ s ∨ x ∈ t) (n : ℕ) :
    reducedSingularHomologyCoefficientMap φ X (n + 1) ≫
        (reducedMayerVietorisConnectingIso S X s t hs ht hcover n).hom =
      (reducedMayerVietorisConnectingIso R X s t hs ht hcover n).hom ≫
        reducedSingularHomologyCoefficientMap φ (TopCat.of ↥(s ∩ t)) n :=
  reducedMayerVietorisConnectingMap_coefficient_naturality φ X s t hs ht hcover n

end DifferentialGeometry.Homology
