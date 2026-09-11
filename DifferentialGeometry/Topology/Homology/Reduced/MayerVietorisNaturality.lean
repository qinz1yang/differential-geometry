import DifferentialGeometry.Topology.Homology.Reduced.MayerVietoris
import DifferentialGeometry.Topology.Homology.Relative.Map

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
noncomputable section
universe u
namespace DifferentialGeometry.Homology
variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)
  {X Y : TopCat.{u}} {s t : Set X} {s' t' : Set Y}
  (f : X ⟶ Y) (hs : Set.MapsTo f s s') (ht : Set.MapsTo f t t')

private theorem augmentedIntersection_left :
    augmentedSingularChainMap R (subspaceInclusion X (show s ∩ t ⊆ s from Set.inter_subset_left)) ≫
      augmentedSingularChainMap R (relativeSubspaceMap f hs) =
    augmentedSingularChainMap R (relativeSubspaceMap f (hs.inter_inter ht)) ≫
      augmentedSingularChainMap R (subspaceInclusion Y (show s' ∩ t' ⊆ s' from Set.inter_subset_left)) := by
  rw [← augmentedSingularChainMap_comp, ← augmentedSingularChainMap_comp]
  rfl

private theorem augmentedIntersection_right :
    augmentedSingularChainMap R (subspaceInclusion X (show s ∩ t ⊆ t from Set.inter_subset_right)) ≫
      augmentedSingularChainMap R (relativeSubspaceMap f ht) =
    augmentedSingularChainMap R (relativeSubspaceMap f (hs.inter_inter ht)) ≫
      augmentedSingularChainMap R (subspaceInclusion Y (show s' ∩ t' ⊆ t' from Set.inter_subset_right)) := by
  rw [← augmentedSingularChainMap_comp, ← augmentedSingularChainMap_comp]
  rfl

def augmentedTwoCoverMap :
    augmentedSmallChainComplex R X (twoSetFamily X s t) ⟶
      augmentedSmallChainComplex R Y (twoSetFamily Y s' t') :=
  (augmentedSubspaceSmallSquare R X s t).desc
    (augmentedSingularChainMap R (relativeSubspaceMap f hs) ≫ augmentedFirstSubspaceToSmall R Y s' t')
    (augmentedSingularChainMap R (relativeSubspaceMap f ht) ≫ augmentedSecondSubspaceToSmall R Y s' t')
    (by
      rw [← Category.assoc, augmentedIntersection_left R f hs ht, Category.assoc,
        (augmentedSubspaceSmallSquare R Y s' t').w, ← Category.assoc,
        ← augmentedIntersection_right R f hs ht, Category.assoc])


@[reassoc (attr := simp)]
theorem augmentedFirstSubspaceToSmall_twoCoverMap :
    augmentedFirstSubspaceToSmall R X s t ≫ augmentedTwoCoverMap R f hs ht =
      augmentedSingularChainMap R (relativeSubspaceMap f hs) ≫ augmentedFirstSubspaceToSmall R Y s' t' :=
  (augmentedSubspaceSmallSquare R X s t).inl_desc _ _ _


@[reassoc (attr := simp)]
theorem augmentedSecondSubspaceToSmall_twoCoverMap :
    augmentedSecondSubspaceToSmall R X s t ≫ augmentedTwoCoverMap R f hs ht =
      augmentedSingularChainMap R (relativeSubspaceMap f ht) ≫ augmentedSecondSubspaceToSmall R Y s' t' :=
  (augmentedSubspaceSmallSquare R X s t).inr_desc _ _ _

private theorem firstSmall_inclusion (X : TopCat.{u}) (s t : Set X) :
    augmentedFirstSubspaceToSmall R X s t ≫
      augmentedSmallChainMap R X (twoSetFamily X s t) =
    augmentedSingularChainMap R
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X))) := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero => exact Category.comp_id _
  | succ n =>
    change ((SSet.chainComplexMap (firstSubspaceToSmall X s t) R) ≫
      SSet.chainComplexMap (smallSingularSimplices X (twoSetFamily X s t)).ι R).f n = _
    rw [← Functor.map_comp, firstSubspaceToSmall_ι]
    rfl

private theorem secondSmall_inclusion (X : TopCat.{u}) (s t : Set X) :
    augmentedSecondSubspaceToSmall R X s t ≫
      augmentedSmallChainMap R X (twoSetFamily X s t) =
    augmentedSingularChainMap R
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(t, X))) := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero => exact Category.comp_id _
  | succ n =>
    change ((SSet.chainComplexMap (secondSubspaceToSmall X s t) R) ≫
      SSet.chainComplexMap (smallSingularSimplices X (twoSetFamily X s t)).ι R).f n = _
    rw [← Functor.map_comp, secondSubspaceToSmall_ι]
    rfl


@[reassoc (attr := simp)]
theorem augmentedTwoCoverMap_inclusion :
    augmentedTwoCoverMap R f hs ht ≫ augmentedSmallChainMap R Y (twoSetFamily Y s' t') =
      augmentedSmallChainMap R X (twoSetFamily X s t) ≫ augmentedSingularChainMap R f := by
  apply (augmentedSubspaceSmallSquare R X s t).hom_ext
  · rw [augmentedFirstSubspaceToSmall_twoCoverMap_assoc,
      firstSmall_inclusion, ← Category.assoc, firstSmall_inclusion,
      ← augmentedSingularChainMap_comp, ← augmentedSingularChainMap_comp]
    rfl
  · rw [augmentedSecondSubspaceToSmall_twoCoverMap_assoc,
      secondSmall_inclusion, ← Category.assoc, secondSmall_inclusion,
      ← augmentedSingularChainMap_comp, ← augmentedSingularChainMap_comp]
    rfl

def augmentedTwoCoverShortComplexMap :
    augmentedSubspaceSmallShortComplex R X s t ⟶ augmentedSubspaceSmallShortComplex R Y s' t' where
  τ₁ := augmentedSingularChainMap R (relativeSubspaceMap f (hs.inter_inter ht))
  τ₂ := biprod.map (augmentedSingularChainMap R (relativeSubspaceMap f hs))
    (augmentedSingularChainMap R (relativeSubspaceMap f ht))
  τ₃ := augmentedTwoCoverMap R f hs ht
  comm₁₂ := by
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst, biprod.map_fst,
        biprod.lift_fst_assoc]
      exact (augmentedIntersection_left R f hs ht).symm
    · simp only [Category.assoc, biprod.lift_snd, biprod.map_snd,
        biprod.lift_snd_assoc, Preadditive.comp_neg, Preadditive.neg_comp]
      exact congrArg Neg.neg (augmentedIntersection_right R f hs ht).symm
  comm₂₃ := by
    apply biprod.hom_ext'
    · simp only [biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc_assoc,
        augmentedFirstSubspaceToSmall_twoCoverMap]
    · simp only [biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc_assoc,
        augmentedSecondSubspaceToSmall_twoCoverMap]

@[reassoc]
theorem augmentedSmallConnectingMap_naturality (n : ℕ) :
    augmentedSmallConnectingMap R X s t n ≫
      reducedSingularHomologyMap R (relativeSubspaceMap f (hs.inter_inter ht)) n =
    HomologicalComplex.homologyMap (augmentedTwoCoverMap R f hs ht) (n + 2) ≫
      augmentedSmallConnectingMap R Y s' t' n :=
  HomologicalComplex.HomologySequence.δ_naturality (augmentedTwoCoverShortComplexMap R f hs ht)
    (augmentedSubspaceSmallShortExact R X s t) (augmentedSubspaceSmallShortExact R Y s' t')
    (n + 2) (n + 1) rfl


@[simp]
theorem augmentedTwoCoverMap_f_zero : (augmentedTwoCoverMap R f hs ht).f 0 = 𝟙 R := by
  have h := congrArg (fun z ↦ z.f 0) (augmentedFirstSubspaceToSmall_twoCoverMap R f hs ht)
  change 𝟙 R ≫ (augmentedTwoCoverMap R f hs ht).f 0 = 𝟙 R ≫ 𝟙 R at h
  exact (Category.id_comp (show R ⟶ R from (augmentedTwoCoverMap R f hs ht).f 0)).symm.trans
    (h.trans (Category.id_comp (𝟙 R)))


@[reassoc]
theorem augmentedTwoCoverMap_homology_inclusion (n : ℕ) :
    HomologicalComplex.homologyMap (augmentedTwoCoverMap R f hs ht) (n + 1) ≫
        HomologicalComplex.homologyMap (augmentedSmallChainMap R Y (twoSetFamily Y s' t')) (n + 1) =
      HomologicalComplex.homologyMap (augmentedSmallChainMap R X (twoSetFamily X s t)) (n + 1) ≫
        reducedSingularHomologyMap R f n := by
  rw [← HomologicalComplex.homologyMap_comp, augmentedTwoCoverMap_inclusion,
    HomologicalComplex.homologyMap_comp]
  rfl

private theorem twoCover_open (X : TopCat.{u}) (s t : Set X)
    (hs : IsOpen s) (ht : IsOpen t) : ∀ b, IsOpen (twoSetFamily X s t b) := by
  intro b
  cases b
  · exact ht
  · exact hs

private theorem twoCover_covers (X : TopCat.{u}) (s t : Set X)
    (hcover : ∀ x : X, x ∈ s ∨ x ∈ t) : ∀ x : X, ∃ b, x ∈ twoSetFamily X s t b := by
  intro x
  rcases hcover x with h | h
  · exact ⟨true, h⟩
  · exact ⟨false, h⟩

def reducedMayerVietorisConnectingMap (X : TopCat.{u}) (s t : Set X)
    (hs : IsOpen s) (ht : IsOpen t) (hcover : ∀ x : X, x ∈ s ∨ x ∈ t) (n : ℕ) :
    reducedSingularHomology R X (n + 1) ⟶ reducedSingularHomology R (TopCat.of ↥(s ∩ t)) n :=
  (augmentedSmallChainHomologyIso R X (twoSetFamily X s t)
    (twoCover_open X s t hs ht) (twoCover_covers X s t hcover) (n + 1)).inv ≫
      augmentedSmallConnectingMap R X s t n


@[reassoc (attr := simp)]
theorem small_inclusion_reducedMayerVietorisConnectingMap (X : TopCat.{u}) (s t : Set X)
    (hs : IsOpen s) (ht : IsOpen t) (hcover : ∀ x : X, x ∈ s ∨ x ∈ t) (n : ℕ) :
    HomologicalComplex.homologyMap
        (augmentedSmallChainMap R X (twoSetFamily X s t)) (n + 2) ≫
      reducedMayerVietorisConnectingMap R X s t hs ht hcover n =
        augmentedSmallConnectingMap R X s t n := by
  change (augmentedSmallChainHomologyIso R X (twoSetFamily X s t)
    (twoCover_open X s t hs ht) (twoCover_covers X s t hcover) (n + 1)).hom ≫
      ((augmentedSmallChainHomologyIso R X (twoSetFamily X s t)
        (twoCover_open X s t hs ht) (twoCover_covers X s t hcover) (n + 1)).inv ≫ _) = _
  rw [Iso.hom_inv_id_assoc]

@[simp]
theorem reducedMayerVietorisConnectingMap_eq_iso (X : TopCat.{u}) (s t : Set X)
    [ContractibleSpace s] [ContractibleSpace t]
    (hs : IsOpen s) (ht : IsOpen t) (hcover : ∀ x : X, x ∈ s ∨ x ∈ t) (n : ℕ) :
    reducedMayerVietorisConnectingMap R X s t hs ht hcover n =
      (reducedMayerVietorisConnectingIso R X s t hs ht hcover n).hom := rfl

@[reassoc]
theorem reducedMayerVietorisConnectingMap_naturality
    (hsO : IsOpen s) (htO : IsOpen t) (hcover : ∀ x : X, x ∈ s ∨ x ∈ t)
    (hsO' : IsOpen s') (htO' : IsOpen t') (hcover' : ∀ y : Y, y ∈ s' ∨ y ∈ t') (n : ℕ) :
    reducedSingularHomologyMap R f (n + 1) ≫
        reducedMayerVietorisConnectingMap R Y s' t' hsO' htO' hcover' n =
      reducedMayerVietorisConnectingMap R X s t hsO htO hcover n ≫
        reducedSingularHomologyMap R (relativeSubspaceMap f (hs.inter_inter ht)) n := by
  have := quasiIso_augmentedSmallChainMap R X (twoSetFamily X s t)
    (twoCover_open X s t hsO htO) (twoCover_covers X s t hcover)
  apply (cancel_epi (HomologicalComplex.homologyMap
    (augmentedSmallChainMap R X (twoSetFamily X s t)) (n + 2))).mp
  simp only [← Category.assoc]
  rw [← augmentedTwoCoverMap_homology_inclusion R f hs ht (n + 1), Category.assoc,
    small_inclusion_reducedMayerVietorisConnectingMap,
    small_inclusion_reducedMayerVietorisConnectingMap]
  exact (augmentedSmallConnectingMap_naturality R f hs ht n).symm


def twoCoverIntersectionSwap (X : TopCat.{u}) (s t : Set X) :
    TopCat.of ↥(s ∩ t) ⟶ TopCat.of ↥(t ∩ s) :=
  subspaceInclusion X (fun _ h ↦ h.symm)

private theorem intersectionSwap_left (X : TopCat.{u}) (s t : Set X) :
    augmentedSingularChainMap R (twoCoverIntersectionSwap X s t) ≫
      augmentedSingularChainMap R (subspaceInclusion X (show t ∩ s ⊆ t from Set.inter_subset_left)) =
    augmentedSingularChainMap R (subspaceInclusion X (show s ∩ t ⊆ t from Set.inter_subset_right)) := by
  rw [← augmentedSingularChainMap_comp]
  rfl

private theorem intersectionSwap_right (X : TopCat.{u}) (s t : Set X) :
    augmentedSingularChainMap R (twoCoverIntersectionSwap X s t) ≫
      augmentedSingularChainMap R (subspaceInclusion X (show t ∩ s ⊆ s from Set.inter_subset_right)) =
    augmentedSingularChainMap R (subspaceInclusion X (show s ∩ t ⊆ s from Set.inter_subset_left)) := by
  rw [← augmentedSingularChainMap_comp]
  rfl


def augmentedTwoCoverSwap (X : TopCat.{u}) (s t : Set X) :
    augmentedSmallChainComplex R X (twoSetFamily X s t) ⟶
      augmentedSmallChainComplex R X (twoSetFamily X t s) :=
  (augmentedSubspaceSmallSquare R X s t).desc
    (augmentedSecondSubspaceToSmall R X t s) (augmentedFirstSubspaceToSmall R X t s)
    (by
      rw [← intersectionSwap_right R X s t, Category.assoc,
        ← (augmentedSubspaceSmallSquare R X t s).w,
        ← Category.assoc, intersectionSwap_left])


@[reassoc (attr := simp)]
theorem augmentedFirstSubspaceToSmall_swap (X : TopCat.{u}) (s t : Set X) :
    augmentedFirstSubspaceToSmall R X s t ≫ augmentedTwoCoverSwap R X s t =
      augmentedSecondSubspaceToSmall R X t s :=
  (augmentedSubspaceSmallSquare R X s t).inl_desc _ _ _


@[reassoc (attr := simp)]
theorem augmentedSecondSubspaceToSmall_swap (X : TopCat.{u}) (s t : Set X) :
    augmentedSecondSubspaceToSmall R X s t ≫ augmentedTwoCoverSwap R X s t =
      augmentedFirstSubspaceToSmall R X t s :=
  (augmentedSubspaceSmallSquare R X s t).inr_desc _ _ _


@[reassoc (attr := simp)]
theorem augmentedTwoCoverSwap_inclusion (X : TopCat.{u}) (s t : Set X) :
    augmentedTwoCoverSwap R X s t ≫ augmentedSmallChainMap R X (twoSetFamily X t s) =
      augmentedSmallChainMap R X (twoSetFamily X s t) := by
  apply (augmentedSubspaceSmallSquare R X s t).hom_ext
  · rw [augmentedFirstSubspaceToSmall_swap_assoc, secondSmall_inclusion, firstSmall_inclusion]
  · rw [augmentedSecondSubspaceToSmall_swap_assoc, firstSmall_inclusion, secondSmall_inclusion]

def augmentedTwoCoverSwapShortComplexMap (X : TopCat.{u}) (s t : Set X) :
    augmentedSubspaceSmallShortComplex R X s t ⟶ augmentedSubspaceSmallShortComplex R X t s where
  τ₁ := -(augmentedSingularChainMap R (twoCoverIntersectionSwap X s t))
  τ₂ := (biprod.braiding (augmentedSingularChainComplex R (TopCat.of s))
    (augmentedSingularChainComplex R (TopCat.of t))).hom
  τ₃ := augmentedTwoCoverSwap R X s t
  comm₁₂ := by
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.braiding_hom, biprod.lift_fst,
        biprod.lift_snd, Preadditive.neg_comp]
      rw [intersectionSwap_left]
    · simp only [Category.assoc, biprod.braiding_hom, biprod.lift_snd,
        biprod.lift_fst, Preadditive.neg_comp, Preadditive.comp_neg, neg_neg]
      rw [intersectionSwap_right]
  comm₂₃ := by
    rw [← biprod.braiding'_eq_braiding]
    apply biprod.hom_ext'
    · simp only [biprod.braiding'_hom, biprod.inl_desc_assoc,
        biprod.inr_desc, augmentedFirstSubspaceToSmall_swap]
    · simp only [biprod.braiding'_hom, biprod.inr_desc_assoc,
        biprod.inl_desc, augmentedSecondSubspaceToSmall_swap]

@[reassoc]
theorem augmentedSmallConnectingMap_swap (X : TopCat.{u}) (s t : Set X) (n : ℕ) :
    HomologicalComplex.homologyMap (augmentedTwoCoverSwap R X s t) (n + 2) ≫
        augmentedSmallConnectingMap R X t s n =
      -(augmentedSmallConnectingMap R X s t n ≫
        reducedSingularHomologyMap R (twoCoverIntersectionSwap X s t) n) := by
  have h := HomologicalComplex.HomologySequence.δ_naturality
    (augmentedTwoCoverSwapShortComplexMap R X s t)
    (augmentedSubspaceSmallShortExact R X s t) (augmentedSubspaceSmallShortExact R X t s)
    (n + 2) (n + 1) rfl
  change augmentedSmallConnectingMap R X s t n ≫
      HomologicalComplex.homologyMap (-(augmentedSingularChainMap R (twoCoverIntersectionSwap X s t)))
        (n + 1) = _ at h
  rw [HomologicalComplex.homologyMap_neg, Preadditive.comp_neg] at h
  exact h.symm


@[simp]
theorem twoCoverIntersectionSwap_comp (X : TopCat.{u}) (s t : Set X) :
    twoCoverIntersectionSwap X s t ≫ twoCoverIntersectionSwap X t s = 𝟙 _ := rfl


@[simp]
theorem augmentedTwoCoverSwap_comp (X : TopCat.{u}) (s t : Set X) :
    augmentedTwoCoverSwap R X s t ≫ augmentedTwoCoverSwap R X t s = 𝟙 _ := by
  apply (augmentedSubspaceSmallSquare R X s t).hom_ext
  · simp
  · simp


def augmentedTwoCoverSwapIso (X : TopCat.{u}) (s t : Set X) :
    augmentedSmallChainComplex R X (twoSetFamily X s t) ≅
      augmentedSmallChainComplex R X (twoSetFamily X t s) where
  hom := augmentedTwoCoverSwap R X s t
  inv := augmentedTwoCoverSwap R X t s
  hom_inv_id := augmentedTwoCoverSwap_comp R X s t
  inv_hom_id := augmentedTwoCoverSwap_comp R X t s

@[reassoc]
theorem reducedMayerVietorisConnectingMap_swap (X : TopCat.{u}) (s t : Set X)
    (hs : IsOpen s) (ht : IsOpen t) (hcover : ∀ x : X, x ∈ s ∨ x ∈ t) (n : ℕ) :
    reducedMayerVietorisConnectingMap R X t s ht hs (fun x ↦ (hcover x).symm) n =
      -(reducedMayerVietorisConnectingMap R X s t hs ht hcover n ≫
        reducedSingularHomologyMap R (twoCoverIntersectionSwap X s t) n) := by
  have := quasiIso_augmentedSmallChainMap R X (twoSetFamily X s t)
    (twoCover_open X s t hs ht) (twoCover_covers X s t hcover)
  have hi := congrArg (fun φ ↦ HomologicalComplex.homologyMap φ (n + 2))
    (augmentedTwoCoverSwap_inclusion R X s t)
  simp only [HomologicalComplex.homologyMap_comp] at hi
  apply (cancel_epi (HomologicalComplex.homologyMap
    (augmentedSmallChainMap R X (twoSetFamily X s t)) (n + 2))).mp
  conv_lhs => rw [← hi, Category.assoc, small_inclusion_reducedMayerVietorisConnectingMap]
  rw [Preadditive.comp_neg, ← Category.assoc, small_inclusion_reducedMayerVietorisConnectingMap]
  exact augmentedSmallConnectingMap_swap R X s t n

end DifferentialGeometry.Homology
