import DifferentialGeometry.Topology.Homology.Relative.Map
import DifferentialGeometry.Topology.Homology.SmallChains.QuasiIso
import DifferentialGeometry.Topology.Homology.SmallChains.Union
import DifferentialGeometry.Topology.Homology.Algebra.CokernelQuasiIso

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
noncomputable section
universe u
namespace Poincare.Homology
variable (X : TopCat.{u}) (s t : Set X) {k : Type u} [Ring k] (R : ModuleCat.{u} k)

private def nestedIntersectionHomeomorph : {x : s // (x : X) ∈ t} ≃ₜ (s ∩ t : Set X) where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

private theorem relativeSmallSquare :
    IsPushout (relativeInclusion (TopCat.of s) {x : s | (x : X) ∈ t} R)
      (((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map
        (relativeSubspaceMap
          (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X)))
          (show Set.MapsTo Subtype.val {x : s | (x : X) ∈ t} t from fun _ hx => hx)))
      (SSet.chainComplexMap (firstSubspaceToSmall X s t) R)
      (SSet.chainComplexMap (secondSubspaceToSmall X s t) R) := by
  apply (subspaceSmallChainSquare X s t R).of_iso'
    (((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).mapIso
      (TopCat.isoOfHomeo (nestedIntersectionHomeomorph X s t)))
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · change _ ≫ _ = _ ≫ 𝟙 _
    erw [Category.comp_id]
    change ((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map _ ≫
      ((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map _ = _
    erw [← Functor.map_comp]
    rfl
  · change _ ≫ _ = _ ≫ 𝟙 _
    erw [Category.comp_id]
    change ((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map _ ≫
      ((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map _ = _
    erw [← Functor.map_comp]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]


theorem quasiIso_relativeChainMap_of_openCover (hs : IsOpen s) (ht : IsOpen t)
    (hcover : s ∪ t = Set.univ) :
    QuasiIso (relativeChainMap R
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X)))
      (show Set.MapsTo Subtype.val {x : s | (x : X) ∈ t} t from fun _ hx => hx)) := by
  let i := relativeInclusion (TopCat.of s) {x : s | (x : X) ∈ t} R
  let j := SSet.chainComplexMap (secondSubspaceToSmall X s t) R
  let a := ((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map
    (relativeSubspaceMap
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X)))
      (show Set.MapsTo Subtype.val {x : s | (x : X) ∈ t} t from fun _ hx => hx))
  let b := SSet.chainComplexMap (firstSubspaceToSmall X s t) R
  have sq : IsPushout i a b j := relativeSmallSquare X s t R
  let q := cokernel.map i j a b sq.w
  have : IsIso q := isIso_cokernel_map_of_isPushout sq
  let I := smallChainMap X (twoSetFamily X s t) R
  have hjI : j ≫ I = relativeInclusion X t R := by
    change SSet.chainComplexMap _ R ≫ SSet.chainComplexMap _ R = _
    erw [← Functor.map_comp]
    rfl
  have hmono : Mono (relativeInclusion X t R) := inferInstance
  have : Mono (j ≫ I) := by
    rw [hjI]
    exact hmono
  have : Mono j := mono_of_mono j I
  have hcov : ∀ x, ∃ b, x ∈ twoSetFamily X s t b := by
    intro x
    have hx : x ∈ s ∪ t := by rw [hcover]; trivial
    rcases hx with hx | hx
    · exact ⟨true, hx⟩
    · exact ⟨false, hx⟩
  have hopen : ∀ b, IsOpen (twoSetFamily X s t b) := by
    intro b
    cases b
    · exact ht
    · exact hs
  have hI : QuasiIso I := quasiIso_smallChainMap X (twoSetFamily X s t) R hopen hcov
  have hab : j ≫ I = 𝟙 _ ≫ relativeInclusion X t R := by simpa using hjI
  let q' := cokernel.map j (relativeInclusion X t R) (𝟙 _) I hab
  have : QuasiIso q' := Poincare.HomologicalComplex.quasiIso_cokernel_map
    j (relativeInclusion X t R) (𝟙 _) I hab (quasiIso_of_isIso (𝟙 _)) hI
  have heq : relativeChainMap R
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X)))
      (show Set.MapsTo Subtype.val {x : s | (x : X) ∈ t} t from fun _ hx => hx) = q ≫ q' := by
    apply (cancel_epi (cokernel.π i)).mp
    change relativeProjection (TopCat.of s) {x : s | (x : X) ∈ t} R ≫ _ = _
    rw [relativeProjection_chainMap]
    change _ = cokernel.π i ≫ cokernel.map i j a b sq.w ≫
      cokernel.map j (relativeInclusion X t R) (𝟙 _) I hab
    erw [cokernel.π_desc_assoc, Category.assoc, cokernel.π_desc]
    change _ = b ≫ I ≫ _
    have hbI : b ≫ I = relativeInclusion X s R := by
      change SSet.chainComplexMap _ R ≫ SSet.chainComplexMap _ R = _
      rw [← Functor.map_comp]
      rfl
    erw [← Category.assoc, hbI]
    rfl
  rw [heq]
  exact quasiIso_comp q q'


def relativeExcisionIso (hs : IsOpen s) (ht : IsOpen t)
    (hcover : s ∪ t = Set.univ) (n : ℕ) :
    relativeHomology (TopCat.of s) {x : s | (x : X) ∈ t} R n ≅
      relativeHomology X t R n := by
  letI := quasiIso_relativeChainMap_of_openCover X s t R hs ht hcover
  exact isoOfQuasiIsoAt (relativeChainMap R
    (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X)))
    (show Set.MapsTo Subtype.val {x : s | (x : X) ∈ t} t from fun _ hx => hx)) n


@[simp]
theorem relativeExcisionIso_hom (hs : IsOpen s) (ht : IsOpen t)
    (hcover : s ∪ t = Set.univ) (n : ℕ) :
    (relativeExcisionIso X s t R hs ht hcover n).hom =
      relativeHomologyMap R
        (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X)))
        (show Set.MapsTo Subtype.val {x : s | (x : X) ∈ t} t from fun _ hx => hx) n := rfl

end Poincare.Homology
