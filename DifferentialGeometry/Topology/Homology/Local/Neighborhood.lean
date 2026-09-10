import DifferentialGeometry.Topology.Homology.Relative.Excision
import DifferentialGeometry.Topology.Homology.Algebra.FiniteTypeMap

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology Set
namespace Poincare.Homology
universe u
variable (X : TopCat.{u}) (U : Set X) (x : X) (hx : x ∈ U)
  {k : Type u} [Ring k] (R : ModuleCat.{u} k)

theorem puncturedNeighborhood_mapsTo :
    Set.MapsTo (Subtype.val : U → X) ({(⟨x, hx⟩ : U)}ᶜ : Set U) ({x}ᶜ : Set X) := by
  intro y hy
  change y ≠ ⟨x, hx⟩ at hy
  change y.val ≠ x
  exact fun he => hy (Subtype.ext he)


def puncturedNeighborhoodChainMap :
    relativeChainComplex (TopCat.of U) ({(⟨x, hx⟩ : U)}ᶜ : Set U) R ⟶
      relativeChainComplex X ({x}ᶜ : Set X) R :=
  relativeChainMap R (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)))
    (puncturedNeighborhood_mapsTo X U x hx)

theorem quasiIso_puncturedNeighborhoodChainMap [T1Space X] (hU : IsOpen U) :
    QuasiIso (puncturedNeighborhoodChainMap X U x hx R) := by
  have hcover : U ∪ ({x}ᶜ : Set X) = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      by_cases hy : y = x
      · exact Or.inl (hy.symm ▸ hx)
      · exact Or.inr hy
  have he : {y : U | (y : X) ∈ ({x}ᶜ : Set X)} = ({(⟨x, hx⟩ : U)}ᶜ : Set U) := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_singleton_iff, Subtype.ext_iff]
  have hq := quasiIso_relativeChainMap_of_openCover X U ({x}ᶜ : Set X) R hU
    isClosed_singleton.isOpen_compl hcover
  let e := relativeChainIso (X := TopCat.of U) (Y := TopCat.of U) R (Homeomorph.refl (↥U))
    (s := ({(⟨x, hx⟩ : U)}ᶜ : Set U))
    (t := {y : U | (y : X) ∈ ({x}ᶜ : Set X)}) (fun y => by rw [he]; rfl)
  have hm : puncturedNeighborhoodChainMap X U x hx R = e.hom ≫
      relativeChainMap R (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)))
        (show Set.MapsTo Subtype.val {y : U | (y : X) ∈ ({x}ᶜ : Set X)} ({x}ᶜ : Set X)
          from fun _ hy => hy) := by
    unfold puncturedNeighborhoodChainMap
    dsimp only [e, relativeChainIso]
    erw [← relativeChainMap_comp]
    apply relativeChainMap_congr
    rfl
  rw [hm]
  exact quasiIso_comp e.hom _

def puncturedNeighborhoodHomologyIso [T1Space X] (hU : IsOpen U) (n : ℕ) :
    relativeHomology (TopCat.of U) ({(⟨x, hx⟩ : U)}ᶜ : Set U) R n ≅
      relativeHomology X ({x}ᶜ : Set X) R n := by
  let := quasiIso_puncturedNeighborhoodChainMap X U x hx R hU
  exact isoOfQuasiIsoAt (puncturedNeighborhoodChainMap X U x hx R) n

@[simp]
theorem puncturedNeighborhoodHomologyIso_hom [T1Space X] (hU : IsOpen U) (n : ℕ) :
    (puncturedNeighborhoodHomologyIso X U x hx R hU n).hom =
      relativeHomologyMap R (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)))
        (puncturedNeighborhood_mapsTo X U x hx) n := rfl

section Field
variable (k : Type u) [Field k]

theorem finiteHomologyType_puncturedNeighborhood_iff [T1Space X] (hU : IsOpen U) :
    Poincare.HomologicalComplex.finiteHomologyType
        (relativeChainComplex (TopCat.of U) ({(⟨x, hx⟩ : U)}ᶜ : Set U) (ModuleCat.of k k)) ↔
      Poincare.HomologicalComplex.finiteHomologyType
        (relativeChainComplex X ({x}ᶜ : Set X) (ModuleCat.of k k)) := by
  let :=  quasiIso_puncturedNeighborhoodChainMap X U x hx (ModuleCat.of k k) hU
  exact Poincare.HomologicalComplex.finiteHomologyType_iff_of_quasiIso
    (puncturedNeighborhoodChainMap X U x hx (ModuleCat.of k k))

theorem relativeEulerChar_puncturedNeighborhood [T1Space X] (hU : IsOpen U) :
    relativeEulerChar (TopCat.of U) ({(⟨x, hx⟩ : U)}ᶜ : Set U) k =
      relativeEulerChar X ({x}ᶜ : Set X) k := by
  let :=  quasiIso_puncturedNeighborhoodChainMap X U x hx (ModuleCat.of k k) hU
  exact Poincare.HomologicalComplex.homologyEulerChar_eq_of_quasiIso
    (puncturedNeighborhoodChainMap X U x hx (ModuleCat.of k k))

end Field

end Poincare.Homology
