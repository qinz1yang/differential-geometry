import DifferentialGeometry.Topology.Homology.Relative.ReducedMap
import DifferentialGeometry.Topology.Homology.Local.Neighborhood

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits Set
namespace Poincare.Homology
universe u
variable (X : TopCat.{u}) [T1Space X] [ContractibleSpace X]
  (U : Set X) [ContractibleSpace U] (x : X) (hx : x ∈ U) (hU : IsOpen U)
  {k : Type u} [Ring k] (R : ModuleCat.{u} k)

def reducedPuncturedNeighborhoodHomologyIso (n : ℕ) :
    reducedSingularHomology R (TopCat.of ({(⟨x,hx⟩ : U)}ᶜ : Set U)) n ≅
      reducedSingularHomology R (TopCat.of ({x}ᶜ : Set X)) n :=
  (relativeReducedConnectingIso (TopCat.of U) ({(⟨x,hx⟩ : U)}ᶜ : Set U) R n).symm ≪≫
    puncturedNeighborhoodHomologyIso X U x hx R hU (n + 1) ≪≫
      relativeReducedConnectingIso X ({x}ᶜ : Set X) R n


@[simp]
theorem reducedPuncturedNeighborhoodHomologyIso_hom (n : ℕ) :
    (reducedPuncturedNeighborhoodHomologyIso X U x hx hU R n).hom =
      reducedSingularHomologyMap R
        (relativeSubspaceMap (X := TopCat.of U) (Y := X)
          (TopCat.ofHom (⟨Subtype.val,continuous_subtype_val⟩ : C(U,X)))
          (puncturedNeighborhood_mapsTo X U x hx)) n := by
  change (relativeReducedConnectingIso (TopCat.of U) ({(⟨x,hx⟩ : U)}ᶜ : Set U) R n).inv ≫
    ((puncturedNeighborhoodHomologyIso X U x hx R hU (n + 1)).hom ≫
      (relativeReducedConnectingIso X ({x}ᶜ : Set X) R n).hom) = _
  apply (Iso.inv_comp_eq _).mpr
  exact (relativeReducedConnectingIso_naturality R
    (TopCat.ofHom (⟨Subtype.val,continuous_subtype_val⟩ : C(U,X)))
    (puncturedNeighborhood_mapsTo X U x hx) n).symm
end Poincare.Homology
