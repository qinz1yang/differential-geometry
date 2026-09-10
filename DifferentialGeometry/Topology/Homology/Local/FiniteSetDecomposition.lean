import DifferentialGeometry.Topology.Homology.Local.FiniteSet
import Mathlib.LinearAlgebra.Pi

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits Set
namespace Poincare.Homology
universe u
variable (X : TopCat.{u}) [T2Space X] (Z : Set X)
  {k : Type u} [Ring k] (A : ModuleCat.{u} k) (hZ : Z.Finite) (n : ℕ)


def finitePunctureHomologyInclusion (p : Z) :
    relativeHomology X ({p.val}ᶜ : Set X) A n ⟶ relativeHomology X Zᶜ A n := by
  classical
  exact ModuleCat.ofHom ((finitePunctureHomologyLinearEquiv X Z A hZ n).symm.toLinearMap.comp
    (LinearMap.single k (fun q : Z => relativeHomology X ({q.val}ᶜ : Set X) A n) p))


@[reassoc (attr := simp)]
theorem finitePunctureHomologyInclusion_projection_self (p : Z) :
    finitePunctureHomologyInclusion X Z A hZ n p ≫ finitePunctureProjection X Z A p n = 𝟙 _ := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rw [ModuleCat.hom_comp,LinearMap.comp_apply,← finitePunctureHomologyLinearEquiv_apply]
  change finitePunctureHomologyLinearEquiv X Z A hZ n
    ((finitePunctureHomologyLinearEquiv X Z A hZ n).symm (Pi.single p z)) p = z
  rw [LinearEquiv.apply_symm_apply,Pi.single_eq_same]


@[reassoc (attr := simp)]
theorem finitePunctureHomologyInclusion_projection_ne (p q : Z) (hpq : p ≠ q) :
    finitePunctureHomologyInclusion X Z A hZ n p ≫ finitePunctureProjection X Z A q n = 0 := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rw [ModuleCat.hom_comp,LinearMap.comp_apply,← finitePunctureHomologyLinearEquiv_apply]
  change finitePunctureHomologyLinearEquiv X Z A hZ n
    ((finitePunctureHomologyLinearEquiv X Z A hZ n).symm (Pi.single p z)) q = 0
  rw [LinearEquiv.apply_symm_apply,Pi.single_eq_of_ne hpq.symm]


theorem finsum_finitePunctureHomologyInclusion
    (z : ∀ p : Z, relativeHomology X ({p.val}ᶜ : Set X) A n) :
    (∑ᶠ p : Z, finitePunctureHomologyInclusion X Z A hZ n p (z p)) =
      (finitePunctureHomologyLinearEquiv X Z A hZ n).symm z := by
  classical
  let := hZ.fintype
  rw [finsum_eq_sum_of_fintype]
  change (∑ p : Z, (finitePunctureHomologyLinearEquiv X Z A hZ n).symm (Pi.single p (z p))) = _
  rw [← map_sum,LinearMap.sum_single_apply]


theorem finsum_finitePunctureHomologyInclusion_projection (z : relativeHomology X Zᶜ A n) :
    (∑ᶠ p : Z, finitePunctureHomologyInclusion X Z A hZ n p (finitePunctureProjection X Z A p n z)) = z := by
  simpa only [finitePunctureHomologyLinearEquiv_apply,LinearEquiv.symm_apply_apply] using
    finsum_finitePunctureHomologyInclusion X Z A hZ n (finitePunctureHomologyLinearEquiv X Z A hZ n z)
end Poincare.Homology
