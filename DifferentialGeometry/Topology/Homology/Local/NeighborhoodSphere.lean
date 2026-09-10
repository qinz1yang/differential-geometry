import DifferentialGeometry.Topology.Homology.Local.NeighborhoodReduced
import DifferentialGeometry.Topology.Homology.Local.Euclidean

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits Set Metric
namespace DifferentialGeometry.Homology
universe u
variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (x : E)

private def puncturedTranslationHomeomorph : ({x}ᶜ : Set E) ≃ₜ ({0}ᶜ : Set E) :=
  (Homeomorph.subRight x).subtype (fun y => by
    change y ≠ x ↔ y - x ≠ 0
    exact sub_ne_zero.symm)


def puncturedRadialMap : C(({x}ᶜ : Set E), sphere (0 : E) 1) :=
  (puncturedSpaceSphereHomotopyEquiv E).toFun.comp (puncturedTranslationHomeomorph E x)


@[simp]
theorem puncturedRadialMap_apply (y : ({x}ᶜ : Set E)) :
    (puncturedRadialMap E x y : E) = ‖y.val - x‖⁻¹ • (y.val - x) :=
  puncturedSpaceSphereHomotopyEquiv_apply E _

variable (U : Set E) (hx : x ∈ U) (hU : IsOpen U)
  {k : Type u} [Ring k] (R : ModuleCat.{u} k)


def puncturedNeighborhoodRadialMap :
    C(({(⟨x,hx⟩ : U)}ᶜ : Set U), sphere (0 : E) 1) :=
  (puncturedRadialMap E x).comp
    (relativeSubspaceMap (X := TopCat.of U) (Y := TopCat.of E)
      (TopCat.ofHom (⟨Subtype.val,continuous_subtype_val⟩ : C(U,E)))
      (puncturedNeighborhood_mapsTo (TopCat.of E) U x hx)).hom


@[simp]
theorem puncturedNeighborhoodRadialMap_apply (y : ({(⟨x,hx⟩ : U)}ᶜ : Set U)) :
    (puncturedNeighborhoodRadialMap E x U hx y : E) =
      ‖y.val.val - x‖⁻¹ • (y.val.val - x) :=
  puncturedRadialMap_apply E x _


def puncturedNeighborhoodSphereHomologyIso [ContractibleSpace U] (n : ℕ) :
    reducedSingularHomology R (TopCat.of ({(⟨x,hx⟩ : U)}ᶜ : Set U)) n ≅
      reducedSingularHomology R (TopCat.of (sphere (0 : E) 1)) n :=
  reducedPuncturedNeighborhoodHomologyIso (TopCat.of E) U x hx hU R n ≪≫
    reducedSingularHomologyIso R (X := TopCat.of ({x}ᶜ : Set E))
      (Y := TopCat.of ({0}ᶜ : Set E)) (puncturedTranslationHomeomorph E x).toHomotopyEquiv n ≪≫
      reducedSingularHomologyIso R (X := TopCat.of ({0}ᶜ : Set E))
        (Y := TopCat.of (sphere (0 : E) 1)) (puncturedSpaceSphereHomotopyEquiv E) n


@[simp]
theorem puncturedNeighborhoodSphereHomologyIso_hom [ContractibleSpace U] (n : ℕ) :
    (puncturedNeighborhoodSphereHomologyIso E x U hx hU R n).hom =
      reducedSingularHomologyMap R
        (TopCat.ofHom (puncturedNeighborhoodRadialMap E x U hx)) n := by
  simp only [puncturedNeighborhoodSphereHomologyIso, Iso.trans_hom,
    reducedPuncturedNeighborhoodHomologyIso_hom]
  change reducedSingularHomologyMap R _ n ≫
    (reducedSingularHomologyMap R _ n ≫ reducedSingularHomologyMap R _ n) = _
  rw [← reducedSingularHomologyMap_comp, ← reducedSingularHomologyMap_comp]
  rfl

variable {r : ℝ} (hr : 0 < r) (hs : sphere x r ⊆ U)


def puncturedNeighborhoodSphereSection :
    C(sphere (0 : E) 1, ({(⟨x,hx⟩ : U)}ᶜ : Set U)) := by
  have hnorm (v : sphere (0 : E) 1) : ‖v.val‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
  have hmem (v : sphere (0 : E) 1) : x + r • v.val ∈ U := hs (by
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hr.le, hnorm, mul_one])
  have hne (v : sphere (0 : E) 1) : x + r • v.val ≠ x := by
    intro h
    have hz : r • v.val = 0 := add_left_cancel (h.trans (add_zero x).symm)
    have hn := congrArg norm hz
    rw [norm_smul, Real.norm_of_nonneg hr.le, hnorm, mul_one, norm_zero] at hn
    exact hr.ne' hn
  exact ⟨fun v => ⟨⟨x + r • v.val, hmem v⟩,
      fun he => hne v (congrArg Subtype.val he)⟩,
    ((continuous_const.add (continuous_const.smul continuous_subtype_val)).subtype_mk _).subtype_mk _⟩


@[simp]
theorem puncturedNeighborhoodSphereSection_apply (v : sphere (0 : E) 1) :
    (puncturedNeighborhoodSphereSection E x U hx hr hs v).val.val = x + r • v.val := rfl


theorem puncturedNeighborhoodRadialMap_comp_section :
    (puncturedNeighborhoodRadialMap E x U hx).comp
      (puncturedNeighborhoodSphereSection E x U hx hr hs) = ContinuousMap.id _ := by
  ext v
  change ((puncturedNeighborhoodRadialMap E x U hx)
    (puncturedNeighborhoodSphereSection E x U hx hr hs v) : E) = v.val
  rw [puncturedNeighborhoodRadialMap_apply, puncturedNeighborhoodSphereSection_apply,
    add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le,
    (show ‖v.val‖ = 1 from mem_sphere_zero_iff_norm.mp v.property), mul_one, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]


theorem puncturedNeighborhoodSphereHomologyIso_inv [ContractibleSpace U] (n : ℕ) :
    (puncturedNeighborhoodSphereHomologyIso E x U hx hU R n).inv =
      reducedSingularHomologyMap R
        (TopCat.ofHom (puncturedNeighborhoodSphereSection E x U hx hr hs)) n := by
  apply (cancel_mono (puncturedNeighborhoodSphereHomologyIso E x U hx hU R n).hom).mp
  rw [Iso.inv_hom_id, puncturedNeighborhoodSphereHomologyIso_hom,
    ← reducedSingularHomologyMap_comp]
  have he : (TopCat.ofHom (puncturedNeighborhoodSphereSection E x U hx hr hs)) ≫
      (TopCat.ofHom (puncturedNeighborhoodRadialMap E x U hx)) = 𝟙 (TopCat.of (sphere (0 : E) 1)) :=
    congrArg TopCat.ofHom (puncturedNeighborhoodRadialMap_comp_section E x U hx hr hs)
  rw [he, reducedSingularHomologyMap_id]
end DifferentialGeometry.Homology
