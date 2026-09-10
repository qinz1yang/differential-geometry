import DifferentialGeometry.Topology.Homology.Relative.DisjointExcision
import DifferentialGeometry.Topology.Homology.Local.Neighborhood
import Mathlib.Topology.Separation.Hausdorff
import DifferentialGeometry.Topology.Homology.Relative.MapZero
import Mathlib.Algebra.Category.ModuleCat.Products

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits Set Function
namespace Poincare.Homology
universe u
variable (X : TopCat.{u}) (Z : Set X) (U : Z → Set X)
  (hp : ∀ p, p.val ∈ U p) (hd : Pairwise (Disjoint on U))
include hd in
private theorem finitePuncture_neighborhood_iff (p : Z) (x : U p) :
    x.val ∈ Zᶜ ↔ x ∈ ({(⟨p.val, hp p⟩ : U p)}ᶜ : Set (U p)) := by
  change x.val ∉ Z ↔ x ≠ ⟨p.val, hp p⟩
  constructor
  · intro hx he
    exact hx (by rw [he]; exact p.property)
  · intro hx hz
    let q : Z := ⟨x.val, hz⟩
    have he : p = q := by
      by_contra h
      exact Set.disjoint_left.mp (hd h) x.property (hp q)
    exact hx (Subtype.ext (congrArg Subtype.val he).symm)

include hp in
private theorem finitePuncture_cover : (⋃ p, U p) ∪ Zᶜ = univ := by
  apply eq_univ_of_forall
  intro x
  by_cases hx : x ∈ Z
  · exact Or.inl (mem_iUnion.mpr ⟨⟨x,hx⟩,hp ⟨x,hx⟩⟩)
  · exact Or.inr hx

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)
private def finitePuncture_neighborhoodIso [T1Space X] (hU : ∀ p, IsOpen (U p))
    (n : ℕ) (p : Z) :
    relativeHomology (TopCat.of (U p)) {x : U p | x.val ∈ Zᶜ} R n ≅
      relativeHomology X ({p.val}ᶜ : Set X) R n :=
  relativeHomologyIso (X := TopCat.of (U p)) (Y := TopCat.of (U p)) R (Homeomorph.refl (U p))
    (s := {x : U p | x.val ∈ Zᶜ}) (t := ({(⟨p.val,hp p⟩ : U p)}ᶜ : Set (U p)))
    (finitePuncture_neighborhood_iff X Z U hp hd p) n ≪≫
      puncturedNeighborhoodHomologyIso X (U p) p.val (hp p) R (hU p) n

private def finitePunctureHomologyIsoOfNeighborhoods [T1Space X] (hZ : Z.Finite)
    (hU : ∀ p, IsOpen (U p)) (n : ℕ) :
    (∐ fun p : Z => relativeHomology X ({p.val}ᶜ : Set X) R n) ≅
      relativeHomology X Zᶜ R n := by
  letI := hZ.to_subtype
  exact Sigma.mapIso (fun p => (finitePuncture_neighborhoodIso X Z U hp hd R hU n p).symm) ≪≫
    disjointRelativeHomologyIso X U Zᶜ R hU hd hZ.isClosed.isOpen_compl
      (finitePuncture_cover X Z U hp) n


def finitePunctureProjection (p : Z) (n : ℕ) :
    relativeHomology X Zᶜ R n ⟶ relativeHomology X ({p.val}ᶜ : Set X) R n :=
  relativeHomologyMap R (𝟙 X) (s := Zᶜ) (t := ({p.val}ᶜ : Set X))
    (fun x hx he => by
      change x = p.val at he
      exact hx (he.symm ▸ p.property)) n

@[reassoc]
private theorem finitePuncture_neighborhoodIso_ι_hom [T1Space X] (hZ : Z.Finite)
    (hU : ∀ p, IsOpen (U p)) (n : ℕ) (p : Z) :
    (finitePuncture_neighborhoodIso X Z U hp hd R hU n p).hom ≫
      Sigma.ι (fun q : Z => relativeHomology X ({q.val}ᶜ : Set X) R n) p ≫
      (finitePunctureHomologyIsoOfNeighborhoods X Z U hp hd R hZ hU n).hom =
    relativeHomologyMap (X := TopCat.of (U p)) (Y := X) R
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(U p,X)))
      (s := {x : U p | x.val ∈ Zᶜ}) (t := Zᶜ) (fun _ hx => hx) n := by
  let := hZ.to_subtype
  simp only [finitePunctureHomologyIsoOfNeighborhoods, Iso.trans_hom,
    Sigma.ι_mapIso_hom_assoc, Iso.symm_hom, Iso.hom_inv_id_assoc,
    disjointRelativeHomologyIso_ι_hom]

private theorem finitePuncture_neighborhoodIso_hom [T1Space X]
    (hU : ∀ p, IsOpen (U p)) (n : ℕ) (p : Z) :
    (finitePuncture_neighborhoodIso X Z U hp hd R hU n p).hom =
    relativeHomologyMap (X := TopCat.of (U p)) (Y := X) R
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(U p,X)))
      (s := {x : U p | x.val ∈ Zᶜ}) (t := ({p.val}ᶜ : Set X))
      (fun x hx he => by
        change x.val = p.val at he
        exact hx (he.symm ▸ p.property)) n := by
  dsimp only [finitePuncture_neighborhoodIso, Iso.trans_hom, relativeHomologyIso_hom,
    puncturedNeighborhoodHomologyIso_hom]
  exact (relativeHomologyMap_comp (X := TopCat.of (U p)) (Y := TopCat.of (U p)) (Z := X) R
    (TopCat.ofHom ⟨Homeomorph.refl (U p), continuous_id⟩)
    (s := {x : U p | x.val ∈ Zᶜ}) (t := ({(⟨p.val,hp p⟩ : U p)}ᶜ : Set (U p)))
    (v := ({p.val}ᶜ : Set X))
    (fun x hx => (finitePuncture_neighborhood_iff X Z U hp hd p x).mp hx)
    (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(U p,X)))
    (puncturedNeighborhood_mapsTo X (U p) p.val (hp p)) n).symm

@[reassoc]
private theorem finitePunctureHomologyIsoOfNeighborhoods_ι_projection_self [T1Space X]
    (hZ : Z.Finite) (hU : ∀ p, IsOpen (U p)) (n : ℕ) (p : Z) :
    Sigma.ι (fun q : Z => relativeHomology X ({q.val}ᶜ : Set X) R n) p ≫
      (finitePunctureHomologyIsoOfNeighborhoods X Z U hp hd R hZ hU n).hom ≫
      finitePunctureProjection X Z R p n = 𝟙 _ := by
  apply (cancel_epi (finitePuncture_neighborhoodIso X Z U hp hd R hU n p).hom).mp
  rw [finitePuncture_neighborhoodIso_ι_hom_assoc, Category.comp_id,
    finitePuncture_neighborhoodIso_hom]
  exact (relativeHomologyMap_comp (X := TopCat.of (U p)) (Y := X) (Z := X) R
    (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(U p,X)))
    (s := {x : U p | x.val ∈ Zᶜ}) (t := Zᶜ) (v := ({p.val}ᶜ : Set X))
    (fun _ hx => hx) (𝟙 X) (fun x hx he => by
      change x = p.val at he
      exact hx (he.symm ▸ p.property)) n).symm

@[reassoc]
private theorem finitePunctureHomologyIsoOfNeighborhoods_ι_projection_ne [T1Space X]
    (hZ : Z.Finite) (hU : ∀ p, IsOpen (U p)) (n : ℕ) (p q : Z) (hpq : p ≠ q) :
    Sigma.ι (fun q : Z => relativeHomology X ({q.val}ᶜ : Set X) R n) p ≫
      (finitePunctureHomologyIsoOfNeighborhoods X Z U hp hd R hZ hU n).hom ≫
      finitePunctureProjection X Z R q n = 0 := by
  apply (cancel_epi (finitePuncture_neighborhoodIso X Z U hp hd R hU n p).hom).mp
  rw [finitePuncture_neighborhoodIso_ι_hom_assoc, comp_zero]
  apply (relativeHomologyMap_comp (X := TopCat.of (U p)) (Y := X) (Z := X) R
    (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(U p,X)))
    (s := {x : U p | x.val ∈ Zᶜ}) (t := Zᶜ) (v := ({q.val}ᶜ : Set X))
    (fun _ hx => hx) (𝟙 X) (fun x hx he => by
      change x = q.val at he
      exact hx (he.symm ▸ q.property)) n).symm.trans
  apply relativeHomologyMap_eq_zero_of_range_subset
  rintro y ⟨x,rfl⟩ he
  change x.val = q.val at he
  exact Set.disjoint_left.mp (hd hpq) (he ▸ x.property) (hp q)


def finitePunctureProductMap (n : ℕ) :
    relativeHomology X Zᶜ R n ⟶
      ∏ᶜ fun p : Z => relativeHomology X ({p.val}ᶜ : Set X) R n :=
  Pi.lift (fun p => finitePunctureProjection X Z R p n)


theorem isIso_finitePunctureProductMap [T2Space X] (hZ : Z.Finite) (n : ℕ) :
    IsIso (finitePunctureProductMap X Z R n) := by
  classical
  let := hZ.to_subtype
  obtain ⟨V,hV,hdV⟩ := hZ.t2_separation
  let U : Z → Set X := fun p => V p.val
  have hp : ∀ p : Z, p.val ∈ U p := fun p => (hV p.val).1
  have hd : Pairwise (Disjoint on U) := fun p q hpq =>
    hdV p.property q.property (fun h => hpq (Subtype.ext h))
  have hU : ∀ p : Z, IsOpen (U p) := fun p => (hV p.val).2
  let A := fun p : Z => relativeHomology X ({p.val}ᶜ : Set X) R n
  let : HasBiproduct A := HasBiproduct.of_hasProduct A
  let e := finitePunctureHomologyIsoOfNeighborhoods X Z U hp hd R hZ hU n
  have hm : e.hom ≫ finitePunctureProductMap X Z R n =
      (biproduct.isoCoproduct A).inv ≫ (biproduct.isoProduct A).hom := by
    apply Sigma.hom_ext
    intro p
    apply Pi.hom_ext
    intro q
    simp only [A, Category.assoc, finitePunctureProductMap, Pi.lift_π,
      biproduct.isoCoproduct_inv, biproduct.isoProduct_hom,
      Sigma.ι_desc_assoc]
    by_cases h : p = q
    · subst q
      exact (finitePunctureHomologyIsoOfNeighborhoods_ι_projection_self X Z U hp hd R hZ hU n p).trans
        (biproduct.ι_π_self A p).symm
    · exact (finitePunctureHomologyIsoOfNeighborhoods_ι_projection_ne X Z U hp hd R hZ hU n p q h).trans
        (biproduct.ι_π_ne A h).symm
  have : IsIso (e.hom ≫ finitePunctureProductMap X Z R n) := by rw [hm]; infer_instance
  have heq : finitePunctureProductMap X Z R n = e.inv ≫ (e.hom ≫ finitePunctureProductMap X Z R n) := by simp
  rw [heq]
  infer_instance


def finitePunctureHomologyIso [T2Space X] (hZ : Z.Finite) (n : ℕ) :
    relativeHomology X Zᶜ R n ≅
      ∏ᶜ fun p : Z => relativeHomology X ({p.val}ᶜ : Set X) R n := by
  letI := isIso_finitePunctureProductMap X Z R hZ n
  exact asIso (finitePunctureProductMap X Z R n)


@[reassoc (attr := simp)]
theorem finitePunctureHomologyIso_hom_π [T2Space X] (hZ : Z.Finite) (n : ℕ) (p : Z) :
    (finitePunctureHomologyIso X Z R hZ n).hom ≫
      Pi.π (fun p : Z => relativeHomology X ({p.val}ᶜ : Set X) R n) p =
        finitePunctureProjection X Z R p n := Pi.lift_π _ _


def finitePunctureHomologyLinearEquiv [T2Space X] (hZ : Z.Finite) (n : ℕ) :
    relativeHomology X Zᶜ R n ≃ₗ[k]
      ∀ p : Z, relativeHomology X ({p.val}ᶜ : Set X) R n :=
  (finitePunctureHomologyIso X Z R hZ n ≪≫
    ModuleCat.piIsoPi (fun p : Z => relativeHomology X ({p.val}ᶜ : Set X) R n)).toLinearEquiv


@[simp]
theorem finitePunctureHomologyLinearEquiv_apply [T2Space X] (hZ : Z.Finite) (n : ℕ)
    (z : relativeHomology X Zᶜ R n) (p : Z) :
    finitePunctureHomologyLinearEquiv X Z R hZ n z p =
      (finitePunctureProjection X Z R p n).hom z := by
  let A := fun p : Z => relativeHomology X ({p.val}ᶜ : Set X) R n
  have hm : ((finitePunctureHomologyIso X Z R hZ n).hom ≫ (ModuleCat.piIsoPi A).hom) ≫
      ModuleCat.ofHom (LinearMap.proj p : (∀ p : Z, A p) →ₗ[k] A p) =
        finitePunctureProjection X Z R p n := by
    rw [Category.assoc, ModuleCat.piIsoPi_hom_ker_subtype,
      finitePunctureHomologyIso_hom_π]
  exact congrArg (fun f => f.hom z) hm


theorem isZero_relativeHomology_finitePuncture [T2Space X] (hZ : Z.Finite) (n : ℕ)
    (h : ∀ p : Z, IsZero (relativeHomology X ({p.val}ᶜ : Set X) R n)) :
    IsZero (relativeHomology X Zᶜ R n) := by
  let : ∀ p : Z, Subsingleton (relativeHomology X ({p.val}ᶜ : Set X) R n) :=
    fun p => ModuleCat.isZero_iff_subsingleton.mp (h p)
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact ⟨fun x y => (finitePunctureHomologyLinearEquiv X Z R hZ n).injective
    (Subsingleton.elim _ _)⟩
end Poincare.Homology
