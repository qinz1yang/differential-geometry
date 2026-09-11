import DifferentialGeometry.Topology.Homology.Relative
import Mathlib.Algebra.Homology.HomologySequenceLemmas

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
noncomputable section
universe u

namespace DifferentialGeometry.Homology
variable {X Y Z : TopCat.{u}} {s : Set X} {t : Set Y} {v : Set Z}
  {k : Type u} [Ring k] (R : ModuleCat.{u} k)


def relativeSubspaceMap (f : X ⟶ Y) (hf : Set.MapsTo f s t) :
    TopCat.of s ⟶ TopCat.of t :=
  TopCat.ofHom ⟨fun x ↦ ⟨f x, hf x.property⟩,
    (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩


theorem relativeInclusion_naturality (f : X ⟶ Y) (hf : Set.MapsTo f s t) :
    relativeInclusion X s R ≫ ((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map f =
      ((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map
        (relativeSubspaceMap f hf) ≫ relativeInclusion Y t R := by
  unfold relativeInclusion
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl


def relativeChainMap (f : X ⟶ Y) (hf : Set.MapsTo f s t) :
    relativeChainComplex X s R ⟶ relativeChainComplex Y t R :=
  cokernel.map (relativeInclusion X s R) (relativeInclusion Y t R)
    (((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map (relativeSubspaceMap f hf))
    (((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map f)
    (relativeInclusion_naturality R f hf)

@[reassoc (attr := simp)]
theorem relativeProjection_chainMap (f : X ⟶ Y) (hf : Set.MapsTo f s t) :
    relativeProjection X s R ≫ relativeChainMap R f hf =
      ((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map f ≫
        relativeProjection Y t R :=
  cokernel.π_desc _ _ _


@[simp]
theorem relativeChainMap_id :
    relativeChainMap R (𝟙 X) (show Set.MapsTo (𝟙 X) s s from fun _ hx ↦ hx) = 𝟙 _ := by
  have : Epi (relativeProjection X s R) := inferInstanceAs (Epi (cokernel.π _))
  apply (cancel_epi (relativeProjection X s R)).mp
  rw [relativeProjection_chainMap, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]


theorem relativeChainMap_comp (f : X ⟶ Y) (hf : Set.MapsTo f s t)
    (g : Y ⟶ Z) (hg : Set.MapsTo g t v) :
    relativeChainMap R (f ≫ g) (hg.comp hf) =
      relativeChainMap R f hf ≫ relativeChainMap R g hg := by
  have : Epi (relativeProjection X s R) := inferInstanceAs (Epi (cokernel.π _))
  apply (cancel_epi (relativeProjection X s R)).mp
  rw [relativeProjection_chainMap, Functor.map_comp]
  rw [← Category.assoc (relativeProjection X s R), relativeProjection_chainMap]
  simp only [Category.assoc]
  rw [relativeProjection_chainMap]


theorem relativeChainMap_congr {f g : X ⟶ Y} (hf : Set.MapsTo f s t)
    (hg : Set.MapsTo g s t) (h : f = g) :
    relativeChainMap R f hf = relativeChainMap R g hg := by
  cases h
  rfl


def relativeShortComplexMap (f : X ⟶ Y) (hf : Set.MapsTo f s t) :
    relativeShortComplex X s R ⟶ relativeShortComplex Y t R where
  τ₁ := ((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map (relativeSubspaceMap f hf)
  τ₂ := ((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map f
  τ₃ := relativeChainMap R f hf
  comm₁₂ := (relativeInclusion_naturality R f hf).symm
  comm₂₃ := (relativeProjection_chainMap R f hf).symm


def relativeHomologyMap (f : X ⟶ Y) (hf : Set.MapsTo f s t) (n : ℕ) :
    relativeHomology X s R n ⟶ relativeHomology Y t R n :=
  _root_.HomologicalComplex.homologyMap (relativeChainMap R f hf) n


@[simp]
theorem relativeHomologyMap_id (n : ℕ) :
    relativeHomologyMap R (𝟙 X) (show Set.MapsTo (𝟙 X) s s from fun _ hx ↦ hx) n = 𝟙 _ := by
  exact (congrArg (_root_.HomologicalComplex.homologyFunctor _ _ n).map
    (relativeChainMap_id (s := s) R)).trans (CategoryTheory.Functor.map_id _ _)


theorem relativeHomologyMap_comp (f : X ⟶ Y) (hf : Set.MapsTo f s t)
    (g : Y ⟶ Z) (hg : Set.MapsTo g t v) (n : ℕ) :
    relativeHomologyMap R (f ≫ g) (hg.comp hf) n =
      relativeHomologyMap R f hf n ≫ relativeHomologyMap R g hg n := by
  exact (congrArg (_root_.HomologicalComplex.homologyFunctor _ _ n).map
    (relativeChainMap_comp R f hf g hg)).trans (CategoryTheory.Functor.map_comp _ _ _)


@[reassoc]
theorem relativeConnecting_naturality (f : X ⟶ Y) (hf : Set.MapsTo f s t) (n : ℕ) :
    relativeConnecting X s R n ≫
        ((singularHomologyFunctor (ModuleCat.{u} k) n).obj R).map (relativeSubspaceMap f hf) =
      relativeHomologyMap R f hf (n + 1) ≫ relativeConnecting Y t R n :=
  _root_.HomologicalComplex.HomologySequence.δ_naturality (relativeShortComplexMap R f hf)
    (relativeShortExact X s R) (relativeShortExact Y t R) (n + 1) n rfl

def relativeChainIso (e : X ≃ₜ Y) (he : ∀ x, x ∈ s ↔ e x ∈ t) :
    relativeChainComplex X s R ≅ relativeChainComplex Y t R where
  hom := relativeChainMap R (TopCat.ofHom ⟨e, e.continuous⟩) (fun x hx ↦ (he x).mp hx)
  inv := relativeChainMap R (TopCat.ofHom ⟨e.symm, e.symm.continuous⟩)
    (fun y hy ↦ (he (e.symm y)).mpr (by simpa using hy))
  hom_inv_id := by
    erw [← relativeChainMap_comp]
    have hh : TopCat.ofHom (⟨e, e.continuous⟩ : C(X, Y)) ≫
        TopCat.ofHom (⟨e.symm, e.symm.continuous⟩ : C(Y, X)) = 𝟙 X := by
      ext x
      exact e.symm_apply_apply x
    exact (relativeChainMap_congr R _ (fun _ hx ↦ hx) hh).trans (relativeChainMap_id R)
  inv_hom_id := by
    erw [← relativeChainMap_comp]
    have hh : TopCat.ofHom (⟨e.symm, e.symm.continuous⟩ : C(Y, X)) ≫
        TopCat.ofHom (⟨e, e.continuous⟩ : C(X, Y)) = 𝟙 Y := by
      ext y
      exact e.apply_symm_apply y
    exact (relativeChainMap_congr R _ (fun _ hx ↦ hx) hh).trans (relativeChainMap_id R)


def relativeHomologyIso (e : X ≃ₜ Y) (he : ∀ x, x ∈ s ↔ e x ∈ t) (n : ℕ) :
    relativeHomology X s R n ≅ relativeHomology Y t R n :=
  (_root_.HomologicalComplex.homologyFunctor _ _ n).mapIso (relativeChainIso R e he)


@[simp]
theorem relativeHomologyIso_hom (e : X ≃ₜ Y) (he : ∀ x, x ∈ s ↔ e x ∈ t) (n : ℕ) :
    (relativeHomologyIso R e he n).hom = relativeHomologyMap R
      (TopCat.ofHom ⟨e, e.continuous⟩) (fun x hx ↦ (he x).mp hx) n := rfl

section Field
variable (k : Type u) [Field k]


theorem relativeEulerChar_eq_of_homeomorph (e : X ≃ₜ Y) (he : ∀ x, x ∈ s ↔ e x ∈ t) :
    relativeEulerChar X s k = relativeEulerChar Y t k := by
  apply finsum_congr
  intro n
  exact congrArg (fun d : ℕ ↦ ((ComplexShape.down ℕ).χ n : ℤ) * (d : ℤ))
    (relativeHomologyIso (ModuleCat.of k k) e he n).toLinearEquiv.finrank_eq

end Field
end DifferentialGeometry.Homology
