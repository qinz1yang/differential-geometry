/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.CategoryTheory.Groupoid.Subgroupoid
import Mathlib.Topology.Connected.PathConnected

set_option autoImplicit false

open CategoryTheory

universe u v

namespace DifferentialGeometry.Topology.VanKampen

structure RepresentativeChoice (C : Type u) [Groupoid.{v} C] (D : Set C) where
  obj : C → C
  obj_mem : ∀ x, obj x ∈ D
  hom : ∀ x, obj x ⟶ x

namespace RepresentativeChoice

variable {C : Type u} [Groupoid.{v} C] {D : Set C} (d : RepresentativeChoice C D)

noncomputable def normalizedObj (x : C) : C := by
  classical
  exact if x ∈ D then x else d.obj x

@[simp]
theorem normalizedObj_of_mem {x : C} (hx : x ∈ D) : d.normalizedObj x = x := by
  simp [normalizedObj, hx]

theorem normalizedObj_mem (x : C) : d.normalizedObj x ∈ D := by
  classical
  by_cases hx : x ∈ D
  · simp [normalizedObj, hx]
  · simp [normalizedObj, hx, d.obj_mem]

noncomputable def normalizedHom (x : C) : d.normalizedObj x ⟶ x := by
  classical
  by_cases hx : x ∈ D
  · exact eqToHom (d.normalizedObj_of_mem hx)
  · exact eqToHom (by simp [normalizedObj, hx]) ≫ d.hom x

@[simp]
theorem normalizedHom_of_mem {x : C} (hx : x ∈ D) :
    d.normalizedHom x = eqToHom (d.normalizedObj_of_mem hx) := by
  classical
  simp [normalizedHom, normalizedObj, hx]

theorem normalizedHom_conjugation_heq {x y : C} (hx : x ∈ D) (hy : y ∈ D) (f : x ⟶ y) :
    d.normalizedHom x ≫ f ≫ inv (d.normalizedHom y) ≍ f := by
  apply (CategoryTheory.conj_eqToHom_iff_heq _ f
    (d.normalizedObj_of_mem hx) (d.normalizedObj_of_mem hy)).mp
  rw [d.normalizedHom_of_mem hx, d.normalizedHom_of_mem hy]
  simp

theorem normalizedHom_heq_id_of_mem {x : C} (hx : x ∈ D) :
    d.normalizedHom x ≍ 𝟙 x := by
  rw [d.normalizedHom_of_mem hx]
  exact CategoryTheory.eqToHom_heq_id_cod _ _ _

theorem normalizedHom_heq_hom_of_not_mem {x : C} (hx : x ∉ D) :
    d.normalizedHom x ≍ d.hom x := by
  classical
  unfold normalizedHom
  simp only [hx, ↓reduceDIte]
  exact CategoryTheory.eqToHom_comp_heq _ _

end RepresentativeChoice

theorem Functor.map_heq {C : Type u} [Category.{v} C] {E : Type*} [Category E]
    (F : C ⥤ E) {x y x' y' : C} {f : x ⟶ y} {g : x' ⟶ y'}
    (hx : x = x') (hy : y = y') (h : f ≍ g) :
    F.map f ≍ F.map g := by
  subst x'
  subst y'
  exact heq_of_eq (congrArg F.map (eq_of_heq h))

theorem Groupoid.inv_heq {C : Type u} [Groupoid.{v} C]
    {x y x' y' : C} {f : x ⟶ y} {g : x' ⟶ y'}
    (hx : x = x') (hy : y = y') (h : f ≍ g) :
    Groupoid.inv f ≍ Groupoid.inv g := by
  subst x'
  subst y'
  exact heq_of_eq (congrArg Groupoid.inv (eq_of_heq h))

noncomputable def representativeRetraction {C : Type u} [Groupoid.{v} C] {D : Set C}
    (d : RepresentativeChoice C D) : C ⥤ (CategoryTheory.Subgroupoid.full D).objs where
  obj x := ⟨d.normalizedObj x, by simpa using d.normalizedObj_mem x⟩
  map {x y} g :=
    ⟨d.normalizedHom x ≫ g ≫ inv (d.normalizedHom y),
      by exact ⟨d.normalizedObj_mem x, d.normalizedObj_mem y⟩⟩
  map_id x := by
    apply Subtype.ext
    change d.normalizedHom x ≫ 𝟙 x ≫ inv (d.normalizedHom x) = 𝟙 (d.normalizedObj x)
    simp
  map_comp f g := by
    apply Subtype.ext
    change d.normalizedHom _ ≫ (f ≫ g) ≫ inv (d.normalizedHom _) =
      (d.normalizedHom _ ≫ f ≫ inv (d.normalizedHom _)) ≫
        (d.normalizedHom _ ≫ g ≫ inv (d.normalizedHom _))
    simp [Category.assoc]

theorem inclusion_comp_representativeRetraction {C : Type u} [Groupoid.{v} C] {D : Set C}
    (d : RepresentativeChoice C D) :
    CategoryTheory.Subgroupoid.hom (CategoryTheory.Subgroupoid.full D) ⋙
      representativeRetraction d = 𝟭 (CategoryTheory.Subgroupoid.full D).objs := by
  apply Functor.hext
  · rintro ⟨x, hx⟩
    have hxD : x ∈ D := (CategoryTheory.Subgroupoid.mem_full_objs_iff D).mp hx
    apply Subtype.ext
    simp [CategoryTheory.Subgroupoid.hom, representativeRetraction,
      RepresentativeChoice.normalizedObj, hxD]
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨f, hf⟩
    have hxD : x ∈ D := (CategoryTheory.Subgroupoid.mem_full_objs_iff D).mp hx
    have hyD : y ∈ D := (CategoryTheory.Subgroupoid.mem_full_objs_iff D).mp hy
    dsimp only [Functor.comp_map, CategoryTheory.Subgroupoid.hom, representativeRetraction,
      Functor.id_map]
    congr 1
    · rw [d.normalizedObj_of_mem hxD, d.normalizedObj_of_mem hyD]
    · apply Function.hfunext
      · rw [d.normalizedObj_of_mem hxD, d.normalizedObj_of_mem hyD]
      · intro g g' hgg
        apply heq_of_eq
        apply propext
        simp [hxD, hyD]
    · exact d.normalizedHom_conjugation_heq hxD hyD f
    · exact proof_irrel_heq _ _

noncomputable def representativeRetractionCompInclusionIso
    {C : Type u} [Groupoid.{v} C] {D : Set C} (d : RepresentativeChoice C D) :
    representativeRetraction d ⋙ CategoryTheory.Subgroupoid.hom
        (CategoryTheory.Subgroupoid.full D) ≅ 𝟭 C :=
  NatIso.ofComponents (fun x =>
    { hom := d.normalizedHom x
      inv := Groupoid.inv (d.normalizedHom x)
      hom_inv_id := Groupoid.comp_inv _
      inv_hom_id := Groupoid.inv_comp _ }) (by
    intro x y f
    change (d.normalizedHom x ≫ f ≫ inv (d.normalizedHom y)) ≫
      d.normalizedHom y = d.normalizedHom x ≫ f
    simp)

noncomputable def representativeInclusionEquivalence
    {C : Type u} [Groupoid.{v} C] {D : Set C} (d : RepresentativeChoice C D) :
    (CategoryTheory.Subgroupoid.full D).objs ≌ C :=
  CategoryTheory.Equivalence.mk
    (CategoryTheory.Subgroupoid.hom (CategoryTheory.Subgroupoid.full D))
    (representativeRetraction d)
    (eqToIso (inclusion_comp_representativeRetraction d).symm)
    (representativeRetractionCompInclusionIso d)

def IsRepresentative {Y : Type u} [TopologicalSpace Y] (A : Set Y) : Prop :=
  ∀ y : Y, ∃ a ∈ A, Joined a y

noncomputable def representativeChoiceOfIsRepresentative {Y : Type u} [TopologicalSpace Y]
    {A : Set Y} (hA : IsRepresentative A) :
    RepresentativeChoice (FundamentalGroupoid Y) {x : FundamentalGroupoid Y | x.as ∈ A} where
  obj x := ⟨(hA x.as).choose⟩
  obj_mem x := (hA x.as).choose_spec.1
  hom x := Path.Homotopic.Quotient.mk (hA x.as).choose_spec.2.somePath

noncomputable def fundamentalGroupoidRepresentativeRetraction {Y : Type u} [TopologicalSpace Y]
    {A : Set Y} (hA : IsRepresentative A) :
    FundamentalGroupoid Y ⥤
      (CategoryTheory.Subgroupoid.full {x : FundamentalGroupoid Y | x.as ∈ A}).objs :=
  representativeRetraction (representativeChoiceOfIsRepresentative hA)

theorem fundamentalGroupoid_inclusion_comp_retraction {Y : Type u} [TopologicalSpace Y]
    {A : Set Y} (hA : IsRepresentative A) :
    CategoryTheory.Subgroupoid.hom
        (CategoryTheory.Subgroupoid.full {x : FundamentalGroupoid Y | x.as ∈ A}) ⋙
      fundamentalGroupoidRepresentativeRetraction hA =
        𝟭 (CategoryTheory.Subgroupoid.full {x : FundamentalGroupoid Y | x.as ∈ A}).objs :=
  inclusion_comp_representativeRetraction (representativeChoiceOfIsRepresentative hA)

end DifferentialGeometry.Topology.VanKampen
