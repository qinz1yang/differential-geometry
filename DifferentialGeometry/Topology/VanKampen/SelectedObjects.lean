/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.VanKampen.FullGroupoid
import DifferentialGeometry.Topology.VanKampen.Representative
import DifferentialGeometry.Topology.VanKampen.RetractPushout

set_option autoImplicit false

open CategoryTheory Set

universe u v

namespace Poincare.Topology.VanKampen

abbrev FundamentalGroupoidOn (Y : Type u) [TopologicalSpace Y] (A : Set Y) :=
  (CategoryTheory.Subgroupoid.full {z : FundamentalGroupoid Y | z.as ∈ A}).objs

def selectedIn {X : Type u} (A B : Set X) : Set B := {x | x.1 ∈ A}

def fundamentalGroupoidMapOn {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    {A : Set Y} {B : Set Z} (f : C(Y, Z)) (hf : MapsTo f A B) :
    FundamentalGroupoidOn Y A ⥤ FundamentalGroupoidOn Z B where
  obj x := ⟨(FundamentalGroupoid.map f).obj x.1, by
    apply (CategoryTheory.Subgroupoid.mem_full_objs_iff _).2
    exact hf ((CategoryTheory.Subgroupoid.mem_full_objs_iff
      {z : FundamentalGroupoid Y | z.as ∈ A}).1 x.2)⟩
  map {x y} g := ⟨(FundamentalGroupoid.map f).map g.1, by
    apply (CategoryTheory.Subgroupoid.mem_full_iff _).2
    constructor
    · exact hf ((CategoryTheory.Subgroupoid.mem_full_objs_iff
        {z : FundamentalGroupoid Y | z.as ∈ A}).1 x.2)
    · exact hf ((CategoryTheory.Subgroupoid.mem_full_objs_iff
        {z : FundamentalGroupoid Y | z.as ∈ A}).1 y.2)⟩
  map_id x := by apply Subtype.ext; exact (FundamentalGroupoid.map f).map_id x.1
  map_comp g h := by apply Subtype.ext; exact (FundamentalGroupoid.map f).map_comp g.1 h.1

theorem fundamentalGroupoidMapOn_comp_inclusion
    {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    {A : Set Y} {B : Set Z} (f : C(Y, Z)) (hf : MapsTo f A B) :
    fundamentalGroupoidMapOn f hf ⋙
        CategoryTheory.Subgroupoid.hom
          (CategoryTheory.Subgroupoid.full {z : FundamentalGroupoid Z | z.as ∈ B}) =
      CategoryTheory.Subgroupoid.hom
          (CategoryTheory.Subgroupoid.full {z : FundamentalGroupoid Y | z.as ∈ A}) ⋙
        FundamentalGroupoid.map f := by
  apply Functor.hext
  · intro x
    rfl
  · intro x y g
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem fundamentalGroupoidMap_comp_representativeRetraction
    {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    {A : Set Y} {B : Set Z} (f : C(Y, Z)) (hf : MapsTo f A B)
    (dY : RepresentativeChoice (FundamentalGroupoid Y) {z | z.as ∈ A})
    (dZ : RepresentativeChoice (FundamentalGroupoid Z) {z | z.as ∈ B})
    (hobj : ∀ z, (FundamentalGroupoid.map f).obj (dY.normalizedObj z) =
      dZ.normalizedObj ((FundamentalGroupoid.map f).obj z))
    (hhom : ∀ z, (FundamentalGroupoid.map f).map (dY.normalizedHom z) ≍
      dZ.normalizedHom ((FundamentalGroupoid.map f).obj z)) :
    FundamentalGroupoid.map f ⋙ representativeRetraction dZ =
      representativeRetraction dY ⋙ fundamentalGroupoidMapOn f hf := by
  let J := FundamentalGroupoid.map f
  apply Functor.hext
  · intro z
    apply Subtype.ext
    exact (hobj z).symm
  · intro x y g
    have hxObj := hobj x
    have hyObj := hobj y
    have hxHom := hhom x
    have hyHom := hhom y
    have hyInv : J.map (inv (dY.normalizedHom y)) ≍
        inv (dZ.normalizedHom (J.obj y)) := by
      have hmapInv : J.map (inv (dY.normalizedHom y)) =
          inv (J.map (dY.normalizedHom y)) := by simp
      exact (heq_of_eq hmapInv).trans
        (by simpa only [Groupoid.inv_eq_inv] using
          Groupoid.inv_heq hyObj rfl hyHom)
    have hfirst : J.map (dY.normalizedHom x) ≫ J.map g ≍
        dZ.normalizedHom (J.obj x) ≫ J.map g :=
      CategoryTheory.heq_comp hxObj rfl rfl hxHom HEq.rfl
    have htotal : J.map (dY.normalizedHom x ≫ g ≫ inv (dY.normalizedHom y)) ≍
        dZ.normalizedHom (J.obj x) ≫ J.map g ≫
          inv (dZ.normalizedHom (J.obj y)) := by
      have hcomp := CategoryTheory.heq_comp hxObj rfl hyObj hfirst hyInv
      exact (heq_of_eq (by simp :
        J.map (dY.normalizedHom x ≫ g ≫ inv (dY.normalizedHom y)) =
          (J.map (dY.normalizedHom x) ≫ J.map g) ≫
            J.map (inv (dY.normalizedHom y)))).trans
        (hcomp.trans (heq_of_eq (Category.assoc _ _ _)))
    dsimp only [Functor.comp_map, representativeRetraction, fundamentalGroupoidMapOn]
    congr 1
    · exact congrArg₂ (fun a b : FundamentalGroupoid Z => a ⟶ b)
        hxObj.symm hyObj.symm
    · apply Function.hfunext
      · exact congrArg₂ (fun a b : FundamentalGroupoid Z => a ⟶ b)
          hxObj.symm hyObj.symm
      · intro q q' hq
        apply heq_of_eq
        apply propext
        simp only [CategoryTheory.Subgroupoid.mem_full_iff]
        exact iff_of_true
          ⟨dZ.normalizedObj_mem (J.obj x), dZ.normalizedObj_mem (J.obj y)⟩
          ⟨hf (dY.normalizedObj_mem x), hf (dY.normalizedObj_mem y)⟩
    · exact htotal.symm
    · exact proof_irrel_heq _ _

noncomputable def fundamentalGroupoidOnInclusionEquivalence
    {Y : Type u} [TopologicalSpace Y] {A : Set Y} (hA : IsRepresentative A) :
    FundamentalGroupoidOn Y A ≌ FundamentalGroupoid Y :=
  representativeInclusionEquivalence (representativeChoiceOfIsRepresentative hA)

def selectedInterToLeft {X : Type u} [TopologicalSpace X]
    (A U V : Set X) :
    FundamentalGroupoidOn (↑(U ∩ V)) (selectedIn A (U ∩ V)) ⥤
      FundamentalGroupoidOn U (selectedIn A U) :=
  fundamentalGroupoidMapOn (interToLeft U V) (fun _ hx => hx)

def selectedInterToRight {X : Type u} [TopologicalSpace X]
    (A U V : Set X) :
    FundamentalGroupoidOn (↑(U ∩ V)) (selectedIn A (U ∩ V)) ⥤
      FundamentalGroupoidOn V (selectedIn A V) :=
  fundamentalGroupoidMapOn (interToRight U V) (fun _ hx => hx)

def selectedLeftToAmbient {X : Type u} [TopologicalSpace X]
    (A U : Set X) : FundamentalGroupoidOn U (selectedIn A U) ⥤
      FundamentalGroupoidOn X A :=
  fundamentalGroupoidMapOn (subsetToAmbient U) (fun _ hx => hx)

def selectedRightToAmbient {X : Type u} [TopologicalSpace X]
    (A V : Set X) : FundamentalGroupoidOn V (selectedIn A V) ⥤
      FundamentalGroupoidOn X A :=
  fundamentalGroupoidMapOn (subsetToAmbient V) (fun _ hx => hx)

theorem selectedGroupoid_coverSquare_commutes
    {X : Type u} [TopologicalSpace X] (A U V : Set X) :
    selectedInterToLeft A U V ⋙ selectedLeftToAmbient A U =
      selectedInterToRight A U V ⋙ selectedRightToAmbient A V := by
  apply Functor.hext
  · intro z
    rfl
  · intro x y g
    apply heq_of_eq
    apply Subtype.ext
    change ((FundamentalGroupoid.map (interToLeft U V) ⋙
        FundamentalGroupoid.map (subsetToAmbient U)).map g.1) =
      ((FundamentalGroupoid.map (interToRight U V) ⋙
        FundamentalGroupoid.map (subsetToAmbient V)).map g.1)
    exact eq_of_heq
      (Functor.hcongr_hom (fundamentalGroupoid_coverSquare_commutes U V) g.1)

def selectedGroupoidSquareIsPushoutStatement
    {X : Type u} [TopologicalSpace X] (A U V : Set X) : Prop :=
  @IsPushout Grpd.{u, u} _
    (Grpd.of (FundamentalGroupoidOn (↑(U ∩ V)) (selectedIn A (U ∩ V))))
    (Grpd.of (FundamentalGroupoidOn U (selectedIn A U)))
    (Grpd.of (FundamentalGroupoidOn V (selectedIn A V)))
    (Grpd.of (FundamentalGroupoidOn X A))
    (selectedInterToLeft A U V)
    (selectedInterToRight A U V)
    (selectedLeftToAmbient A U)
    (selectedRightToAmbient A V)

theorem isRepresentative_of_cover {X : Type u} [TopologicalSpace X]
    {A U V : Set X} (hcover : U ∪ V = univ)
    (hAU : IsRepresentative (selectedIn A U))
    (hAV : IsRepresentative (selectedIn A V)) : IsRepresentative A := by
  intro x
  have hx : x ∈ U ∪ V := by rw [hcover]; trivial
  rcases hx with hxU | hxV
  · obtain ⟨a, haA, hax⟩ := hAU ⟨x, hxU⟩
    exact ⟨a.1, haA, hax.map continuous_subtype_val⟩
  · obtain ⟨a, haA, hax⟩ := hAV ⟨x, hxV⟩
    exact ⟨a.1, haA, hax.map continuous_subtype_val⟩

noncomputable def leftRepresentativeChoice {X : Type u} [TopologicalSpace X]
    (A U V : Set X) (hAU : IsRepresentative (selectedIn A U))
    (dW : RepresentativeChoice (FundamentalGroupoid (↑(U ∩ V)))
      {z | z.as ∈ selectedIn A (U ∩ V)}) :
    RepresentativeChoice (FundamentalGroupoid U) {z | z.as ∈ selectedIn A U} := by
  classical
  exact {
  obj z := if hzV : z.as.1 ∈ V then
      (FundamentalGroupoid.map (interToLeft U V)).obj
        (dW.obj ⟨⟨z.as.1, z.as.2, hzV⟩⟩)
    else
      (representativeChoiceOfIsRepresentative hAU).obj z
  obj_mem z := by
    classical
    by_cases hzV : z.as.1 ∈ V
    · simp only [hzV]
      change (dW.obj ⟨⟨z.as.1, z.as.2, hzV⟩⟩).as.1 ∈ A
      exact dW.obj_mem ⟨⟨z.as.1, z.as.2, hzV⟩⟩
    · simpa [hzV] using (representativeChoiceOfIsRepresentative hAU).obj_mem z
  hom z := by
    by_cases hzV : z.as.1 ∈ V
    · exact eqToHom (by simp [hzV]) ≫
        (FundamentalGroupoid.map (interToLeft U V)).map
          (dW.hom ⟨⟨z.as.1, z.as.2, hzV⟩⟩) ≫
        eqToHom (by apply FundamentalGroupoid.ext; rfl)
    · exact eqToHom (by simp [hzV]) ≫
        (representativeChoiceOfIsRepresentative hAU).hom z }

noncomputable def rightRepresentativeChoice {X : Type u} [TopologicalSpace X]
    (A U V : Set X) (hAV : IsRepresentative (selectedIn A V))
    (dW : RepresentativeChoice (FundamentalGroupoid (↑(U ∩ V)))
      {z | z.as ∈ selectedIn A (U ∩ V)}) :
    RepresentativeChoice (FundamentalGroupoid V) {z | z.as ∈ selectedIn A V} := by
  classical
  exact {
  obj z := if hzU : z.as.1 ∈ U then
      (FundamentalGroupoid.map (interToRight U V)).obj
        (dW.obj ⟨⟨z.as.1, hzU, z.as.2⟩⟩)
    else
      (representativeChoiceOfIsRepresentative hAV).obj z
  obj_mem z := by
    classical
    by_cases hzU : z.as.1 ∈ U
    · simp only [hzU]
      change (dW.obj ⟨⟨z.as.1, hzU, z.as.2⟩⟩).as.1 ∈ A
      exact dW.obj_mem ⟨⟨z.as.1, hzU, z.as.2⟩⟩
    · simpa [hzU] using (representativeChoiceOfIsRepresentative hAV).obj_mem z
  hom z := by
    by_cases hzU : z.as.1 ∈ U
    · exact eqToHom (by simp [hzU]) ≫
        (FundamentalGroupoid.map (interToRight U V)).map
          (dW.hom ⟨⟨z.as.1, hzU, z.as.2⟩⟩) ≫
        eqToHom (by apply FundamentalGroupoid.ext; rfl)
    · exact eqToHom (by simp [hzU]) ≫
        (representativeChoiceOfIsRepresentative hAV).hom z }

noncomputable def ambientRepresentativeChoice {X : Type u} [TopologicalSpace X]
    (A U V : Set X) (hcover : U ∪ V = univ)
    (dU : RepresentativeChoice (FundamentalGroupoid U) {z | z.as ∈ selectedIn A U})
    (dV : RepresentativeChoice (FundamentalGroupoid V) {z | z.as ∈ selectedIn A V}) :
    RepresentativeChoice (FundamentalGroupoid X) {z | z.as ∈ A} := by
  classical
  exact {
  obj z := if hzU : z.as ∈ U then
      (FundamentalGroupoid.map (subsetToAmbient U)).obj (dU.obj ⟨⟨z.as, hzU⟩⟩)
    else
      (FundamentalGroupoid.map (subsetToAmbient V)).obj
        (dV.obj ⟨⟨z.as, by
          have hz : z.as ∈ U ∪ V := by rw [hcover]; trivial
          exact hz.resolve_left hzU⟩⟩)
  obj_mem z := by
    classical
    by_cases hzU : z.as ∈ U
    · simp only [hzU]
      change (dU.obj ⟨⟨z.as, hzU⟩⟩).as.1 ∈ A
      exact dU.obj_mem ⟨⟨z.as, hzU⟩⟩
    · simp only [hzU]
      change (dV.obj ⟨⟨z.as, by
        have hz : z.as ∈ U ∪ V := by rw [hcover]; trivial
        exact hz.resolve_left hzU⟩⟩).as.1 ∈ A
      exact dV.obj_mem ⟨⟨z.as, by
        have hz : z.as ∈ U ∪ V := by rw [hcover]; trivial
        exact hz.resolve_left hzU⟩⟩
  hom z := by
    by_cases hzU : z.as ∈ U
    · exact eqToHom (by simp [hzU]) ≫
        (FundamentalGroupoid.map (subsetToAmbient U)).map (dU.hom ⟨⟨z.as, hzU⟩⟩) ≫
        eqToHom (by apply FundamentalGroupoid.ext; rfl)
    · exact eqToHom (by simp [hzU]) ≫
        (FundamentalGroupoid.map (subsetToAmbient V)).map (dV.hom ⟨⟨z.as, by
          have hz : z.as ∈ U ∪ V := by rw [hcover]; trivial
          exact hz.resolve_left hzU⟩⟩) ≫
        eqToHom (by apply FundamentalGroupoid.ext; rfl) }

set_option backward.isDefEq.respectTransparency false in
theorem interToLeft_map_normalizedObj_eq
    {X : Type u} [TopologicalSpace X] (A U V : Set X)
    (hAU : IsRepresentative (selectedIn A U))
    (dW : RepresentativeChoice (FundamentalGroupoid (↑(U ∩ V)))
      {z | z.as ∈ selectedIn A (U ∩ V)})
    (z : FundamentalGroupoid (↑(U ∩ V))) :
    (FundamentalGroupoid.map (interToLeft U V)).obj (dW.normalizedObj z) =
      (leftRepresentativeChoice A U V hAU dW).normalizedObj
        ((FundamentalGroupoid.map (interToLeft U V)).obj z) := by
  classical
  let J := FundamentalGroupoid.map (interToLeft U V)
  let dU := leftRepresentativeChoice A U V hAU dW
  have hzV : (J.obj z).as.1 ∈ V := z.as.2.2
  have hzV' : ((interToLeft U V) z.as).1 ∈ V := z.as.2.2
  have hzw : (⟨⟨(J.obj z).as.1, (J.obj z).as.2, hzV⟩⟩ :
      FundamentalGroupoid (↑(U ∩ V))) = z := by
    apply FundamentalGroupoid.ext
    apply Subtype.ext
    rfl
  have hzw' : (⟨⟨((interToLeft U V) z.as).1,
      ((interToLeft U V) z.as).2, hzV'⟩⟩ :
      FundamentalGroupoid (↑(U ∩ V))) = z := by
    apply FundamentalGroupoid.ext
    apply Subtype.ext
    rfl
  by_cases hzA : z.as.1 ∈ A
  · have hzW : z ∈ {q | q.as ∈ selectedIn A (U ∩ V)} := hzA
    have hzU : J.obj z ∈ {q | q.as ∈ selectedIn A U} := hzA
    rw [dW.normalizedObj_of_mem hzW, dU.normalizedObj_of_mem hzU]
  · have hzW : z ∉ {q | q.as ∈ selectedIn A (U ∩ V)} := hzA
    have hzU : J.obj z ∉ {q | q.as ∈ selectedIn A U} := hzA
    unfold RepresentativeChoice.normalizedObj
    rw [if_neg hzW, if_neg hzU]
    change J.obj (dW.obj z) = dU.obj (J.obj z)
    simp [dU, leftRepresentativeChoice, J, hzV', hzw']

set_option backward.isDefEq.respectTransparency false in
theorem interToLeft_map_normalizedHom_heq
    {X : Type u} [TopologicalSpace X] (A U V : Set X)
    (hAU : IsRepresentative (selectedIn A U))
    (dW : RepresentativeChoice (FundamentalGroupoid (↑(U ∩ V)))
      {z | z.as ∈ selectedIn A (U ∩ V)})
    (z : FundamentalGroupoid (↑(U ∩ V))) :
    (FundamentalGroupoid.map (interToLeft U V)).map (dW.normalizedHom z) ≍
      (leftRepresentativeChoice A U V hAU dW).normalizedHom
        ((FundamentalGroupoid.map (interToLeft U V)).obj z) := by
  classical
  let J := FundamentalGroupoid.map (interToLeft U V)
  let dU := leftRepresentativeChoice A U V hAU dW
  have hzV : (J.obj z).as.1 ∈ V := z.as.2.2
  have hzV' : ((interToLeft U V) z.as).1 ∈ V := z.as.2.2
  have hzw : (⟨⟨(J.obj z).as.1, (J.obj z).as.2, hzV⟩⟩ :
      FundamentalGroupoid (↑(U ∩ V))) = z := by
    apply FundamentalGroupoid.ext
    apply Subtype.ext
    rfl
  by_cases hzA : z.as.1 ∈ A
  · have hzW : z ∈ {q | q.as ∈ selectedIn A (U ∩ V)} := hzA
    have hzU : J.obj z ∈ {q | q.as ∈ selectedIn A U} := hzA
    have hmap := Functor.map_heq J (dW.normalizedObj_of_mem hzW) rfl
      (dW.normalizedHom_heq_id_of_mem hzW)
    exact hmap.trans ((heq_of_eq (J.map_id z)).trans
      (dU.normalizedHom_heq_id_of_mem hzU).symm)
  · have hzW : z ∉ {q | q.as ∈ selectedIn A (U ∩ V)} := hzA
    have hzU : J.obj z ∉ {q | q.as ∈ selectedIn A U} := hzA
    have hmap := Functor.map_heq J
      (by simp [RepresentativeChoice.normalizedObj, hzW]) rfl
      (dW.normalizedHom_heq_hom_of_not_mem hzW)
    have hraw : dU.hom (J.obj z) ≍ J.map (dW.hom z) := by
      have hhom : dW.hom
          (⟨⟨(J.obj z).as.1, (J.obj z).as.2, hzV⟩⟩ :
            FundamentalGroupoid (↑(U ∩ V))) ≍ dW.hom z := by
        cases hzw
        rfl
      have hmapraw := Functor.map_heq J (congrArg dW.obj hzw) hzw hhom
      simpa [dU, leftRepresentativeChoice, J, hzV'] using hmapraw
    exact hmap.trans (hraw.symm.trans
      (dU.normalizedHom_heq_hom_of_not_mem hzU).symm)

set_option backward.isDefEq.respectTransparency false in
theorem interToLeft_comp_representativeRetraction
    {X : Type u} [TopologicalSpace X] (A U V : Set X)
    (hAU : IsRepresentative (selectedIn A U))
    (dW : RepresentativeChoice (FundamentalGroupoid (↑(U ∩ V)))
      {z | z.as ∈ selectedIn A (U ∩ V)}) :
    FundamentalGroupoid.map (interToLeft U V) ⋙
        representativeRetraction (leftRepresentativeChoice A U V hAU dW) =
      representativeRetraction dW ⋙ selectedInterToLeft A U V := by
  apply fundamentalGroupoidMap_comp_representativeRetraction
  · exact interToLeft_map_normalizedObj_eq A U V hAU dW
  · exact interToLeft_map_normalizedHom_heq A U V hAU dW

set_option backward.isDefEq.respectTransparency false in
theorem interToRight_map_normalizedObj_eq
    {X : Type u} [TopologicalSpace X] (A U V : Set X)
    (hAV : IsRepresentative (selectedIn A V))
    (dW : RepresentativeChoice (FundamentalGroupoid (↑(U ∩ V)))
      {z | z.as ∈ selectedIn A (U ∩ V)})
    (z : FundamentalGroupoid (↑(U ∩ V))) :
    (FundamentalGroupoid.map (interToRight U V)).obj (dW.normalizedObj z) =
      (rightRepresentativeChoice A U V hAV dW).normalizedObj
        ((FundamentalGroupoid.map (interToRight U V)).obj z) := by
  classical
  let J := FundamentalGroupoid.map (interToRight U V)
  let dV := rightRepresentativeChoice A U V hAV dW
  have hzU : (J.obj z).as.1 ∈ U := z.as.2.1
  have hzU' : ((interToRight U V) z.as).1 ∈ U := z.as.2.1
  have hzw : (⟨⟨(J.obj z).as.1, hzU, (J.obj z).as.2⟩⟩ :
      FundamentalGroupoid (↑(U ∩ V))) = z := by
    apply FundamentalGroupoid.ext
    apply Subtype.ext
    rfl
  have hzw' : (⟨⟨((interToRight U V) z.as).1, hzU',
      ((interToRight U V) z.as).2⟩⟩ :
      FundamentalGroupoid (↑(U ∩ V))) = z := by
    apply FundamentalGroupoid.ext
    apply Subtype.ext
    rfl
  by_cases hzA : z.as.1 ∈ A
  · have hzW : z ∈ {q | q.as ∈ selectedIn A (U ∩ V)} := hzA
    have hzV : J.obj z ∈ {q | q.as ∈ selectedIn A V} := hzA
    rw [dW.normalizedObj_of_mem hzW, dV.normalizedObj_of_mem hzV]
  · have hzW : z ∉ {q | q.as ∈ selectedIn A (U ∩ V)} := hzA
    have hzV : J.obj z ∉ {q | q.as ∈ selectedIn A V} := hzA
    unfold RepresentativeChoice.normalizedObj
    rw [if_neg hzW, if_neg hzV]
    change J.obj (dW.obj z) = dV.obj (J.obj z)
    simp [dV, rightRepresentativeChoice, J, hzU', hzw']

set_option backward.isDefEq.respectTransparency false in
theorem interToRight_map_normalizedHom_heq
    {X : Type u} [TopologicalSpace X] (A U V : Set X)
    (hAV : IsRepresentative (selectedIn A V))
    (dW : RepresentativeChoice (FundamentalGroupoid (↑(U ∩ V)))
      {z | z.as ∈ selectedIn A (U ∩ V)})
    (z : FundamentalGroupoid (↑(U ∩ V))) :
    (FundamentalGroupoid.map (interToRight U V)).map (dW.normalizedHom z) ≍
      (rightRepresentativeChoice A U V hAV dW).normalizedHom
        ((FundamentalGroupoid.map (interToRight U V)).obj z) := by
  classical
  let J := FundamentalGroupoid.map (interToRight U V)
  let dV := rightRepresentativeChoice A U V hAV dW
  have hzU : (J.obj z).as.1 ∈ U := z.as.2.1
  have hzU' : ((interToRight U V) z.as).1 ∈ U := z.as.2.1
  have hzw : (⟨⟨(J.obj z).as.1, hzU, (J.obj z).as.2⟩⟩ :
      FundamentalGroupoid (↑(U ∩ V))) = z := by
    apply FundamentalGroupoid.ext
    apply Subtype.ext
    rfl
  by_cases hzA : z.as.1 ∈ A
  · have hzW : z ∈ {q | q.as ∈ selectedIn A (U ∩ V)} := hzA
    have hzV : J.obj z ∈ {q | q.as ∈ selectedIn A V} := hzA
    have hmap := Functor.map_heq J (dW.normalizedObj_of_mem hzW) rfl
      (dW.normalizedHom_heq_id_of_mem hzW)
    exact hmap.trans ((heq_of_eq (J.map_id z)).trans
      (dV.normalizedHom_heq_id_of_mem hzV).symm)
  · have hzW : z ∉ {q | q.as ∈ selectedIn A (U ∩ V)} := hzA
    have hzV : J.obj z ∉ {q | q.as ∈ selectedIn A V} := hzA
    have hmap := Functor.map_heq J
      (by simp [RepresentativeChoice.normalizedObj, hzW]) rfl
      (dW.normalizedHom_heq_hom_of_not_mem hzW)
    have hraw : dV.hom (J.obj z) ≍ J.map (dW.hom z) := by
      have hhom : dW.hom
          (⟨⟨(J.obj z).as.1, hzU, (J.obj z).as.2⟩⟩ :
            FundamentalGroupoid (↑(U ∩ V))) ≍ dW.hom z := by
        cases hzw
        rfl
      have hmapraw := Functor.map_heq J (congrArg dW.obj hzw) hzw hhom
      simpa [dV, rightRepresentativeChoice, J, hzU'] using hmapraw
    exact hmap.trans (hraw.symm.trans
      (dV.normalizedHom_heq_hom_of_not_mem hzV).symm)

theorem interToRight_comp_representativeRetraction
    {X : Type u} [TopologicalSpace X] (A U V : Set X)
    (hAV : IsRepresentative (selectedIn A V))
    (dW : RepresentativeChoice (FundamentalGroupoid (↑(U ∩ V)))
      {z | z.as ∈ selectedIn A (U ∩ V)}) :
    FundamentalGroupoid.map (interToRight U V) ⋙
        representativeRetraction (rightRepresentativeChoice A U V hAV dW) =
      representativeRetraction dW ⋙ selectedInterToRight A U V := by
  apply fundamentalGroupoidMap_comp_representativeRetraction
  · exact interToRight_map_normalizedObj_eq A U V hAV dW
  · exact interToRight_map_normalizedHom_heq A U V hAV dW

set_option backward.isDefEq.respectTransparency false in
theorem leftToAmbient_map_normalizedObj_eq
    {X : Type u} [TopologicalSpace X] (A U V : Set X) (hcover : U ∪ V = univ)
    (dU : RepresentativeChoice (FundamentalGroupoid U) {z | z.as ∈ selectedIn A U})
    (dV : RepresentativeChoice (FundamentalGroupoid V) {z | z.as ∈ selectedIn A V})
    (z : FundamentalGroupoid U) :
    (FundamentalGroupoid.map (subsetToAmbient U)).obj (dU.normalizedObj z) =
      (ambientRepresentativeChoice A U V hcover dU dV).normalizedObj
        ((FundamentalGroupoid.map (subsetToAmbient U)).obj z) := by
  classical
  let J := FundamentalGroupoid.map (subsetToAmbient U)
  let dX := ambientRepresentativeChoice A U V hcover dU dV
  have hzU : (J.obj z).as ∈ U := z.as.2
  have hzU' : (subsetToAmbient U z.as) ∈ U := z.as.2
  have hzu : (⟨⟨(J.obj z).as, hzU⟩⟩ : FundamentalGroupoid U) = z := by
    apply FundamentalGroupoid.ext
    apply Subtype.ext
    rfl
  have hzu' : (⟨⟨subsetToAmbient U z.as, hzU'⟩⟩ : FundamentalGroupoid U) = z := by
    apply FundamentalGroupoid.ext
    apply Subtype.ext
    rfl
  by_cases hzA : z.as.1 ∈ A
  · have hzSelU : z ∈ {q | q.as ∈ selectedIn A U} := hzA
    have hzSelX : J.obj z ∈ {q | q.as ∈ A} := hzA
    rw [dU.normalizedObj_of_mem hzSelU, dX.normalizedObj_of_mem hzSelX]
  · have hzSelU : z ∉ {q | q.as ∈ selectedIn A U} := hzA
    have hzSelX : J.obj z ∉ {q | q.as ∈ A} := hzA
    unfold RepresentativeChoice.normalizedObj
    rw [if_neg hzSelU, if_neg hzSelX]
    change J.obj (dU.obj z) = dX.obj (J.obj z)
    simp [dX, ambientRepresentativeChoice, J, hzU', hzu']

set_option backward.isDefEq.respectTransparency false in
theorem leftToAmbient_map_normalizedHom_heq
    {X : Type u} [TopologicalSpace X] (A U V : Set X) (hcover : U ∪ V = univ)
    (dU : RepresentativeChoice (FundamentalGroupoid U) {z | z.as ∈ selectedIn A U})
    (dV : RepresentativeChoice (FundamentalGroupoid V) {z | z.as ∈ selectedIn A V})
    (z : FundamentalGroupoid U) :
    (FundamentalGroupoid.map (subsetToAmbient U)).map (dU.normalizedHom z) ≍
      (ambientRepresentativeChoice A U V hcover dU dV).normalizedHom
        ((FundamentalGroupoid.map (subsetToAmbient U)).obj z) := by
  classical
  let J := FundamentalGroupoid.map (subsetToAmbient U)
  let dX := ambientRepresentativeChoice A U V hcover dU dV
  have hzU : (J.obj z).as ∈ U := z.as.2
  have hzU' : (subsetToAmbient U z.as) ∈ U := z.as.2
  have hzu : (⟨⟨(J.obj z).as, hzU⟩⟩ : FundamentalGroupoid U) = z := by
    apply FundamentalGroupoid.ext
    apply Subtype.ext
    rfl
  by_cases hzA : z.as.1 ∈ A
  · have hzSelU : z ∈ {q | q.as ∈ selectedIn A U} := hzA
    have hzSelX : J.obj z ∈ {q | q.as ∈ A} := hzA
    have hmap := Functor.map_heq J (dU.normalizedObj_of_mem hzSelU) rfl
      (dU.normalizedHom_heq_id_of_mem hzSelU)
    exact hmap.trans ((heq_of_eq (J.map_id z)).trans
      (dX.normalizedHom_heq_id_of_mem hzSelX).symm)
  · have hzSelU : z ∉ {q | q.as ∈ selectedIn A U} := hzA
    have hzSelX : J.obj z ∉ {q | q.as ∈ A} := hzA
    have hmap := Functor.map_heq J
      (by simp [RepresentativeChoice.normalizedObj, hzSelU]) rfl
      (dU.normalizedHom_heq_hom_of_not_mem hzSelU)
    have hraw : dX.hom (J.obj z) ≍ J.map (dU.hom z) := by
      have hhom : dU.hom (⟨⟨(J.obj z).as, hzU⟩⟩ : FundamentalGroupoid U) ≍
          dU.hom z := by
        cases hzu
        rfl
      have hmapraw := Functor.map_heq J (congrArg dU.obj hzu) hzu hhom
      simpa [dX, ambientRepresentativeChoice, J, hzU'] using hmapraw
    exact hmap.trans (hraw.symm.trans
      (dX.normalizedHom_heq_hom_of_not_mem hzSelX).symm)

theorem leftToAmbient_comp_representativeRetraction
    {X : Type u} [TopologicalSpace X] (A U V : Set X) (hcover : U ∪ V = univ)
    (dU : RepresentativeChoice (FundamentalGroupoid U) {z | z.as ∈ selectedIn A U})
    (dV : RepresentativeChoice (FundamentalGroupoid V) {z | z.as ∈ selectedIn A V}) :
    FundamentalGroupoid.map (subsetToAmbient U) ⋙
        representativeRetraction (ambientRepresentativeChoice A U V hcover dU dV) =
      representativeRetraction dU ⋙ selectedLeftToAmbient A U := by
  apply fundamentalGroupoidMap_comp_representativeRetraction
  · exact leftToAmbient_map_normalizedObj_eq A U V hcover dU dV
  · exact leftToAmbient_map_normalizedHom_heq A U V hcover dU dV

set_option backward.isDefEq.respectTransparency false in
theorem rightToAmbient_map_normalizedObj_eq
    {X : Type u} [TopologicalSpace X] (A U V : Set X) (hcover : U ∪ V = univ)
    (hAU : IsRepresentative (selectedIn A U))
    (hAV : IsRepresentative (selectedIn A V))
    (dW : RepresentativeChoice (FundamentalGroupoid (↑(U ∩ V)))
      {z | z.as ∈ selectedIn A (U ∩ V)})
    (z : FundamentalGroupoid V) :
    let dU := leftRepresentativeChoice A U V hAU dW
    let dV := rightRepresentativeChoice A U V hAV dW
    (FundamentalGroupoid.map (subsetToAmbient V)).obj (dV.normalizedObj z) =
      (ambientRepresentativeChoice A U V hcover dU dV).normalizedObj
        ((FundamentalGroupoid.map (subsetToAmbient V)).obj z) := by
  classical
  dsimp only
  let KWU := FundamentalGroupoid.map (interToLeft U V)
  let KWV := FundamentalGroupoid.map (interToRight U V)
  let JU := FundamentalGroupoid.map (subsetToAmbient U)
  let JV := FundamentalGroupoid.map (subsetToAmbient V)
  let dU := leftRepresentativeChoice A U V hAU dW
  let dV := rightRepresentativeChoice A U V hAV dW
  let dX := ambientRepresentativeChoice A U V hcover dU dV
  by_cases hzU : z.as.1 ∈ U
  · let w : FundamentalGroupoid (↑(U ∩ V)) := ⟨⟨z.as.1, hzU, z.as.2⟩⟩
    have hVz : KWV.obj w = z := by
      apply FundamentalGroupoid.ext
      apply Subtype.ext
      rfl
    have hSquare (q : FundamentalGroupoid (↑(U ∩ V))) :
        JU.obj (KWU.obj q) = JV.obj (KWV.obj q) :=
      Functor.congr_obj (fundamentalGroupoid_coverSquare_commutes U V) q
    calc
      JV.obj (dV.normalizedObj z) = JV.obj (dV.normalizedObj (KWV.obj w)) :=
        congrArg (fun q => JV.obj (dV.normalizedObj q)) hVz.symm
      _ = JV.obj (KWV.obj (dW.normalizedObj w)) :=
        congrArg JV.obj (interToRight_map_normalizedObj_eq A U V hAV dW w).symm
      _ = JU.obj (KWU.obj (dW.normalizedObj w)) := (hSquare _).symm
      _ = JU.obj (dU.normalizedObj (KWU.obj w)) :=
        congrArg JU.obj (interToLeft_map_normalizedObj_eq A U V hAU dW w)
      _ = dX.normalizedObj (JU.obj (KWU.obj w)) :=
        leftToAmbient_map_normalizedObj_eq A U V hcover dU dV (KWU.obj w)
      _ = dX.normalizedObj (JV.obj z) :=
        congrArg dX.normalizedObj ((hSquare w).trans (congrArg JV.obj hVz))
  · have hzU' : (JV.obj z).as ∉ U := hzU
    have hzU'' : subsetToAmbient V z.as ∉ U := hzU
    have hzV : (JV.obj z).as ∈ V := z.as.2
    have hzV' : subsetToAmbient V z.as ∈ V := z.as.2
    have hzv : (⟨⟨(JV.obj z).as, hzV⟩⟩ : FundamentalGroupoid V) = z := by
      apply FundamentalGroupoid.ext
      apply Subtype.ext
      rfl
    have hzv' : (⟨⟨subsetToAmbient V z.as, hzV'⟩⟩ : FundamentalGroupoid V) = z := by
      apply FundamentalGroupoid.ext
      apply Subtype.ext
      rfl
    by_cases hzA : z.as.1 ∈ A
    · have hzSelV : z ∈ {q | q.as ∈ selectedIn A V} := hzA
      have hzSelX : JV.obj z ∈ {q | q.as ∈ A} := hzA
      rw [dV.normalizedObj_of_mem hzSelV, dX.normalizedObj_of_mem hzSelX]
    · have hzSelV : z ∉ {q | q.as ∈ selectedIn A V} := hzA
      have hzSelX : JV.obj z ∉ {q | q.as ∈ A} := hzA
      unfold RepresentativeChoice.normalizedObj
      rw [if_neg hzSelV, if_neg hzSelX]
      change JV.obj (dV.obj z) = dX.obj (JV.obj z)
      simp [dX, ambientRepresentativeChoice, JV, hzU'', hzv']

set_option backward.isDefEq.respectTransparency false in
theorem rightToAmbient_map_normalizedHom_heq
    {X : Type u} [TopologicalSpace X] (A U V : Set X) (hcover : U ∪ V = univ)
    (hAU : IsRepresentative (selectedIn A U))
    (hAV : IsRepresentative (selectedIn A V))
    (dW : RepresentativeChoice (FundamentalGroupoid (↑(U ∩ V)))
      {z | z.as ∈ selectedIn A (U ∩ V)})
    (z : FundamentalGroupoid V) :
    let dU := leftRepresentativeChoice A U V hAU dW
    let dV := rightRepresentativeChoice A U V hAV dW
    (FundamentalGroupoid.map (subsetToAmbient V)).map (dV.normalizedHom z) ≍
      (ambientRepresentativeChoice A U V hcover dU dV).normalizedHom
        ((FundamentalGroupoid.map (subsetToAmbient V)).obj z) := by
  classical
  dsimp only
  let KWU := FundamentalGroupoid.map (interToLeft U V)
  let KWV := FundamentalGroupoid.map (interToRight U V)
  let JU := FundamentalGroupoid.map (subsetToAmbient U)
  let JV := FundamentalGroupoid.map (subsetToAmbient V)
  let dU := leftRepresentativeChoice A U V hAU dW
  let dV := rightRepresentativeChoice A U V hAV dW
  let dX := ambientRepresentativeChoice A U V hcover dU dV
  by_cases hzU : z.as.1 ∈ U
  · let w : FundamentalGroupoid (↑(U ∩ V)) := ⟨⟨z.as.1, hzU, z.as.2⟩⟩
    have hVz : KWV.obj w = z := by
      apply FundamentalGroupoid.ext
      apply Subtype.ext
      rfl
    have hSquareObj (q : FundamentalGroupoid (↑(U ∩ V))) :
        JU.obj (KWU.obj q) = JV.obj (KWV.obj q) :=
      Functor.congr_obj (fundamentalGroupoid_coverSquare_commutes U V) q
    have hStart : JV.map (dV.normalizedHom z) ≍
        JV.map (dV.normalizedHom (KWV.obj w)) := by
      have htransport : dV.normalizedHom z ≍ dV.normalizedHom (KWV.obj w) := by
        cases hVz
        rfl
      exact Functor.map_heq JV
        (congrArg dV.normalizedObj hVz.symm) hVz.symm htransport
    have hRight := interToRight_map_normalizedHom_heq A U V hAV dW w
    have hThroughRight : JV.map (dV.normalizedHom (KWV.obj w)) ≍
        JV.map (KWV.map (dW.normalizedHom w)) := by
      exact Functor.map_heq JV
        (interToRight_map_normalizedObj_eq A U V hAV dW w).symm rfl hRight.symm
    have hSquare := Functor.hcongr_hom
      (fundamentalGroupoid_coverSquare_commutes U V) (dW.normalizedHom w)
    have hThroughLeft : JU.map (KWU.map (dW.normalizedHom w)) ≍
        JU.map (dU.normalizedHom (KWU.obj w)) := by
      exact Functor.map_heq JU
        (interToLeft_map_normalizedObj_eq A U V hAU dW w) rfl
        (interToLeft_map_normalizedHom_heq A U V hAU dW w)
    have hAmbient := leftToAmbient_map_normalizedHom_heq
      A U V hcover dU dV (KWU.obj w)
    have hEndpoint : JU.obj (KWU.obj w) = JV.obj z :=
      (hSquareObj w).trans (congrArg JV.obj hVz)
    have hFinish : dX.normalizedHom (JU.obj (KWU.obj w)) ≍
        dX.normalizedHom (JV.obj z) := by
      cases hEndpoint
      rfl
    exact hStart.trans (hThroughRight.trans
      (hSquare.symm.trans (hThroughLeft.trans (hAmbient.trans hFinish))))
  · have hzU' : (JV.obj z).as ∉ U := hzU
    have hzU'' : subsetToAmbient V z.as ∉ U := hzU
    have hzV : (JV.obj z).as ∈ V := z.as.2
    have hzV' : subsetToAmbient V z.as ∈ V := z.as.2
    have hzv : (⟨⟨(JV.obj z).as, hzV⟩⟩ : FundamentalGroupoid V) = z := by
      apply FundamentalGroupoid.ext
      apply Subtype.ext
      rfl
    by_cases hzA : z.as.1 ∈ A
    · have hzSelV : z ∈ {q | q.as ∈ selectedIn A V} := hzA
      have hzSelX : JV.obj z ∈ {q | q.as ∈ A} := hzA
      have hmap := Functor.map_heq JV (dV.normalizedObj_of_mem hzSelV) rfl
        (dV.normalizedHom_heq_id_of_mem hzSelV)
      exact hmap.trans ((heq_of_eq (JV.map_id z)).trans
        (dX.normalizedHom_heq_id_of_mem hzSelX).symm)
    · have hzSelV : z ∉ {q | q.as ∈ selectedIn A V} := hzA
      have hzSelX : JV.obj z ∉ {q | q.as ∈ A} := hzA
      have hmap := Functor.map_heq JV
        (by simp [RepresentativeChoice.normalizedObj, hzSelV]) rfl
        (dV.normalizedHom_heq_hom_of_not_mem hzSelV)
      have hraw : dX.hom (JV.obj z) ≍ JV.map (dV.hom z) := by
        have hhom : dV.hom (⟨⟨(JV.obj z).as, hzV⟩⟩ : FundamentalGroupoid V) ≍
            dV.hom z := by
          cases hzv
          rfl
        have hmapraw := Functor.map_heq JV (congrArg dV.obj hzv) hzv hhom
        simpa [dX, ambientRepresentativeChoice, JV, hzU'', hzV'] using hmapraw
      exact hmap.trans (hraw.symm.trans
        (dX.normalizedHom_heq_hom_of_not_mem hzSelX).symm)

theorem rightToAmbient_comp_representativeRetraction
    {X : Type u} [TopologicalSpace X] (A U V : Set X) (hcover : U ∪ V = univ)
    (hAU : IsRepresentative (selectedIn A U))
    (hAV : IsRepresentative (selectedIn A V))
    (dW : RepresentativeChoice (FundamentalGroupoid (↑(U ∩ V)))
      {z | z.as ∈ selectedIn A (U ∩ V)}) :
    let dU := leftRepresentativeChoice A U V hAU dW
    let dV := rightRepresentativeChoice A U V hAV dW
    FundamentalGroupoid.map (subsetToAmbient V) ⋙
        representativeRetraction (ambientRepresentativeChoice A U V hcover dU dV) =
      representativeRetraction dV ⋙ selectedRightToAmbient A V := by
  dsimp only
  apply fundamentalGroupoidMap_comp_representativeRetraction
  · exact rightToAmbient_map_normalizedObj_eq A U V hcover hAU hAV dW
  · exact rightToAmbient_map_normalizedHom_heq A U V hcover hAU hAV dW

theorem seifertVanKampenOn {X : Type u} [TopologicalSpace X] (A U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (hAU : IsRepresentative (selectedIn A U))
    (hAV : IsRepresentative (selectedIn A V))
    (hAW : IsRepresentative (selectedIn A (U ∩ V))) :
    selectedGroupoidSquareIsPushoutStatement A U V := by
  let dW := representativeChoiceOfIsRepresentative hAW
  let dU := leftRepresentativeChoice A U V hAU dW
  let dV := rightRepresentativeChoice A U V hAV dW
  let dX := ambientRepresentativeChoice A U V hcover dU dV
  let iW := CategoryTheory.Subgroupoid.hom
    (CategoryTheory.Subgroupoid.full
      {z : FundamentalGroupoid (↑(U ∩ V)) | z.as ∈ selectedIn A (U ∩ V)})
  let iU := CategoryTheory.Subgroupoid.hom
    (CategoryTheory.Subgroupoid.full {z : FundamentalGroupoid U | z.as ∈ selectedIn A U})
  let iV := CategoryTheory.Subgroupoid.hom
    (CategoryTheory.Subgroupoid.full {z : FundamentalGroupoid V | z.as ∈ selectedIn A V})
  let iX := CategoryTheory.Subgroupoid.hom
    (CategoryTheory.Subgroupoid.full {z : FundamentalGroupoid X | z.as ∈ A})
  let R : @CommSqRetract Grpd.{u, u} _
      (Grpd.of (FundamentalGroupoidOn (↑(U ∩ V)) (selectedIn A (U ∩ V))))
      (Grpd.of (FundamentalGroupoidOn U (selectedIn A U)))
      (Grpd.of (FundamentalGroupoidOn V (selectedIn A V)))
      (Grpd.of (FundamentalGroupoidOn X A))
      (Grpd.of (FundamentalGroupoid (↑(U ∩ V))))
      (Grpd.of (FundamentalGroupoid U))
      (Grpd.of (FundamentalGroupoid V))
      (Grpd.of (FundamentalGroupoid X))
      (selectedInterToLeft A U V) (selectedInterToRight A U V)
      (selectedLeftToAmbient A U) (selectedRightToAmbient A V)
      (FundamentalGroupoid.map (interToLeft U V))
      (FundamentalGroupoid.map (interToRight U V))
      (FundamentalGroupoid.map (subsetToAmbient U))
      (FundamentalGroupoid.map (subsetToAmbient V)) := {
    small := { w := by exact selectedGroupoid_coverSquare_commutes A U V }
    iZ := iW
    iX := iU
    iY := iV
    iP := iX
    rZ := representativeRetraction dW
    rX := representativeRetraction dU
    rY := representativeRetraction dV
    rP := representativeRetraction dX
    retract_z := inclusion_comp_representativeRetraction dW
    retract_x := inclusion_comp_representativeRetraction dU
    retract_y := inclusion_comp_representativeRetraction dV
    retract_p := inclusion_comp_representativeRetraction dX
    i_top := (fundamentalGroupoidMapOn_comp_inclusion (interToLeft U V) _).symm
    i_left := (fundamentalGroupoidMapOn_comp_inclusion (interToRight U V) _).symm
    i_right := (fundamentalGroupoidMapOn_comp_inclusion (subsetToAmbient U) _).symm
    i_bottom := (fundamentalGroupoidMapOn_comp_inclusion (subsetToAmbient V) _).symm
    r_top := interToLeft_comp_representativeRetraction A U V hAU dW
    r_left := interToRight_comp_representativeRetraction A U V hAV dW
    r_right := leftToAmbient_comp_representativeRetraction A U V hcover dU dV
    r_bottom := rightToAmbient_comp_representativeRetraction A U V hcover hAU hAV dW }
  unfold selectedGroupoidSquareIsPushoutStatement
  exact R.isPushout (seifertVanKampen U V hU hV hcover)

end Poincare.Topology.VanKampen
