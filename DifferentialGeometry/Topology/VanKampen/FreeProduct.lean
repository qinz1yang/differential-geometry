/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.Algebra.Group.FreeProduct
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import DifferentialGeometry.Topology.VanKampen.AmalgamatedProduct

set_option autoImplicit false

open CategoryTheory Set

universe u

namespace Poincare.Topology.VanKampen

abbrev fundamentalGroupFreeProduct {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :=
  Monoid.CoprodI (fundamentalGroupFactor U V x₀ hx₀)

noncomputable def fundamentalGroupFreeProductLeft {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    GrpCat.of (FundamentalGroup U (leftBasepoint U x₀ hx₀.1)) ⟶
      GrpCat.of (fundamentalGroupFreeProduct U V x₀ hx₀) :=
  GrpCat.ofHom (Monoid.CoprodI.of
    (M := fundamentalGroupFactor U V x₀ hx₀) (i := false))

noncomputable def fundamentalGroupFreeProductRight {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    GrpCat.of (FundamentalGroup V (rightBasepoint V x₀ hx₀.2)) ⟶
      GrpCat.of (fundamentalGroupFreeProduct U V x₀ hx₀) :=
  GrpCat.ofHom (Monoid.CoprodI.of
    (M := fundamentalGroupFactor U V x₀ hx₀) (i := true))

theorem fundamentalGroupFreeProduct_coverSquare_commutes
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [SimplyConnectedSpace (↑(U ∩ V))] :
    fundamentalGroupInterToLeft U V x₀ hx₀ ≫
        fundamentalGroupFreeProductLeft U V x₀ hx₀ =
      fundamentalGroupInterToRight U V x₀ hx₀ ≫
        fundamentalGroupFreeProductRight U V x₀ hx₀ := by
  apply GrpCat.ext
  intro w
  change Monoid.CoprodI.of (M := fundamentalGroupFactor U V x₀ hx₀) (i := false)
      ((fundamentalGroupInterToLeft U V x₀ hx₀).hom w) =
    Monoid.CoprodI.of (M := fundamentalGroupFactor U V x₀ hx₀) (i := true)
      ((fundamentalGroupInterToRight U V x₀ hx₀).hom w)
  have hw : w = 1 := Subsingleton.elim _ _
  subst w
  simp only [map_one]

noncomputable def freeProductToFundamentalGroup
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    GrpCat.of (fundamentalGroupFreeProduct U V x₀ hx₀) ⟶
      GrpCat.of (FundamentalGroup X x₀) :=
  GrpCat.ofHom (Monoid.CoprodI.lift (fundamentalGroupFactorToAmbient U V x₀ hx₀))

theorem fundamentalGroupFreeProductLeft_toFundamentalGroup
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    fundamentalGroupFreeProductLeft U V x₀ hx₀ ≫
        freeProductToFundamentalGroup U V x₀ hx₀ =
      fundamentalGroupLeftToAmbient U x₀ hx₀.1 := by
  apply GrpCat.ext
  intro g
  change Monoid.CoprodI.lift (fundamentalGroupFactorToAmbient U V x₀ hx₀)
      (Monoid.CoprodI.of (M := fundamentalGroupFactor U V x₀ hx₀) (i := false) g) =
    (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom g
  rw [Monoid.CoprodI.lift_of]
  rfl

theorem fundamentalGroupFreeProductRight_toFundamentalGroup
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    fundamentalGroupFreeProductRight U V x₀ hx₀ ≫
        freeProductToFundamentalGroup U V x₀ hx₀ =
      fundamentalGroupRightToAmbient V x₀ hx₀.2 := by
  apply GrpCat.ext
  intro g
  change Monoid.CoprodI.lift (fundamentalGroupFactorToAmbient U V x₀ hx₀)
      (Monoid.CoprodI.of (M := fundamentalGroupFactor U V x₀ hx₀) (i := true) g) =
    (fundamentalGroupRightToAmbient V x₀ hx₀.2).hom g
  rw [Monoid.CoprodI.lift_of]
  rfl

noncomputable def fundamentalGroupToFreeProduct
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (↑(U ∩ V))] :
    GrpCat.of (FundamentalGroup X x₀) ⟶
      GrpCat.of (fundamentalGroupFreeProduct U V x₀ hx₀) :=
  (fundamentalGroup_isPushout U V hU hV hcover x₀ hx₀).desc
    (fundamentalGroupFreeProductLeft U V x₀ hx₀)
    (fundamentalGroupFreeProductRight U V x₀ hx₀)
    (fundamentalGroupFreeProduct_coverSquare_commutes U V x₀ hx₀)

theorem fundamentalGroupLeftToAmbient_toFreeProduct
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (↑(U ∩ V))] :
    fundamentalGroupLeftToAmbient U x₀ hx₀.1 ≫
        fundamentalGroupToFreeProduct U V hU hV hcover x₀ hx₀ =
      fundamentalGroupFreeProductLeft U V x₀ hx₀ := by
  apply (fundamentalGroup_isPushout U V hU hV hcover x₀ hx₀).inl_desc

theorem fundamentalGroupRightToAmbient_toFreeProduct
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (↑(U ∩ V))] :
    fundamentalGroupRightToAmbient V x₀ hx₀.2 ≫
        fundamentalGroupToFreeProduct U V hU hV hcover x₀ hx₀ =
      fundamentalGroupFreeProductRight U V x₀ hx₀ := by
  apply (fundamentalGroup_isPushout U V hU hV hcover x₀ hx₀).inr_desc

theorem freeProductCanonicalMaps_forward_inverse
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (↑(U ∩ V))] :
    fundamentalGroupToFreeProduct U V hU hV hcover x₀ hx₀ ≫
        freeProductToFundamentalGroup U V x₀ hx₀ =
      𝟙 (GrpCat.of (FundamentalGroup X x₀)) := by
  apply (fundamentalGroup_isPushout U V hU hV hcover x₀ hx₀).hom_ext
  · rw [← Category.assoc, fundamentalGroupLeftToAmbient_toFreeProduct,
      fundamentalGroupFreeProductLeft_toFundamentalGroup, Category.comp_id]
  · rw [← Category.assoc, fundamentalGroupRightToAmbient_toFreeProduct,
      fundamentalGroupFreeProductRight_toFundamentalGroup, Category.comp_id]

theorem freeProductCanonicalMaps_inverse_forward
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (↑(U ∩ V))] :
    freeProductToFundamentalGroup U V x₀ hx₀ ≫
        fundamentalGroupToFreeProduct U V hU hV hcover x₀ hx₀ =
      𝟙 (GrpCat.of (fundamentalGroupFreeProduct U V x₀ hx₀)) := by
  apply GrpCat.hom_ext
  apply Monoid.CoprodI.ext_hom
  intro i
  cases i with
  | false =>
      have hleft : fundamentalGroupFreeProductLeft U V x₀ hx₀ ≫
            (freeProductToFundamentalGroup U V x₀ hx₀ ≫
              fundamentalGroupToFreeProduct U V hU hV hcover x₀ hx₀) =
          fundamentalGroupFreeProductLeft U V x₀ hx₀ ≫ 𝟙 _ := by
        rw [← Category.assoc, fundamentalGroupFreeProductLeft_toFundamentalGroup,
          fundamentalGroupLeftToAmbient_toFreeProduct, Category.comp_id]
      simpa only [fundamentalGroupFreeProductLeft, GrpCat.hom_comp,
        GrpCat.hom_id, GrpCat.hom_ofHom] using congrArg GrpCat.Hom.hom hleft
  | true =>
      have hright : fundamentalGroupFreeProductRight U V x₀ hx₀ ≫
            (freeProductToFundamentalGroup U V x₀ hx₀ ≫
              fundamentalGroupToFreeProduct U V hU hV hcover x₀ hx₀) =
          fundamentalGroupFreeProductRight U V x₀ hx₀ ≫ 𝟙 _ := by
        rw [← Category.assoc, fundamentalGroupFreeProductRight_toFundamentalGroup,
          fundamentalGroupRightToAmbient_toFreeProduct, Category.comp_id]
      simpa only [fundamentalGroupFreeProductRight, GrpCat.hom_comp,
        GrpCat.hom_id, GrpCat.hom_ofHom] using congrArg GrpCat.Hom.hom hright

noncomputable def fundamentalGroupEquivFreeProduct
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (↑(U ∩ V))] :
    fundamentalGroupFreeProduct U V x₀ hx₀ ≃* FundamentalGroup X x₀ :=
  MonoidHom.toMulEquiv
    (freeProductToFundamentalGroup U V x₀ hx₀).hom
    (fundamentalGroupToFreeProduct U V hU hV hcover x₀ hx₀).hom
    (congrArg GrpCat.Hom.hom <|
      freeProductCanonicalMaps_inverse_forward U V hU hV hcover x₀ hx₀)
    (congrArg GrpCat.Hom.hom <|
      freeProductCanonicalMaps_forward_inverse U V hU hV hcover x₀ hx₀)

theorem fundamentalGroupEquivFreeProduct_comp_left
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (↑(U ∩ V))] :
    (fundamentalGroupEquivFreeProduct U V hU hV hcover x₀ hx₀).toMonoidHom.comp
        (fundamentalGroupFreeProductLeft U V x₀ hx₀).hom =
      (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom := by
  exact congrArg GrpCat.Hom.hom
    (fundamentalGroupFreeProductLeft_toFundamentalGroup U V x₀ hx₀)

theorem fundamentalGroupEquivFreeProduct_comp_right
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (↑(U ∩ V))] :
    (fundamentalGroupEquivFreeProduct U V hU hV hcover x₀ hx₀).toMonoidHom.comp
        (fundamentalGroupFreeProductRight U V x₀ hx₀).hom =
      (fundamentalGroupRightToAmbient V x₀ hx₀.2).hom := by
  exact congrArg GrpCat.Hom.hom
    (fundamentalGroupFreeProductRight_toFundamentalGroup U V x₀ hx₀)

end Poincare.Topology.VanKampen
