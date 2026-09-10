/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import DifferentialGeometry.Topology.VanKampen.Based

set_option autoImplicit false

open CategoryTheory Set

universe u

namespace Poincare.Topology.VanKampen

noncomputable def pushoutInlMulEquivOfIsIso
    {Z X Y P : GrpCat.{u}} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
    (h : IsPushout f g inl inr) [IsIso g] : X ≃* P := by
  letI : IsIso inl := h.isIso_inl_of_isIso
  exact CategoryTheory.Iso.groupIsoToMulEquiv (asIso inl)

@[simp]
theorem pushoutInlMulEquivOfIsIso_toMonoidHom
    {Z X Y P : GrpCat.{u}} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
    (h : IsPushout f g inl inr) [IsIso g] :
    (↑(pushoutInlMulEquivOfIsIso h) : X →* P) = inl.hom := by
  rfl

noncomputable def fundamentalGroupLeftToAmbientEquivOfSimplyConnected
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) [PathConnectedSpace U]
    [SimplyConnectedSpace V] [SimplyConnectedSpace (↑(U ∩ V))] :
    FundamentalGroup U (leftBasepoint U x₀ hx₀.1) ≃* FundamentalGroup X x₀ := by
  let g := fundamentalGroupInterToRight U V x₀ hx₀
  have hg : Function.Bijective g := by
    constructor
    · intro a b _
      exact Subsingleton.elim a b
    · intro y
      exact ⟨1, Subsingleton.elim _ y⟩
  letI : IsIso g := (ConcreteCategory.isIso_iff_bijective g).2 hg
  exact pushoutInlMulEquivOfIsIso
    (fundamentalGroup_isPushout U V hU hV hcover x₀ hx₀)

@[simp]
theorem fundamentalGroupLeftToAmbientEquivOfSimplyConnected_toMonoidHom
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) [PathConnectedSpace U]
    [SimplyConnectedSpace V] [SimplyConnectedSpace (↑(U ∩ V))] :
    (↑(fundamentalGroupLeftToAmbientEquivOfSimplyConnected
      U V hU hV hcover x₀ hx₀) :
        FundamentalGroup U (leftBasepoint U x₀ hx₀.1) →* FundamentalGroup X x₀) =
        (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom := by
  rfl

noncomputable def fundamentalGroupRightToAmbientEquivOfSimplyConnected
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) [PathConnectedSpace V]
    [SimplyConnectedSpace U] [SimplyConnectedSpace (↑(U ∩ V))] :
    FundamentalGroup V (rightBasepoint V x₀ hx₀.2) ≃* FundamentalGroup X x₀ := by
  let f := fundamentalGroupInterToLeft U V x₀ hx₀
  have hf : Function.Bijective f := by
    constructor
    · intro a b _
      exact Subsingleton.elim a b
    · intro y
      exact ⟨1, Subsingleton.elim _ y⟩
  letI : IsIso f := (ConcreteCategory.isIso_iff_bijective f).2 hf
  letI : IsIso (fundamentalGroupRightToAmbient V x₀ hx₀.2) :=
    (fundamentalGroup_isPushout U V hU hV hcover x₀ hx₀).isIso_inr_of_isIso
  exact CategoryTheory.Iso.groupIsoToMulEquiv
    (asIso (fundamentalGroupRightToAmbient V x₀ hx₀.2))

@[simp]
theorem fundamentalGroupRightToAmbientEquivOfSimplyConnected_toMonoidHom
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) [PathConnectedSpace V]
    [SimplyConnectedSpace U] [SimplyConnectedSpace (↑(U ∩ V))] :
    (↑(fundamentalGroupRightToAmbientEquivOfSimplyConnected
      U V hU hV hcover x₀ hx₀) :
        FundamentalGroup V (rightBasepoint V x₀ hx₀.2) →* FundamentalGroup X x₀) =
        (fundamentalGroupRightToAmbient V x₀ hx₀.2).hom := by
  rfl

end Poincare.Topology.VanKampen
