/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.FundamentalGroup.BasepointChange
import DifferentialGeometry.Topology.VanKampen.HomotopyEquivalentFreeProductCover

set_option autoImplicit false

open Set
open scoped ContinuousMap

universe u

namespace Poincare.Topology.VanKampen

noncomputable def fundamentalGroupSourceFactorEquivOfConnectors
    {K L X : Type u} [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (k₀ : K) (l₀ : L)
    (eU : K ≃ₕ U) (βU : Path (leftBasepoint U x₀ hx₀.1) (eU k₀))
    (eV : L ≃ₕ V) (βV : Path (rightBasepoint V x₀ hx₀.2) (eV l₀)) :
    ∀ i, fundamentalGroupSourceFactor k₀ l₀ i ≃*
      fundamentalGroupFactor U V x₀ hx₀ i
  | false =>
      (Poincare.Topology.fundamentalGroupMulEquivOfHomotopyEquiv
        eU k₀ (eU k₀) rfl).trans
        (Poincare.Topology.fundamentalGroupChangeBasepoint βU)
  | true =>
      (Poincare.Topology.fundamentalGroupMulEquivOfHomotopyEquiv
        eV l₀ (eV l₀) rfl).trans
        (Poincare.Topology.fundamentalGroupChangeBasepoint βV)

theorem fundamentalGroupSourceFactorEquivOfConnectors_false_toMonoidHom
    {K L X : Type u} [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (k₀ : K) (l₀ : L)
    (eU : K ≃ₕ U) (βU : Path (leftBasepoint U x₀ hx₀.1) (eU k₀))
    (eV : L ≃ₕ V) (βV : Path (rightBasepoint V x₀ hx₀.2) (eV l₀)) :
    (↑(fundamentalGroupSourceFactorEquivOfConnectors
      U V x₀ hx₀ k₀ l₀ eU βU eV βV false) :
        FundamentalGroup K k₀ →*
          FundamentalGroup U (leftBasepoint U x₀ hx₀.1)) =
      (Poincare.Topology.fundamentalGroupChangeBasepoint βU).toMonoidHom.comp
        (FundamentalGroup.mapOfEq eU.toFun rfl) := by
  rfl

theorem fundamentalGroupSourceFactorEquivOfConnectors_true_toMonoidHom
    {K L X : Type u} [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (k₀ : K) (l₀ : L)
    (eU : K ≃ₕ U) (βU : Path (leftBasepoint U x₀ hx₀.1) (eU k₀))
    (eV : L ≃ₕ V) (βV : Path (rightBasepoint V x₀ hx₀.2) (eV l₀)) :
    (↑(fundamentalGroupSourceFactorEquivOfConnectors
      U V x₀ hx₀ k₀ l₀ eU βU eV βV true) :
        FundamentalGroup L l₀ →*
          FundamentalGroup V (rightBasepoint V x₀ hx₀.2)) =
      (Poincare.Topology.fundamentalGroupChangeBasepoint βV).toMonoidHom.comp
        (FundamentalGroup.mapOfEq eV.toFun rfl) := by
  rfl

noncomputable def fundamentalGroupEquivFreeProductOfHomotopyEquivOfConnectors
    {K L X : Type u} [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) (k₀ : K) (l₀ : L)
    (eU : K ≃ₕ U) (βU : Path (leftBasepoint U x₀ hx₀.1) (eU k₀))
    (eV : L ≃ₕ V) (βV : Path (rightBasepoint V x₀ hx₀.2) (eV l₀))
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (↑(U ∩ V))] :
    fundamentalGroupSourceFreeProduct k₀ l₀ ≃* FundamentalGroup X x₀ :=
  (Poincare.Algebra.Group.coprodIMulEquiv
      (fundamentalGroupSourceFactor k₀ l₀)
      (fundamentalGroupFactor U V x₀ hx₀)
      (fundamentalGroupSourceFactorEquivOfConnectors
        U V x₀ hx₀ k₀ l₀ eU βU eV βV)).trans
    (fundamentalGroupEquivFreeProduct U V hU hV hcover x₀ hx₀)

theorem fundamentalGroupEquivFreeProductOfHomotopyEquivOfConnectors_comp_left
    {K L X : Type u} [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) (k₀ : K) (l₀ : L)
    (eU : K ≃ₕ U) (βU : Path (leftBasepoint U x₀ hx₀.1) (eU k₀))
    (eV : L ≃ₕ V) (βV : Path (rightBasepoint V x₀ hx₀.2) (eV l₀))
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (↑(U ∩ V))] :
    (↑(fundamentalGroupEquivFreeProductOfHomotopyEquivOfConnectors
      U V hU hV hcover x₀ hx₀ k₀ l₀ eU βU eV βV) :
        fundamentalGroupSourceFreeProduct k₀ l₀ →* FundamentalGroup X x₀).comp
      (Monoid.CoprodI.of (M := fundamentalGroupSourceFactor k₀ l₀) (i := false)) =
      (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom.comp
        ((Poincare.Topology.fundamentalGroupChangeBasepoint βU).toMonoidHom.comp
          (FundamentalGroup.mapOfEq eU.toFun rfl)) := by
  ext g
  change (fundamentalGroupEquivFreeProduct U V hU hV hcover x₀ hx₀)
      (Monoid.CoprodI.of (M := fundamentalGroupFactor U V x₀ hx₀) (i := false)
        (Poincare.Topology.fundamentalGroupChangeBasepoint βU
          (FundamentalGroup.mapOfEq eU.toFun rfl g))) = _
  simpa only [MonoidHom.comp_apply, fundamentalGroupFreeProductLeft,
    GrpCat.hom_ofHom, MulEquiv.coe_toMonoidHom] using DFunLike.congr_fun
      (fundamentalGroupEquivFreeProduct_comp_left U V hU hV hcover x₀ hx₀)
      (Poincare.Topology.fundamentalGroupChangeBasepoint βU
        (FundamentalGroup.mapOfEq eU.toFun rfl g))

theorem fundamentalGroupEquivFreeProductOfHomotopyEquivOfConnectors_comp_right
    {K L X : Type u} [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) (k₀ : K) (l₀ : L)
    (eU : K ≃ₕ U) (βU : Path (leftBasepoint U x₀ hx₀.1) (eU k₀))
    (eV : L ≃ₕ V) (βV : Path (rightBasepoint V x₀ hx₀.2) (eV l₀))
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (↑(U ∩ V))] :
    (↑(fundamentalGroupEquivFreeProductOfHomotopyEquivOfConnectors
      U V hU hV hcover x₀ hx₀ k₀ l₀ eU βU eV βV) :
        fundamentalGroupSourceFreeProduct k₀ l₀ →* FundamentalGroup X x₀).comp
      (Monoid.CoprodI.of (M := fundamentalGroupSourceFactor k₀ l₀) (i := true)) =
      (fundamentalGroupRightToAmbient V x₀ hx₀.2).hom.comp
        ((Poincare.Topology.fundamentalGroupChangeBasepoint βV).toMonoidHom.comp
          (FundamentalGroup.mapOfEq eV.toFun rfl)) := by
  ext g
  change (fundamentalGroupEquivFreeProduct U V hU hV hcover x₀ hx₀)
      (Monoid.CoprodI.of (M := fundamentalGroupFactor U V x₀ hx₀) (i := true)
        (Poincare.Topology.fundamentalGroupChangeBasepoint βV
          (FundamentalGroup.mapOfEq eV.toFun rfl g))) = _
  simpa only [MonoidHom.comp_apply, fundamentalGroupFreeProductRight,
    GrpCat.hom_ofHom, MulEquiv.coe_toMonoidHom] using DFunLike.congr_fun
      (fundamentalGroupEquivFreeProduct_comp_right U V hU hV hcover x₀ hx₀)
      (Poincare.Topology.fundamentalGroupChangeBasepoint βV
        (FundamentalGroup.mapOfEq eV.toFun rfl g))

end Poincare.Topology.VanKampen
