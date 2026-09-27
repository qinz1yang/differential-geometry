/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.FundamentalGroup.HomotopyEquiv
import DifferentialGeometry.Topology.VanKampen.FreeProduct

set_option autoImplicit false

open Set
open scoped ContinuousMap

universe u

namespace DifferentialGeometry.Topology.VanKampen

abbrev fundamentalGroupSourceFactor
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (k₀ : K) (l₀ : L) : Bool → Type u
  | false => FundamentalGroup K k₀
  | true => FundamentalGroup L l₀

noncomputable instance fundamentalGroupSourceFactorGroup
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (k₀ : K) (l₀ : L) (i : Bool) :
    Group (fundamentalGroupSourceFactor k₀ l₀ i) := by
  cases i <;> simp only [fundamentalGroupSourceFactor] <;> infer_instance

abbrev fundamentalGroupSourceFreeProduct
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (k₀ : K) (l₀ : L) :=
  Monoid.CoprodI (fundamentalGroupSourceFactor k₀ l₀)

noncomputable def fundamentalGroupSourceFactorEquiv
    {K L X : Type u} [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (k₀ : K) (l₀ : L)
    (eU : K ≃ₕ U) (hbaseU : eU k₀ = leftBasepoint U x₀ hx₀.1)
    (eV : L ≃ₕ V) (hbaseV : eV l₀ = rightBasepoint V x₀ hx₀.2) :
    ∀ i, fundamentalGroupSourceFactor k₀ l₀ i ≃*
      fundamentalGroupFactor U V x₀ hx₀ i
  | false => DifferentialGeometry.Topology.fundamentalGroupMulEquivOfHomotopyEquiv
      eU k₀ (leftBasepoint U x₀ hx₀.1) hbaseU
  | true => DifferentialGeometry.Topology.fundamentalGroupMulEquivOfHomotopyEquiv
      eV l₀ (rightBasepoint V x₀ hx₀.2) hbaseV

theorem fundamentalGroupSourceFactorEquiv_false_toMonoidHom
    {K L X : Type u} [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (k₀ : K) (l₀ : L)
    (eU : K ≃ₕ U) (hbaseU : eU k₀ = leftBasepoint U x₀ hx₀.1)
    (eV : L ≃ₕ V) (hbaseV : eV l₀ = rightBasepoint V x₀ hx₀.2) :
    (↑(fundamentalGroupSourceFactorEquiv
      U V x₀ hx₀ k₀ l₀ eU hbaseU eV hbaseV false) :
        FundamentalGroup K k₀ →*
          FundamentalGroup U (leftBasepoint U x₀ hx₀.1)) =
      FundamentalGroup.mapOfEq eU.toFun hbaseU := by
  rfl

theorem fundamentalGroupSourceFactorEquiv_true_toMonoidHom
    {K L X : Type u} [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (k₀ : K) (l₀ : L)
    (eU : K ≃ₕ U) (hbaseU : eU k₀ = leftBasepoint U x₀ hx₀.1)
    (eV : L ≃ₕ V) (hbaseV : eV l₀ = rightBasepoint V x₀ hx₀.2) :
    (↑(fundamentalGroupSourceFactorEquiv
      U V x₀ hx₀ k₀ l₀ eU hbaseU eV hbaseV true) :
        FundamentalGroup L l₀ →*
          FundamentalGroup V (rightBasepoint V x₀ hx₀.2)) =
      FundamentalGroup.mapOfEq eV.toFun hbaseV := by
  rfl

noncomputable def fundamentalGroupEquivFreeProductOfHomotopyEquiv
    {K L X : Type u} [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) (k₀ : K) (l₀ : L)
    (eU : K ≃ₕ U) (hbaseU : eU k₀ = leftBasepoint U x₀ hx₀.1)
    (eV : L ≃ₕ V) (hbaseV : eV l₀ = rightBasepoint V x₀ hx₀.2)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (↑(U ∩ V))] :
    fundamentalGroupSourceFreeProduct k₀ l₀ ≃* FundamentalGroup X x₀ :=
  (DifferentialGeometry.Algebra.Group.coprodIMulEquiv
      (fundamentalGroupSourceFactor k₀ l₀)
      (fundamentalGroupFactor U V x₀ hx₀)
      (fundamentalGroupSourceFactorEquiv U V x₀ hx₀ k₀ l₀ eU hbaseU eV hbaseV)).trans
    (fundamentalGroupEquivFreeProduct U V hU hV hcover x₀ hx₀)

theorem fundamentalGroupEquivFreeProductOfHomotopyEquiv_comp_left
    {K L X : Type u} [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) (k₀ : K) (l₀ : L)
    (eU : K ≃ₕ U) (hbaseU : eU k₀ = leftBasepoint U x₀ hx₀.1)
    (eV : L ≃ₕ V) (hbaseV : eV l₀ = rightBasepoint V x₀ hx₀.2)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (↑(U ∩ V))] :
    (↑(fundamentalGroupEquivFreeProductOfHomotopyEquiv
      U V hU hV hcover x₀ hx₀ k₀ l₀ eU hbaseU eV hbaseV) :
        fundamentalGroupSourceFreeProduct k₀ l₀ →* FundamentalGroup X x₀).comp
      (Monoid.CoprodI.of (M := fundamentalGroupSourceFactor k₀ l₀) (i := false)) =
      (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom.comp
        (FundamentalGroup.mapOfEq eU.toFun hbaseU) := by
  ext g
  change (fundamentalGroupEquivFreeProduct U V hU hV hcover x₀ hx₀)
      (Monoid.CoprodI.of (M := fundamentalGroupFactor U V x₀ hx₀) (i := false)
        (FundamentalGroup.mapOfEq eU.toFun hbaseU g)) =
    (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom
      (FundamentalGroup.mapOfEq eU.toFun hbaseU g)
  simpa only [MonoidHom.comp_apply, fundamentalGroupFreeProductLeft,
    GrpCat.hom_ofHom, MulEquiv.coe_toMonoidHom] using DFunLike.congr_fun
      (fundamentalGroupEquivFreeProduct_comp_left U V hU hV hcover x₀ hx₀)
      (FundamentalGroup.mapOfEq eU.toFun hbaseU g)

theorem fundamentalGroupEquivFreeProductOfHomotopyEquiv_comp_right
    {K L X : Type u} [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) (k₀ : K) (l₀ : L)
    (eU : K ≃ₕ U) (hbaseU : eU k₀ = leftBasepoint U x₀ hx₀.1)
    (eV : L ≃ₕ V) (hbaseV : eV l₀ = rightBasepoint V x₀ hx₀.2)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (↑(U ∩ V))] :
    (↑(fundamentalGroupEquivFreeProductOfHomotopyEquiv
      U V hU hV hcover x₀ hx₀ k₀ l₀ eU hbaseU eV hbaseV) :
        fundamentalGroupSourceFreeProduct k₀ l₀ →* FundamentalGroup X x₀).comp
      (Monoid.CoprodI.of (M := fundamentalGroupSourceFactor k₀ l₀) (i := true)) =
      (fundamentalGroupRightToAmbient V x₀ hx₀.2).hom.comp
        (FundamentalGroup.mapOfEq eV.toFun hbaseV) := by
  ext g
  change (fundamentalGroupEquivFreeProduct U V hU hV hcover x₀ hx₀)
      (Monoid.CoprodI.of (M := fundamentalGroupFactor U V x₀ hx₀) (i := true)
        (FundamentalGroup.mapOfEq eV.toFun hbaseV g)) =
    (fundamentalGroupRightToAmbient V x₀ hx₀.2).hom
      (FundamentalGroup.mapOfEq eV.toFun hbaseV g)
  simpa only [MonoidHom.comp_apply, fundamentalGroupFreeProductRight,
    GrpCat.hom_ofHom, MulEquiv.coe_toMonoidHom] using DFunLike.congr_fun
      (fundamentalGroupEquivFreeProduct_comp_right U V hU hV hcover x₀ hx₀)
      (FundamentalGroup.mapOfEq eV.toFun hbaseV g)

end DifferentialGeometry.Topology.VanKampen
