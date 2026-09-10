/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.FundamentalGroup.HomotopyEquiv
import DifferentialGeometry.Topology.VanKampen.SimplyConnectedCover

set_option autoImplicit false

open Set
open scoped ContinuousMap

universe u

namespace DifferentialGeometry.Topology.VanKampen


noncomputable def fundamentalGroupEquivOfHomotopyEquivToLeftCover
    {K X : Type u} [TopologicalSpace K] [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (k₀ : K) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (e : K ≃ₕ U) (hbase : e k₀ = leftBasepoint U x₀ hx₀.1)
    [PathConnectedSpace U] [SimplyConnectedSpace V]
    [SimplyConnectedSpace (↑(U ∩ V))] :
    FundamentalGroup K k₀ ≃* FundamentalGroup X x₀ :=
  (DifferentialGeometry.Topology.fundamentalGroupMulEquivOfHomotopyEquiv
    e k₀ (leftBasepoint U x₀ hx₀.1) hbase).trans
      (fundamentalGroupLeftToAmbientEquivOfSimplyConnected
        U V hU hV hcover x₀ hx₀)

theorem fundamentalGroupEquivOfHomotopyEquivToLeftCover_toMonoidHom
    {K X : Type u} [TopologicalSpace K] [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (k₀ : K) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (e : K ≃ₕ U) (hbase : e k₀ = leftBasepoint U x₀ hx₀.1)
    [PathConnectedSpace U] [SimplyConnectedSpace V]
    [SimplyConnectedSpace (↑(U ∩ V))] :
    (↑(fundamentalGroupEquivOfHomotopyEquivToLeftCover
      U V hU hV hcover k₀ x₀ hx₀ e hbase) :
        FundamentalGroup K k₀ →* FundamentalGroup X x₀) =
      (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom.comp
        (FundamentalGroup.mapOfEq e.toFun hbase) := by
  rfl


noncomputable def fundamentalGroupEquivOfHomotopyEquivToRightCover
    {K X : Type u} [TopologicalSpace K] [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (k₀ : K) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (e : K ≃ₕ V) (hbase : e k₀ = rightBasepoint V x₀ hx₀.2)
    [PathConnectedSpace V] [SimplyConnectedSpace U]
    [SimplyConnectedSpace (↑(U ∩ V))] :
    FundamentalGroup K k₀ ≃* FundamentalGroup X x₀ :=
  (DifferentialGeometry.Topology.fundamentalGroupMulEquivOfHomotopyEquiv
    e k₀ (rightBasepoint V x₀ hx₀.2) hbase).trans
      (fundamentalGroupRightToAmbientEquivOfSimplyConnected
        U V hU hV hcover x₀ hx₀)

theorem fundamentalGroupEquivOfHomotopyEquivToRightCover_toMonoidHom
    {K X : Type u} [TopologicalSpace K] [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (k₀ : K) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (e : K ≃ₕ V) (hbase : e k₀ = rightBasepoint V x₀ hx₀.2)
    [PathConnectedSpace V] [SimplyConnectedSpace U]
    [SimplyConnectedSpace (↑(U ∩ V))] :
    (↑(fundamentalGroupEquivOfHomotopyEquivToRightCover
      U V hU hV hcover k₀ x₀ hx₀ e hbase) :
        FundamentalGroup K k₀ →* FundamentalGroup X x₀) =
      (fundamentalGroupRightToAmbient V x₀ hx₀.2).hom.comp
        (FundamentalGroup.mapOfEq e.toFun hbase) := by
  rfl

end DifferentialGeometry.Topology.VanKampen
