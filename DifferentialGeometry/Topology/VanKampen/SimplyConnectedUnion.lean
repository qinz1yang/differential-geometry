/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import DifferentialGeometry.Topology.Algebra.Group.AmalgamatedProduct
import DifferentialGeometry.Topology.VanKampen.AmalgamatedProduct

set_option autoImplicit false

open CategoryTheory Set

universe u

namespace Poincare.Topology.VanKampen

theorem simplyConnectedSpace_iff_fundamentalGroup_subsingleton
    (Y : Type u) [TopologicalSpace Y] [PathConnectedSpace Y] (y₀ : Y) :
    SimplyConnectedSpace Y ↔ Subsingleton (FundamentalGroup Y y₀) := by
  constructor
  · intro _
    infer_instance
  · intro h
    rw [simply_connected_iff_loops_nullhomotopic]
    refine ⟨inferInstance, ?_⟩
    intro y γ
    let e := FundamentalGroup.fundamentalGroupMulEquivOfPathConnected y₀ y
    have hySub : Subsingleton (FundamentalGroup Y y) :=
      ⟨fun a b => e.symm.injective (h.elim _ _)⟩
    rw [← Path.Homotopic.Quotient.eq]
    exact hySub.elim _ _

theorem simplyConnectedSpace_of_open_cover
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [SimplyConnectedSpace U] [SimplyConnectedSpace V]
    [PathConnectedSpace (↑(U ∩ V))] :
    SimplyConnectedSpace X := by
  have hpcU : IsPathConnected U := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have hpcV : IsPathConnected V := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have hpcX : IsPathConnected (univ : Set X) := by
    rw [← hcover]
    exact hpcU.union hpcV ⟨x₀, hx₀⟩
  let _ : PathConnectedSpace X := pathConnectedSpace_iff_univ.mpr hpcX
  let _ : ∀ i, Subsingleton (fundamentalGroupFactor U V x₀ hx₀ i) := by
    intro i
    cases i <;> simp only [fundamentalGroupFactor] <;> infer_instance
  have hP : Subsingleton (fundamentalGroupAmalgamatedProduct U V x₀ hx₀) :=
    Poincare.Algebra.Group.pushoutI_subsingleton_of_factors
      (fundamentalGroupFactor U V x₀ hx₀)
      (FundamentalGroup (↑(U ∩ V)) (overlapBasepoint U V x₀ hx₀))
      (fundamentalGroupAmalgamation U V x₀ hx₀)
  let e := fundamentalGroupEquivAmalgamatedProduct U V hU hV hcover x₀ hx₀
  have hX : Subsingleton (FundamentalGroup X x₀) := e.symm.subsingleton
  exact (simplyConnectedSpace_iff_fundamentalGroup_subsingleton X x₀).2 hX

theorem simplyConnected_coverMembers_of_union
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace X] [SimplyConnectedSpace (↑(U ∩ V))] :
    SimplyConnectedSpace U ∧ SimplyConnectedSpace V := by
  let e := fundamentalGroupEquivAmalgamatedProduct U V hU hV hcover x₀ hx₀
  have hP : Subsingleton (fundamentalGroupAmalgamatedProduct U V x₀ hx₀) := e.subsingleton
  have hφ : ∀ i, Function.Injective (fundamentalGroupAmalgamation U V x₀ hx₀ i) := by
    intro i a b _
    exact Subsingleton.elim a b
  have hleft : Subsingleton (FundamentalGroup U (leftBasepoint U x₀ hx₀.1)) :=
    ⟨fun a b => Monoid.PushoutI.of_injective hφ false (hP.elim _ _)⟩
  have hright : Subsingleton (FundamentalGroup V (rightBasepoint V x₀ hx₀.2)) :=
    ⟨fun a b => Monoid.PushoutI.of_injective hφ true (hP.elim _ _)⟩
  constructor
  · exact (simplyConnectedSpace_iff_fundamentalGroup_subsingleton
      U (leftBasepoint U x₀ hx₀.1)).2 hleft
  · exact (simplyConnectedSpace_iff_fundamentalGroup_subsingleton
      V (rightBasepoint V x₀ hx₀.2)).2 hright

end Poincare.Topology.VanKampen
