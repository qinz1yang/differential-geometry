/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Algebra.Group.Equiv.Opposite
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.ZMultiples
import DifferentialGeometry.Topology.FundamentalGroup.HomotopyEquiv
import DifferentialGeometry.Topology.FundamentalGroup.Product

set_option autoImplicit false

open AddSubgroup

universe u

namespace DifferentialGeometry.Topology

noncomputable def intEquivZMultiplesOne : ℤ ≃+ zmultiples (1 : ℝ) :=
  AddEquiv.ofBijective
    ((Int.castAddHom ℝ).codRestrict (zmultiples (1 : ℝ))
      (fun n ↦ intCast_mem_zmultiples_one (R := ℝ) n)) <| by
    constructor
    · intro m n h
      have hr : (m : ℝ) = (n : ℝ) := congrArg Subtype.val h
      exact Int.cast_injective hr
    · rintro ⟨x, hx⟩
      rw [mem_zmultiples_iff] at hx
      obtain ⟨n, hn⟩ := hx
      refine ⟨n, Subtype.ext ?_⟩
      change (n : ℝ) = x
      simpa using hn

noncomputable def fundamentalGroupUnitAddCircleEquivInt :
    FundamentalGroup (AddCircle (1 : ℝ)) 0 ≃* Multiplicative ℤ :=
  ((AddCircle.isAddQuotientCoveringMap_coe (1 : ℝ)).fundamentalGroupEquiv
      (⟨0, rfl⟩ : ((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' {0})).trans
    (MulOpposite.opMulEquiv.symm.trans intEquivZMultiplesOne.toMultiplicative.symm)

noncomputable def fundamentalGroupCircleEquivInt :
    FundamentalGroup Circle (1 : Circle) ≃* Multiplicative ℤ :=
  (fundamentalGroupMulEquivOfHomotopyEquiv
      (AddCircle.homeomorphCircle one_ne_zero).toHomotopyEquiv
      (0 : AddCircle (1 : ℝ)) (1 : Circle) (by
        change AddCircle.homeomorphCircle one_ne_zero 0 = 1
        rw [AddCircle.homeomorphCircle_apply]
        exact AddCircle.toCircle_zero)).symm.trans
    fundamentalGroupUnitAddCircleEquivInt

noncomputable def fundamentalGroupProdCircleEquivIntOfSimplyConnected
    {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    FundamentalGroup (X × Circle) (x, 1) ≃* Multiplicative ℤ :=
  (fundamentalGroupProdRightEquivOfSimplyConnected x (1 : Circle)).trans
    fundamentalGroupCircleEquivInt

end DifferentialGeometry.Topology
