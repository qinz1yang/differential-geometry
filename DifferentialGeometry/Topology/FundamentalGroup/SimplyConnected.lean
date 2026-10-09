/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] [PathConnectedSpace X]

theorem simplyConnectedSpace_iff_fundamentalGroup_eq_one (x : X) :
    SimplyConnectedSpace X ↔ ∀ g : FundamentalGroup X x, g = 1 := by
  constructor
  · intro h
    let _ := h
    exact fun g => Subsingleton.elim g 1
  · intro h
    apply simply_connected_iff_loops_nullhomotopic.mpr
    refine ⟨inferInstance, fun y p => ?_⟩
    let e := FundamentalGroup.fundamentalGroupMulEquivOfPathConnected y x
    apply Path.Homotopic.Quotient.exact
    change Path.Homotopic.Quotient.mk p = (1 : FundamentalGroup X y)
    apply e.injective
    rw [map_one]
    exact h _

theorem exists_fundamentalGroup_ne_one_of_not_simplyConnectedSpace
    (h : ¬ SimplyConnectedSpace X) (x : X) :
    ∃ g : FundamentalGroup X x, g ≠ 1 := by
  classical
  exact not_forall.mp ((simplyConnectedSpace_iff_fundamentalGroup_eq_one x).not.mp h)

end DifferentialGeometry.Topology
