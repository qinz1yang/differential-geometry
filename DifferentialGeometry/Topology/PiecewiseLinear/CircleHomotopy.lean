/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleParametrization
import DifferentialGeometry.Topology.FundamentalGroup.Circle
import DifferentialGeometry.Topology.FundamentalGroup.SimplyConnected

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLSphere.not_simplyConnectedSpace_one {J : Set E} (hJ : IsPLSphere 1 J) :
    ¬ SimplyConnectedSpace J := by
  intro h
  obtain ⟨e⟩ := nonempty_homeomorph_loopCircle_of_isPLSphere_one hJ
  let circleEquiv : Circle ≃ₜ J :=
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm.trans e
  let _ : SimplyConnectedSpace Circle := circleEquiv.toHomotopyEquiv.simplyConnectedSpace
  let g := fundamentalGroupCircleEquivInt
  have hg := (simplyConnectedSpace_iff_fundamentalGroup_eq_one (1 : Circle)).mp
    inferInstance (g.symm (Multiplicative.ofAdd (1 : ℤ)))
  have he := congrArg (fun x => Multiplicative.toAdd (g x)) hg
  simp only [MulEquiv.apply_symm_apply, map_one, toAdd_ofAdd, toAdd_one] at he
  exact one_ne_zero he

end DifferentialGeometry.Topology.PiecewiseLinear
