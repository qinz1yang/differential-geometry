/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.LocalDegree.BoundarySphereDegree
import DifferentialGeometry.Topology.PiecewiseLinear.CircleDegreeOrientation

open Set Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.LocalDegree

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "S1" => sphere (0 : Plane) 1

theorem isPLCirclePositive_unitSphere_iff_localDegree_eq_one
    {f : Plane → Plane} (h : IsolatingRadius f 0 1) (hb : BijOn f S1 S1) :
    IsPLCirclePositive S1 f ↔ euclideanLocalDegree f 0 ⟨1, h⟩ = 1 := by
  let g : loopCircle → Plane := fun θ => planarCircleParam θ
  have hgc : Continuous g := continuous_subtype_val.comp planarCircleParam.continuous
  have hgb : BijOn g univ S1 := by
    refine ⟨fun θ _ => (planarCircleParam θ).2, ?_, ?_⟩
    · intro a _ b _ hab
      exact planarCircleParam.injective (Subtype.ext hab)
    · intro z hz
      refine ⟨planarCircleParam.symm ⟨z, hz⟩, mem_univ _, ?_⟩
      exact congrArg Subtype.val (planarCircleParam.apply_symm_apply ⟨z, hz⟩)
  have hfc : ContinuousOn f S1 := h.continuousOn.mono sphere_subset_closedBall
  have heq : (circleSphereHomeomorph hgc hgb hfc hb).toHomotopyEquiv.toFun =
      h.boundarySphereMap hb.mapsTo := by
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    have hval := circleConj_spec hgb hb.mapsTo (planarCircleParam.symm z)
    change (planarCircleParam (circleConj g f (planarCircleParam.symm z)) : Plane) =
      f (planarCircleParam (planarCircleParam.symm z)) at hval
    rw [planarCircleParam.apply_symm_apply] at hval
    exact hval
  rw [isPLCirclePositive_iff_euclideanSphereDegree_eq_one hgc hgb hfc hb, heq,
    euclideanLocalDegree_eq_boundarySphereDegree h hb.mapsTo]

end DifferentialGeometry.Topology.PiecewiseLinear
