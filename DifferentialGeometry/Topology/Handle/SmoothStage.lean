/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Geometry.Manifold.Instances.Real

open Set Topology Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

def IsSmoothHandleStage (Y : Type*) [TopologicalSpace Y] (Bd : Set Y) : Prop :=
  ∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace (EuclideanHalfSpace 3) M),
    IsManifold (𝓡∂ 3) ∞ M ∧ T2Space M ∧ CompactSpace M ∧
      ∃ h : Y ≃ₜ M, h '' Bd = (𝓡∂ 3).boundary M

theorem isSmoothHandleStage_of_isEmpty (Y : Type*) [TopologicalSpace Y] [IsEmpty Y] (Bd : Set Y) :
    IsSmoothHandleStage Y Bd := by
  let _ : ChartedSpace (EuclideanHalfSpace 3) Empty := ChartedSpace.empty _ Empty
  refine ⟨Empty, inferInstance, inferInstance, IsManifold.empty _, inferInstance,
    inferInstance, Homeomorph.empty, ?_⟩
  exact Set.ext fun x => isEmptyElim x

theorem IsSmoothHandleStage.transport {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    {Bd : Set Y} (hY : IsSmoothHandleStage Y Bd) (e : Y ≃ₜ Z) :
    IsSmoothHandleStage Z (e '' Bd) := by
  obtain ⟨M, iT, iC, hM, hT2, hc, f, hf⟩ := hY
  refine ⟨M, iT, iC, hM, hT2, hc, e.symm.trans f, ?_⟩
  rw [Set.image_image]
  simp only [Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
  exact hf

end DifferentialGeometry.Topology.PiecewiseLinear
