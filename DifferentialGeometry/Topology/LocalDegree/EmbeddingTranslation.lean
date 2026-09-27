/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.LocalDegree.EmbeddingParity

open Set

namespace DifferentialGeometry.LocalDegree

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (d + 1))

theorem embeddingOrientationParity_sub_const
    {U : Set E} (hU : IsOpen U) {f : E → E} (hf : ContinuousOn f U)
    (hfi : InjOn f U) (b : E) (x : U) :
    embeddingOrientationParity hU
      (show ContinuousOn (fun y => f y - b) U from hf.sub continuousOn_const)
      (fun y hy z hz hyz => hfi hy hz
        (add_right_cancel (by simpa only [sub_eq_add_neg] using hyz))) x =
      embeddingOrientationParity hU hf hfi x := by
  unfold embeddingOrientationParity
  simp only [sub_sub_sub_cancel_right]

end DifferentialGeometry.LocalDegree
