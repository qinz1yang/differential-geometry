/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.LocalDegree.HalfSpaceOpen
import DifferentialGeometry.Topology.LocalDegree.EmbeddingTranslation

open Set

namespace DifferentialGeometry.LocalDegree

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (d + 1))
local notation "E'" => EuclideanSpace ℝ (Fin ((d + 1) + 1))

theorem embeddingOrientationParity_eq_of_boundary_trace
    {f : E → E} {F : E' → E'} {V : Set E} {U : Set E'}
    (hV : IsOpen V) (hU : IsOpen U) (hf : ContinuousOn f V) (hfi : InjOn f V)
    (hF : ContinuousOn F U) (hFi : InjOn F U)
    (hV0 : (0 : E) ∈ V) (hU0 : (0 : E') ∈ U)
    (htrace : ∀ y ∈ U, (euclideanProductChart d y).2 = 0 →
      F y = euclideanProductPoint d (f (euclideanProductChart d y).1) 0)
    (hpos : ∀ y ∈ U, 0 < (euclideanProductChart d y).2 →
      0 < (euclideanProductChart d (F y)).2)
    (hneg : ∀ y ∈ U, (euclideanProductChart d y).2 < 0 →
      (euclideanProductChart d (F y)).2 < 0) :
    embeddingOrientationParity hU hF hFi ⟨0, hU0⟩ =
      embeddingOrientationParity hV hf hfi ⟨0, hV0⟩ := by
  let g : E → E := fun x => f x - f 0
  let G : E' → E' := fun y => F y - F 0
  have hg : ContinuousOn g V := hf.sub continuousOn_const
  have hG : ContinuousOn G U := hF.sub continuousOn_const
  have hgi : InjOn g V := fun x hx y hy hxy =>
    hfi hx hy (add_right_cancel (by simpa only [g, sub_eq_add_neg] using hxy))
  have hGi : InjOn G U := fun x hx y hy hxy =>
    hFi hx hy (add_right_cancel (by simpa only [G, sub_eq_add_neg] using hxy))
  have hzero : F 0 = euclideanProductPoint d (f 0) 0 := by
    simpa using htrace 0 hU0 (by simp)
  have hcoords : euclideanProductChart d (F 0) = (f 0, 0) := by
    rw [hzero]
    exact (euclideanProductChart d).apply_symm_apply (f 0, 0)
  have hheight (y : E') :
      (euclideanProductChart d (G y)).2 = (euclideanProductChart d (F y)).2 := by
    change (euclideanProductChart d (F y - F 0)).2 = _
    rw [map_sub, hcoords]
    change (euclideanProductChart d (F y)).2 - 0 = _
    exact sub_zero _
  have hGtrace : ∀ y ∈ U, (euclideanProductChart d y).2 = 0 →
      G y = euclideanProductPoint d (g (euclideanProductChart d y).1) 0 := by
    intro y hy hy0
    change F y - F 0 = euclideanProductPoint d (f (euclideanProductChart d y).1 - f 0) 0
    rw [htrace y hy hy0, hzero]
    change (euclideanProductChart d).symm (f (euclideanProductChart d y).1, 0) -
        (euclideanProductChart d).symm (f 0, 0) =
      (euclideanProductChart d).symm (f (euclideanProductChart d y).1 - f 0, 0)
    rw [← map_sub]
    congr 1
    ext <;> simp
  have hmid := embeddingOrientationParity_eq_of_preserves_halfspaces hV hU hg hgi hG hGi
    hV0 hU0 (by simp [g]) (by simp [G]) hGtrace
    (fun y hy hyp => by rw [hheight]; exact hpos y hy hyp)
    (fun y hy hyn => by rw [hheight]; exact hneg y hy hyn)
  exact (embeddingOrientationParity_sub_const hU hF hFi (F 0) ⟨0, hU0⟩).symm.trans
    (hmid.trans (embeddingOrientationParity_sub_const hV hf hfi (f 0) ⟨0, hV0⟩))

end DifferentialGeometry.LocalDegree
