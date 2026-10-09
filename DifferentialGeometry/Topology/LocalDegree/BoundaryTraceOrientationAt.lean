/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.LocalDegree.BoundaryTraceOrientation
import DifferentialGeometry.Topology.LocalDegree.HomeomorphConjugation

open Set

namespace DifferentialGeometry.LocalDegree

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (d + 1))
local notation "E'" => EuclideanSpace ℝ (Fin ((d + 1) + 1))

theorem embeddingOrientationParity_eq_of_boundary_trace_at
    {f : E → E} {F : E' → E'} {V : Set E} {U : Set E'}
    (hV : IsOpen V) (hU : IsOpen U) (hf : ContinuousOn f V) (hfi : InjOn f V)
    (hF : ContinuousOn F U) (hFi : InjOn F U)
    {x : E} (hx : x ∈ V) (hUx : euclideanProductPoint d x 0 ∈ U)
    (htrace : ∀ y ∈ U, (euclideanProductChart d y).2 = 0 →
      F y = euclideanProductPoint d (f (euclideanProductChart d y).1) 0)
    (hpos : ∀ y ∈ U, 0 < (euclideanProductChart d y).2 →
      0 < (euclideanProductChart d (F y)).2)
    (hneg : ∀ y ∈ U, (euclideanProductChart d y).2 < 0 →
      (euclideanProductChart d (F y)).2 < 0) :
    embeddingOrientationParity hU hF hFi ⟨euclideanProductPoint d x 0, hUx⟩ =
      embeddingOrientationParity hV hf hfi ⟨x, hx⟩ := by
  let a := euclideanProductPoint d x 0
  let e := Homeomorph.addRight (-x)
  let c := Homeomorph.addRight (-a)
  have he (z : E) : e z = z - x := (sub_eq_add_neg z x).symm
  have hc (z : E') : c z = z - a := (sub_eq_add_neg z a).symm
  have hei (z : E) : e.symm z = z + x := by
    apply e.injective
    rw [e.apply_symm_apply, he, add_sub_cancel_right]
  have hci (z : E') : c.symm z = z + a := by
    apply c.injective
    rw [c.apply_symm_apply, hc, add_sub_cancel_right]
  have he0 : e x = 0 := by rw [he, sub_self]
  have hc0 : c a = 0 := by rw [hc, sub_self]
  let V' := e.symm ⁻¹' V
  let U' := c.symm ⁻¹' U
  let g := e ∘ f ∘ e.symm
  let G := c ∘ F ∘ c.symm
  have hV' : IsOpen V' := hV.preimage e.symm.continuous
  have hU' : IsOpen U' := hU.preimage c.symm.continuous
  have hV0 : (0 : E) ∈ V' := by
    change e.symm 0 ∈ V
    rwa [hei, zero_add]
  have hU0 : (0 : E') ∈ U' := by
    change c.symm 0 ∈ U
    rw [hci, zero_add]
    exact hUx
  have hg : ContinuousOn g V' := e.continuous.comp_continuousOn
    (hf.comp e.symm.continuous.continuousOn (fun _ hz => hz))
  have hG : ContinuousOn G U' := c.continuous.comp_continuousOn
    (hF.comp c.symm.continuous.continuousOn (fun _ hz => hz))
  have hgi : InjOn g V' := fun z hz w hw hzw =>
    e.symm.injective (hfi hz hw (e.injective hzw))
  have hGi : InjOn G U' := fun z hz w hw hzw =>
    c.symm.injective (hFi hz hw (c.injective hzw))
  have hca : euclideanProductChart d a = (x, 0) :=
    (euclideanProductChart d).apply_symm_apply (x, 0)
  have hin (y : E') : euclideanProductChart d (c.symm y) =
      ((euclideanProductChart d y).1 + x, (euclideanProductChart d y).2) := by
    rw [hci, map_add, hca]
    ext <;> simp
  have hout (y : E') :
      (euclideanProductChart d (c y)).2 = (euclideanProductChart d y).2 := by
    rw [hc, map_sub, hca]
    change (euclideanProductChart d y).2 - 0 = _
    exact sub_zero _
  have hGtrace : ∀ y ∈ U', (euclideanProductChart d y).2 = 0 →
      G y = euclideanProductPoint d (g (euclideanProductChart d y).1) 0 := by
    intro y hy hy0
    have hyi : (euclideanProductChart d (c.symm y)).2 = 0 := by rwa [hin]
    change c (F (c.symm y)) = euclideanProductPoint d (e (f (e.symm _))) 0
    rw [hc, htrace (c.symm y) hy hyi, he, hei, hin]
    change (euclideanProductChart d).symm (f ((euclideanProductChart d y).1 + x), 0) -
        (euclideanProductChart d).symm (x, 0) =
      (euclideanProductChart d).symm (f ((euclideanProductChart d y).1 + x) - x, 0)
    rw [← map_sub]
    congr 1
    ext <;> simp
  have hGpos : ∀ y ∈ U', 0 < (euclideanProductChart d y).2 →
      0 < (euclideanProductChart d (G y)).2 := by
    intro y hy hp
    change 0 < (euclideanProductChart d (c (F (c.symm y)))).2
    rw [hout]
    exact hpos (c.symm y) hy (by rwa [hin])
  have hGneg : ∀ y ∈ U', (euclideanProductChart d y).2 < 0 →
      (euclideanProductChart d (G y)).2 < 0 := by
    intro y hy hn
    change (euclideanProductChart d (c (F (c.symm y)))).2 < 0
    rw [hout]
    exact hneg (c.symm y) hy (by rwa [hin])
  have hmid := embeddingOrientationParity_eq_of_boundary_trace hV' hU' hg hgi hG hGi
    hV0 hU0 hGtrace hGpos hGneg
  have hgchar : embeddingOrientationParity hV' hg hgi ⟨0, hV0⟩ =
      embeddingOrientationParity hV hf hfi ⟨x, hx⟩ := by
    simpa only [he0] using embeddingOrientationParity_conj_homeomorph e hV hf hfi ⟨x, hx⟩
  have hGchar : embeddingOrientationParity hU' hG hGi ⟨0, hU0⟩ =
      embeddingOrientationParity hU hF hFi ⟨a, hUx⟩ := by
    simpa only [hc0] using embeddingOrientationParity_conj_homeomorph c hU hF hFi ⟨a, hUx⟩
  exact hGchar.symm.trans (hmid.trans hgchar)

end DifferentialGeometry.LocalDegree
