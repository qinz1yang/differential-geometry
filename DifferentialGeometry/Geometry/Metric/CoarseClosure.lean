import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Metric

namespace GC.MetricGeometry

theorem le_on_closure_of_coarse_bound {X : Type*} [PseudoMetricSpace X]
    {s U : Set X} (hU : IsOpen U) {f : X → ℝ} {A δ : ℝ}
    (hsource : ∀ x ∈ s ∩ U, f x ≤ A)
    (hcoarse : ∀ x ∈ U, ∀ y ∈ U, |f x - f y| ≤ dist x y + δ)
    {x : X} (hx : x ∈ closure s ∩ U) : f x ≤ A + δ := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx.2
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx.1 (min ε r) (lt_min hε hr)
  have hyU : y ∈ U := hball (by rw [mem_ball, dist_comm]; exact hxy.trans_le (min_le_right _ _))
  have hfy := hsource y ⟨hy, hyU⟩
  have hh := hcoarse x hx.2 y hyU
  have he : dist x y < ε := hxy.trans_le (min_le_left _ _)
  linarith [(abs_le.mp hh).2]

end GC.MetricGeometry
