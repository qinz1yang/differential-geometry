import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Calculus.ContDiff.Basic

set_option autoImplicit false
noncomputable section
open Set Metric

namespace Metric

theorem biUnion_ball_of_mem_ball_eq_ball_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : E) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (⋃ v ∈ ball c a, ball v b) = ball c (a + b) := by
  rw [← thickening_eq_biUnion_ball, _root_.thickening_ball hb ha, add_comm b a]

end Metric

namespace DifferentialGeometry.Analysis

theorem contDiffOn_iUnion_ball_add_of_contDiffOn_neighborhoods
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : WithTop ℕ∞} (f : E → F) (c : ι → E) (a b : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hf : ∀ i, ∀ v ∈ ball (c i) (a i), ContDiffOn ℝ n f (ball v (b i))) :
    ContDiffOn ℝ n f (⋃ i, ball (c i) (a i + b i)) := by
  intro x hx
  obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
  rw [← Metric.biUnion_ball_of_mem_ball_eq_ball_add (c i) (ha i) (hb i)] at hxi
  obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hxi
  exact ((hf i v hv).contDiffAt (isOpen_ball.mem_nhds hxv)).contDiffWithinAt

end DifferentialGeometry.Analysis
