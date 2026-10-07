import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

open Filter
open scoped ENNReal Topology

namespace MeasureTheory

theorem continuousAt_measure_ball_of_continuousAt_radius
    {X F : Type*} [PseudoMetricSpace X]
    [FunLike F (Set X) ℝ≥0∞] [OuterMeasureClass F X]
    (μ : F) {x : X} {r : ℝ}
    (h : ContinuousAt (fun s : ℝ ↦ μ (Metric.ball x s)) r) :
    ContinuousAt (fun z : X × ℝ ↦ μ (Metric.ball z.1 z.2)) (x, r) := by
  have hd : Continuous (fun z : X × ℝ ↦ dist x z.1) :=
    continuous_const.dist continuous_fst
  have hlo : Tendsto (fun z : X × ℝ ↦ z.2 - dist x z.1) (𝓝 (x, r)) (𝓝 r) := by
    simpa only [Pi.sub_def, dist_self, sub_zero] using (continuous_snd.sub hd).tendsto (x, r)
  have hhi : Tendsto (fun z : X × ℝ ↦ z.2 + dist x z.1) (𝓝 (x, r)) (𝓝 r) := by
    simpa only [Pi.add_def, dist_self, add_zero] using (continuous_snd.add hd).tendsto (x, r)
  exact (h.tendsto.comp hlo).squeeze (h.tendsto.comp hhi)
    (fun z ↦ measure_mono (Metric.ball_subset_ball' (sub_add_cancel _ _).le))
    (fun z ↦ measure_mono (Metric.ball_subset_ball' (by rw [dist_comm])))

end MeasureTheory
