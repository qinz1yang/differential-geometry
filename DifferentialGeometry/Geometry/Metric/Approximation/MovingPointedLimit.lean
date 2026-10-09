import DifferentialGeometry.Geometry.Metric.Approximation.MarkedPointEvaluation
import DifferentialGeometry.Geometry.Metric.Approximation.TargetBasepointRepair
import Mathlib.Topology.Sequences

set_option autoImplicit false

namespace GC.MetricGeometry

open Set Filter Metric
open scoped Topology

universe u v
variable {X : ℕ → Type u} [∀ i, MetricSpace (X i)]
variable {Y : Type v} [MetricSpace Y] {p c : ∀ i, X i} {q y : Y}
variable {R ε : ℕ → ℝ} {C : ℝ}

theorem pointedGHConverges_of_marked_point_tendsto [CompleteSpace Y]
    (f : ∀ i, PointedBallApprox (p i) q (R i) (ε i))
    (hR : Tendsto R atTop atTop) (hε : Tendsto ε atTop (𝓝 0))
    (hc : ∀ i, dist (c i) (p i) ≤ C)
    (hy : Tendsto (fun i => (f i).extendToWholeSpace (c i)) atTop (𝓝 y)) :
    PointedGHConverges c y := by
  have hη : Tendsto (fun i => dist ((f i).extendToWholeSpace (c i)) y) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp hy
  have hE : Tendsto (fun i => 3 * ε i + 2 * dist ((f i).extendToWholeSpace (c i)) y)
      atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add] using (hε.const_mul 3).add (hη.const_mul 2)
  refine ⟨inferInstance, fun s α hα hαs => ?_⟩
  filter_upwards [hR.eventually (eventually_ge_atTop (C + s)),
    hE.eventually (eventually_lt_nhds hα)] with i hiR hiE
  have hs : 0 < s := hα.trans hαs
  have hci : dist (c i) (p i) ≤ R i := by linarith [hc i]
  have h3 : 3 * ε i < s := by linarith [dist_nonneg (x := (f i).extendToWholeSpace (c i)) (y := y)]
  have hpad : dist (c i) (p i) + s ≤ R i := by linarith [hc i]
  have hval := (f i).extendToWholeSpace_apply (c i) hci
  let G : PointedBallApprox (c i) ((f i).extendToWholeSpace (c i)) s (3 * ε i) := by
    rw [hval]
    exact (f i).recenter (c i) h3 hpad
  let K := G.repairTarget y dist_nonneg le_rfl (hiE.trans hαs)
  exact ⟨K.enlargeError hiE.le hαs⟩

theorem exists_subsequence_moving_pointed_limit [ProperSpace Y]
    (f : ∀ i, PointedBallApprox (p i) q (R i) (ε i))
    (hR : Tendsto R atTop atTop) (hε : Tendsto ε atTop (𝓝 0))
    (hc : ∀ i, dist (c i) (p i) ≤ C) :
    ∃ (y : Y) (χ : ℕ → ℕ), StrictMono χ ∧
      dist y q ≤ C + 1 ∧
      Tendsto (fun i => (f (χ i)).extendToWholeSpace (c (χ i))) atTop (𝓝 y) ∧
      PointedGHConverges (fun i => c (χ i)) y ∧
      ∀ d : ℝ, Tendsto (fun i => dist (c (χ i)) (p (χ i))) atTop (𝓝 d) → dist y q = d := by
  have hbound : ∀ᶠ i in atTop, (f i).extendToWholeSpace (c i) ∈ closedBall q (C + 1) := by
    filter_upwards [eventually_marked_point_radial_error f hR hc,
      hε.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with i hi he
    change dist ((f i).extendToWholeSpace (c i)) q ≤ C + 1
    linarith [(abs_lt.mp hi).2, hc i]
  obtain ⟨y, hyball, χ, hχ, hy⟩ := (isCompact_closedBall q (C + 1)).tendsto_subseq' hbound.frequently
  refine ⟨y, χ, hχ, hyball, hy, ?_, ?_⟩
  · exact pointedGHConverges_of_marked_point_tendsto (fun i => f (χ i))
      (hR.comp hχ.tendsto_atTop) (hε.comp hχ.tendsto_atTop) (fun i => hc (χ i)) hy
  · intro d hd
    exact marked_point_limit_dist (fun i => f (χ i))
      (hR.comp hχ.tendsto_atTop) (hε.comp hχ.tendsto_atTop) (fun i => hc (χ i)) hy hd

end GC.MetricGeometry
