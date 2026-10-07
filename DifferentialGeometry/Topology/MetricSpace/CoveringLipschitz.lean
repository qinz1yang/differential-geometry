import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.SeparatedMap
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open scoped Topology NNReal

namespace Metric

theorem exists_nhds_edist_le_of_image_ball
    {X B : Type*} [PseudoMetricSpace X] [PseudoEMetricSpace B] {p : X → B}
    (hp : IsLocallyInjective p)
    (hball : ∀ x r, 0 < r → p '' Metric.ball x r = Metric.eball (p x) (ENNReal.ofReal r))
    (x : X) :
    ∃ V ∈ 𝓝 x, ∀ u ∈ V, ∀ v ∈ V, edist u v ≤ edist (p u) (p v) := by
  obtain ⟨U, hU, hxU, hinj⟩ := hp x
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hxU)
  refine ⟨Metric.ball x (r / 4), Metric.ball_mem_nhds x (by positivity), ?_⟩
  intro u hu v hv
  by_contra hnot
  have hlt : edist (p u) (p v) < edist u v := lt_of_not_ge hnot
  have hpv : p v ∈ Metric.eball (p u) (ENNReal.ofReal (dist u v)) := by
    simpa only [Metric.mem_eball, edist_comm, edist_dist] using hlt
  have hdist : 0 < dist u v := ENNReal.ofReal_pos.mp (by
    simpa only [edist_dist] using ((show 0 ≤ edist (p u) (p v) from zero_le).trans_lt hlt))
  rw [← hball u (dist u v) hdist] at hpv
  obtain ⟨w, hw, hpw⟩ := hpv
  have hu' : dist u x < r / 4 := hu
  have hv' : dist v x < r / 4 := hv
  have hw' : dist w u < dist u v := hw
  have huv : dist u v < r / 2 := by
    have h := dist_triangle u x v
    rw [dist_comm x v] at h
    linarith
  have hwU : w ∈ U := by
    apply hsub
    have h := dist_triangle w u x
    change dist w x < r
    linarith
  have hvU : v ∈ U := hsub (by change dist v x < r; linarith)
  have hwv : w = v := hinj hwU hvU hpw
  rw [hwv, dist_comm v u] at hw'
  exact (lt_irrefl _ hw')

theorem exists_lipschitzOnWith_nhds_of_comp
    {X Y B : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    [PseudoEMetricSpace B] {f : X → Y} {p : Y → B} {L : ℝ≥0}
    (hf : Continuous f)
    (hp : ∀ y, ∃ V ∈ 𝓝 y, ∀ u ∈ V, ∀ v ∈ V, edist u v ≤ edist (p u) (p v))
    (hcomp : LipschitzWith L (p ∘ f)) (x : X) :
    ∃ U ∈ 𝓝 x, LipschitzOnWith L f U := by
  obtain ⟨V, hV, hpV⟩ := hp (f x)
  refine ⟨f ⁻¹' V, hf.continuousAt.preimage_mem_nhds hV, ?_⟩
  intro u hu v hv
  exact (hpV (f u) hu (f v) hv).trans (hcomp u v)

end Metric
