import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Metric

theorem eventually_mapsTo_ball_of_approximation
    {X Z ι : Type*} [PseudoMetricSpace Z]
    {Y : ι → Type*} [∀ i, PseudoMetricSpace (Y i)] {l : Filter ι}
    {S : Set X} (f : ∀ i, X → Y i) (q : ∀ i, Y i → Z)
    (g : X → Z) (c : Z) (b : ∀ i, Y i) {r R : ℝ} (hrR : r < R)
    (hbound : ∀ x ∈ S, dist (g x) c ≤ r)
    (hconv : TendstoUniformlyOn (fun i x ↦ q i (f i x)) g l S)
    (hcenter : Tendsto (fun i ↦ q i (b i)) l (𝓝 c))
    (ε : ι → ℝ) (hε : Tendsto ε l (𝓝 0))
    (hdist : ∀ᶠ i in l, ∀ x ∈ S,
      dist (f i x) (b i) ≤ dist (q i (f i x)) (q i (b i)) + ε i) :
    ∀ᶠ i in l, MapsTo (f i) S (ball (b i) R) := by
  let η := (R - r) / 3
  have hη : 0 < η := by dsimp [η]; linarith
  have hf := tendstoUniformlyOn_iff.mp hconv η hη
  have hb := hcenter.eventually (ball_mem_nhds c hη)
  have he := hε.eventually (gt_mem_nhds hη)
  filter_upwards [hf, hb, he, hdist] with i hfi hbi hei hdi
  intro x hx
  have hfx : dist (q i (f i x)) (g x) < η := by
    simpa only [dist_comm] using hfi x hx
  have hbx : dist c (q i (b i)) < η := by
    simpa only [mem_ball, dist_comm] using hbi
  have htriangle := dist_triangle4 (q i (f i x)) (g x) c (q i (b i))
  have hradial := hbound x hx
  have hcomparison := hdi x hx
  change dist (f i x) (b i) < R
  dsimp [η] at hfx hbx hei
  linarith

end Metric
