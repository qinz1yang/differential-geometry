import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology

namespace Metric

theorem exists_isometry_of_compact_approximation
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y]
    {ι : Type*} {l : Filter ι} [l.NeBot] (f : ι → X → Y)
    {eps : ι → ℝ} (heps : Tendsto eps l (𝓝 0))
    (hdist : ∀ᶠ i in l, ∀ x y, |dist (f i x) (f i y) - dist x y| ≤ eps i)
    (p : X) (R : ℝ)
    (hcover : ∀ᶠ i in l, ∀ y ∈ ball (f i p) R, ∃ x, dist y (f i x) ≤ eps i) :
    ∃ F : X → Y, Isometry F ∧ ball (F p) R ⊆ range F := by
  classical
  obtain ⟨F, _, hF⟩ := (isCompact_univ : IsCompact (univ : Set (X → Y))).exists_mapClusterPt
    (u := f) (f := l) (by simp)
  obtain ⟨U, hUl, hFU⟩ := mapClusterPt_iff_ultrafilter.mp hF
  have hconv (x : X) : Tendsto (fun i => f i x) U (𝓝 (F x)) :=
    (continuous_apply x).tendsto F |>.comp hFU
  have hFiso : Isometry F := by
    apply Isometry.of_dist_eq
    intro x y
    have hh : |dist (F x) (F y) - dist x y| ≤ 0 :=
      le_of_tendsto_of_tendsto (((hconv x).dist (hconv y)).sub tendsto_const_nhds).abs
        (heps.mono_left hUl) (Filter.Eventually.mono (hUl hdist) fun i hi => hi x y)
    exact sub_eq_zero.mp (abs_nonpos_iff.mp hh)
  refine ⟨F, hFiso, ?_⟩
  intro y hy
  change dist y (F p) < R at hy
  have hyU : ∀ᶠ i in (U : Filter ι), dist y (f i p) < R :=
    ((tendsto_const_nhds.dist (hconv p)).eventually (eventually_lt_nhds hy))
  let z (i : ι) : X := if h : ∃ x, dist y (f i x) ≤ eps i then h.choose else p
  have hz : ∀ᶠ i in (U : Filter ι), dist y (f i (z i)) ≤ eps i := by
    filter_upwards [hUl hcover, hyU] with i hi hiy
    have hex : ∃ x, dist y (f i x) ≤ eps i := hi y hiy
    simpa only [z, dif_pos hex] using hex.choose_spec
  obtain ⟨x, _, hx⟩ := (isCompact_univ : IsCompact (univ : Set X)).exists_mapClusterPt
    (u := z) (f := (U : Filter ι)) (by simp)
  obtain ⟨V, hVU, hxV⟩ := mapClusterPt_iff_ultrafilter.mp hx
  have heV := heps.mono_left (hVU.trans hUl)
  have hfxV := (hconv x).mono_left hVU
  have hzV := tendsto_iff_dist_tendsto_zero.mp hxV
  have hsum : Tendsto (fun i => eps i + (dist (z i) x + eps i) + dist (f i x) (F x))
      V (𝓝 (0 : ℝ)) := by
    simpa only [zero_add, add_zero] using
      (heV.add (hzV.add heV)).add (tendsto_iff_dist_tendsto_zero.mp hfxV)
  have hle : ∀ᶠ i in (V : Filter ι),
      dist y (F x) ≤ eps i + (dist (z i) x + eps i) + dist (f i x) (F x) := by
    filter_upwards [hVU hz, hVU (hUl hdist)] with i hi hdi
    have hd := (abs_le.mp (hdi (z i) x)).2
    have ht := dist_triangle4 y (f i (z i)) (f i x) (F x)
    linarith only [hi, hd, ht]
  have heq : y = F x := dist_le_zero.mp (le_of_tendsto_of_tendsto tendsto_const_nhds hsum hle)
  exact ⟨x, heq.symm⟩

end Metric
