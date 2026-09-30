import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace Metric

theorem exists_isometry_of_local_distortion
    {D Y : Type*} [MetricSpace D] [MetricSpace Y] [ProperSpace Y]
    (p : D) {K : Set Y} (hK : IsCompact K)
    (g : ℕ → D → Y) (hbase : ∀ n, g n p ∈ K)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hdist : ∀ S : ℝ, ∀ᶠ n in atTop, ∀ s t : D,
      dist s p ≤ S → dist t p ≤ S → |dist (g n s) (g n t) - dist s t| ≤ ε n) :
    ∃ F : D → Y, Isometry F ∧ F p ∈ K := by
  classical
  let q := g 0 p
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall q
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  have hcompact (x : D) :
      ∃ y ∈ closedBall q (R + dist x p + 1), Tendsto (fun n => g n x) U (𝓝 y) := by
    apply (isCompact_closedBall q (R + dist x p + 1)).ultrafilter_le_nhds
      (Ultrafilter.map (fun n => g n x) U)
    apply le_principal_iff.mpr
    change ∀ᶠ n in (U : Filter ℕ), g n x ∈ closedBall q (R + dist x p + 1)
    apply hU
    filter_upwards [hdist (dist x p), hε.eventually
      (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))] with n hn he
    have hh := hn x p le_rfl (by simp)
    have hb : dist (g n p) q ≤ R := hR (hbase n)
    change dist (g n x) q ≤ R + dist x p + 1
    linarith [(abs_le.mp hh).2, dist_triangle (g n x) (g n p) q]
  choose F hFball hconv using hcompact
  refine ⟨F, Isometry.of_dist_eq (fun s t => ?_), ?_⟩
  · have hh : ∀ᶠ n in (U : Filter ℕ), |dist (g n s) (g n t) - dist s t| ≤ ε n := by
      filter_upwards [hU (hdist (max (dist s p) (dist t p)))] with n hn
      exact hn s t (le_max_left _ _) (le_max_right _ _)
    have hzero : |dist (F s) (F t) - dist s t| ≤ 0 :=
      le_of_tendsto_of_tendsto (((hconv s).dist (hconv t)).sub tendsto_const_nhds).abs
        (hε.mono_left hU) hh
    exact sub_eq_zero.mp (abs_nonpos_iff.mp hzero)
  · exact hK.isClosed.mem_of_tendsto (hconv p) (Eventually.of_forall hbase)

end Metric
