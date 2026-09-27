import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.MetricSpace.Pseudo.Basic

open Set Filter

namespace IsCompact

variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_segment_subset_open {K U : Set F} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a ∈ K, ∀ b : F, ‖a - b‖ < ε → segment ℝ a b ⊆ U := by
  obtain ⟨ε, hε, hεU⟩ := hK.exists_thickening_subset_open hU hKU
  refine ⟨ε, hε, ?_⟩
  intro a ha b hab
  have hb : b ∈ Metric.ball a ε := by
    rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]
    exact hab
  exact ((convex_ball a ε).segment_subset (Metric.mem_ball_self hε) hb).trans
    ((Metric.ball_subset_thickening ha ε).trans hεU)

theorem eventually_segment_subset_open_of_tendstoUniformlyOn_sub
    {ι α : Type*} {l : Filter ι} {S : Set α} {K U : Set F}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {a b : ι → α → F} (ha : ∀ᶠ n in l, MapsTo (a n) S K)
    (hclose : TendstoUniformlyOn (fun n x => a n x - b n x) (fun _ => 0) l S) :
    ∀ᶠ n in l, ∀ x ∈ S, segment ℝ (a n x) (b n x) ⊆ U := by
  obtain ⟨ε, hε, hεU⟩ := hK.exists_segment_subset_open hU hKU
  filter_upwards [ha, (Metric.tendstoUniformlyOn_iff.mp hclose) ε hε] with n han hn
  intro x hx
  apply hεU (a n x) (han hx) (b n x)
  simpa only [dist_eq_norm, zero_sub, norm_neg] using hn x hx

theorem eventually_mapsTo_interpolation_cylinder_of_tendstoUniformlyOn_sub
    {ι α : Type*} {l : Filter ι} {S : Set α} {K U : Set F}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {a b : ι → α → F} (ha : ∀ᶠ n in l, MapsTo (a n) S K)
    (hclose : TendstoUniformlyOn (fun n x => a n x - b n x) (fun _ => 0) l S)
    (h : ι → ℝ) :
    ∀ᶠ n in l, MapsTo
      (fun p : α × ℝ => (1 - p.2 / h n) • a n p.1 + (p.2 / h n) • b n p.1)
      (S ×ˢ Icc 0 (h n)) U := by
  filter_upwards [hK.eventually_segment_subset_open_of_tendstoUniformlyOn_sub
    hU hKU ha hclose] with n hn
  intro p hp
  apply hn p.1 hp.1
  have hhn : 0 ≤ h n := hp.2.1.trans hp.2.2
  have ht : p.2 / h n ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hp.2.1 hhn, div_le_one_of_le₀ hp.2.2 hhn⟩
  simpa only [AffineMap.lineMap_apply_module] using
    (lineMap_mem_segment ℝ (a n p.1) (b n p.1) ht)

end IsCompact
