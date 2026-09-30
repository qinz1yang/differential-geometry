import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

noncomputable section
open Set Filter
open scoped Topology

namespace Real

def firstPositiveLevel (f : ℝ → ℝ) (w : ℝ) : ℝ :=
  sInf {r : ℝ | 0 < r ∧ f r = w}

private theorem exists_initial_interval_above {f : ℝ → ℝ} {c w : ℝ}
    (h : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 c)) (hw : w < c) :
    ∃ a > 0, ∀ r, 0 < r → r ≤ a → w < f r := by
  obtain ⟨ε, hε, he⟩ := Metric.tendsto_nhdsWithin_nhds.mp h (c - w) (sub_pos.mpr hw)
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro r hr hra
  have hd : dist r 0 < ε := by rw [Real.dist_eq, sub_zero, abs_of_pos hr]; linarith
  have hh := he hr hd
  rw [Real.dist_eq] at hh
  have := (abs_lt.mp hh).1
  linarith

theorem firstPositiveLevel_spec {f : ℝ → ℝ} {c w : ℝ}
    (hf : ContinuousOn f (Ioi 0))
    (hzero : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 c))
    (hinfty : Tendsto f atTop (𝓝 0)) (hw : 0 < w) (hwc : w < c) :
    0 < firstPositiveLevel f w ∧ f (firstPositiveLevel f w) = w ∧
      ∀ r, 0 < r → r < firstPositiveLevel f w → w < f r := by
  obtain ⟨a, ha, hnear⟩ := exists_initial_interval_above hzero hwc
  obtain ⟨b, hb⟩ := (eventually_atTop.1 (hinfty.eventually (eventually_lt_nhds hw)))
  let B := max a b
  have haB : a ≤ B := le_max_left _ _
  have hB : f B < w := hb B (le_max_right _ _)
  have hc : ContinuousOn f (Icc a B) := hf.mono (fun r hr => ha.trans_le hr.1)
  obtain ⟨r, hr, hfr⟩ := intermediate_value_Icc' haB hc
    ⟨hB.le, (hnear a ha le_rfl).le⟩
  let S : Set ℝ := {r | 0 < r ∧ f r = w}
  have hS : S.Nonempty := ⟨r, ha.trans_le hr.1, hfr⟩
  have hlow : ∀ r ∈ S, a ≤ r := by
    intro r hr
    by_contra! h
    exact (hnear r hr.1 h.le).ne' hr.2
  have hclosed : IsClosed (Icc a B ∩ f ⁻¹' {w}) :=
    hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hcompact : IsCompact (Icc a B ∩ f ⁻¹' {w}) :=
    isCompact_Icc.of_isClosed_subset hclosed inter_subset_left
  obtain ⟨s, hs, hleast⟩ := hcompact.exists_isLeast ⟨r, hr, hfr⟩
  have hsS : s ∈ S := ⟨ha.trans_le hs.1.1, hs.2⟩
  have hleastS : IsLeast S s := by
    refine ⟨hsS, ?_⟩
    intro r hr
    by_cases hrB : r ≤ B
    · exact hleast ⟨⟨hlow r hr, hrB⟩, hr.2⟩
    · exact hs.1.2.trans (le_of_not_ge hrB)
  have heq : firstPositiveLevel f w = s := hleastS.csInf_eq
  rw [heq]
  refine ⟨hsS.1, hsS.2, ?_⟩
  intro t ht hts
  by_contra! htw
  by_cases hta : t ≤ a
  · exact (hnear t ht hta).not_ge htw
  · have hat : a ≤ t := le_of_not_ge hta
    obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc' hat
      (hf.mono (fun x hx => ha.trans_le hx.1)) ⟨htw, (hnear a ha le_rfl).le⟩
    have hsu := hleastS.2 (show u ∈ S from ⟨ha.trans_le hu.1, hfu⟩)
    linarith [hu.2]

theorem firstPositiveLevel_strictAntiOn {f : ℝ → ℝ} {c : ℝ}
    (hf : ContinuousOn f (Ioi 0))
    (hzero : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 c))
    (hinfty : Tendsto f atTop (𝓝 0)) :
    StrictAntiOn (firstPositiveLevel f) (Ioo 0 c) := by
  intro u hu v hv huv
  obtain ⟨hru, heu, hbu⟩ := firstPositiveLevel_spec hf hzero hinfty hu.1 hu.2
  obtain ⟨hrv, hev, hbv⟩ := firstPositiveLevel_spec hf hzero hinfty hv.1 hv.2
  by_contra! h
  rcases h.eq_or_lt with h | h
  · rw [← h, heu] at hev
    exact huv.ne hev
  · have hh := hbv _ hru h
    rw [heu] at hh
    linarith

end Real
