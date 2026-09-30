import Mathlib.Topology.MetricSpace.Thickening

open Set Metric

variable {F : Type*} [PseudoEMetricSpace F] [LocallyCompactSpace F]

theorem IsCompact.exists_compact_cthickening_subset {S U : Set F} (hS : IsCompact S)
    (hU : IsOpen U) (hSU : S ⊆ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ IsCompact (cthickening ρ S) ∧ cthickening ρ S ⊆ U := by
  obtain ⟨a, ha, haU⟩ := hS.exists_cthickening_subset_open hU hSU
  obtain ⟨b, hb, hbK⟩ := hS.exists_isCompact_cthickening
  exact ⟨min a b, lt_min ha hb,
    hbK.of_isClosed_subset isClosed_cthickening (cthickening_mono (min_le_right _ _) _),
    (cthickening_mono (min_le_left _ _) _).trans haU⟩
