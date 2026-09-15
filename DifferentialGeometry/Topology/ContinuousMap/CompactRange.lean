import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.ContinuousMap.Compact

open Set Metric

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
  [PseudoMetricSpace Y] [LocallyCompactSpace Y]

theorem exists_isCompact_range_subset_of_dist_le
    (f : C(X, Y)) {U : Set Y} (hU : IsOpen U) (hf : range f ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ K : Set Y, IsCompact K ∧ K ⊆ U ∧
      ∀ g : C(X, Y), dist g f ≤ δ → range g ⊆ K := by
  have hcompact : IsCompact (range f) := isCompact_range f.continuous
  obtain ⟨ε, hε, hεU⟩ := hcompact.exists_cthickening_subset_open hU hf
  obtain ⟨η, hη, hηcompact⟩ := hcompact.exists_isCompact_cthickening
  let δ := min ε η
  refine ⟨δ, lt_min hε hη, cthickening δ (range f), ?_, ?_, ?_⟩
  · exact hηcompact.of_isClosed_subset isClosed_cthickening
      (cthickening_mono (min_le_right ε η) (range f))
  · exact (cthickening_mono (min_le_left ε η) (range f)).trans hεU
  · intro g hg y hy
    obtain ⟨x, rfl⟩ := hy
    exact mem_cthickening_of_dist_le (g x) (f x) δ (range f)
      (mem_range_self x) ((dist_apply_le_dist x).trans hg)

end ContinuousMap

theorem ContinuousAt.exists_isCompact_range_subset
    {X Y Z : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [LocallyCompactSpace Y] [TopologicalSpace Z]
    {F : Z → C(X, Y)} {z : Z} (hF : ContinuousAt F z)
    {U : Set Y} (hU : IsOpen U) (hz : range (F z) ⊆ U) :
    ∃ K : Set Y, IsCompact K ∧ K ⊆ U ∧
      ∀ᶠ w in nhds z, range (F w) ⊆ K := by
  obtain ⟨K, hK, hzK, hKU⟩ :=
    exists_compact_between (isCompact_range (F z).continuous) hU hz
  refine ⟨K, hK, hKU, ?_⟩
  exact (hF.eventually
    (ContinuousMap.eventually_range_subset isOpen_interior hzK)).mono
      fun w hw => hw.trans interior_subset
