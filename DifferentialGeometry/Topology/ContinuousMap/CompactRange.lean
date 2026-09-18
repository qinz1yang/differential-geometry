import DifferentialGeometry.Topology.UniformConvergence
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

open Filter Set

namespace TendstoUniformlyOn

variable {X S A E : Type*} [TopologicalSpace A] [CompactSpace A]
  [PseudoMetricSpace E] {l : Filter X} {K : Set S}
  {q : X → S → C(A, E)} {q₀ : S → C(A, E)}

theorem continuousMap_eval (hq : TendstoUniformlyOn q q₀ l K) :
    TendstoUniformlyOn (fun x (p : S × A) => q x p.1 p.2)
      (fun p : S × A => q₀ p.1 p.2) l (K ×ˢ univ) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hq ε hε] with x hx p hp
  exact (ContinuousMap.dist_apply_le_dist p.2).trans_lt (hx p.1 hp.1)

variable [TopologicalSpace S] [LocallyCompactSpace E]

theorem exists_isCompact_eventually_forall_eval_mem
    (hq : TendstoUniformlyOn q q₀ l K) (hK : IsCompact K)
    (hq₀ : ContinuousOn q₀ K) {U : Set E} (hU : IsOpen U)
    (hmap : ∀ s ∈ K, ∀ a, q₀ s a ∈ U) :
    ∃ L : Set E, IsCompact L ∧ L ⊆ U ∧
      (∀ s ∈ K, ∀ a, q₀ s a ∈ interior L) ∧
      ∀ᶠ x in l, ∀ s ∈ K, ∀ a, q x s a ∈ L := by
  have hq₀eval : ContinuousOn (fun p : S × A => q₀ p.1 p.2) (K ×ˢ univ) :=
    continuous_eval.comp_continuousOn (hq₀.prodMap continuousOn_id)
  have hq₀U : MapsTo (fun p : S × A => q₀ p.1 p.2) (K ×ˢ univ) U :=
    fun p hp => hmap p.1 hp.1 p.2
  obtain ⟨L, hL, hLU, hq₀L, hqL⟩ :=
    hq.continuousMap_eval.exists_isCompact_eventually_mapsTo_of_isCompact
      (hK.prod isCompact_univ) hq₀eval hU hq₀U
  refine ⟨L, hL, hLU, ?_, ?_⟩
  · intro s hs a
    exact hq₀L (x := (s, a)) ⟨hs, mem_univ a⟩
  · filter_upwards [hqL] with x hx s hs a
    exact hx (x := (s, a)) ⟨hs, mem_univ a⟩

end TendstoUniformlyOn
