import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Constructions.SumProd

open Set

namespace IsCompact

theorem exists_subset_closed_interval_prod
    {X : Type*} [TopologicalSpace X] {S : Set (ℝ × X)} (hS : IsCompact S)
    {a c : ℝ} {W : Set X} (hSW : S ⊆ Ioo a c ×ˢ W) :
    ∃ a' c' : ℝ, ∃ K : Set X, a < a' ∧ c' < c ∧ IsCompact K ∧ K ⊆ W ∧
      S ⊆ Icc a' c' ×ˢ K := by
  obtain ⟨a', haa, ha'⟩ := hS.exists_forall_le' continuous_fst.continuousOn
    (fun z hz => (hSW hz).1.1)
  obtain ⟨c', hcc, hc'⟩ := hS.exists_forall_le' (α := ℝᵒᵈ) continuous_fst.continuousOn
    (fun z hz => (hSW hz).1.2)
  refine ⟨a', c', Prod.snd '' S, haa, hcc, hS.image continuous_snd, ?_, ?_⟩
  · rintro y ⟨z, hz, rfl⟩
    exact (hSW hz).2
  · intro z hz
    exact ⟨⟨ha' z hz, hc' z hz⟩, mem_image_of_mem _ hz⟩

end IsCompact
