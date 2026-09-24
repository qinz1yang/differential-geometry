import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Semicontinuity.Defs
import Mathlib.Order.Filter.Cofinite
import Mathlib.Order.Filter.AtTopBot.Tendsto

open Set Filter Topology

namespace UpperSemicontinuous

theorem locallyFinite_of_tendsto_lower_bound
    {X L ι : Type*} [TopologicalSpace X] [Preorder L] [NoMaxOrder L]
    {f : X → L} (hf : UpperSemicontinuous f) {a : ι → L}
    (ha : Tendsto a cofinite atTop) (s : ι → Set X)
    (hbound : ∀ i, ∀ x ∈ s i, a i ≤ f x) : LocallyFinite s := by
  intro x
  obtain ⟨b, hb⟩ := exists_gt (f x)
  refine ⟨{y | f y < b}, hf x b hb, ?_⟩
  apply (Filter.eventually_cofinite.mp (ha.eventually_ge_atTop b)).subset
  rintro i ⟨y, hy, hyb⟩ hi
  exact (not_lt_of_ge (hi.trans (hbound i y hy))) hyb

end UpperSemicontinuous
