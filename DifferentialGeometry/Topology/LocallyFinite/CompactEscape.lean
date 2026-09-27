import DifferentialGeometry.Topology.LocallyFinite.Superlevel
import Mathlib.Topology.Compactness.LocallyFinite

set_option autoImplicit false
open Set Filter
open scoped Topology

namespace UpperSemicontinuous

theorem eventually_disjoint_compact_of_tendsto_lower_bound
    {X L ι : Type*} [TopologicalSpace X] [Preorder L] [NoMaxOrder L]
    {f : X → L} (hf : UpperSemicontinuous f) {a : ι → L}
    (ha : Tendsto a cofinite atTop) (s : ι → Set X)
    (hbound : ∀ i, ∀ x ∈ s i, a i ≤ f x) {K : Set X} (hK : IsCompact K) :
    ∀ᶠ i in cofinite, Disjoint (s i) K := by
  have hloc := hf.locallyFinite_of_tendsto_lower_bound ha s hbound
  have hfin := hloc.finite_nonempty_inter_compact hK
  filter_upwards [hfin.compl_mem_cofinite] with i hi
  rw [Set.disjoint_iff_inter_eq_empty]
  exact Set.not_nonempty_iff_eq_empty.mp hi

end UpperSemicontinuous
