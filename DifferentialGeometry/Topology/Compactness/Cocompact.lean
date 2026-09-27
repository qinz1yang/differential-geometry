import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Order.Filter.AtTopBot.Tendsto

set_option autoImplicit false
open Set Filter
open scoped Topology

variable {X Y ι L : Type*} [TopologicalSpace X]

theorem Continuous.comap_nhds_le_cocompact [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) {q : Y} (hq : q ∉ range f) :
    comap f (𝓝 q) ≤ cocompact X := by
  intro s hs
  obtain ⟨K, hK, hKs⟩ := mem_cocompact.mp hs
  apply Filter.mem_comap.mpr
  refine ⟨(f '' K)ᶜ, (hK.image hf).isClosed.isOpen_compl.mem_nhds ?_, ?_⟩
  · rintro ⟨x, _, hx⟩
    exact hq ⟨x, hx⟩
  · intro x hx
    apply hKs
    intro hxK
    exact hx ⟨x, hxK, rfl⟩

theorem tendsto_atTop_of_compact_cover [Preorder L]
    {K : ι → Set X} (hK : ∀ i, IsCompact (K i))
    {a : ι → L} (ha : Tendsto a cofinite atTop)
    {f : X → L} (hbound : ∀ᶠ i in cofinite, ∀ x ∈ K i, a i ≤ f x) :
    Tendsto f (cocompact X ⊓ 𝓟 (⋃ i, K i)) atTop := by
  apply tendsto_atTop.2
  intro b
  have hfin : {i | ¬ (b ≤ a i ∧ ∀ x ∈ K i, a i ≤ f x)}.Finite :=
    (ha.eventually_ge_atTop b).and hbound
  have hc : IsCompact (⋃ i ∈ {i | ¬ (b ≤ a i ∧ ∀ x ∈ K i, a i ≤ f x)}, K i) :=
    hfin.isCompact_biUnion (fun i _ => hK i)
  filter_upwards [Filter.mem_inf_of_left hc.compl_mem_cocompact,
    Filter.mem_inf_of_right (Filter.mem_principal_self (⋃ i, K i))] with x hx hxK
  obtain ⟨i, hi⟩ := mem_iUnion.mp hxK
  have hbi : b ≤ a i ∧ ∀ x ∈ K i, a i ≤ f x := by
    by_contra hbi
    exact hx (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hbi, hi⟩⟩)
  exact hbi.1.trans (hbi.2 x hi)
