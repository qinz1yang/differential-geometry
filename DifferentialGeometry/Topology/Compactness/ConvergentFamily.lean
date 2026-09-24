import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false
open Set Filter
open scoped Topology

variable {X ι : Type*} [TopologicalSpace X]

theorem isCompact_insert_iUnion_of_eventually_subset {K : ι → Set X} {q : X}
    (hK : ∀ i, IsCompact (K i))
    (hlim : ∀ U ∈ 𝓝 q, ∀ᶠ i in cofinite, K i ⊆ U) :
    IsCompact (insert q (⋃ i, K i)) := by
  classical
  apply isCompact_iff_finite_subcover.mpr
  intro J U hU hcover
  obtain ⟨j, hqj⟩ := mem_iUnion.mp (hcover (mem_insert q _))
  have hfin : {i | ¬ K i ⊆ U j}.Finite := hlim (U j) ((hU j).mem_nhds hqj)
  have hcompact : IsCompact (⋃ i ∈ {i | ¬ K i ⊆ U j}, K i) :=
    hfin.isCompact_biUnion (fun i _ => hK i)
  obtain ⟨s, hs⟩ := hcompact.elim_finite_subcover U hU (by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨_, hxi⟩ := mem_iUnion.mp hi
    exact hcover (mem_insert_of_mem _ (mem_iUnion.mpr ⟨i, hxi⟩)))
  refine ⟨insert j s, ?_⟩
  intro x hx
  rcases hx with rfl | hx
  · exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨Finset.mem_insert_self _ _, hqj⟩⟩
  · obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    by_cases hi : K i ⊆ U j
    · exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨Finset.mem_insert_self _ _, hi hxi⟩⟩
    · obtain ⟨k, hk⟩ := mem_iUnion.mp (hs (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hxi⟩⟩))
      obtain ⟨hks, hxk⟩ := mem_iUnion.mp hk
      exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨Finset.mem_insert_of_mem hks, hxk⟩⟩

theorem insert_iUnion_nat_add_mem_nhds
    {X : Type*} [TopologicalSpace X] {K : ℕ → Set X} {q : X}
    (hK : ∀ n, IsClosed (K n)) (hq : ∀ n, q ∉ K n)
    (hnhds : insert q (⋃ n, K n) ∈ 𝓝 q) (N : ℕ) :
    insert q (⋃ n, K (n + N)) ∈ 𝓝 q := by
  induction N with
  | zero => simpa only [Nat.add_zero] using hnhds
  | succ N ih =>
    filter_upwards [ih, (hK N).isOpen_compl.mem_nhds (hq N)] with x hx hnot
    rcases hx with rfl | hx
    · exact mem_insert _ _
    · obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      cases n with
      | zero => exact False.elim (hnot (by simpa only [Nat.zero_add] using hn))
      | succ n =>
        exact mem_insert_of_mem _ (mem_iUnion.mpr ⟨n, by simpa only [Nat.succ_add, Nat.add_succ] using hn⟩)

theorem eventually_insert_iUnion_nat_add_subset
    {X : Type*} [TopologicalSpace X] {K : ℕ → Set X} {q : X}
    (hlim : ∀ U ∈ 𝓝 q, ∀ᶠ n in atTop, K n ⊆ U) {U : Set X} (hU : U ∈ 𝓝 q) :
    ∀ᶠ N in atTop, insert q (⋃ n, K (n + N)) ⊆ U := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim U hU)
  apply eventually_atTop.mpr
  refine ⟨N, fun n hn x hx => ?_⟩
  rcases hx with rfl | hx
  · exact mem_of_mem_nhds hU
  · obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    exact hN (k + n) (hn.trans (Nat.le_add_left _ _)) hk
