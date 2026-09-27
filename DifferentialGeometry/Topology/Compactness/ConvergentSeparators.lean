import DifferentialGeometry.Topology.FirstExit
import DifferentialGeometry.Topology.Compactness.ConvergentFamily
import DifferentialGeometry.Topology.Embedding.Frontier

set_option autoImplicit false
open Set Filter
open scoped Topology

namespace DifferentialGeometry.Topology

theorem eventually_exists_frontier_intersection_of_convergent_separators
    {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X] [T2Space X]
    {e : Y → X} (he : _root_.Topology.IsOpenEmbedding e) {q : X} (hq : q ∉ range e)
    {A : ℕ → Set Y} (hA : ∀ n, IsCompact (A n))
    (hlim : ∀ U ∈ 𝓝 q, ∀ᶠ n in atTop, e '' A n ⊆ U)
    (hnhds : insert q (⋃ n, e '' A n) ∈ 𝓝 q)
    {gamma : ℝ → X} {L : ℝ} (hL : 0 < L)
    (hgamma : ContinuousOn gamma (Icc 0 L)) (hzero : gamma 0 = q) (hend : gamma L ≠ q) :
    ∀ᶠ N in atTop, ∃ t ∈ Ioc 0 L, ∃ y ∈ frontier (⋃ n, A (n + N)), gamma t = e y := by
  let T (N : ℕ) : Set X := insert q (⋃ n, e '' A (n + N))
  have hTclosed (N : ℕ) : IsClosed (T N) := by
    apply IsCompact.isClosed
    apply isCompact_insert_iUnion_of_eventually_subset (fun n => (hA (n + N)).image he.continuous)
    intro U hU
    simpa only [Nat.cofinite_eq_atTop] using (tendsto_add_atTop_nat N).eventually (hlim U hU)
  have hTnhds (N : ℕ) : T N ∈ 𝓝 q :=
    insert_iUnion_nat_add_mem_nhds (fun n => ((hA n).image he.continuous).isClosed)
      (fun n hn => hq (image_subset_range e (A n) hn)) hnhds N
  have hTfront (N : ℕ) : frontier (T N) = e '' frontier (⋃ n, A (n + N)) := by
    have hTeq : T N = insert q (e '' (⋃ n, A (n + N))) := by rw [image_iUnion]
    rw [hTeq]
    exact he.frontier_insert_image hq (hTeq ▸ hTclosed N) (hTeq ▸ hTnhds N)
  have hU : ({gamma L} : Set X)ᶜ ∈ 𝓝 q :=
    isClosed_singleton.isOpen_compl.mem_nhds (Ne.symm hend)
  filter_upwards [eventually_insert_iUnion_nat_add_subset hlim hU] with N hN
  obtain ⟨t, ht, _, htF⟩ := exists_first_exit_frontier (hTclosed N) hL hgamma
    (hzero.symm ▸ mem_interior_iff_mem_nhds.mpr (hTnhds N))
    (fun h => hN h (mem_singleton _))
  rw [hTfront N] at htF
  obtain ⟨y, hy, hyt⟩ := htF
  exact ⟨t, ht, y, hy, hyt.symm⟩

end DifferentialGeometry.Topology
