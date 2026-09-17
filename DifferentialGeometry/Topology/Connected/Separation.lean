import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.PathConnected

open Set Topology

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X]

def Separates (C H K : Set X) : Prop :=
  ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ∪ V = Cᶜ ∧ H ⊆ U ∧ K ⊆ V

theorem Separates.symm {C H K : Set X} (h : Separates C H K) : Separates C K H := by
  obtain ⟨U, V, hU, hV, hd, heq, hH, hK⟩ := h
  exact ⟨V, U, hV, hU, hd.symm, (union_comm V U).trans heq, hK, hH⟩

theorem Separates.left_subset_compl {C H K : Set X} (h : Separates C H K) : H ⊆ Cᶜ := by
  obtain ⟨U, V, _, _, _, heq, hH, _⟩ := h
  exact hH.trans (subset_union_left.trans heq.subset)

theorem Separates.right_subset_compl {C H K : Set X} (h : Separates C H K) : K ⊆ Cᶜ :=
  h.symm.left_subset_compl

theorem Separates.not_mem_connectedComponentIn {C H K : Set X} (h : Separates C H K)
    {x y : X} (hx : x ∈ H) (hy : y ∈ K) : y ∉ connectedComponentIn Cᶜ x := by
  obtain ⟨U, V, hU, hV, hd, heq, hH, hK⟩ := h
  intro hyx
  have hsub : connectedComponentIn Cᶜ x ⊆ U :=
    isPreconnected_connectedComponentIn.subset_left_of_subset_union hU hV hd
      ((connectedComponentIn_subset _ _).trans heq.symm.subset)
      ⟨x, mem_connectedComponentIn (heq ▸ Or.inl (hH hx)), hH hx⟩
  exact disjoint_left.mp hd (hsub hyx) (hK hy)

theorem separates_empty_left {C K : Set X} (hC : IsClosed C) (hK : K ⊆ Cᶜ) :
    Separates C ∅ K :=
  ⟨∅, Cᶜ, isOpen_empty, hC.isOpen_compl, by simp, empty_union _,
    empty_subset _, hK⟩

theorem separates_iff_not_mem_connectedComponentIn [LocallyConnectedSpace X]
    {C H K : Set X} (hC : IsClosed C) (hH : IsPreconnected H) (hK : IsPreconnected K)
    (hHC : H ⊆ Cᶜ) (hKC : K ⊆ Cᶜ) {x y : X} (hx : x ∈ H) (hy : y ∈ K) :
    Separates C H K ↔ y ∉ connectedComponentIn Cᶜ x := by
  refine ⟨fun h => h.not_mem_connectedComponentIn hx hy, fun hxy => ?_⟩
  let U := connectedComponentIn Cᶜ x
  have hHU : H ⊆ U := hH.subset_connectedComponentIn hx hHC
  have hKV : K ⊆ Cᶜ \ U := by
    intro z hz
    refine ⟨hKC hz, fun hzU => ?_⟩
    have hsub := hK.subset_connectedComponentIn hz hKC
    rw [← connectedComponentIn_eq hzU] at hsub
    exact hxy (hsub hy)
  have hV : IsOpen (Cᶜ \ U) := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    apply Filter.mem_of_superset
      (hC.isOpen_compl.connectedComponentIn.mem_nhds (mem_connectedComponentIn hz.1))
    intro w hw
    refine ⟨connectedComponentIn_subset _ _ hw, fun hwU => ?_⟩
    have heq := (connectedComponentIn_eq hw).trans (connectedComponentIn_eq hwU).symm
    exact hz.2 (show z ∈ connectedComponentIn Cᶜ x from heq ▸ mem_connectedComponentIn hz.1)
  refine ⟨U, Cᶜ \ U, hC.isOpen_compl.connectedComponentIn, hV,
    disjoint_sdiff_right, ?_, hHU, hKV⟩
  exact union_sdiff_cancel (connectedComponentIn_subset _ _)

theorem joinedIn_compl_of_not_separates [LocallyConnectedSpace X]
    (hpath : ∀ U : Set X, IsOpen U → IsConnected U → IsPathConnected U)
    {C H K : Set X} (hC : IsClosed C) (hH : IsPreconnected H) (hK : IsPreconnected K)
    (hHC : H ⊆ Cᶜ) (hKC : K ⊆ Cᶜ) (h : ¬ Separates C H K)
    {x y : X} (hx : x ∈ H) (hy : y ∈ K) : JoinedIn Cᶜ x y := by
  have hyU : y ∈ connectedComponentIn Cᶜ x := by
    by_contra hn
    exact h ((separates_iff_not_mem_connectedComponentIn hC hH hK hHC hKC hx hy).mpr hn)
  exact ((hpath _ hC.isOpen_compl.connectedComponentIn
    (isConnected_connectedComponentIn_iff.mpr (hHC hx))).joinedIn x
      (mem_connectedComponentIn (hHC hx)) y hyU).mono (connectedComponentIn_subset _ _)

end DifferentialGeometry.Topology
