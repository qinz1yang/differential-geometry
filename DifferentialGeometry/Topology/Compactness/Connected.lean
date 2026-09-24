import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Connected.Basic

section

open Set

namespace DifferentialGeometry.Topology

theorem sigmaCompactSpace_of_preconnected (X : Type*) [TopologicalSpace X]
    [WeaklyLocallyCompactSpace X] [ParacompactSpace X]
    [PreconnectedSpace X] : SigmaCompactSpace X := by
  classical
  cases isEmpty_or_nonempty X with
  | inl h =>
      let _ := h
      exact inferInstance
  | inr h =>
      let _ := h
      choose K hKc hKn using fun x : X => exists_compact_mem_nhds x
      obtain ⟨V, hVo, hVcov, hVfin, hVK⟩ := precise_refinement
        (fun x => interior (K x)) (fun _ => isOpen_interior)
        (iUnion_eq_univ_iff.mpr fun x => ⟨x, mem_interior_iff_mem_nhds.mpr (hKn x)⟩)
      have hVK' : ∀ i, V i ⊆ K i := fun i => (hVK i).trans interior_subset
      let N : X → Set X := fun i => {j | (V j ∩ K i).Nonempty}
      have hN : ∀ i, (N i).Finite := fun i =>
        hVfin.finite_nonempty_inter_compact (hKc i)
      obtain ⟨i₀, hi₀⟩ := iUnion_eq_univ_iff.mp hVcov (Classical.arbitrary X)
      let F : ℕ → Set X := fun n => Nat.rec {i₀} (fun _ s => ⋃ i ∈ s, N i) n
      have hF : ∀ n, (F n).Finite := by
        intro n
        induction n with
        | zero => exact finite_singleton i₀
        | succ n ih => exact ih.biUnion fun i _ => hN i
      let S : Set X := ⋃ n, F n
      have hSc : S.Countable := countable_iUnion fun n => (hF n).countable
      have hSN : ∀ i ∈ S, N i ⊆ S := by
        intro i hi j hj
        obtain ⟨n, hn⟩ := mem_iUnion.mp hi
        exact mem_iUnion.mpr ⟨n + 1, mem_iUnion₂.mpr ⟨i, hn, hj⟩⟩
      have hi₀S : i₀ ∈ S := mem_iUnion.mpr ⟨0, mem_singleton i₀⟩
      have hSall : ∀ j, (V j).Nonempty → j ∈ S := by
        intro j hj
        have hpre : IsPreconnected (⋃ i, V i) := by
          rw [hVcov]
          exact isPreconnected_univ
        have hpath := hpre.transGen_of_iUnion hVo
          i₀ j ⟨Classical.arbitrary X, hi₀⟩ hj
        induction hpath with
        | single hij =>
            obtain ⟨x, hxi, hxj⟩ := hij
            exact hSN i₀ hi₀S ⟨x, hxj, hVK' i₀ hxi⟩
        | @tail i j _ hij ih =>
            obtain ⟨x, hxi, hxj⟩ := hij
            exact hSN i (ih ⟨x, hxi⟩) ⟨x, hxj, hVK' i hxi⟩
      have hKcov : (⋃ i : S, K i) = univ := by
        apply iUnion_eq_univ_iff.mpr
        intro x
        obtain ⟨j, hj⟩ := iUnion_eq_univ_iff.mp hVcov x
        exact ⟨⟨j, hSall j ⟨x, hj⟩⟩, hVK' j hj⟩
      have : Countable S := hSc.to_subtype
      apply isSigmaCompact_univ_iff.mp
      rw [← hKcov]
      exact isSigmaCompact_iUnion_of_isCompact _ (fun i : S => hKc i)

end DifferentialGeometry.Topology

end
