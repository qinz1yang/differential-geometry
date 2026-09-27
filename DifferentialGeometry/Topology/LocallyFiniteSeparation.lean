/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.ShrinkingLemma

open Set Function

namespace DifferentialGeometry.Topology

theorem exists_locallyFinite_pairwise_disjoint_open_supersets
    {X ι : Type*} [TopologicalSpace X] [NormalSpace X] [ParacompactSpace X]
    (F : ι → Set X) (hclosed : ∀ i, IsClosed (F i)) (hloc : LocallyFinite F)
    (hdis : Pairwise (Disjoint on F)) {U : Set X} (hU : IsOpen U)
    (hFU : ∀ i, F i ⊆ U) :
    ∃ V : ι → Set X,
      (∀ i, IsOpen (V i)) ∧
      (∀ i, F i ⊆ V i) ∧
      (∀ i, V i ⊆ U) ∧
      LocallyFinite V ∧
      Pairwise (Disjoint on V) := by
  classical
  let S : Set X := ⋃ i, F i
  let A : ι → Set X := fun i => U ∩ (⋃ j : {j // j ≠ i}, F j)ᶜ
  have hSclosed : IsClosed S := hloc.isClosed_iUnion hclosed
  have hAopen (i : ι) : IsOpen (A i) := by
    apply hU.inter
    change IsOpen ((⋃ j : {j // j ≠ i}, (F ∘ Subtype.val) j)ᶜ)
    exact ((hloc.comp_injective Subtype.val_injective).isClosed_iUnion
      fun j => by change IsClosed (F j.val); exact hclosed j.val).isOpen_compl
  have hFA (i : ι) : F i ⊆ A i := by
    intro x hxi
    refine ⟨hFU i hxi, ?_⟩
    rw [mem_compl_iff]
    intro hx
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
    exact Set.disjoint_left.mp (hdis j.property) hxj hxi
  have hSA : S ⊆ ⋃ i, A i := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨i, hFA i hxi⟩
  obtain ⟨B, hBopen, hSB, hBloc, hBA⟩ :=
    precise_refinement_set hSclosed A hAopen hSA
  obtain ⟨O, hSO, hOopen, hOBclosure⟩ :=
    exists_subset_iUnion_closure_subset hSclosed hBopen
      (fun x _ => hBloc.point_finite x) hSB
  have hOB (i : ι) : O i ⊆ B i := subset_closure.trans (hOBclosure i)
  have hOloc : LocallyFinite O := hBloc.subset hOB
  have hFO (i : ι) : F i ⊆ O i := by
    intro x hxi
    obtain ⟨j, hxj⟩ := mem_iUnion.mp (hSO (mem_iUnion.mpr ⟨i, hxi⟩))
    have hji : j = i := by
      by_contra hne
      have hxAj := hBA j (hOB j hxj)
      exact hxAj.2 (mem_iUnion.mpr ⟨⟨i, Ne.symm hne⟩, hxi⟩)
    exact hji ▸ hxj
  let V : ι → Set X := fun i => O i ∩ (⋃ j : {j // j ≠ i}, closure (O j))ᶜ
  have hVopen (i : ι) : IsOpen (V i) := by
    apply (hOopen i).inter
    change IsOpen ((⋃ j : {j // j ≠ i}, ((fun k => closure (O k)) ∘ Subtype.val) j)ᶜ)
    exact ((hOloc.closure.comp_injective Subtype.val_injective).isClosed_iUnion
      fun _ => isClosed_closure).isOpen_compl
  have hFV (i : ι) : F i ⊆ V i := by
    intro x hxi
    refine ⟨hFO i hxi, ?_⟩
    rw [mem_compl_iff]
    intro hx
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
    have hxAj := hBA j (hOBclosure j hxj)
    exact hxAj.2 (mem_iUnion.mpr ⟨⟨i, Ne.symm j.property⟩, hxi⟩)
  have hVU (i : ι) : V i ⊆ U :=
    inter_subset_left.trans ((hOB i).trans ((hBA i).trans inter_subset_left))
  have hVloc : LocallyFinite V := hOloc.subset fun _ => inter_subset_left
  have hVdis : Pairwise (Disjoint on V) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact hxj.2 (mem_iUnion.mpr ⟨⟨i, hij⟩, subset_closure hxi.1⟩)
  exact ⟨V, hVopen, hFV, hVU, hVloc, hVdis⟩

end DifferentialGeometry.Topology
