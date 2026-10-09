/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.LocallyFinite

open Set Topology

theorem frontier_subset_iUnion_of_locallyFinite_closed_cover
    {ι X : Type*} [TopologicalSpace X] {U : Set X} (hU : IsOpen U)
    (F : ι → Set X) (hF : ∀ i, IsClosed (F i)) (hcover : (⋃ i, F i) = U)
    (hlocal : ∀ x ∈ U, ∃ V ∈ 𝓝 x, {i | (F i ∩ V).Nonempty}.Finite) (i : ι) :
    frontier (F i) ⊆ ⋃ j ∈ {j | j ≠ i}, F j := by
  classical
  intro x hx
  have hxU : x ∈ U := hcover ▸ mem_iUnion_of_mem i ((hF i).frontier_subset hx)
  by_contra hnot
  have hxnot : ∀ j, j ≠ i → x ∉ F j := fun j hji hxj =>
    hnot (mem_iUnion₂.mpr ⟨j, hji, hxj⟩)
  obtain ⟨V, hV, hfin⟩ := hlocal x hxU
  let A := {j | (F j ∩ V).Nonempty} \ {i}
  have hAc : (⋂ j ∈ A, (F j)ᶜ) ∈ 𝓝 x := (Filter.biInter_mem hfin.sdiff).mpr
    fun j hj => (hF j).isOpen_compl.mem_nhds (hxnot j hj.2)
  have hN : (U ∩ V) ∩ (⋂ j ∈ A, (F j)ᶜ) ∈ 𝓝 x :=
    Filter.inter_mem (Filter.inter_mem (hU.mem_nhds hxU) hV) hAc
  have hsub : (U ∩ V) ∩ (⋂ j ∈ A, (F j)ᶜ) ⊆ F i := by
    rintro y ⟨⟨hyU, hyV⟩, hyA⟩
    obtain ⟨j, hyj⟩ := mem_iUnion.mp (hcover.symm ▸ hyU)
    by_cases hji : j = i
    · exact hji ▸ hyj
    · exact (mem_iInter₂.mp hyA j ⟨⟨y, hyj, hyV⟩, hji⟩ hyj).elim
  exact hx.2 (mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset hN hsub))
