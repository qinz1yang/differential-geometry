/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.LocallyFinite

open Set Topology

theorem LocallyFinite.exists_isOpen_mem_subset_of_inter_nonempty
    {ι X : Type*} [TopologicalSpace X] {F O : ι → Set X}
    (hF : LocallyFinite F) (hclosed : ∀ i, IsClosed (F i)) {x : X}
    (hO : ∀ i, x ∈ F i → O i ∈ 𝓝 x) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∀ i, (V ∩ F i).Nonempty → x ∈ F i ∧ V ⊆ O i := by
  have hgood : (⋂ i ∈ {i | x ∈ F i}, O i) ∈ 𝓝 x :=
    Filter.biInter_mem (hF.point_finite x) |>.mpr hO
  obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp
    (Filter.inter_mem (hF.iInter_compl_mem_nhds hclosed x) hgood)
  refine ⟨V, hVopen, hxV, fun i hi => ?_⟩
  have hxi : x ∈ F i := by
    by_contra hxi
    obtain ⟨y, hyV, hyF⟩ := hi
    exact mem_iInter₂.mp (hVsub hyV).1 i hxi hyF
  exact ⟨hxi, fun y hy => mem_iInter₂.mp (hVsub hy).2 i hxi⟩

theorem LocallyFinite.exists_isOpen_cover_with_incident_buffers
    {ι X : Type*} [TopologicalSpace X] {F O : ι → Set X} {C : Set X}
    (hF : LocallyFinite F) (hclosed : ∀ i, IsClosed (F i)) (hC : IsClosed C)
    (hO : ∀ i, IsOpen (O i)) (hCO : ∀ i, C ∩ F i ⊆ O i) :
    ∃ V : Option C → Set X, (∀ j, IsOpen (V j)) ∧ (⋃ j, V j) = univ ∧
      ∀ j i, (V j ∩ C ∩ F i).Nonempty → V j ⊆ O i := by
  choose V hV hxV hinc using fun x : C =>
    hF.exists_isOpen_mem_subset_of_inter_nonempty hclosed
      (fun i hi => (hO i).mem_nhds (hCO i ⟨x.2, hi⟩))
  let W : Option C → Set X := fun j => j.elim Cᶜ V
  refine ⟨W, ?_, ?_, ?_⟩
  · intro j
    cases j with
    | none => exact hC.isOpen_compl
    | some x => exact hV x
  · apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ C
    · exact mem_iUnion.mpr ⟨some ⟨x, hx⟩, hxV ⟨x, hx⟩⟩
    · exact mem_iUnion.mpr ⟨none, hx⟩
  · intro j i hi
    cases j with
    | none =>
        obtain ⟨x, ⟨hxW, hxC⟩, -⟩ := hi
        exact False.elim (hxW hxC)
    | some x =>
        exact (hinc x i (hi.mono (fun _ hy => ⟨hy.1.1, hy.2⟩))).2
