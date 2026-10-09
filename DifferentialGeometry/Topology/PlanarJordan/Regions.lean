/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Connected.Frontier
import DifferentialGeometry.External.Schoenflies.JordanClosed
import DifferentialGeometry.External.Schoenflies.PolyArcRealize
import DifferentialGeometry.External.Schoenflies.FaceCyclesProof
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
open Set Topology

namespace Schoenflies.IsSeparating

theorem inside_eq_compl_closure_outside {C : Set Plane} (hC : IsSeparating C) :
    inside C = (closure (outside C))ᶜ := by
  rw [(IsRegionOf.outside C).closure_eq hC]
  ext p
  constructor
  · intro hp
    rintro (ho | hc)
    · exact disjoint_left.mp disjoint_inside_outside hp ho
    · exact hp.1 hc
  · intro hp
    have hpc : p ∉ C := fun hc => hp (Or.inr hc)
    have hm : p ∈ inside C ∪ outside C := by
      rw [inside_union_outside]
      exact hpc
    exact hm.resolve_right (fun ho => hp (Or.inl ho))

theorem outside_eq_compl_closure_inside {C : Set Plane} (hC : IsSeparating C) :
    outside C = (closure (inside C))ᶜ := by
  rw [(IsRegionOf.inside C).closure_eq hC]
  ext p
  constructor
  · intro hp
    rintro (hi | hc)
    · exact disjoint_left.mp disjoint_inside_outside hi hp
    · exact hp.1 hc
  · intro hp
    have hpc : p ∉ C := fun hc => hp (Or.inr hc)
    have hm : p ∈ inside C ∪ outside C := by
      rw [inside_union_outside]
      exact hpc
    exact hm.resolve_left (fun hi => hp (Or.inl hi))

theorem frontier_closure_inside {C : Set Plane} (hC : IsSeparating C) :
    frontier (closure (inside C)) = C := by
  rw [← frontier_compl, ← hC.outside_eq_compl_closure_inside, hC.frontier_outside]

end Schoenflies.IsSeparating

namespace DifferentialGeometry.Topology.PlanarJordan

theorem eq_or_eq_of_isArcBetween_subset_isCutPair {J A B C : Set Schoenflies.Plane}
    {p q : Schoenflies.Plane} (hcut : Schoenflies.IsCutPair J p q B C)
    (hA : Schoenflies.IsArcBetween A p q) (hAJ : A ⊆ J) : A = B ∨ A = C := by
  have hsub : A \ {p, q} ⊆ Bᶜ ∪ Cᶜ := by
    intro z hz
    by_cases hzB : z ∈ B
    · exact Or.inr fun hzC => hz.2 (hcut.inter_eq.subset ⟨hzB, hzC⟩)
    · exact Or.inl hzB
  have hnone : ¬ ((A \ {p, q}) ∩ (Bᶜ ∩ Cᶜ)).Nonempty := by
    rintro ⟨z, hz, hzB, hzC⟩
    exact (hcut.union_eq.symm.subset (hAJ hz.1)).elim hzB hzC
  have hends : ∀ D : Set Schoenflies.Plane, p ∈ D → q ∈ D →
      A \ {p, q} ⊆ D → A ⊆ D := by
    intro D hpD hqD hD z hz
    by_cases hzp : z ∈ ({p, q} : Set Schoenflies.Plane)
    · rcases hzp with rfl | rfl
      · exact hpD
      · exact hqD
    · exact hD ⟨hz, hzp⟩
  by_cases hmeet : ((A \ {p, q}) ∩ Bᶜ).Nonempty
  · refine Or.inr (hcut.snd.eq_of_subset hA
      (hends C hcut.snd.left_mem hcut.snd.right_mem fun z hz => ?_))
    by_contra hzC
    exact hnone (hA.isPreconnected_diff _ _ hcut.fst.isArc.isClosed.isOpen_compl
      hcut.snd.isArc.isClosed.isOpen_compl hsub hmeet ⟨z, hz, hzC⟩)
  · refine Or.inl (hcut.fst.eq_of_subset hA
      (hends B hcut.fst.left_mem hcut.fst.right_mem fun z hz => ?_))
    by_contra hzB
    exact hmeet ⟨z, hz, hzB⟩

theorem eq_of_isJordanCurve_of_subset {C J : Set Schoenflies.Plane}
    (hC : Schoenflies.IsJordanCurve C) (hJ : Schoenflies.IsJordanCurve J) (hCJ : C ⊆ J) : C =
      J := by
  obtain ⟨γ, hγ, hγC⟩ := hC
  have hp : γ 0 ∈ C := hγC.subset ⟨0, Schoenflies.zero_mem_I, rfl⟩
  have hq : γ (1 / 2) ∈ C := hγC.subset ⟨1 / 2, by norm_num, rfl⟩
  have hpq : γ 0 ≠ γ (1 / 2) := by
    intro h
    have heq := hγ.injOn (by norm_num) (by norm_num) h
    norm_num at heq
  obtain ⟨A, B, hcut⟩ := Schoenflies.exists_isCutPair ⟨γ, hγ, hγC⟩ hp hq hpq
  obtain ⟨A', B', hcut'⟩ := Schoenflies.exists_isCutPair hJ (hCJ hp) (hCJ hq) hpq
  rcases eq_or_eq_of_isArcBetween_subset_isCutPair hcut' hcut.fst
    (hcut.fst_subset.trans hCJ) with hA | hA <;>
    rcases eq_or_eq_of_isArcBetween_subset_isCutPair hcut' hcut.snd
      (hcut.snd_subset.trans hCJ) with hB | hB
  · exact (hcut.ne (hA.trans hB.symm)).elim
  · rw [← hcut.union_eq, hA, hB, hcut'.union_eq]
  · rw [← hcut.union_eq, hA, hB, union_comm, hcut'.union_eq]
  · exact (hcut.ne (hA.trans hB.symm)).elim

theorem frontier_closure_inside {J : Set Schoenflies.Plane} (hJ : Schoenflies.IsJordanCurve J) :
    frontier (closure (Schoenflies.inside J)) = J :=
  (Schoenflies.jordan_curve_theorem hJ).frontier_closure_inside

theorem closure_inside_union_of_isCrosscut {J P A B : Set Schoenflies.Plane}
    {p q : Schoenflies.Plane} (h : Schoenflies.IsCrosscut J P p q)
    (hcut : Schoenflies.IsCutPair J p q A B) :
    closure (Schoenflies.inside (A ∪ P)) ∪ closure (Schoenflies.inside (B ∪ P)) =
      closure (Schoenflies.inside J) := by
  have hj : ∀ S, Schoenflies.IsJordanCurve S → Schoenflies.IsSeparating S :=
    fun _ => Schoenflies.jordan_curve_theorem
  have hP : P ⊆ Schoenflies.inside J ∪ J := by
    intro x hx
    by_cases hxpq : x ∈ ({p, q} : Set Schoenflies.Plane)
    · rcases hxpq with rfl | rfl
      · exact Or.inr h.left_mem
      · exact Or.inr h.right_mem
    · exact Or.inl (h.sdiff_subset ⟨hx, hxpq⟩)
  rw [h.closure_side hj hcut, h.closure_side hj hcut.symm,
    (Schoenflies.IsRegionOf.inside J).closure_eq (hj J h.curve)]
  calc
    _ = (Schoenflies.inside (A ∪ P) ∪ Schoenflies.inside (B ∪ P)) ∪ ((A ∪ B) ∪ P) := by
      ext x
      simp only [mem_union]
      tauto
    _ = (Schoenflies.inside J \ P) ∪ (J ∪ P) := by
      rw [← h.inside_diff_eq hj hcut h.hasArcCollars, hcut.union_eq]
    _ = Schoenflies.inside J ∪ J := by
      ext x
      have hp : x ∈ P → x ∈ Schoenflies.inside J ∨ x ∈ J := fun hx => hP hx
      simp only [mem_union, mem_sdiff]
      tauto

theorem closure_inside_inter_of_isCrosscut {J P A B : Set Schoenflies.Plane}
    {p q : Schoenflies.Plane} (h : Schoenflies.IsCrosscut J P p q)
    (hcut : Schoenflies.IsCutPair J p q A B) :
    closure (Schoenflies.inside (A ∪ P)) ∩ closure (Schoenflies.inside (B ∪ P)) = P := by
  have hj : ∀ S, Schoenflies.IsJordanCurve S → Schoenflies.IsSeparating S :=
    fun _ => Schoenflies.jordan_curve_theorem
  rw [h.closure_side hj hcut, h.closure_side hj hcut.symm]
  refine Subset.antisymm ?_ fun x hx => ⟨Or.inr (Or.inr hx), Or.inr (Or.inr hx)⟩
  rintro x ⟨hx | hx, hy | hy⟩
  · exact False.elim (Set.disjoint_left.mp (h.disjoint_sides hj hcut) hx hy)
  · have hx' := h.side_subset hj hcut hx
    rcases hy with hy | hy
    · exact False.elim (Schoenflies.inside_subset_compl hx'.1 (hcut.snd_subset hy))
    · exact hy
  · have hy' := h.side_subset hj hcut.symm hy
    rcases hx with hx | hx
    · exact False.elim (Schoenflies.inside_subset_compl hy'.1 (hcut.fst_subset hx))
    · exact hx
  · rcases hx with hx | hx
    · rcases hy with hy | hy
      · have hxpq := hcut.inter_eq.subset ⟨hx, hy⟩
        rcases hxpq with rfl | rfl
        · exact h.arc.left_mem
        · exact h.arc.right_mem
      · exact hy
    · exact hx

theorem exists_regions_of_simple_closed_curve
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1)) (hclose : γ 0 = γ 1)
    (hinj : InjOn γ (Ico 0 1)) :
    ∃ U V : Set ℂ, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ U ∪ V = (γ '' Icc 0 1)ᶜ ∧
      frontier U = γ '' Icc 0 1 ∧ frontier V = γ '' Icc 0 1 ∧
      IsCompact (closure U) ∧ ¬ IsCompact (closure V) := by
  let e : ℂ ≃ₜ Schoenflies.Plane := Complex.orthonormalBasisOneI.repr.toHomeomorph
  let C : Set Schoenflies.Plane := (fun t ↦ e (γ t)) '' Icc 0 1
  have hC : Schoenflies.IsJordanCurve C :=
    ⟨fun t ↦ e (γ t), ⟨e.continuous.comp_continuousOn hγ,
      congrArg e hclose, fun _ hx _ hy he ↦ hinj hx hy (e.injective he)⟩, rfl⟩
  have hsep := Schoenflies.jordan_curve_theorem hC
  have hpre : e ⁻¹' C = γ '' Icc 0 1 := by
    ext z
    constructor
    · rintro ⟨t, ht, he⟩
      exact ⟨t, ht, e.injective he⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ht, rfl⟩
  let U := e ⁻¹' Schoenflies.inside C
  let V := e ⁻¹' Schoenflies.outside C
  have hU : IsOpen U := hsep.isOpen_inside.preimage e.continuous
  have hV : IsOpen V := hsep.isOpen_outside.preimage e.continuous
  have hUi : IsConnected U := e.isConnected_preimage.mpr hsep.isConnected_inside
  have hVi : IsConnected V := e.isConnected_preimage.mpr hsep.isConnected_outside
  have hUfr : frontier U = γ '' Icc 0 1 := by
    rw [← e.preimage_frontier, hsep.frontier_inside, hpre]
  have hVfr : frontier V = γ '' Icc 0 1 := by
    rw [← e.preimage_frontier, hsep.frontier_outside, hpre]
  refine ⟨U, V, hU, hV, hUi, hVi, ?_, ?_, hUfr, hVfr, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    exact fun z hz hz' ↦ hz'.2 hz.2
  · change (e ⁻¹' Schoenflies.inside C) ∪ (e ⁻¹' Schoenflies.outside C) = _
    rw [← preimage_union, Schoenflies.inside_union_outside, preimage_compl, hpre]
  · have hcompact : IsCompact (closure (Schoenflies.inside C)) :=
      hsep.isBounded_inside.isCompact_closure
    have he := e.isCompact_preimage.mpr hcompact
    simpa only [e.preimage_closure] using he
  · intro hcompact
    have he : IsCompact (closure (Schoenflies.outside C)) :=
      e.isCompact_preimage.mp (by simpa only [e.preimage_closure] using hcompact)
    exact hsep.not_isBounded_outside (he.isBounded.subset subset_closure)

theorem eq_closure_inside_of_isCompact_of_frontier_subset
    {K C : Set Schoenflies.Plane} (hK : IsCompact K)
    (hC : Schoenflies.IsJordanCurve C) (hne : (interior K).Nonempty)
    (hfront : frontier K ⊆ C) : K = closure (Schoenflies.inside C) := by
  have hsep := Schoenflies.jordan_curve_theorem hC
  have hdisj : Disjoint (Schoenflies.outside C) (frontier K) :=
    disjoint_left.mpr (fun x hx hxf => hx.1 (hfront hxf))
  have hKout : Disjoint K (Schoenflies.outside C) := by
    apply disjoint_left.mpr
    intro x hxK hxo
    have hxi : x ∈ interior K := (mem_interior_iff_notMem_frontier hxK).mpr
      (fun hxf => hxo.1 (hfront hxf))
    have hsub :=
      DifferentialGeometry.Topology.subset_interior_of_isPreconnected_of_disjoint_frontier
      hsep.isConnected_outside.isPreconnected hdisj ⟨x, hxo, hxi⟩
    exact hsep.not_isBounded_outside (hK.isBounded.subset (hsub.trans interior_subset))
  have hsub : K ⊆ closure (Schoenflies.inside C) := by
    intro x hx
    by_contra hn
    have hout : x ∈ Schoenflies.outside C := by
      rw [hsep.outside_eq_compl_closure_inside]
      exact hn
    exact disjoint_left.mp hKout hx hout
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hyK, hyinside⟩ := mem_closure_iff.mp (hsub (interior_subset hx))
    (interior K) isOpen_interior hx
  have hinside : Schoenflies.inside C ⊆ interior K :=
    DifferentialGeometry.Topology.subset_interior_of_isPreconnected_of_disjoint_frontier
      hsep.isConnected_inside.isPreconnected
      (disjoint_left.mpr (fun z hz hzf => hz.1 (hfront hzf))) ⟨y, hyinside, hyK⟩
  exact subset_antisymm hsub (closure_minimal (hinside.trans interior_subset) hK.isClosed)

end DifferentialGeometry.Topology.PlanarJordan
