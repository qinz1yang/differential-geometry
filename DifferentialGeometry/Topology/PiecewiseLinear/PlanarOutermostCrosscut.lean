/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.External.Schoenflies.FaceCyclesLand
import DifferentialGeometry.External.Schoenflies.Subarc
import DifferentialGeometry.Topology.PiecewiseLinear.NestedJordanCurves
import DifferentialGeometry.Topology.PlanarJordan.Crosscut
import DifferentialGeometry.Topology.PlanarJordan.Regions

open Set Topology Schoenflies

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_outermost_crosscut {γ : Set Plane} (hγ : IsJordanCurve γ) {a : Plane}
    (ha : a ∈ inside γ) {ι : Type*} [Finite ι] [Nonempty ι] {T : ι → Set Plane}
    {p q : ι → Plane} (harc : ∀ i, IsArcBetween (T i) (p i) (q i)) (hpγ : ∀ i, p i ∈ γ)
    (hqγ : ∀ i, q i ∈ γ) (hin : ∀ i, T i \ {p i, q i} ⊆ inside γ)
    (hdisj : Pairwise fun i j => Disjoint (T i) (T j)) (haT : ∀ i, a ∉ T i) :
    ∃ i, ∃ β : Set Plane, (∃ β' : Set Plane, IsCutPair γ (p i) (q i) β β') ∧
      β ∩ T i = {p i, q i} ∧
      IsJordanCurve (β ∪ T i) ∧ inside (β ∪ T i) ⊆ inside γ ∧ a ∉ inside (β ∪ T i) ∧
      closure (inside (β ∪ T i)) ∩ γ = β ∧
      ∀ j, j ≠ i → Disjoint (T j) (closure (inside (β ∪ T i))) := by
  classical
  have hsep := jordan_curve_theorem hγ
  have hbeta : ∀ i, ∃ β β' : Set Plane, IsCutPair γ (p i) (q i) β β' ∧
      a ∉ inside (β ∪ T i) ∧ a ∈ inside (β' ∪ T i) := by
    intro i
    obtain ⟨A₁, A₂, hcut⟩ := Schoenflies.exists_isCutPair hγ (hpγ i) (hqγ i)
      (harc i).ne
    obtain ⟨hcov, hdis, -, -⟩ := PlanarJordan.crosscut_regions hγ (harc i) hcut (hin i)
    have hai : a ∈ inside γ \ T i := ⟨ha, haT i⟩
    rw [hcov] at hai
    rcases hai with h1 | h1
    · exact ⟨A₂, A₁, hcut.symm, fun h2 => Set.disjoint_left.mp hdis h1 h2, h1⟩
    · exact ⟨A₁, A₂, hcut, fun h2 => Set.disjoint_left.mp hdis h2 h1, h1⟩
  choose β β' hcut haβ haβ' using hbeta
  have hreg := fun i => PlanarJordan.crosscut_regions hγ (harc i) (hcut i) (hin i)
  have hΓ := fun i => PlanarJordan.isJordanCurve_cut_arc_union (harc i) (hcut i) (hin i)
  have hΓ' := fun i => PlanarJordan.isJordanCurve_cut_arc_union (harc i) (hcut i).symm (hin i)
  have hinsub : ∀ i, inside (β i ∪ T i) ⊆ inside γ := fun i =>
    subset_union_left.trans ((hreg i).1.symm.subset.trans sdiff_subset)
  have hmeet : ∀ i, T i ∩ γ = {p i, q i} := fun i =>
    PlanarJordan.arc_inter_curve_eq_pair (harc i) (hpγ i) (hqγ i) (hin i)
  obtain ⟨i, -, hmin⟩ := (Set.finite_univ (α := ι)).exists_minimalFor
    (fun j => inside (β j ∪ T j)) univ univ_nonempty
  refine ⟨i, β i, ⟨β' i, hcut i⟩, ?_, hΓ i, hinsub i, haβ i,
    (hreg i).2.2.1, ?_⟩
  · apply Subset.antisymm
    · intro x hx
      rw [← hmeet i]
      exact ⟨hx.2, (hcut i).fst_subset hx.1⟩
    · rintro x (rfl | rfl)
      · exact ⟨(hcut i).fst.left_mem, (harc i).left_mem⟩
      · exact ⟨(hcut i).fst.right_mem, (harc i).right_mem⟩
  intro j hji
  have hdij : Disjoint (T j) (T i) := hdisj hji
  have hTj : IsPreconnected (T j \ {p j, q j}) := (harc j).isPreconnected_diff
  have hTjsub : T j \ {p j, q j} ⊆ inside γ \ T i := fun x hx =>
    ⟨hin j hx, fun hxi => Set.disjoint_left.mp hdij hx.1 hxi⟩
  have hsepΓ := jordan_curve_theorem (hΓ i)
  have hsepΓ' := jordan_curve_theorem (hΓ' i)
  have hpjT : p j ∉ T i := fun h => Set.disjoint_left.mp hdij (harc j).left_mem h
  have hqjT : q j ∉ T i := fun h => Set.disjoint_left.mp hdij (harc j).right_mem h
  have hends : ∀ R : Set Plane, T j \ {p j, q j} ⊆ R → p j ∈ closure R ∧ q j ∈ closure R :=
    fun R hR => ⟨closure_mono hR (harc j).left_mem_closure_diff,
      closure_mono hR (harc j).right_mem_closure_diff⟩
  rcases hTj.subset_or_subset hsepΓ.isOpen_inside hsepΓ'.isOpen_inside (hreg i).2.1
      (hTjsub.trans (hreg i).1.subset) with hsub | hsub
  · exfalso
    obtain ⟨hpcl, hqcl⟩ := hends _ hsub
    have hpβ : p j ∈ β i := (hreg i).2.2.1.subset ⟨hpcl, hpγ j⟩
    have hqβ : q j ∈ β i := (hreg i).2.2.1.subset ⟨hqcl, hqγ j⟩
    obtain ⟨f, hfc, hfi, hfimg, hf0, hf1⟩ := (hcut i).fst
    obtain ⟨s, hs, hfs⟩ := hfimg.symm.subset hpβ
    obtain ⟨t, ht, hft⟩ := hfimg.symm.subset hqβ
    have hst : s ≠ t := fun h => (harc j).ne (hfs.symm.trans (h ▸ hft))
    have hσ := isArcBetween_subarc_of_injOn_I hfc hfi hs ht hst
    rw [hfs, hft] at hσ
    have hσβ : f '' uIcc s t ⊆ β i := hfimg ▸ image_mono (uIcc_subset_I hs ht)
    have hβΓ : β i ⊆ β i ∪ T i := subset_union_left
    obtain ⟨C₁, C₂, hcutΓ⟩ := Schoenflies.exists_isCutPair (hΓ i)
      (hβΓ hpβ) (hβΓ hqβ) (harc j).ne
    have hTjin : T j \ {p j, q j} ⊆ inside (β i ∪ T i) := hsub
    have hσeq := PlanarJordan.eq_or_eq_of_isArcBetween_subset_isCutPair hcutΓ hσ
      (hσβ.trans hβΓ)
    have hsmall : inside (f '' uIcc s t ∪ T j) ⊆ inside (β i ∪ T i) := by
      rcases hσeq with h1 | h1
      · have hreg' := PlanarJordan.crosscut_regions (hΓ i) (harc j) hcutΓ hTjin
        rw [h1]
        exact subset_union_left.trans (hreg'.1.symm.subset.trans sdiff_subset)
      · have hreg' := PlanarJordan.crosscut_regions (hΓ i) (harc j) hcutΓ.symm hTjin
        rw [h1]
        exact subset_union_left.trans (hreg'.1.symm.subset.trans sdiff_subset)
    rcases PlanarJordan.eq_or_eq_of_isArcBetween_subset_isCutPair (hcut j) hσ
        (hσβ.trans (hcut i).fst_subset) with h2 | h2
    · have hle := hmin (mem_univ j) (show inside (β j ∪ T j) ⊆ inside (β i ∪ T i) by
        rw [← h2]
        exact hsmall)
      obtain ⟨x, hx⟩ := (harc j).nonempty_diff
      have hx1 : x ∈ inside (β j ∪ T j) := hle (hsub hx)
      rw [← h2] at hx1
      exact inside_subset_compl hx1 (Or.inr hx.1)
    · exact haβ i (hsmall (h2 ▸ haβ' j))
  · refine Set.disjoint_left.mpr fun x hxT hxcl => ?_
    rw [closure_inside_eq_union (hΓ i)] at hxcl
    by_cases hxe : x ∈ ({p j, q j} : Set Plane)
    · have hxγ : x ∈ γ := by
        rcases hxe with rfl | rfl
        · exact hpγ j
        · exact hqγ j
      have hx1 : x ∈ β i := by
        rcases hxcl with h1 | h1
        · exact absurd hxγ (hinsub i h1).1
        · rcases h1 with h1 | h1
          · exact h1
          · exact absurd h1 (Set.disjoint_left.mp hdij hxT)
      have hx2 : x ∈ β' i := by
        have hcl := hends _ hsub
        have hxcl2 : x ∈ closure (inside (β' i ∪ T i)) := by
          rcases hxe with rfl | rfl
          · exact hcl.1
          · exact hcl.2
        exact (hreg i).2.2.2.subset ⟨hxcl2, hxγ⟩
      have hx3 : x ∈ ({p i, q i} : Set Plane) := (hcut i).inter_eq.subset ⟨hx1, hx2⟩
      rcases hx3 with rfl | rfl
      · exact Set.disjoint_left.mp hdij hxT (harc i).left_mem
      · exact Set.disjoint_left.mp hdij hxT (harc i).right_mem
    · have hx' : x ∈ inside (β' i ∪ T i) := hsub ⟨hxT, hxe⟩
      rcases hxcl with h1 | h1
      · exact Set.disjoint_left.mp (hreg i).2.1 h1 hx'
      · rcases h1 with h1 | h1
        · exact ((subset_union_right.trans ((hreg i).1.symm.subset.trans sdiff_subset)) hx').1
            ((hcut i).fst_subset h1)
        · exact Set.disjoint_left.mp hdij hxT h1

end DifferentialGeometry.Topology.PiecewiseLinear
