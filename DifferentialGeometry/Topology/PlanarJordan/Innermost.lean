/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.External.Schoenflies.JordanClosed
import DifferentialGeometry.Topology.Connected.Loop
import Mathlib.Order.Preorder.Finite
import Mathlib.Topology.Perfect

open Set

namespace DifferentialGeometry.Topology.PlanarJordan

theorem isConnected_sdiff_singleton_of_isJordanCurve {J : Set Schoenflies.Plane}
    (hJ : Schoenflies.IsJordanCurve J) (p : Schoenflies.Plane) : IsConnected (J \ {p}) := by
  obtain ⟨f, hf, rfl⟩ := hJ
  exact isConnected_image_Icc_sdiff_singleton (by norm_num) hf.continuousOn hf.closes hf.injOn p

theorem closure_sdiff_singleton_of_isJordanCurve {J : Set Schoenflies.Plane}
    (hJ : Schoenflies.IsJordanCurve J) (p : Schoenflies.Plane) : closure (J \ {p}) = J := by
  apply Subset.antisymm (closure_minimal sdiff_subset hJ.isClosed)
  intro x hx
  by_cases hxp : x = p
  · subst x
    obtain ⟨y, hyJ, hyp⟩ := (isConnected_sdiff_singleton_of_isJordanCurve hJ p).nonempty
    have hnontrivial : J.Nontrivial := ⟨p, hx, y, hyJ, Ne.symm hyp⟩
    have hacc := hJ.isConnected.isPreconnected.preperfect_of_nontrivial hnontrivial p hx
    rwa [accPt_principal_iff_clusterPt, ← mem_closure_iff_clusterPt] at hacc
  · exact subset_closure ⟨hx, hxp⟩

theorem inside_subset_of_subset_closure_inside {C J : Set Schoenflies.Plane}
    (hC : Schoenflies.IsSeparating C) (hJ : Schoenflies.IsSeparating J)
    (hJC : J ⊆ closure (Schoenflies.inside C)) :
    Schoenflies.inside J ⊆ Schoenflies.inside C := by
  have hdis : Disjoint (Schoenflies.outside C) J :=
    (Schoenflies.disjoint_inside_outside.closure_left hC.isOpen_outside).symm.mono_right hJC
  obtain ⟨W, V, hWV, hout⟩ := hJ.exists_isRegionPair_subset
    hC.isConnected_outside.isPreconnected hC.isConnected_outside.nonempty hdis
  rcases hWV with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (hC.not_isBounded_outside (hJ.isBounded_inside.subset hout)).elim
  · have hCout : C \ J ⊆ Schoenflies.outside J :=
      hC.absorption hJ (Or.inr rfl) (Or.inr rfl) hout
    intro z hz
    have hzC : z ∉ C := by
      intro hzC
      by_cases hzJ : z ∈ J
      · exact Schoenflies.inside_subset_compl hz hzJ
      · exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hz (hCout ⟨hzC, hzJ⟩)
    have hzcover : z ∈ Schoenflies.inside C ∪ Schoenflies.outside C := by
      rwa [Schoenflies.inside_union_outside]
    exact hzcover.resolve_right fun hzout =>
      Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hz (hout hzout)

theorem exists_innermost_jordan_curve_of_inter_subset_singleton
    (curves : Finset (Set Schoenflies.Plane)) (hne : curves.Nonempty)
    (hcurves : ∀ C ∈ curves, Schoenflies.IsJordanCurve C) (p : Schoenflies.Plane)
    (hinter : ∀ C ∈ curves, ∀ J ∈ curves, C ≠ J → C ∩ J ⊆ {p}) :
    ∃ C ∈ curves, ∀ J ∈ curves, Disjoint (Schoenflies.inside C) J := by
  classical
  obtain ⟨C, hmin⟩ := curves.exists_minimalFor Schoenflies.inside hne
  have hC := Schoenflies.jordan_curve_theorem (hcurves C hmin.1)
  refine ⟨C, hmin.1, ?_⟩
  intro J hJmem
  by_cases hJC : J = C
  · subst J
    exact Set.disjoint_left.mpr fun _ hx hxc => Schoenflies.inside_subset_compl hx hxc
  have hJ := Schoenflies.jordan_curve_theorem (hcurves J hJmem)
  have hJconn := isConnected_sdiff_singleton_of_isJordanCurve hJ.isJordanCurve p
  have hJclosed := closure_sdiff_singleton_of_isJordanCurve hJ.isJordanCurve p
  have hdis : Disjoint (J \ {p}) C := by
    apply Set.disjoint_left.mpr
    rintro x ⟨hxJ, hxp⟩ hxC
    exact hxp (hinter J hJmem C hmin.1 hJC ⟨hxJ, hxC⟩)
  obtain ⟨W, V, hWV, hsub⟩ := hC.exists_isRegionPair_subset
    hJconn.isPreconnected hJconn.nonempty hdis
  rcases hWV with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hJcl : J ⊆ closure (Schoenflies.inside C) :=
      hJclosed.symm.subset.trans (closure_mono hsub)
    have hproper : Schoenflies.inside J ⊂ Schoenflies.inside C := by
      refine ssubset_iff_subset_ne.mpr ⟨inside_subset_of_subset_closure_inside hC hJ hJcl, ?_⟩
      intro h
      obtain ⟨z, hzJ, hzp⟩ := hJconn.nonempty
      have hzin : z ∈ Schoenflies.inside J := h.symm ▸ hsub ⟨hzJ, hzp⟩
      exact Schoenflies.inside_subset_compl hzin hzJ
    exact (hproper.not_ge (hmin.2 hJmem hproper.le)).elim
  · have hJcl : J ⊆ closure (Schoenflies.outside C) :=
      hJclosed.symm.subset.trans (closure_mono hsub)
    exact (Schoenflies.disjoint_inside_outside.closure_right hC.isOpen_inside).mono_right hJcl

theorem exists_innermost_jordan_curve
    (curves : Finset (Set Schoenflies.Plane))
    (hne : curves.Nonempty)
    (hcurves : ∀ C ∈ curves, Schoenflies.IsJordanCurve C)
    (hdisjoint : (curves : Set (Set Schoenflies.Plane)).Pairwise Disjoint) :
    ∃ C ∈ curves, ∀ J ∈ curves, Disjoint (Schoenflies.inside C) J := by
  apply exists_innermost_jordan_curve_of_inter_subset_singleton curves hne hcurves 0
  intro C hC J hJ hCJ
  rw [Set.disjoint_iff_inter_eq_empty.mp (hdisjoint hC hJ hCJ)]
  exact empty_subset _

theorem inside_ssubset_of_subset_inside
    {C J : Set Schoenflies.Plane}
    (hC : Schoenflies.IsSeparating C) (hJ : Schoenflies.IsSeparating J)
    (hJC : J ⊆ Schoenflies.inside C) :
    Schoenflies.inside J ⊂ Schoenflies.inside C := by
  have hCJ : Disjoint C J := Set.disjoint_left.2 fun _ hzC hzJ ↦
    Schoenflies.inside_subset_compl (hJC hzJ) hzC
  have hdis : Disjoint (Schoenflies.outside C) J :=
    Schoenflies.disjoint_inside_outside.symm.mono_right hJC
  obtain ⟨W, V, hWV, hout⟩ := hJ.exists_isRegionPair_subset
    hC.isConnected_outside.isPreconnected hC.isConnected_outside.nonempty hdis
  rcases hWV with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (hC.not_isBounded_outside (hJ.isBounded_inside.subset hout)).elim
  · have hCout : C ⊆ Schoenflies.outside J := by
      intro z hz
      exact hC.absorption hJ (Or.inr rfl) (Or.inr rfl) hout
        ⟨hz, Set.disjoint_left.1 hCJ hz⟩
    have hinsub : Schoenflies.inside J ⊆ Schoenflies.inside C := by
      intro z hz
      have hzC : z ∉ C := fun h ↦
        Set.disjoint_left.1 Schoenflies.disjoint_inside_outside hz (hCout h)
      have hzcover : z ∈ Schoenflies.inside C ∪ Schoenflies.outside C := by
        rwa [Schoenflies.inside_union_outside]
      exact hzcover.resolve_right fun h ↦
        Set.disjoint_left.1 Schoenflies.disjoint_inside_outside hz (hout h)
    refine (ssubset_iff_subset_ne).2 ⟨hinsub, ?_⟩
    intro h
    obtain ⟨z, hz⟩ := hJ.isJordanCurve.nonempty
    have hz' : z ∈ Schoenflies.inside J := by
      rw [h]
      exact hJC hz
    exact Schoenflies.inside_subset_compl hz' hz

theorem disjoint_jordan_curves_trichotomy
    {C J : Set Schoenflies.Plane} (hC : Schoenflies.IsJordanCurve C)
    (hJ : Schoenflies.IsJordanCurve J) (hdisj : Disjoint C J) :
    (C ⊆ Schoenflies.inside J ∧ J ⊆ Schoenflies.outside C) ∨
      (J ⊆ Schoenflies.inside C ∧ C ⊆ Schoenflies.outside J) ∨
      (C ⊆ Schoenflies.outside J ∧ J ⊆ Schoenflies.outside C) := by
  have hCs := Schoenflies.jordan_curve_theorem hC
  have hJs := Schoenflies.jordan_curve_theorem hJ
  obtain ⟨W, V, hWV, hCW⟩ := hJs.exists_isRegionPair_subset
    hC.isConnected.isPreconnected hC.nonempty hdisj
  obtain ⟨W', V', hWV', hJW⟩ := hCs.exists_isRegionPair_subset
    hJ.isConnected.isPreconnected hJ.nonempty hdisj.symm
  rcases hWV with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases hWV' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact False.elim ((inside_ssubset_of_subset_inside hJs hCs hCW).not_ge
        (inside_ssubset_of_subset_inside hCs hJs hJW).le)
    · exact Or.inl ⟨hCW, hJW⟩
  · rcases hWV' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨hJW, hCW⟩)
    · exact Or.inr (Or.inr ⟨hCW, hJW⟩)

end DifferentialGeometry.Topology.PlanarJordan
