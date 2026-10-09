/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DualCellDecomposition
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitDerivedCellBase

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLBall_graphDualCell_two
    [FiniteDimensional ℝ E] (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hL : L.faces ⊆ K.faces)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) {v : E} (hv : {v} ∈ L.faces) :
    IsPLBall 2 (graphDualCell K L v).space := by
  classical
  let A := dualCell K {v} (hL hv)
  let _ : Finite A.faces := (dualCell_faces_finite K (hL hv)).to_subtype
  have hvA : {v} ∈ A.faces := by
    change {v} ∈ (dualCell K {v} (hL hv)).faces
    simpa only [Finset.centroid_singleton, id_eq] using
      singleton_centroid_mem_dualCell K (hL hv)
  have hAball : IsPLBall 2 A.space := by
    simpa using hK.isPLBall_dualCell K (hL hv) (k := 0)
      (Finset.card_singleton v) (by omega)
  have hA : IsCombinatorialManifoldWithBoundary 2 A :=
    hAball.isCombinatorialManifoldWithBoundary
  let I := {s : Finset E // s ∈ L.faces ∧ s.card = 2 ∧ v ∈ s}
  have hIfin : {s : Finset E | s ∈ L.faces ∧ s.card = 2 ∧ v ∈ s}.Finite :=
    (Set.toFinite K.faces).subset fun _ hs => hL hs.1
  let _ : Finite I := hIfin.to_subtype
  let _ : Fintype I := Fintype.ofFinite I
  have hsK (s : I) : s.1 ∈ K.faces := hL s.2.1
  have hsA (s : I) : {s.1.centroid ℝ id} ∈ A.faces := by
    change {s.1.centroid ℝ id} ∈ (dualCell K {v} (hL hv)).faces
    have hflag : IsFlag K {s.1} := by
      refine ⟨?_, ?_⟩
      · intro a ha
        have ha' : a = s.1 := Finset.mem_singleton.mp ha
        subst a
        exact hsK s
      · intro a ha b hb
        have ha' : a = s.1 := Finset.mem_singleton.mp ha
        have hb' : b = s.1 := Finset.mem_singleton.mp hb
        subst a
        subst b
        exact Or.inl Finset.Subset.rfl
    apply (mem_dualCell_faces_iff_of_flag (hL hv) hflag (Finset.singleton_nonempty s.1)).mpr
    intro a ha
    have ha' : a = s.1 := Finset.mem_singleton.mp ha
    subst a
    exact Finset.singleton_subset_iff.mpr s.2.2.2
  have hvcentroid (s : I) : v ≠ s.1.centroid ℝ id := by
    intro heq
    have hcentroid : ({v} : Finset E).centroid ℝ id = s.1.centroid ℝ id := by
      simpa only [Finset.centroid_singleton, id_eq] using heq
    have hface := injOn_faces_of_mem_openSimplex K
      (centroid_mem_openSimplex_of_mem_faces K) (hL hv) (hsK s) hcentroid
    have hcards := congrArg Finset.card hface
    simp only [Finset.card_singleton, s.2.2.1] at hcards
    omega
  have hpairA (s : I) : {v, s.1.centroid ℝ id} ∈ A.faces := by
    change {v, s.1.centroid ℝ id} ∈ (dualCell K {v} (hL hv)).faces
    have hvs : ({v} : Finset E) ⊆ s.1 := Finset.singleton_subset_iff.mpr s.2.2.2
    have hflag : IsFlag K {{v}, s.1} := by
      refine ⟨?_, ?_⟩
      · intro a ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl
        · exact hL hv
        · exact hsK s
      · intro a ha b hb
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact Or.inl Finset.Subset.rfl
        · exact Or.inl hvs
        · exact Or.inr hvs
        · exact Or.inl Finset.Subset.rfl
    have hmem := (mem_dualCell_faces_iff_of_flag (hL hv) hflag
      (Finset.insert_nonempty {v} {s.1})).mpr fun a ha => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl
        · exact Finset.Subset.rfl
        · exact hvs
    simpa only [Finset.image_insert, Finset.image_singleton, Finset.centroid_singleton,
      id_eq] using hmem
  have hdualSpace (s : Finset E) (hs : s ∈ L.faces)
      (hsA' : {s.centroid ℝ id} ∈ A.faces) :
      (dualCell A {s.centroid ℝ id} hsA').space ⊆ (graphDualCell K L v).space := by
    intro x hx
    obtain ⟨u, hu, hxu⟩ := (dualCell A {s.centroid ℝ id} hsA').mem_space_iff.mp hx
    obtain ⟨D, hD, hne, hsub, rfl⟩ := (mem_dualCell_faces_iff A hsA').mp hu
    have hDK : IsFlag (PiecewiseLinear.barycentricSubdivision K) D :=
      hD.of_le (dualCell_faces_subset K (hL hv))
    apply (graphDualCell K L v).convexHull_subset_space
      ((mem_graphDualCell_faces_iff_of_flag L (hL hv) hDK hne).mpr ⟨?_, ?_⟩) hxu
    · intro e he
      exact ⟨s, hs, Finset.singleton_subset_iff.mp (hsub e he)⟩
    · exact fun e he => hD.mem_faces he
  let C := (dualCell A {v} hvA).space
  let T : I → Set E := fun s => (dualCell A {s.1.centroid ℝ id} (hsA s)).space
  have hCsub : C ⊆ (graphDualCell K L v).space := by
    have hvA' : {({v} : Finset E).centroid ℝ id} ∈ A.faces := by
      simpa only [Finset.centroid_singleton, id_eq] using hvA
    simpa only [C, Finset.centroid_singleton, id_eq] using
      hdualSpace {v} hv hvA'
  have hTsub (s : I) : T s ⊆ (graphDualCell K L v).space := by
    exact hdualSpace s.1 s.2.1 (hsA s)
  have hspace : (graphDualCell K L v).space = C ∪ ⋃ s : I, T s := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨u, hu, hxu⟩ := (graphDualCell K L v).mem_space_iff.mp hx
      obtain ⟨D, hD, hne, rfl⟩ := derivedNeighborhood_faces_subset K L hu.1
      obtain ⟨hDN, hDA⟩ :=
        (mem_graphDualCell_faces_iff_of_flag L (hL hv) hD hne).mp hu
      obtain ⟨e, he, hbot⟩ := hD.exists_bot hne
      obtain ⟨s, hs, hcse⟩ := hDN e he
      have hsA' : {s.centroid ℝ id} ∈ A.faces :=
        A.down_closed (hDA e he) (Finset.singleton_subset_iff.mpr hcse)
          (Finset.singleton_nonempty _)
      have hDAflag : IsFlag A D := ⟨hDA, hD.2⟩
      have huS : (D.image fun a => a.centroid ℝ id) ∈
          (dualCell A {s.centroid ℝ id} hsA').faces :=
        (mem_dualCell_faces_iff_of_flag hsA' hDAflag hne).mpr fun a ha =>
          Finset.singleton_subset_iff.mpr (hbot a ha hcse)
      have hxS := (dualCell A {s.centroid ℝ id} hsA').convexHull_subset_space huS hxu
      have hcentA : s.centroid ℝ id ∈ A.space :=
        A.convexHull_subset_space (hDA e he) (subset_convexHull ℝ _ hcse)
      have hvs : ({v} : Finset E) ⊆ s :=
        subset_of_mem_dualCell_of_mem_convexHull K (hL hv) (hL hs) hcentA
          (s.centroid_mem_convexHull (L.nonempty_of_mem_faces hs))
      have hpos : 0 < s.card := Finset.card_pos.mpr (L.nonempty_of_mem_faces hs)
      have hle : s.card ≤ 2 := hcard s hs
      have hcases : s.card = 1 ∨ s.card = 2 := by omega
      rcases hcases with hsingle | hedge
      · obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp hsingle
        have hvw : v = w := by
          simpa only [Finset.singleton_subset_iff, Finset.mem_singleton] using hvs
        subst w
        exact Or.inl (by simpa only [C, Finset.centroid_singleton, id_eq] using hxS)
      · exact Or.inr (mem_iUnion.mpr
          ⟨⟨s, hs, hedge, Finset.singleton_subset_iff.mp hvs⟩, hxS⟩)
    · rintro x (hx | hx)
      · exact hCsub hx
      · obtain ⟨s, hxs⟩ := mem_iUnion.mp hx
        exact hTsub s hxs
  have hC : IsPLBall 2 C := by
    simpa only [C] using hA.isPLBall_dualCell A hvA (k := 0)
      (Finset.card_singleton v) (by omega)
  have hT (s : I) : IsPLBall 2 (T s) := by
    simpa only [T] using hA.isPLBall_dualCell A (hsA s) (k := 0)
      (Finset.card_singleton (s.1.centroid ℝ id)) (by omega)
  have hCA : C ⊆ A.space := by
    rw [← (barycentricSubdivision_isSubdivision A).space_eq]
    exact space_mono_of_faces_subset (dualCell_faces_subset A hvA)
  have hTA (s : I) : T s ⊆ A.space := by
    rw [← (barycentricSubdivision_isSubdivision A).space_eq]
    exact space_mono_of_faces_subset (dualCell_faces_subset A (hsA s))
  have hI (s : I) : IsPLBall 1 (C ∩ T s) := by
    exact hA.isPLBall_inter_dualCell_singleton A hvA (hsA s) (hvcentroid s) (hpairA s)
  have hdis (s : I) (t : I) (hst : s ≠ t) : Disjoint (T s) (T t) := by
    have hst' : s.1 ≠ t.1 := fun h => hst (Subtype.ext h)
    have hnot : {s.1.centroid ℝ id, t.1.centroid ℝ id} ∉ A.faces := by
      intro hpair
      have hcomp := subset_or_subset_of_centroid_mem_face K (hsK s) (hsK t)
        (dualCell_faces_subset K (hL hv) hpair)
        (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      rcases hcomp with h | h
      · exact hst' (Finset.eq_of_subset_of_card_le h (by rw [s.2.2.1, t.2.2.1]))
      · exact hst' (Finset.eq_of_subset_of_card_le h (by rw [t.2.2.1, s.2.2.1])).symm
    exact disjoint_dualCell_space A (hsA s) (hsA t)
      (by simpa only [Finset.singleton_union] using hnot)
  rw [hspace]
  simpa only [Finset.mem_univ, iUnion_true] using
    hA.isPLBall_union_iUnion_of_pairwiseDisjoint_in_surface hC hCA Finset.univ T
      (fun s _ => hT s) (fun s _ => hTA s) (fun s _ => hI s)
      (fun s _ t _ hst => hdis s t hst)

end DifferentialGeometry.Topology.PiecewiseLinear
