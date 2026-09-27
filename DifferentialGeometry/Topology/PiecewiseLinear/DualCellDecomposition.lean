/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodCells
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexBallGluing

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem union_mem_faces_of_nonempty_dualCell_inter
    (K : Geometry.SimplicialComplex ℝ E) {s t : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    (hne : ((dualCell K s hs).space ∩ (dualCell K t ht).space).Nonempty) :
    s ∪ t ∈ K.faces := by
  obtain ⟨x, hxs, hxt⟩ := hne
  obtain ⟨u, hu, hxu⟩ := exists_face_mem_openSimplex (dualCell K s hs) hxs
  have hut := mem_faces_of_mem_openSimplex_of_mem_space (dualCell_faces_subset K ht)
    (dualCell_faces_subset K hs hu) hxu hxt
  obtain ⟨d, hd, hdne, rfl⟩ := dualCell_faces_subset K hs hu
  have hsd := (mem_dualCell_faces_iff_of_flag hs hd hdne).mp hu
  have htd := (mem_dualCell_faces_iff_of_flag ht hd hdne).mp hut
  obtain ⟨e, he⟩ := hdne
  exact K.down_closed (hd.mem_faces he) (Finset.union_subset (hsd e he) (htd e he))
    ((K.nonempty_of_mem_faces hs).mono Finset.subset_union_left)

open Classical in
theorem disjoint_dualCell_space (K : Geometry.SimplicialComplex ℝ E) {s t : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hst : s ∪ t ∉ K.faces) :
    Disjoint (dualCell K s hs).space (dualCell K t ht).space :=
  disjoint_left.mpr fun x hxs hxt =>
    hst (union_mem_faces_of_nonempty_dualCell_inter K hs ht ⟨x, hxs, hxt⟩)

open Classical in
theorem dualCell_space_eq_singleton_of_card (K : Geometry.SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) (hcard : ∀ t ∈ K.faces, t.card ≤ s.card) :
    (dualCell K s hs).space = {s.centroid ℝ id} := by
  have hsub : (dualCell K s hs).space ⊆ K.space := by
    rw [← (barycentricSubdivision_isSubdivision K).space_eq]
    exact space_mono_of_faces_subset (dualCell_faces_subset K hs)
  have h := dualCell_space_inter K K Subset.rfl hs hcard
  rwa [inter_eq_left.mpr hsub] at h

open Classical in
theorem finite_inter_dualCell_space_inter (K : Geometry.SimplicialComplex ℝ E)
    {s t u : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hu : u ∈ K.faces)
    (hcard : ∀ v ∈ K.faces, v.card ≤ (s ∪ t ∪ u).card) :
    ((dualCell K s hs).space ∩ (dualCell K t ht).space ∩ (dualCell K u hu).space).Finite := by
  by_cases hst : s ∪ t ∈ K.faces
  · rw [dualCell_space_inter_eq_dualCell K hs ht hst]
    by_cases hstu : s ∪ t ∪ u ∈ K.faces
    · rw [dualCell_space_inter_eq_dualCell K hst hu hstu,
        dualCell_space_eq_singleton_of_card K hstu hcard]
      exact finite_singleton _
    · rw [(disjoint_dualCell_space K hst hu hstu).inter_eq]
      exact finite_empty
  · rw [(disjoint_dualCell_space K hs ht hst).inter_eq, empty_inter]
    exact finite_empty

open Classical in
theorem iUnion_dualCell_singleton_space (K : Geometry.SimplicialComplex ℝ E) :
    (⋃ v : {v : E // ({v} : Finset E) ∈ K.faces}, (dualCell K {v.1} v.2).space) = K.space := by
  apply Subset.antisymm
  · apply iUnion_subset
    intro v
    rw [← (barycentricSubdivision_isSubdivision K).space_eq]
    exact space_mono_of_faces_subset (dualCell_faces_subset K v.2)
  · intro x hx
    have hx' : x ∈ (barycentricSubdivision K).space :=
      (barycentricSubdivision_isSubdivision K).space_eq.symm ▸ hx
    obtain ⟨u, ⟨d, hd, hdne, rfl⟩, hxu⟩ := (barycentricSubdivision K).mem_space_iff.mp hx'
    obtain ⟨s, hs, hbot⟩ := hd.exists_bot hdne
    obtain ⟨v, hvs⟩ := K.nonempty_of_mem_faces (hd.mem_faces hs)
    have hv : {v} ∈ K.faces := K.down_closed (hd.mem_faces hs)
      (Finset.singleton_subset_iff.mpr hvs) (Finset.singleton_nonempty v)
    refine mem_iUnion.mpr ⟨⟨v, hv⟩, (dualCell K {v} hv).convexHull_subset_space ?_ hxu⟩
    exact (mem_dualCell_faces_iff_of_flag hv hd hdne).mpr fun t ht =>
      Finset.singleton_subset_iff.mpr (hbot t ht hvs)

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLBall_inter_dualCell_singleton
    [FiniteDimensional ℝ E] {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 2) K) {v w : E}
    (hv : {v} ∈ K.faces) (hw : {w} ∈ K.faces) (hvw : v ≠ w) (hpair : {v, w} ∈ K.faces) :
    IsPLBall (n + 1) ((dualCell K {v} hv).space ∩ (dualCell K {w} hw).space) := by
  have hpair' : {v} ∪ {w} ∈ K.faces := by simpa only [Finset.singleton_union] using hpair
  rw [dualCell_space_inter_eq_dualCell K hv hw hpair']
  simpa only [Finset.singleton_union, Nat.add_sub_cancel] using
    hK.isPLBall_dualCell K hpair (k := 1) (by simp [hvw]) (by omega)

open Classical in
theorem IsCombinatorialManifoldWithBoundary.inter_dualCell_singleton_subset_boundaryComplex
    [FiniteDimensional ℝ E] {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 2) K) {v w : E}
    (hv : {v} ∈ K.faces) (hw : {w} ∈ K.faces) (hvw : v ≠ w) (hpair : {v, w} ∈ K.faces) :
    (dualCell K {v} hv).space ∩ (dualCell K {w} hw).space ⊆
      (boundaryComplex (n + 2) (dualCell K {v} hv)).space := by
  let _ : Finite (dualCell K {v} hv).faces := (dualCell_faces_finite K hv).to_subtype
  let _ : Finite (dualCell K {w} hw).faces := (dualCell_faces_finite K hw).to_subtype
  exact PiecewiseLinear.inter_subset_boundaryComplex_of_isPLBall
    (PiecewiseLinear.barycentricSubdivision K)
    (dualCell K {v} hv) (dualCell K {w} hw) hK.barycentricSubdivision
    (hK.isPLBall_dualCell K hv (k := 0) (Finset.card_singleton v) (by omega))
    (hK.isPLBall_dualCell K hw (k := 0) (Finset.card_singleton w) (by omega))
    (dualCell_faces_subset K hv) (dualCell_faces_subset K hw)
    (hK.isPLBall_inter_dualCell_singleton K hv hw hvw hpair)

open Classical in
theorem IsCombinatorialManifoldWithBoundary.finite_inter_dualCell_singleton_inter
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) {u v w : E}
    (hu : {u} ∈ K.faces) (hv : {v} ∈ K.faces) (hw : {w} ∈ K.faces)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    ((dualCell K {u} hu).space ∩ (dualCell K {v} hv).space ∩
      (dualCell K {w} hw).space).Finite := by
  apply finite_inter_dualCell_space_inter K hu hv hw
  intro t ht
  simpa [huv, huw, hvw] using hK.card_le K ht

open Classical in
theorem IsCombinatorialManifoldWithBoundary.finite_inter_dualCell_singleton_iUnion
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K)
    (d : Finset {v : E // ({v} : Finset E) ∈ K.faces})
    {u v : {v : E // ({v} : Finset E) ∈ K.faces}}
    (huv : u ≠ v) (hu : u ∉ d) (hv : v ∉ d) :
    ((dualCell K {u.1} u.2).space ∩ (dualCell K {v.1} v.2).space ∩
      (⋃ w ∈ d, (dualCell K {w.1} w.2).space)).Finite := by
  have hfinite : ∀ w ∈ d, ((dualCell K {u.1} u.2).space ∩
      (dualCell K {v.1} v.2).space ∩ (dualCell K {w.1} w.2).space).Finite := by
    intro w hw
    exact hK.finite_inter_dualCell_singleton_inter K u.2 v.2 w.2
      (fun heq => huv (Subtype.ext heq))
      (fun heq => hu ((Subtype.ext heq : u = w).symm ▸ hw))
      (fun heq => hv ((Subtype.ext heq : v = w).symm ▸ hw))
  have h := d.finite_toSet.biUnion hfinite
  simpa only [inter_iUnion, Finset.mem_coe] using h

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_boundary_arcs_cover_inter_dualCell_iUnion
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K)
    (d : Finset {v : E // ({v} : Finset E) ∈ K.faces})
    {v : {v : E // ({v} : Finset E) ∈ K.faces}} (hv : v ∉ d) :
    ∃ e : Finset {v : E // ({v} : Finset E) ∈ K.faces}, e ⊆ d ∧
      (∀ w ∈ e, IsPLBall 1 ((dualCell K {v.1} v.2).space ∩ (dualCell K {w.1} w.2).space) ∧
        (dualCell K {v.1} v.2).space ∩ (dualCell K {w.1} w.2).space ⊆
          (boundaryComplex 2 (dualCell K {v.1} v.2)).space) ∧
      (⋃ w ∈ e, (dualCell K {v.1} v.2).space ∩ (dualCell K {w.1} w.2).space) =
        (dualCell K {v.1} v.2).space ∩ (⋃ w ∈ d, (dualCell K {w.1} w.2).space) := by
  let e := d.filter (fun w => ({v.1, w.1} : Finset E) ∈ K.faces)
  refine ⟨e, Finset.filter_subset _ _, ?_, ?_⟩
  · intro w hw
    obtain ⟨hwd, hpair⟩ := Finset.mem_filter.mp hw
    have hvw : v.1 ≠ w.1 := fun heq => hv ((Subtype.ext heq : v = w).symm ▸ hwd)
    exact ⟨hK.isPLBall_inter_dualCell_singleton K v.2 w.2 hvw hpair,
      hK.inter_dualCell_singleton_subset_boundaryComplex K v.2 w.2 hvw hpair⟩
  · apply Subset.antisymm
    · intro x hx
      obtain ⟨w, hx⟩ := mem_iUnion.mp hx
      obtain ⟨hw, hxv, hxw⟩ := mem_iUnion.mp hx
      exact ⟨hxv, mem_iUnion.mpr ⟨w, mem_iUnion.mpr ⟨(Finset.mem_filter.mp hw).1, hxw⟩⟩⟩
    · rintro x ⟨hxv, hx⟩
      obtain ⟨w, hx⟩ := mem_iUnion.mp hx
      obtain ⟨hw, hxw⟩ := mem_iUnion.mp hx
      have hpair : ({v.1, w.1} : Finset E) ∈ K.faces := by
        simpa only [Finset.singleton_union] using
          union_mem_faces_of_nonempty_dualCell_inter K v.2 w.2 ⟨x, hxv, hxw⟩
      exact mem_iUnion.mpr ⟨w, mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨hw, hpair⟩, hxv, hxw⟩⟩
open Classical in
theorem IsCombinatorialManifold.isPLBall_graphDualCell
    [FiniteDimensional ℝ E] (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 3 K) (hL : L.faces ⊆ K.faces)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) {v : E} (hv : {v} ∈ L.faces) :
    IsPLBall 3 (graphDualCell K L v).space := by
  classical
  let A := dualCell K {v} (hL hv)
  let _ : Finite A.faces := (dualCell_faces_finite K (hL hv)).to_subtype
  have hvA : {v} ∈ A.faces := by
    change {v} ∈ (dualCell K {v} (hL hv)).faces
    simpa only [Finset.centroid_singleton, id_eq] using
      singleton_centroid_mem_dualCell K (hL hv)
  have hAball : IsPLBall 3 A.space := by
    simpa using hK.isPLBall_dualCell K (hL hv) (k := 0)
      (Finset.card_singleton v) (by omega)
  have hA : IsCombinatorialManifoldWithBoundary 3 A :=
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
  have hC : IsPLBall 3 C := by
    simpa only [C] using hA.isPLBall_dualCell A hvA (k := 0)
      (Finset.card_singleton v) (by omega)
  have hT (s : I) : IsPLBall 3 (T s) := by
    simpa only [T] using hA.isPLBall_dualCell A (hsA s) (k := 0)
      (Finset.card_singleton (s.1.centroid ℝ id)) (by omega)
  have hCA : C ⊆ A.space := by
    rw [← (barycentricSubdivision_isSubdivision A).space_eq]
    exact space_mono_of_faces_subset (dualCell_faces_subset A hvA)
  have hTA (s : I) : T s ⊆ A.space := by
    rw [← (barycentricSubdivision_isSubdivision A).space_eq]
    exact space_mono_of_faces_subset (dualCell_faces_subset A (hsA s))
  have hI (s : I) : IsPLBall 2 (C ∩ T s) := by
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
    hA.isPLBall_union_iUnion_of_pairwiseDisjoint hC hCA Finset.univ T
      (fun s _ => hT s) (fun s _ => hTA s) (fun s _ => hI s)
      (fun s _ t _ hst => hdis s t hst)

end DifferentialGeometry.Topology.PiecewiseLinear
