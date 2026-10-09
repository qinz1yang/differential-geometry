/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallStarring
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryFacets
import DifferentialGeometry.Topology.PiecewiseLinear.ClosedStarCone
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedCellCone
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRayEmbedding
import DifferentialGeometry.Topology.PiecewiseLinear.DualCellDecomposition

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLBall_graphDualCell
    [FiniteDimensional ℝ E] (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : L.faces ⊆ K.faces)
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

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLBall_splittingDisk [FiniteDimensional ℝ E]
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) {e : Finset E} (he : e ∈ K.faces)
    {k : ℕ} (hcard : e.card = k + 1) (hk : k ≤ n) :
    IsPLBall (n - k + 1) (splittingDisk K e he).space := by
  classical
  let _ : Finite (dualCell K e he).faces := (dualCell_faces_finite K he).to_subtype
  have hsub := barycentricSubdivision_isSubdivision (dualCell K e he)
  have hball :
      IsPLBall (n - k + 1) (PiecewiseLinear.barycentricSubdivision (dualCell K e he)).space := by
    rw [hsub.space_eq]
    exact hK.isPLBall_dualCell K he hcard hk
  rw [splittingDisk_space]
  exact hball.isCombinatorialManifoldWithBoundary.isPLBall_closedStar
    (hsub.singleton_mem (singleton_centroid_mem_dualCell K he))

open Classical in
theorem IsCombinatorialManifoldWithBoundary.mem_boundaryComplex_starComplex_faces_iff
    [FiniteDimensional ℝ E] {n : ℕ} {X : Geometry.SimplicialComplex ℝ E} [Finite X.faces]
    (hX : IsCombinatorialManifoldWithBoundary (n + 1) X) {c : E} (hc : {c} ∈ X.faces)
    (hlink : IsPLSphere n (SimplicialComplex.geometricLink X {c}).space) {s : Finset E} :
    s ∈ (boundaryComplex (n + 1) (starComplex X c)).faces ↔
      s ∈ (starComplex X c).faces ∧ c ∉ s := by
  classical
  let _ : Finite (starComplex X c).faces := (starComplex_faces_finite X c).to_subtype
  have hball : IsPLBall (n + 1) (starComplex X c).space := by
    rw [starComplex_space X c hc]
    exact hX.isPLBall_closedStar hc
  have hD : IsCombinatorialManifoldWithBoundary (n + 1) (starComplex X c) :=
    hball.isCombinatorialManifoldWithBoundary
  have hcB : {c} ∉ (boundaryComplex (n + 1) X).faces := by
    intro h
    have hb := ((hX.mem_boundaryComplex_faces_iff X).mp h).2.2
    rw [Finset.card_singleton, Nat.add_sub_cancel] at hb
    exact hb.not_isPLSphere hlink
  constructor
  · intro hs
    obtain ⟨hsD, hscard, hb⟩ := (hD.mem_boundaryComplex_faces_iff (starComplex X c)).mp hs
    refine ⟨hsD, fun hcs => ?_⟩
    have hsX : s ∈ X.faces := hsD.1
    have hsB : s ∉ (boundaryComplex (n + 1) X).faces := fun h =>
      hcB ((boundaryComplex (n + 1) X).down_closed h (Finset.singleton_subset_iff.mpr hcs)
        (Finset.singleton_nonempty c))
    obtain ⟨k, hk⟩ : ∃ k, s.card = k + 1 :=
      ⟨s.card - 1, by have := Finset.card_pos.mpr (X.nonempty_of_mem_faces hsX); omega⟩
    have hsph := hX.isPLSphere_geometricLink_of_not_mem_boundaryComplex X hsX hsB hk
      (by omega)
    have hlinkeq : SimplicialComplex.geometricLink (starComplex X c) s =
        SimplicialComplex.geometricLink X s := by
      ext t
      rw [mem_geometricLink_faces_iff, mem_geometricLink_faces_iff, mem_starComplex_faces_iff]
      constructor
      · rintro ⟨hne, hdis, hst, -⟩
        exact ⟨hne, hdis, hst⟩
      · rintro ⟨hne, hdis, hst⟩
        refine ⟨hne, hdis, hst, ?_⟩
        rwa [Finset.insert_eq_of_mem (Finset.mem_union_left t hcs)]
    rw [hlinkeq, hk, show n + 1 - (k + 1) = n - k by omega] at hb
    exact hb.not_isPLSphere hsph
  · rintro ⟨hsD, hcs⟩
    have hsL : s ∈ (SimplicialComplex.geometricLink X {c}).faces :=
      (SimplicialComplex.mem_geometricLink_singleton X c s).mpr
        ⟨X.nonempty_of_mem_faces hsD.1, hcs, hsD.2⟩
    obtain ⟨t, ht, hst, htcard⟩ := exists_face_superset_card_eq_of_isPLSphere _ hlink hsL
    obtain ⟨htne, hct, hinst⟩ := (SimplicialComplex.mem_geometricLink_singleton X c t).mp ht
    have htB : t ∈ (boundaryComplex (n + 1) (starComplex X c)).faces := by
      refine (hD.mem_boundaryComplex_iff_unique_coface (starComplex X c) htcard).mpr ⟨c, ?_⟩
      ext w
      constructor
      · rintro ⟨hwt, hw⟩
        by_contra hwc
        have hle := hX.card_le X hw.2
        have hcw : c ∉ insert w t := by
          rw [Finset.mem_insert, not_or]
          exact ⟨fun h => hwc (mem_singleton_iff.mpr h.symm), hct⟩
        rw [Finset.card_insert_of_notMem hcw, Finset.card_insert_of_notMem hwt, htcard] at hle
        omega
      · intro hwc
        rw [mem_singleton_iff] at hwc
        subst hwc
        exact ⟨hct, hinst, by rwa [Finset.insert_idem]⟩
    exact (boundaryComplex (n + 1) (starComplex X c)).down_closed htB hst
      (X.nonempty_of_mem_faces hsD.1)

open Classical in
theorem IsCombinatorialManifoldWithBoundary.notMem_boundaryComplex_faces_of_forall_mem_interior
    [FiniteDimensional ℝ E] {n : ℕ} (hn : Module.finrank ℝ E = n + 1)
    {A : Geometry.SimplicialComplex ℝ E} [Finite A.faces]
    (hA : IsCombinatorialManifoldWithBoundary (n + 1) A) {s : Finset E} (hs : s ∈ A.faces)
    (hint : ∀ v ∈ s, v ∈ interior A.space) : s ∉ (boundaryComplex (n + 1) A).faces := by
  classical
  intro hsB
  obtain ⟨v, hv⟩ := A.nonempty_of_mem_faces hs
  have hvB : {v} ∈ (boundaryComplex (n + 1) A).faces :=
    (boundaryComplex (n + 1) A).down_closed hsB (Finset.singleton_subset_iff.mpr hv)
      (Finset.singleton_nonempty v)
  have hvfr : v ∈ frontier A.space := by
    rw [frontier_space_eq_boundaryComplex_space_of_finrank hn A hA]
    exact (boundaryComplex (n + 1) A).convexHull_subset_space hvB
      (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_singleton_self v)))
  exact hvfr.2 (hint v hv)

theorem IsCombinatorialManifoldWithBoundary.space_subset_interior_of_forall_vertex
    [FiniteDimensional ℝ E] {n : ℕ} (hn : Module.finrank ℝ E = n + 1)
    {A L : Geometry.SimplicialComplex ℝ E} [Finite A.faces]
    (hA : IsCombinatorialManifoldWithBoundary (n + 1) A) (hLA : L.faces ⊆ A.faces)
    (hint : ∀ v ∈ L.vertices, v ∈ interior A.space) : L.space ⊆ interior A.space := by
  classical
  intro x hx
  obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex L hx
  have hsB := hA.notMem_boundaryComplex_faces_of_forall_mem_interior hn (hLA hs) fun v hv =>
    hint v (L.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v))
  by_contra hxint
  have hxfr : x ∈ frontier A.space :=
    ⟨subset_closure (space_mono_of_faces_subset hLA hx), hxint⟩
  rw [frontier_space_eq_boundaryComplex_space_of_finrank hn A hA] at hxfr
  exact notMem_space_of_notMem_faces (boundaryComplex_faces_subset (n + 1) A) (hLA hs) hsB hxs
    hxfr

theorem IsCombinatorialManifoldWithBoundary.space_subset_interior_iUnion_graphDualCell
    [FiniteDimensional ℝ E] {n : ℕ} (hn : Module.finrank ℝ E = n + 1)
    {A L : Geometry.SimplicialComplex ℝ E} [Finite A.faces]
    (hA : IsCombinatorialManifoldWithBoundary (n + 1) A) (hLA : L.faces ⊆ A.faces)
    (hint : ∀ v ∈ L.vertices, v ∈ interior A.space) :
    L.space ⊆ interior (⋃ v ∈ L.vertices, (graphDualCell A L v).space) := by
  classical
  intro x hx
  rw [show (⋃ v ∈ L.vertices, (graphDualCell A L v).space) =
      (PiecewiseLinear.derivedNeighborhood A L).space from iUnion_graphDualCell_space A L hLA]
  obtain ⟨U, hU, hUsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp
    (derivedNeighborhood_mem_nhdsWithin hLA hx)
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (Filter.inter_mem hU
    (mem_interior_iff_mem_nhds.mp (hA.space_subset_interior_of_forall_vertex hn hLA hint hx)))
    hUsub)

open Classical in
theorem graphDualCell_space_inter_of_mem (K L : Geometry.SimplicialComplex ℝ E)
    (hL : L.faces ⊆ K.faces) (hcard : ∀ s ∈ L.faces, s.card ≤ 2) {e : Finset E}
    (he : e ∈ L.faces) {v w : E} (hv : v ∈ e) (hw : w ∈ e) (hvw : v ≠ w) :
    (graphDualCell K L v).space ∩ (graphDualCell K L w).space =
      (splittingDisk K e (hL he)).space := by
  have hpair : ({v, w} : Finset E) = e := Finset.eq_of_subset_of_card_le
    (Finset.insert_subset_iff.mpr ⟨hv, Finset.singleton_subset_iff.mpr hw⟩)
    (by rw [Finset.card_pair hvw]; exact hcard e he)
  subst hpair
  exact graphDualCell_space_inter K L hL hcard hvw he

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isPLHomeomorphOn_splittingDisk_inter_frontier
    [FiniteDimensional ℝ E] {n k : ℕ} (hn : Module.finrank ℝ E = n + 1)
    {A L : Geometry.SimplicialComplex ℝ E} [Finite A.faces]
    (hA : IsCombinatorialManifoldWithBoundary (n + 1) A) (hLA : L.faces ⊆ A.faces)
    (hint : ∀ v ∈ L.vertices, v ∈ interior A.space) {e : Finset E} (he : e ∈ L.faces)
    (hcard : e.card = k + 1) (hk : k ≤ n) (hmax : ∀ s ∈ L.faces, s.card ≤ e.card) :
    ∃ r : (Fin (n - k + 2) → ℝ) → E,
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin (n - k + 2))) (splittingDisk A e (hLA he)).space ∧
      (splittingDisk A e (hLA he)).space ∩
          frontier (⋃ v ∈ L.vertices, (graphDualCell A L v).space) =
        r '' stdSimplexBoundary (n - k + 1) := by
  classical
  let _ : Finite (dualCell A e (hLA he)).faces := (dualCell_faces_finite A (hLA he)).to_subtype
  let _ : Finite (splittingDisk A e (hLA he)).faces :=
    (splittingDisk_faces_finite A (hLA he)).to_subtype
  have hsub := barycentricSubdivision_isSubdivision (dualCell A e (hLA he))
  have hcX :
      {e.centroid ℝ id} ∈ (PiecewiseLinear.barycentricSubdivision (dualCell A e (hLA he))).faces :=
    hsub.singleton_mem (singleton_centroid_mem_dualCell A (hLA he))
  have heB : e ∉ (boundaryComplex (n + 1) A).faces :=
    hA.notMem_boundaryComplex_faces_of_forall_mem_interior hn (hLA he) fun v hv =>
      hint v (L.down_closed he (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v))
  have hXball : IsPLBall (n - k + 1)
      (PiecewiseLinear.barycentricSubdivision (dualCell A e (hLA he))).space := by
    rw [hsub.space_eq]
    exact hA.isPLBall_dualCell A (hLA he) hcard hk
  have hlink : IsPLSphere (n - k)
      (SimplicialComplex.geometricLink
        (PiecewiseLinear.barycentricSubdivision (dualCell A e (hLA he)))
        {e.centroid ℝ id}).space := by
    rw [isPLSphere_geometricLink_iff_of_isSubdivision hsub
      (singleton_centroid_mem_dualCell A (hLA he)), geometricLink_dualCell]
    exact hA.isPLSphere_upperLink_of_not_mem_boundaryComplex A (hLA he) heB hcard hk
  have hbd : ∀ u, u ∈ (boundaryComplex (n - k + 1) (splittingDisk A e (hLA he))).faces ↔
      u ∈ (splittingDisk A e (hLA he)).faces ∧ e.centroid ℝ id ∉ u := fun u =>
    hXball.isCombinatorialManifoldWithBoundary.mem_boundaryComplex_starComplex_faces_iff hcX
      hlink
  have hNint : (PiecewiseLinear.derivedNeighborhood A L).space ⊆ interior A.space :=
    derivedNeighborhood_space_subset_interior hn hA hLA
      (hA.space_subset_interior_of_forall_vertex hn hLA hint)
  have hDN :
      (splittingDisk A e (hLA he)).space ⊆ (PiecewiseLinear.derivedNeighborhood A L).space := by
    intro x hx
    obtain ⟨u, hu, hxu⟩ := (splittingDisk A e (hLA he)).mem_space_iff.mp hx
    obtain ⟨Δ, hΔ, hne, rfl⟩ := splittingDisk_faces_subset A (hLA he) hu
    have hc := ((mem_splittingDisk_faces_iff_of_flag (hLA he) hΔ hne).mp hu).2
    exact (PiecewiseLinear.derivedNeighborhood A L).convexHull_subset_space
      ((mem_derivedNeighborhood_faces_iff_of_flag hΔ hne).mpr fun σ hσ => ⟨e, he, hc σ hσ⟩) hxu
  have hflag : ∀ {Δ : Finset (Finset E)}, IsFlag (PiecewiseLinear.barycentricSubdivision A) Δ →
      Δ.Nonempty → ∀ {x : E}, x ∈ openSimplex (Δ.image fun s => s.centroid ℝ id) →
      ∃ T ∈ Δ, (∀ σ ∈ Δ, σ ⊆ T) ∧ x ∈ openSimplex T ∧ x ∈ convexHull ℝ (T : Set E) ∧
        x ∈ (PiecewiseLinear.barycentricSubdivision A).space ∧ (∀ v, barycentricCoordinate
          (PiecewiseLinear.barycentricSubdivision A) v x = if v ∈ T then weights T x v else 0) ∧
        ∃ μ : Finset E → ℝ, (∀ σ ∈ Δ, 0 < μ σ) ∧ ∑ σ ∈ Δ, μ σ = 1 ∧
          ∑ σ ∈ Δ, μ σ • σ.centroid ℝ id = x := by
    intro Δ hΔ hne x hx
    obtain ⟨T, hT, htop⟩ := hΔ.exists_top hne
    have hTA := hΔ.mem_faces hT
    have hxTo : x ∈ openSimplex T := mem_openSimplex_top (PiecewiseLinear.barycentricSubdivision A)
      (centroid_mem_openSimplex_of_mem_faces (PiecewiseLinear.barycentricSubdivision A)) hΔ hT
      htop hx
    have hxT : x ∈ convexHull ℝ (T : Set E) := openSimplex_subset_convexHull T hxTo
    obtain ⟨μ, hμ0, hμ1, hμx⟩ := (mem_openSimplex_image_iff
      (hΔ.injOn (PiecewiseLinear.barycentricSubdivision A)
        (centroid_mem_openSimplex_of_mem_faces (PiecewiseLinear.barycentricSubdivision A)))).mp hx
    exact ⟨T, hT, htop, hxTo, hxT,
      (PiecewiseLinear.barycentricSubdivision A).convexHull_subset_space hTA hxT,
      barycentricCoordinate_eq _ hTA hxT, μ, hμ0, hμ1, hμx⟩
  obtain ⟨r, hr⟩ := hA.isPLBall_splittingDisk A (hLA he) hcard hk
  refine ⟨r, hr, ?_⟩
  rw [show (⋃ v ∈ L.vertices, (graphDualCell A L v).space) =
      (PiecewiseLinear.derivedNeighborhood A L).space from iUnion_graphDualCell_space A L hLA,
    hr.image_stdSimplexBoundary_eq_boundaryComplex _ rfl]
  have hcL : e.centroid ℝ id ∈ (PiecewiseLinear.barycentricSubdivision L).vertices :=
    singleton_centroid_mem_barycentricSubdivision L he
  apply Subset.antisymm
  · rintro x ⟨hxD, hxfr⟩
    obtain ⟨u, hu, hxu⟩ := exists_face_mem_openSimplex _ hxD
    by_cases hcu : e.centroid ℝ id ∈ u
    · exfalso
      obtain ⟨Δ, hΔ, hne, rfl⟩ := splittingDisk_faces_subset A (hLA he) hu
      have hΔc := ((mem_splittingDisk_faces_iff_of_flag (hLA he) hΔ hne).mp hu).2
      obtain ⟨σ, hσ, hσc⟩ := Finset.mem_image.mp hcu
      have hσeq : σ = {e.centroid ℝ id} :=
        injOn_faces_of_mem_openSimplex _ (centroid_mem_openSimplex_of_mem_faces _)
          (hΔ.mem_faces hσ) (singleton_centroid_mem_barycentricSubdivision A (hLA he))
          (by rw [hσc, Finset.centroid_singleton]; rfl)
      subst hσeq
      obtain ⟨T, hT, htop, hxTo, hxT, hxA, hβ, μ, hμ0, hμ1, hμx⟩ := hflag hΔ hne hxu
      have hTind := (PiecewiseLinear.barycentricSubdivision A).indep (hΔ.mem_faces hT)
      have hd : ∀ τ ∈ Δ, τ.Nonempty ∧ τ ⊆ T := fun τ hτ =>
        ⟨(PiecewiseLinear.barycentricSubdivision A).nonempty_of_mem_faces (hΔ.mem_faces hτ),
          htop τ hτ⟩
      have hcT : e.centroid ℝ id ∈ T := htop _ hσ (Finset.mem_singleton_self _)
      have hcpos : 0 < weights T x (e.centroid ℝ id) :=
        (mem_openSimplex_self_iff hTind hxT).mp hxTo _ hcT
      have hlt : ∀ v, v ≠ e.centroid ℝ id →
          barycentricCoordinate (PiecewiseLinear.barycentricSubdivision A) v x <
            barycentricCoordinate (PiecewiseLinear.barycentricSubdivision A)
              (e.centroid ℝ id) x := by
        intro v hvc
        rw [hβ v, hβ (e.centroid ℝ id), ite_eq_left hcT]
        split_ifs with hvT
        · rw [← hμx]
          exact weights_sum_centroid_lt_of_notMem_min hTind hd hσ
            (fun τ hτ => Finset.singleton_subset_iff.mpr (hΔc τ hτ)) (fun τ hτ => (hμ0 τ hτ).le)
            hμ1 (hμ0 _ hσ) hvT (fun h => hvc (Finset.mem_singleton.mp h))
            (Finset.mem_singleton_self _)
        · exact hcpos
      exact hxfr.2 (mem_interior_derivedNeighborhood_of_barycentricCoordinate_lt (hNint (hDN hxD))
        hcL fun w hw => hlt w fun h => hw (by rw [h]; exact hcL))
    · exact (boundaryComplex _ _).convexHull_subset_space ((hbd u).mpr ⟨hu, hcu⟩)
        (openSimplex_subset_convexHull u hxu)
  · intro x hx
    obtain ⟨u, hu, hxu⟩ := exists_face_mem_openSimplex _ hx
    obtain ⟨huD, hcu⟩ := (hbd u).mp hu
    have hxD : x ∈ (splittingDisk A e (hLA he)).space :=
      (splittingDisk A e (hLA he)).convexHull_subset_space huD (openSimplex_subset_convexHull u hxu)
    refine ⟨hxD, subset_closure (hDN hxD), ?_⟩
    obtain ⟨Δ, hΔ, hne, rfl⟩ := splittingDisk_faces_subset A (hLA he) huD
    obtain ⟨hΔdual, hΔc⟩ := (mem_splittingDisk_faces_iff_of_flag (hLA he) hΔ hne).mp huD
    obtain ⟨m, hm, hbot⟩ := hΔ.exists_bot hne
    have hcm : e.centroid ℝ id ∈ m := hΔc m hm
    have hm1 : 1 < m.card := by
      by_contra hle
      apply hcu
      have hmeq : m = {e.centroid ℝ id} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hcm, fun y hy => Finset.card_le_one.mp (not_lt.mp hle) y hy _ hcm⟩
      exact Finset.mem_image.mpr ⟨m, hm, by rw [hmeq, Finset.centroid_singleton]; rfl⟩
    obtain ⟨w, hwm, hwc⟩ := Finset.exists_mem_ne hm1 (e.centroid ℝ id)
    obtain ⟨T, hT, htop, -, hxT, hxA, hβ, μ, hμ0, hμ1, hμx⟩ := hflag hΔ hne hxu
    have hTind := (PiecewiseLinear.barycentricSubdivision A).indep (hΔ.mem_faces hT)
    have hd : ∀ τ ∈ Δ, τ.Nonempty ∧ τ ⊆ T := fun τ hτ =>
      ⟨(PiecewiseLinear.barycentricSubdivision A).nonempty_of_mem_faces (hΔ.mem_faces hτ),
        htop τ hτ⟩
    have hle : ∀ v, barycentricCoordinate (PiecewiseLinear.barycentricSubdivision A) v x ≤
        barycentricCoordinate (PiecewiseLinear.barycentricSubdivision A) w x := by
      intro v
      rw [hβ v, hβ w, ite_eq_left (htop m hm hwm)]
      split_ifs with hvT
      · rw [← hμx]
        exact (weights_sum_centroid_le_of_mem_min hTind hd hm hbot (fun τ hτ => (hμ0 τ hτ).le)
          hμ1 hvT hcm).trans (weights_sum_centroid_le_of_mem_min hTind hd hm hbot
            (fun τ hτ => (hμ0 τ hτ).le) hμ1 (htop m hm hcm) hwm)
      · exact weights_nonneg hxT (htop m hm hwm)
    have hwL : w ∉ (PiecewiseLinear.barycentricSubdivision L).vertices := by
      intro hwL
      obtain ⟨t, ht, htw⟩ := exists_eq_centroid_of_singleton_mem_barycentricSubdivision L hwL
      have hwD : w ∈ (dualCell A e (hLA he)).space :=
        (dualCell A e (hLA he)).convexHull_subset_space (hΔdual m hm)
          (subset_convexHull ℝ _ (Finset.mem_coe.mpr hwm))
      have hwt : w ∈ convexHull ℝ (t : Set E) := by
        rw [← htw]
        exact t.centroid_mem_convexHull (L.nonempty_of_mem_faces ht)
      have het := subset_of_mem_dualCell_of_mem_convexHull A (hLA he) (hLA ht) hwD hwt
      have heq : e = t := Finset.eq_of_subset_of_card_le het (hmax t ht)
      exact hwc (by rw [← htw, ← heq])
    exact notMem_interior_derivedNeighborhood_of_barycentricCoordinate_le hxA hwL
      (barycentricCoordinate_pos_of_forall_le hxA hle) fun v _ => hle v

end DifferentialGeometry.Topology.PiecewiseLinear
