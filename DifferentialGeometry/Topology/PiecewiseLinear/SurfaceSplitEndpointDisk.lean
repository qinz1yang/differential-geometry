/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.StarIntersection
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitCompatibleSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitCurveGluing

/-! Endpoint disks cut out by derived neighborhoods of embedded disks. -/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
open Classical in
theorem derivedNeighborhood_space_inter_subcomplex
    (K A B : Geometry.SimplicialComplex ℝ E)
    (hBK : B.faces ⊆ K.faces) (hAB : A.faces ⊆ B.faces) :
    (PiecewiseLinear.derivedNeighborhood K A).space ∩ B.space =
      (PiecewiseLinear.derivedNeighborhood B A).space := by
  classical
  have hAK : A.faces ⊆ K.faces := hAB.trans hBK
  have hcell (s : Finset E) (hs : s ∈ A.faces) :
      (derivedNeighborhoodCell K s).space ∩ B.space =
        (derivedNeighborhoodCell B s).space := by
    rw [derivedNeighborhoodCell_space_eq_closedStar K (hAK hs),
      ← (barycentricSubdivision_isSubdivision B).space_eq,
      derivedNeighborhoodCell_space_eq_closedStar B (hAB hs)]
    exact closedStar_barycentricSubdivision_inter_space_eq
      (barycentricSubdivision_faces_subset hBK)
      (singleton_centroid_mem_barycentricSubdivision B (hAB hs))
  rw [← iUnion_derivedNeighborhoodCell_space K A hAK,
    ← iUnion_derivedNeighborhoodCell_space B A hAB]
  apply Subset.antisymm
  · rintro x ⟨hx, hxB⟩
    obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨s, hs, (hcell s hs).subset ⟨hxs, hxB⟩⟩
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
    have hx' := (hcell s hs).symm.subset hxs
    exact ⟨mem_iUnion₂.mpr ⟨s, hs, hx'.1⟩, hx'.2⟩

open Classical in
private theorem isPLBall_derivedNeighborhoodCell_inter_edge_one
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K)
    {t s : Finset E} (ht : t ∈ K.faces) (hs : s ∈ K.faces)
    (htcard : t.card = 3) (hscard : s.card = 2) (hst : s ⊆ t) :
    IsPLBall 1 ((derivedNeighborhoodCell K t).space ∩
      ((derivedNeighborhoodCell K s).space ∪
        ⋃ v ∈ s, (derivedNeighborhoodCell K {v}).space)) := by
  classical
  let d := s.image (fun v => ({v} : Finset E))
  have htne : t ≠ s := by
    intro heq
    have hc := congrArg Finset.card heq
    omega
  have hdspace : (⋃ u ∈ d, (derivedNeighborhoodCell K u).space) =
      ⋃ v ∈ s, (derivedNeighborhoodCell K {v}).space := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      exact mem_iUnion₂.mpr ⟨v, hv, hxu⟩
    · intro x hx
      obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion₂.mpr ⟨{v}, Finset.mem_image.mpr ⟨v, hv, rfl⟩, hxv⟩
  have hvK (v : E) (hv : v ∈ s) : {v} ∈ K.faces :=
    K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  have h := hK.isPLBall_derivedNeighborhoodCell_inter_union_of_mem_faces_one ht hs htne
    (Or.inr hst) d
    (by intro u hu; obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu; exact hvK v hv)
    (by
      intro u hu
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      constructor <;> intro heq <;> have hc := congrArg Finset.card heq
      · simp only [Finset.card_singleton, htcard] at hc
        omega
      · simp only [Finset.card_singleton, hscard] at hc
        omega)
    (by
      intro u hu
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      exact ⟨Or.inr (Finset.singleton_subset_iff.mpr (hst hv)),
        Or.inr (Finset.singleton_subset_iff.mpr hv)⟩)
    (by
      intro u hu v hv huv
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
      simp only [Finset.singleton_subset_iff, Finset.mem_singleton]
      exact ⟨fun h => huv (h ▸ rfl), fun h => huv (h.symm ▸ rfl)⟩)
  rwa [hdspace] at h

open Classical in
private theorem isPLBall_derivedNeighborhoodCell_inter_erase_of_s_card_two_one
    {K A : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hA : IsPLBall 2 A.space)
    (hAK : A.faces ⊆ K.faces)
    {t s : Finset E} (ht : t ∈ A.faces) (htcard : t.card = 3)
    (hst : s ⊆ t) (hscard : s.card = 2)
    (htrace : (boundaryComplex 2 A).space ∩ convexHull ℝ (t : Set E) =
      ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset E) : Set E))
    (hinter : ∀ u ∈ A.faces, u.card = 3 → ¬s ⊆ u →
      (u ∩ t).card ≤ 1 ∧ (s.card = 2 → u ∩ t ⊆ s)) :
    IsPLBall 1 ((derivedNeighborhoodCell K t).space ∩
      (derivedNeighborhood K (eraseTriangleComplex A t)).space) := by
  classical
  let A' := eraseTriangleComplex A t
  have hA'K : A'.faces ⊆ K.faces :=
    (eraseTriangleComplex_faces_subset A t).trans hAK
  have htK := hAK ht
  have htA' : t ∉ A'.faces := by
    intro ht'
    exact ((mem_eraseTriangleComplex_triangle_iff A t
      (fun u hu => card_le_of_isPLBall A hA hu) htcard).mp ht').2 rfl
  have heq := derivedNeighborhoodCell_inter_derivedNeighborhood_eq_subfaces
    K A' hA'K htK htA'
  have hunion := iUnion_eraseTriangleComplex_subfaces_eq_edge A hA ht htcard hst hscard
    htrace hinter (fun r => (derivedNeighborhoodCell K r).space)
  rw [heq, hunion]
  exact isPLBall_derivedNeighborhoodCell_inter_edge_one hK htK
    (hAK (A.down_closed ht hst (Finset.card_pos.mp (by omega)))) htcard hscard hst

open Classical in
private theorem isPLBall_derivedNeighborhoodCell_inter_vertex_one
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K)
    {t s : Finset E} (ht : t ∈ K.faces)
    (htcard : t.card = 3) (hscard : s.card = 1) (hst : s ⊆ t) :
    let q := t \ s
    let edges := t.powersetCard 2 |>.filter (fun e => s ⊆ e)
    IsPLBall 1 ((derivedNeighborhoodCell K t).space ∩
      (((derivedNeighborhoodCell K s).space ∪
        ⋃ e ∈ edges, (derivedNeighborhoodCell K e).space) ∪
          ⋃ v ∈ q, (derivedNeighborhoodCell K {v}).space)) := by
  classical
  dsimp only
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hscard
  let q := t \ {a}
  let edges := t.powersetCard 2 |>.filter (fun e => ({a} : Finset E) ⊆ e)
  let C := fun r : Finset E => (derivedNeighborhoodCell K r).space
  let B := (derivedNeighborhoodCellBase K t).space
  let D := C t ∩ (C {a} ∪ ⋃ e ∈ edges, C e)
  let P := fun e : Finset E => C t ∩ C e
  let A := fun v : E => C t ∩ C {v}
  have htK := ht
  have hat : a ∈ t := Finset.singleton_subset_iff.mp hst
  have haK : {a} ∈ K.faces := K.down_closed htK hst (Finset.singleton_nonempty a)
  have htneA : t ≠ {a} := by
    intro heq
    have hc := congrArg Finset.card heq
    simp only [Finset.card_singleton, htcard] at hc
    omega
  let _ : Finite (derivedNeighborhoodCellBase K t).faces :=
    (upperLink_faces_finite (PiecewiseLinear.barycentricSubdivision K)
      {t.centroid ℝ id}).to_subtype
  have hbase := hK.isCombinatorialManifoldWithBoundary_derivedNeighborhoodCellBase_one htK
  have hedge (e : Finset E) (he : e ∈ edges) : e ⊆ t ∧ e.card = 2 ∧ a ∈ e := by
    have hep := (Finset.mem_filter.mp he).1
    exact ⟨(Finset.mem_powersetCard.mp hep).1, (Finset.mem_powersetCard.mp hep).2,
      Finset.singleton_subset_iff.mp (Finset.mem_filter.mp he).2⟩
  have heK (e : Finset E) (he : e ∈ edges) : e ∈ K.faces :=
    K.down_closed htK (hedge e he).1 (Finset.card_pos.mp (by rw [(hedge e he).2.1]; decide))
  have hte (e : Finset E) (he : e ∈ edges) : t ≠ e := by
    intro heq
    have hc := congrArg Finset.card heq
    rw [htcard, (hedge e he).2.1] at hc
    omega
  have hD : IsPLBall 1 D := by
    exact hK.isPLBall_derivedNeighborhoodCell_inter_union_of_mem_faces_one htK haK htneA
      (Or.inr (Finset.singleton_subset_iff.mpr hat)) edges heK
      (by
        intro e he
        constructor
        · intro heq
          have hc := congrArg Finset.card heq
          rw [(hedge e he).2.1, htcard] at hc
          omega
        · intro heq
          have hc := congrArg Finset.card heq
          simp only [(hedge e he).2.1, Finset.card_singleton] at hc
          omega)
      (by
        intro e he
        exact ⟨Or.inr (hedge e he).1,
          Or.inl (Finset.singleton_subset_iff.mpr (hedge e he).2.2)⟩)
      (by
        intro e he f hf hef
        have hec := (hedge e he).2.1
        have hfc := (hedge f hf).2.1
        exact ⟨fun h => hef (Finset.eq_of_subset_of_card_le h (by omega)),
          fun h => hef (Finset.eq_of_subset_of_card_le h (by omega)).symm⟩)
  have hDB : D ⊆ B := by
    rintro x ⟨hxt, hxa | hxe⟩
    · exact derivedNeighborhoodCell_inter_subset_base K htK haK htneA ⟨hxt, hxa⟩
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxe
      exact derivedNeighborhoodCell_inter_subset_base K htK (heK e he) (hte e he) ⟨hxt, hxe⟩
  have hqcard : q.card = 2 := by
    dsimp [q]
    rw [Finset.card_sdiff_of_subset hst, htcard, Finset.card_singleton]
  have hvK (v : E) (hv : v ∈ q) : {v} ∈ K.faces :=
    K.down_closed htK (Finset.singleton_subset_iff.mpr (Finset.mem_sdiff.mp hv).1)
      (Finset.singleton_nonempty v)
  have hvne (v : E) (hv : v ∈ q) : v ≠ a := by
    intro heq
    exact (Finset.mem_sdiff.mp hv).2 (heq ▸ Finset.mem_singleton_self a)
  have hA (v : E) (hv : v ∈ q) : IsPLBall 1 (A v) :=
    hK.isPLBall_derivedNeighborhoodCell_inter htK (hvK v hv)
      (by intro heq; have hc := congrArg Finset.card heq;
          simp only [Finset.card_singleton, htcard] at hc; omega)
      (Or.inr (Finset.singleton_subset_iff.mpr (Finset.mem_sdiff.mp hv).1))
  have hAB (v : E) (hv : v ∈ q) : A v ⊆ B :=
    derivedNeighborhoodCell_inter_subset_base K htK (hvK v hv)
      (by intro heq; have hc := congrArg Finset.card heq;
          simp only [Finset.card_singleton, htcard] at hc; omega)
  have hDI (v : E) (hv : v ∈ q) : IsPLBall 0 (D ∩ A v) := by
    let e : Finset E := {a, v}
    have hecard : e.card = 2 := Finset.card_pair (hvne v hv).symm
    have het : e ⊆ t := by
      intro w hw
      simp only [e, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hat
      · exact (Finset.mem_sdiff.mp hv).1
    have heEdges : e ∈ edges := Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨het, hecard⟩,
        Finset.singleton_subset_iff.mpr (Finset.mem_insert_self a {v})⟩
    have heK' := heK e heEdges
    have heq : D ∩ A v = C t ∩ C e ∩ C {v} := by
      apply Subset.antisymm
      · rintro x ⟨hxD, hxt, hxv⟩
        have hright : x ∈ C e := by
          rcases hxD.2 with hxa | hxe
          · have hdis := disjoint_derivedNeighborhoodCell_space K haK (hvK v hv)
                (by simpa only [Finset.singleton_subset_iff, Finset.mem_singleton] using
                  (hvne v hv).symm)
                (by simpa only [Finset.singleton_subset_iff, Finset.mem_singleton] using hvne v hv)
            exact (hdis.le_bot ⟨hxa, hxv⟩).elim
          · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hxe
            rcases subset_or_subset_of_nonempty_derivedNeighborhoodCell_inter K
                (heK f hf) (hvK v hv) ⟨x, hxf, hxv⟩ with hfv | hvf
            · have hc := Finset.card_le_card hfv
              rw [(hedge f hf).2.1, Finset.card_singleton] at hc
              omega
            · have hvfmem : v ∈ f := Finset.singleton_subset_iff.mp hvf
              have hef : e = f := Finset.eq_of_subset_of_card_le (by
                intro w hw
                simp only [e, Finset.mem_insert, Finset.mem_singleton] at hw
                rcases hw with rfl | rfl
                · exact (hedge f hf).2.2
                · exact hvfmem) (by rw [hecard, (hedge f hf).2.1])
              exact hef ▸ hxf
        exact ⟨⟨hxt, hright⟩, hxv⟩
      · rintro x ⟨⟨hxt, hxe⟩, hxv⟩
        exact ⟨⟨hxt, Or.inr (mem_iUnion₂.mpr ⟨e, heEdges, hxe⟩)⟩, hxt, hxv⟩
    rw [heq]
    exact hK.isPLBall_derivedNeighborhoodCell_inter_inter_zero htK heK' (hvK v hv)
      (by intro heq'; have hc := congrArg Finset.card heq'; rw [htcard, hecard] at hc; omega)
      (by intro heq'; have hc := congrArg Finset.card heq';
          simp only [Finset.card_singleton, htcard] at hc; omega)
      (by intro heq'; have hc := congrArg Finset.card heq';
          simp only [Finset.card_singleton, hecard] at hc; omega)
      (Or.inr het) (Or.inr (Finset.singleton_subset_iff.mpr (Finset.mem_sdiff.mp hv).1))
      (Or.inr (Finset.singleton_subset_iff.mpr
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self v))))
  have hAdis (v : E) (hv : v ∈ q) (w : E) (hw : w ∈ q) (hvw : v ≠ w) :
      Disjoint (A v) (A w) :=
    (disjoint_derivedNeighborhoodCell_space K (hvK v hv) (hvK w hw)
      (by simpa only [Finset.singleton_subset_iff, Finset.mem_singleton] using hvw)
      (by simpa only [Finset.singleton_subset_iff, Finset.mem_singleton] using hvw.symm)).mono
        inter_subset_right inter_subset_right
  have hball := hbase.isPLBall_union_iUnion_of_pairwiseDisjoint_in_curve hD hDB
    q A hA hAB hDI hAdis
  simpa only [D, C, A, inter_union_distrib_left, inter_iUnion, union_assoc] using hball

open Classical in
private theorem isPLBall_derivedNeighborhoodCell_inter_erase_of_s_card_one_one
    {K A : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hA : IsPLBall 2 A.space)
    (hAK : A.faces ⊆ K.faces)
    {t s : Finset E} (ht : t ∈ A.faces) (htcard : t.card = 3)
    (hst : s ⊆ t) (hscard : s.card = 1)
    (htrace : (boundaryComplex 2 A).space ∩ convexHull ℝ (t : Set E) =
      ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset E) : Set E))
    (hinter : ∀ u ∈ A.faces, u.card = 3 → ¬s ⊆ u →
      (u ∩ t).card ≤ 1 ∧ (s.card = 2 → u ∩ t ⊆ s)) :
    IsPLBall 1 ((derivedNeighborhoodCell K t).space ∩
      (derivedNeighborhood K (eraseTriangleComplex A t)).space) := by
  classical
  let A' := eraseTriangleComplex A t
  have hA'K : A'.faces ⊆ K.faces :=
    (eraseTriangleComplex_faces_subset A t).trans hAK
  have htK := hAK ht
  have htA' : t ∉ A'.faces := by
    intro ht'
    exact ((mem_eraseTriangleComplex_triangle_iff A t
      (fun u hu => card_le_of_isPLBall A hA hu) htcard).mp ht').2 rfl
  have heq := derivedNeighborhoodCell_inter_derivedNeighborhood_eq_subfaces
    K A' hA'K htK htA'
  have hunion := iUnion_eraseTriangleComplex_subfaces_eq_vertex A hA ht htcard hst hscard
    htrace hinter (fun r => (derivedNeighborhoodCell K r).space)
  rw [heq, hunion]
  exact isPLBall_derivedNeighborhoodCell_inter_vertex_one hK (hAK ht) htcard hscard hst

open Classical in
private theorem
    IsCombinatorialManifoldWithBoundary.isPLBall_free_triangle_surface_one
    {K A : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hA : IsPLBall 2 A.space)
    (hAK : A.faces ⊆ K.faces)
    {t s : Finset E} (ht : t ∈ A.faces) (htcard : t.card = 3)
    (hst : s ⊆ t) (hscard : s.card = 1)
    (htrace : (boundaryComplex 2 A).space ∩ convexHull ℝ (t : Set E) =
      ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset E) : Set E))
    (hinter : ∀ u ∈ A.faces, u.card = 3 → ¬s ⊆ u →
      (u ∩ t).card ≤ 1 ∧ (s.card = 2 → u ∩ t ⊆ s))
    (hprev : IsPLBall 2 (PiecewiseLinear.derivedNeighborhood K
      (eraseTriangleComplex A t)).space) :
    IsPLBall 2 (PiecewiseLinear.derivedNeighborhood K A).space := by
  classical
  let A' := eraseTriangleComplex A t
  let q := t \ s
  let C := fun r : Finset E => (derivedNeighborhoodCell K r).space
  let N := (PiecewiseLinear.derivedNeighborhood K A').space
  have hAKK : A.faces ⊆ K.faces := hAK
  have hA'K : A'.faces ⊆ K.faces := (eraseTriangleComplex_faces_subset A t).trans hAKK
  have htK := hAKK ht
  have htball : IsPLBall 2 (C t) := hK.isPLBall_derivedNeighborhoodCell htK
  have hD : IsPLBall 1 (C t ∩ N) :=
    isPLBall_derivedNeighborhoodCell_inter_erase_of_s_card_one_one hK hA hAK ht htcard
      hst hscard htrace hinter
  have hmeet₁ : N ∩ C t = C t ∩ N := inter_comm _ _
  have hI₁ : IsPLBall 1 (N ∩ C t) := hmeet₁ ▸ hD
  have hNK : N ⊆ K.space := derivedNeighborhood_space_subset K A'
  have htspaceK : C t ⊆ K.space := derivedNeighborhoodCell_space_subset K t
  have hfirst : IsPLBall 2 (N ∪ C t) :=
    hK.isPLBall_union_of_inter_isPLBall_one hprev htball hNK htspaceK hI₁
  have hqcard : q.card = 2 := by
    dsimp [q]
    rw [Finset.card_sdiff_of_subset hst, htcard, hscard]
  have hqne : q.Nonempty := Finset.card_pos.mp (by omega)
  have hqA : q ∈ A.faces := A.down_closed ht Finset.sdiff_subset hqne
  have hqK := hAK hqA
  have hqball : IsPLBall 2 (C q) := hK.isPLBall_derivedNeighborhoodCell hqK
  have hfree (r : Finset E) : r ∈ A'.faces ↔ r ∈ A.faces ∧ ¬q ⊆ r :=
    mem_eraseTriangleComplex_iff_of_free_triangle A hA ht htcard hst
      (Or.inl hscard) htrace hinter
  have hqA' : q ∉ A'.faces := fun h => ((hfree q).mp h).2 Finset.Subset.rfl
  have hqold := derivedNeighborhoodCell_inter_derivedNeighborhood_eq_subfaces K A'
    hA'K hqK hqA'
  have hqsub := iUnion_eraseTriangleComplex_subfaces_free_edge A hA ht htcard hst hscard
    htrace hinter C
  rw [hqsub] at hqold
  have hmeet₂ : (N ∪ C t) ∩ C q = C q ∩ (C t ∪ ⋃ v ∈ q, C {v}) := by
    apply Subset.antisymm
    · rintro x ⟨hxN | hxt, hxq⟩
      · have hx : x ∈ C q ∩ N := ⟨hxq, hxN⟩
        rw [hqold] at hx
        exact ⟨hxq, Or.inr hx.2⟩
      · exact ⟨hxq, Or.inl hxt⟩
    · rintro x ⟨hxq, hxt | hxv⟩
      · exact ⟨Or.inr hxt, hxq⟩
      · have hxold : x ∈ C q ∩ N := by
          rw [hqold]
          exact ⟨hxq, hxv⟩
        exact ⟨Or.inl hxold.2, hxq⟩
  let d := q.image (fun v => ({v} : Finset E))
  have hdspace : (⋃ u ∈ d, C u) = ⋃ v ∈ q, C {v} := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      exact mem_iUnion₂.mpr ⟨v, hv, hxu⟩
    · intro x hx
      obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion₂.mpr ⟨{v}, Finset.mem_image.mpr ⟨v, hv, rfl⟩, hxv⟩
  have hqt : q ≠ t := by
    intro heq
    have hc := congrArg Finset.card heq
    rw [hqcard, htcard] at hc
    omega
  have hd (u : Finset E) (hu : u ∈ d) : u ∈ K.faces := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    exact K.down_closed hqK (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  have hdne (u : Finset E) (hu : u ∈ d) : u ≠ q ∧ u ≠ t := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    constructor <;> intro heq <;> have hc := congrArg Finset.card heq
    · simp only [Finset.card_singleton, hqcard] at hc
      omega
    · simp only [Finset.card_singleton, htcard] at hc
      omega
  have hdcomp (u : Finset E) (hu : u ∈ d) :
      (q ⊆ u ∨ u ⊆ q) ∧ (t ⊆ u ∨ u ⊆ t) := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    exact ⟨Or.inr (Finset.singleton_subset_iff.mpr hv),
      Or.inr (Finset.singleton_subset_iff.mpr (Finset.sdiff_subset hv))⟩
  have hdincomp (u : Finset E) (hu : u ∈ d) (v : Finset E) (hv : v ∈ d)
      (huv : u ≠ v) : ¬u ⊆ v ∧ ¬v ⊆ u := by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
    simp only [Finset.singleton_subset_iff, Finset.mem_singleton]
    exact ⟨fun h => huv (h ▸ rfl), fun h => huv (h.symm ▸ rfl)⟩
  have hattach₀ :=
    hK.isPLBall_derivedNeighborhoodCell_inter_union_of_mem_faces_one hqK htK hqt
      (Or.inl Finset.sdiff_subset) d hd hdne hdcomp hdincomp
  rw [hdspace] at hattach₀
  have hI₂ : IsPLBall 1 ((N ∪ C t) ∩ C q) := hmeet₂ ▸ hattach₀
  have hfirstK : N ∪ C t ⊆ K.space := union_subset hNK htspaceK
  have hqspaceK : C q ⊆ K.space := derivedNeighborhoodCell_space_subset K q
  have hfinal : IsPLBall 2 ((N ∪ C t) ∪ C q) :=
    hK.isPLBall_union_of_inter_isPLBall_one hfirst hqball hfirstK hqspaceK hI₂
  have hspace : (PiecewiseLinear.derivedNeighborhood K A).space = (N ∪ C t) ∪ C q := by
    dsimp only [N]
    rw [← iUnion_derivedNeighborhoodCell_space K A hAKK,
      ← iUnion_derivedNeighborhoodCell_space K A' hA'K]
    apply Subset.antisymm
    · intro x hx
      obtain ⟨r, hrA, hxr⟩ := mem_iUnion₂.mp hx
      by_cases hqr : q ⊆ r
      · have hrt := face_subset_of_sdiff_subset_free_triangle A hA htcard hst
          (Or.inl hscard) hinter hrA hqr
        have hqle := Finset.card_le_card hqr
        have hrtle := Finset.card_le_card hrt
        rw [hqcard] at hqle
        rw [htcard] at hrtle
        have hrcard : r.card = 2 ∨ r.card = 3 := by omega
        rcases hrcard with hrcard | hrcard
        · have heq : r = q := (Finset.eq_of_subset_of_card_le hqr (by omega)).symm
          exact Or.inr (heq ▸ hxr)
        · have heq : r = t := Finset.eq_of_subset_of_card_le hrt (by omega)
          exact Or.inl (Or.inr (heq ▸ hxr))
      · exact Or.inl (Or.inl (mem_iUnion₂.mpr ⟨r, (hfree r).mpr ⟨hrA, hqr⟩, hxr⟩))
    · rintro x ((hxN | hxt) | hxq)
      · obtain ⟨r, hr, hxr⟩ := mem_iUnion₂.mp hxN
        exact mem_iUnion₂.mpr ⟨r, eraseTriangleComplex_faces_subset A t hr, hxr⟩
      · exact mem_iUnion₂.mpr ⟨t, ht, hxt⟩
      · exact mem_iUnion₂.mpr ⟨q, hqA, hxq⟩
  exact hspace.symm ▸ hfinal

open Classical in
private theorem
    IsCombinatorialManifoldWithBoundary.isPLBall_free_triangle_surface_two
    {K A : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hA : IsPLBall 2 A.space)
    (hAK : A.faces ⊆ K.faces)
    {t s : Finset E} (ht : t ∈ A.faces) (htcard : t.card = 3)
    (hst : s ⊆ t) (hscard : s.card = 2)
    (htrace : (boundaryComplex 2 A).space ∩ convexHull ℝ (t : Set E) =
      ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset E) : Set E))
    (hinter : ∀ u ∈ A.faces, u.card = 3 → ¬s ⊆ u →
      (u ∩ t).card ≤ 1 ∧ (s.card = 2 → u ∩ t ⊆ s))
    (hprev : IsPLBall 2 (PiecewiseLinear.derivedNeighborhood K
      (eraseTriangleComplex A t)).space) :
    IsPLBall 2 (PiecewiseLinear.derivedNeighborhood K A).space := by
  classical
  have hqcard : (t \ s).card = 1 := by
    rw [Finset.card_sdiff_of_subset hst, htcard, hscard]
  obtain ⟨a, hqa⟩ := Finset.card_eq_one.mp hqcard
  have ha : a ∈ t ∧ a ∉ s := Finset.mem_sdiff.mp (hqa.symm ▸ Finset.mem_singleton_self a)
  let A' := eraseTriangleComplex A t
  let C := fun r : Finset E => (derivedNeighborhoodCell K r).space
  let N := (PiecewiseLinear.derivedNeighborhood K A').space
  let e := fun v : E => ({a, v} : Finset E)
  have hAKK : A.faces ⊆ K.faces := hAK
  have hA'K : A'.faces ⊆ K.faces := (eraseTriangleComplex_faces_subset A t).trans hAKK
  have hN : N = ⋃ r ∈ A'.faces, C r := (iUnion_derivedNeighborhoodCell_space K A' hA'K).symm
  have hfree (r : Finset E) : r ∈ A'.faces ↔ r ∈ A.faces ∧ a ∉ r := by
    simpa only [hqa, Finset.singleton_subset_iff] using
      (mem_eraseTriangleComplex_iff_of_free_triangle A hA ht htcard hst
        (Or.inr hscard) htrace hinter :
        r ∈ A'.faces ↔ r ∈ A.faces ∧ ¬t \ s ⊆ r)
  have htK := hAKK ht
  have htball : IsPLBall 2 (C t) := hK.isPLBall_derivedNeighborhoodCell htK
  have hD : IsPLBall 1 (C t ∩ N) :=
    isPLBall_derivedNeighborhoodCell_inter_erase_of_s_card_two_one hK hA hAK ht htcard
      hst hscard htrace hinter
  have hNK : N ⊆ K.space := derivedNeighborhood_space_subset K A'
  have htspaceK : C t ⊆ K.space := derivedNeighborhoodCell_space_subset K t
  have hfirst : IsPLBall 2 (N ∪ C t) :=
    hK.isPLBall_union_of_inter_isPLBall_one hprev htball hNK htspaceK
      ((inter_comm _ _).symm ▸ hD)
  have hav (v : E) (hv : v ∈ s) : a ≠ v := fun h => ha.2 (h.symm ▸ hv)
  have hecard (v : E) (hv : v ∈ s) : (e v).card = 2 := Finset.card_pair (hav v hv)
  have het (v : E) (hv : v ∈ s) : e v ⊆ t := by
    intro w hw
    simp only [e, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact ha.1
    · exact hst hv
  have heA (v : E) (hv : v ∈ s) : e v ∈ A.faces :=
    A.down_closed ht (het v hv) (Finset.insert_nonempty _ _)
  have hvA (v : E) (hv : v ∈ s) : {v} ∈ A.faces :=
    A.down_closed ht (Finset.singleton_subset_iff.mpr (hst hv)) (Finset.singleton_nonempty v)
  have heK (v : E) (hv : v ∈ s) : e v ∈ K.faces := hAKK (heA v hv)
  have hetne (v : E) (hv : v ∈ s) : e v ≠ t := by
    intro h
    have hc := congrArg Finset.card h
    rw [hecard v hv, htcard] at hc
    omega
  have hold (v : E) (hv : v ∈ s) : C (e v) ∩ N = C (e v) ∩ C {v} := by
    apply Subset.antisymm
    · rintro x ⟨hxe, hxN⟩
      rw [hN] at hxN
      obtain ⟨r, hr, hxr⟩ := mem_iUnion₂.mp hxN
      have hra := ((hfree r).mp hr).2
      rcases subset_or_subset_of_nonempty_derivedNeighborhoodCell_inter K
          (heK v hv) (hA'K hr) ⟨x, hxe, hxr⟩ with her | hre
      · exact (hra (her (Finset.mem_insert_self a {v}))).elim
      · have hrv : r = {v} := by
          apply Finset.eq_of_subset_of_card_le
          · intro w hw
            have hwe := hre hw
            simp only [e, Finset.mem_insert, Finset.mem_singleton] at hwe ⊢
            exact hwe.resolve_left (fun h => hra (h ▸ hw))
          · have := Finset.card_pos.mpr (A'.nonempty_of_mem_faces hr)
            simp only [Finset.card_singleton]
            omega
        exact ⟨hxe, hrv ▸ hxr⟩
    · rintro x ⟨hxe, hxv⟩
      refine ⟨hxe, ?_⟩
      rw [hN]
      exact mem_iUnion₂.mpr ⟨{v}, (hfree {v}).mpr ⟨hvA v hv, by
        simpa only [Finset.mem_singleton] using hav v hv⟩, hxv⟩
  have hattach (v : E) (hv : v ∈ s) : IsPLBall 1 ((N ∪ C t) ∩ C (e v)) := by
    have hgroup :=
      hK.isPLBall_derivedNeighborhoodCell_inter_union_of_mem_faces_one (heK v hv) htK
        (hetne v hv) (Or.inl (het v hv)) {{v}}
        (by intro u hu; simp only [Finset.mem_singleton] at hu; subst u; exact hAKK (hvA v hv))
        (by
          intro u hu
          simp only [Finset.mem_singleton] at hu
          subst u
          constructor <;> intro h <;> have hc := congrArg Finset.card h
          · simp only [Finset.card_singleton, hecard v hv] at hc
            omega
          · simp only [Finset.card_singleton, htcard] at hc
            omega)
        (by
          intro u hu
          simp only [Finset.mem_singleton] at hu
          subst u
          exact ⟨Or.inr (Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem
            (Finset.mem_singleton_self v))), Or.inr (Finset.singleton_subset_iff.mpr (hst hv))⟩)
        (by
          intro u hu w hw hne
          simp only [Finset.mem_singleton] at hu hw
          exact (hne (hu.trans hw.symm)).elim)
    have hmeet : (N ∪ C t) ∩ C (e v) = C (e v) ∩ (C t ∪ C {v}) := by
      rw [inter_comm, inter_union_distrib_left, hold v hv]
      simp only [inter_union_distrib_left, union_comm]
    rw [hmeet]
    simpa only [Finset.set_biUnion_singleton] using hgroup
  have hedis (v : E) (hv : v ∈ s) (w : E) (hw : w ∈ s) (hvw : v ≠ w) :
      Disjoint (C (e v)) (C (e w)) := by
    have hneq : e v ≠ e w := by
      intro heq
      have hvw' : v ∈ e w := heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self v)
      simp only [e, Finset.mem_insert, Finset.mem_singleton] at hvw'
      exact hvw (hvw'.resolve_left (hav v hv).symm)
    exact disjoint_derivedNeighborhoodCell_space K (heK v hv) (heK w hw)
      (fun h => hneq (Finset.eq_of_subset_of_card_le h (by rw [hecard v hv, hecard w hw])))
      (fun h => hneq (Finset.eq_of_subset_of_card_le h (by rw [hecard w hw, hecard v hv])).symm)
  let P := (N ∪ C t) ∪ ⋃ v ∈ s, C (e v)
  have hP : IsPLBall 2 P := hK.isPLBall_union_iUnion_of_pairwiseDisjoint_in_surface hfirst
    (union_subset hNK htspaceK) s (fun v => C (e v))
    (fun v hv => hK.isPLBall_derivedNeighborhoodCell (heK v hv))
    (fun v _ => derivedNeighborhoodCell_space_subset K (e v)) hattach hedis
  have hPK : P ⊆ K.space := union_subset (union_subset hNK htspaceK)
    (iUnion₂_subset fun v _ => derivedNeighborhoodCell_space_subset K (e v))
  have haA : {a} ∈ A.faces := A.down_closed ht (Finset.singleton_subset_iff.mpr ha.1)
    (Finset.singleton_nonempty a)
  have haK := hAKK haA
  have haN : Disjoint (C {a}) N := by
    rw [Set.disjoint_left]
    intro x hxa hxN
    rw [hN] at hxN
    obtain ⟨r, hr, hxr⟩ := mem_iUnion₂.mp hxN
    have hra := ((hfree r).mp hr).2
    rcases subset_or_subset_of_nonempty_derivedNeighborhoodCell_inter K haK (hA'K hr)
        ⟨x, hxa, hxr⟩ with har | hra'
    · exact hra (Finset.singleton_subset_iff.mp har)
    · obtain ⟨v, hv⟩ := A'.nonempty_of_mem_faces hr
      exact hra (Finset.mem_singleton.mp (hra' hv) ▸ hv)
  let d := s.image e
  have hdspace : (⋃ u ∈ d, C u) = ⋃ v ∈ s, C (e v) := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      exact mem_iUnion₂.mpr ⟨v, hv, hxu⟩
    · intro x hx
      obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion₂.mpr ⟨e v, Finset.mem_image.mpr ⟨v, hv, rfl⟩, hxv⟩
  have hatne : ({a} : Finset E) ≠ t := by
    intro h
    have hc := congrArg Finset.card h
    simp only [Finset.card_singleton, htcard] at hc
    omega
  have hgroup := hK.isPLBall_derivedNeighborhoodCell_inter_union_of_mem_faces_one haK htK
    hatne (Or.inl (Finset.singleton_subset_iff.mpr ha.1)) d
    (by intro u hu; obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu; exact heK v hv)
    (by
      intro u hu
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      refine ⟨?_, hetne v hv⟩
      intro h
      have hc := congrArg Finset.card h
      simp only [Finset.card_singleton, hecard v hv] at hc
      omega)
    (by
      intro u hu
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      exact ⟨Or.inl (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self a {v})),
        Or.inr (het v hv)⟩)
    (by
      intro u hu w hw huw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
      exact ⟨fun h => huw (Finset.eq_of_subset_of_card_le h (by rw [hecard v hv, hecard z hz])),
        fun h => huw (Finset.eq_of_subset_of_card_le h (by rw [hecard z hz, hecard v hv])).symm⟩)
  rw [hdspace] at hgroup
  have hmeet : P ∩ C {a} = C {a} ∩ (C t ∪ ⋃ v ∈ s, C (e v)) := by
    ext x
    simp only [P, mem_inter_iff, mem_union]
    constructor
    · rintro ⟨(hxN | hxt) | hxe, hxa⟩
      · exact (haN.le_bot ⟨hxa, hxN⟩).elim
      · exact ⟨hxa, Or.inl hxt⟩
      · exact ⟨hxa, Or.inr hxe⟩
    · rintro ⟨hxa, hxt | hxe⟩
      · exact ⟨Or.inl (Or.inr hxt), hxa⟩
      · exact ⟨Or.inr hxe, hxa⟩
  have hfinal : IsPLBall 2 (P ∪ C {a}) := hK.isPLBall_union_of_inter_isPLBall_one hP
    (hK.isPLBall_derivedNeighborhoodCell haK) hPK (derivedNeighborhoodCell_space_subset K {a})
    (hmeet.symm ▸ hgroup)
  have hspace : (PiecewiseLinear.derivedNeighborhood K A).space = P ∪ C {a} := by
    rw [← iUnion_derivedNeighborhoodCell_space K A hAKK]
    apply Subset.antisymm
    · intro x hx
      obtain ⟨r, hrA, hxr⟩ := mem_iUnion₂.mp hx
      by_cases har : a ∈ r
      · have hqr : t \ s ⊆ r := hqa ▸ Finset.singleton_subset_iff.mpr har
        have hrt := face_subset_of_sdiff_subset_free_triangle A hA htcard hst
          (Or.inr hscard) hinter hrA hqr
        have hpos := Finset.card_pos.mpr (A.nonempty_of_mem_faces hrA)
        have hle := Finset.card_le_card hrt
        rw [htcard] at hle
        have hrcard : r.card = 1 ∨ r.card = 2 ∨ r.card = 3 := by omega
        rcases hrcard with hrcard | hrcard | hrcard
        · have heq : r = {a} := (Finset.eq_of_subset_of_card_le
            (Finset.singleton_subset_iff.mpr har)
            (by simp only [Finset.card_singleton]; omega)).symm
          exact Or.inr (heq ▸ hxr)
        · obtain ⟨v, hva, hrv⟩ := Finset.exists_eq_insert_iff.mpr
            ⟨Finset.singleton_subset_iff.mpr har, by simp only [Finset.card_singleton]; omega⟩
          have hvR : v ∈ r := hrv ▸ Finset.mem_insert_self v {a}
          have hvS : v ∈ s := by
            by_contra hvs
            have hvq : v ∈ t \ s := Finset.mem_sdiff.mpr ⟨hrt hvR, hvs⟩
            rw [hqa] at hvq
            exact hva hvq
          have hre : r = e v := hrv.symm.trans (by ext w; simp [e, or_comm])
          exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨v, hvS, hre ▸ hxr⟩))
        · have heq : r = t := Finset.eq_of_subset_of_card_le hrt (by omega)
          exact Or.inl (Or.inl (Or.inr (heq ▸ hxr)))
      · have hxN : x ∈ N := by
          rw [hN]
          exact mem_iUnion₂.mpr ⟨r, (hfree r).mpr ⟨hrA, har⟩, hxr⟩
        exact Or.inl (Or.inl (Or.inl hxN))
    · rintro x (((hxN | hxt) | hxe) | hxa)
      · rw [hN] at hxN
        obtain ⟨r, hr, hxr⟩ := mem_iUnion₂.mp hxN
        exact mem_iUnion₂.mpr ⟨r, eraseTriangleComplex_faces_subset A t hr, hxr⟩
      · exact mem_iUnion₂.mpr ⟨t, ht, hxt⟩
      · obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hxe
        exact mem_iUnion₂.mpr ⟨e v, heA v hv, hxv⟩
      · exact mem_iUnion₂.mpr ⟨{a}, haA, hxa⟩
  exact hspace.symm ▸ hfinal

open Classical in
private theorem
    IsCombinatorialManifoldWithBoundary.isPLBall_free_triangle_surface
    {K A : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hA : IsPLBall 2 A.space)
    (hAK : A.faces ⊆ K.faces)
    {t s : Finset E} (ht : t ∈ A.faces) (htcard : t.card = 3)
    (hst : s ⊆ t) (hscard : s.card = 1 ∨ s.card = 2)
    (htrace : (boundaryComplex 2 A).space ∩ convexHull ℝ (t : Set E) =
      ⋃ v ∈ s, convexHull ℝ ((t.erase v : Finset E) : Set E))
    (hinter : ∀ u ∈ A.faces, u.card = 3 → ¬s ⊆ u →
      (u ∩ t).card ≤ 1 ∧ (s.card = 2 → u ∩ t ⊆ s))
    (hprev : IsPLBall 2 (PiecewiseLinear.derivedNeighborhood K
      (eraseTriangleComplex A t)).space) :
    IsPLBall 2 (PiecewiseLinear.derivedNeighborhood K A).space := by
  rcases hscard with hscard | hscard
  · exact hK.isPLBall_free_triangle_surface_one hA hAK ht
      htcard hst hscard htrace hinter hprev
  · exact hK.isPLBall_free_triangle_surface_two hA hAK ht
      htcard hst hscard htrace hinter hprev

open Classical in
private theorem isPLBall_triangle_subcomplex_cells_surface
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K)
    {s : Finset E} (hs : s ∈ K.faces) (hcard : s.card = 3) :
    IsPLBall 2 (((derivedNeighborhoodCell K s).space ∪
      ⋃ e ∈ s.powersetCard 2, (derivedNeighborhoodCell K e).space) ∪
        ⋃ v ∈ s, (derivedNeighborhoodCell K {v}).space) := by
  classical
  let C := fun t : Finset E => (derivedNeighborhoodCell K t).space
  let edges := s.powersetCard 2
  let B := C s ∪ ⋃ e ∈ edges, C e
  have hedges (e : Finset E) (he : e ∈ edges) :
      e ⊆ s ∧ e.card = 2 := Finset.mem_powersetCard.mp he
  have heK (e : Finset E) (he : e ∈ edges) : e ∈ K.faces :=
    K.down_closed hs (hedges e he).1
      (Finset.card_pos.mp (by rw [(hedges e he).2]; decide))
  have hse (e : Finset E) (he : e ∈ edges) : s ≠ e := by
    intro heq
    have hc := congrArg Finset.card heq
    rw [hcard, (hedges e he).2] at hc
    omega
  have hB : IsPLBall 2 B :=
    hK.isPLBall_union_iUnion_of_pairwiseDisjoint_in_surface
      (hK.isPLBall_derivedNeighborhoodCell hs) (derivedNeighborhoodCell_space_subset K s)
      edges C
      (fun e he => hK.isPLBall_derivedNeighborhoodCell (heK e he))
      (fun e _ => derivedNeighborhoodCell_space_subset K e)
      (fun e he => hK.isPLBall_derivedNeighborhoodCell_inter hs (heK e he) (hse e he)
        (Or.inr (hedges e he).1))
      (by
        intro e he f hf hef
        exact disjoint_derivedNeighborhoodCell_space K (heK e he) (heK f hf)
          (fun h => hef (Finset.eq_of_subset_of_card_le h (by
            rw [(hedges e he).2, (hedges f hf).2])))
          (fun h => hef (Finset.eq_of_subset_of_card_le h (by
            rw [(hedges f hf).2, (hedges e he).2])).symm))
  suffices h : ∀ a : Finset E, a ⊆ s →
      IsPLBall 2 (B ∪ ⋃ v ∈ a, C {v}) from h s Finset.Subset.rfl
  intro a
  induction a using Finset.induction_on with
  | empty => intro _; simpa using hB
  | @insert v a hva ih =>
    intro has
    have hvs : v ∈ s := has (Finset.mem_insert_self _ _)
    have ha : a ⊆ s := (Finset.subset_insert _ _).trans has
    have hprev := ih ha
    have hvK : {v} ∈ K.faces := K.down_closed hs (Finset.singleton_subset_iff.mpr hvs)
      (Finset.singleton_nonempty v)
    have hvne : ({v} : Finset E) ≠ s := by
      intro heq
      have hc := congrArg Finset.card heq
      simp only [Finset.card_singleton, hcard] at hc
      omega
    let arms := edges.filter (fun e => v ∈ e)
    have harme (e : Finset E) (he : e ∈ arms) : e ∈ edges :=
      Finset.mem_of_mem_filter e he
    have harms (e : Finset E) (he : e ∈ arms) :
        e ≠ {v} ∧ e ≠ s := by
      have hc := (hedges e (harme e he)).2
      constructor <;> intro heq <;> rw [heq] at hc
      · simp only [Finset.card_singleton] at hc
        omega
      · omega
    have hcomp (e : Finset E) (he : e ∈ arms) :
        ({v} ⊆ e ∨ e ⊆ {v}) ∧ (s ⊆ e ∨ e ⊆ s) :=
      ⟨Or.inl (Finset.singleton_subset_iff.mpr (Finset.mem_filter.mp he).2),
        Or.inr (hedges e (harme e he)).1⟩
    have hincomp (e : Finset E) (he : e ∈ arms)
        (f : Finset E) (hf : f ∈ arms) (hne : e ≠ f) :
        ¬e ⊆ f ∧ ¬f ⊆ e := by
      have hec := (hedges e (harme e he)).2
      have hfc := (hedges f (harme f hf)).2
      exact ⟨fun h => hne (Finset.eq_of_subset_of_card_le h (by omega)),
        fun h => hne (Finset.eq_of_subset_of_card_le h (by omega)).symm⟩
    have hattach : IsPLBall 1 (C {v} ∩ (C s ∪ ⋃ e ∈ arms, C e)) :=
      hK.isPLBall_derivedNeighborhoodCell_inter_union_of_mem_faces_one hvK hs hvne
        (Or.inl (Finset.singleton_subset_iff.mpr hvs)) arms
        (fun e he => heK e (harme e he)) harms hcomp hincomp
    have hinter :
        (B ∪ ⋃ w ∈ a, C {w}) ∩ C {v} = C {v} ∩ (C s ∪ ⋃ e ∈ arms, C e) := by
      apply Subset.antisymm
      · rintro x ⟨hx | hx, hxv⟩
        · rcases hx with hxs | hxe
          · exact ⟨hxv, Or.inl hxs⟩
          · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxe
            have hve : v ∈ e := by
              rcases subset_or_subset_of_nonempty_derivedNeighborhoodCell_inter K hvK
                  (heK e he) ⟨x, hxv, hxe⟩ with h | h
              · exact Finset.singleton_subset_iff.mp h
              · have hc := Finset.card_le_card h
                rw [(hedges e he).2, Finset.card_singleton] at hc
                omega
            exact ⟨hxv, Or.inr
              (mem_iUnion₂.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hve⟩, hxe⟩)⟩
        · obtain ⟨w, hw, hxw⟩ := mem_iUnion₂.mp hx
          have hwK : {w} ∈ K.faces := K.down_closed hs
            (Finset.singleton_subset_iff.mpr (ha hw)) (Finset.singleton_nonempty w)
          have hwv : w ≠ v := ne_of_mem_of_not_mem hw hva
          have hdis := disjoint_derivedNeighborhoodCell_space K hwK hvK
            (by simpa only [Finset.singleton_subset_iff, Finset.mem_singleton] using hwv)
            (by simpa only [Finset.singleton_subset_iff, Finset.mem_singleton] using hwv.symm)
          exact (hdis.le_bot ⟨hxw, hxv⟩).elim
      · rintro x ⟨hxv, hxs | hxarms⟩
        · exact ⟨Or.inl (Or.inl hxs), hxv⟩
        · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxarms
          exact ⟨Or.inl (Or.inr (mem_iUnion₂.mpr ⟨e, harme e he, hxe⟩)), hxv⟩
    have hI : IsPLBall 1 ((B ∪ ⋃ w ∈ a, C {w}) ∩ C {v}) := hinter.symm ▸ hattach
    have hvball : IsPLBall 2 (C {v}) := hK.isPLBall_derivedNeighborhoodCell hvK
    have hprevK : (B ∪ ⋃ w ∈ a, C {w}) ⊆ K.space :=
      union_subset (union_subset (derivedNeighborhoodCell_space_subset K s)
        (iUnion₂_subset fun e _ => derivedNeighborhoodCell_space_subset K e))
        (iUnion₂_subset fun w _ => derivedNeighborhoodCell_space_subset K {w})
    have h := hK.isPLBall_union_of_inter_isPLBall_one hprev hvball hprevK
      (derivedNeighborhoodCell_space_subset K {v}) hI
    simpa only [Finset.set_biUnion_insert, union_assoc, union_left_comm, union_comm] using h

namespace IsCombinatorialManifoldWithBoundary

open Classical in
private theorem isPLBall_derivedNeighborhood_triangle_subcomplex_surface
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K)
    {s : Finset E} (hs : s ∈ K.faces) (hcard : s.card = 3) :
    IsPLBall 2 (PiecewiseLinear.derivedNeighborhood K
      (simplexComplex s (K.indep hs))).space := by
  rw [derivedNeighborhood_simplex_space_eq_of_card_le_three K hs (by omega)]
  exact isPLBall_triangle_subcomplex_cells_surface hK hs hcard

section

variable [dE : DecidableEq E] [dP : DecidableEq (EuclideanSpace ℝ (Fin 2))]

open Classical in
private theorem isPLBall_derivedNeighborhood_planar_subcomplex_surface_aux
    (K A : Geometry.SimplicialComplex ℝ E)
    (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    [Finite K.faces] [Finite A.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hAK : A.faces ⊆ K.faces)
    {φ : E → EuclideanSpace ℝ (Fin 2)} {ψ : EuclideanSpace ℝ (Fin 2) → E}
    (hL : IsPLBall 2 L.space) (hIso : IsGlueIso A L φ ψ)
    {t₀ : Finset E} (ht₀ : t₀ ∈ A.faces) (ht₀card : t₀.card = 3) :
    IsPLBall 2 (PiecewiseLinear.derivedNeighborhood K A).space := by
  have hdE : dE = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  have hdP : dP = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst dE
  subst dP
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 2)) := Classical.decEq _
  generalize hn : {u ∈ A.faces | u.card = 3}.ncard = n
  induction n using Nat.strong_induction_on generalizing A L with
  | h n ih =>
    have hA := hL.of_isPLHomeomorphOn hIso.symm.isPLHomeomorphOn
    by_cases heq : A.space = convexHull ℝ (t₀ : Set E)
    · have hAsimplex : A = simplexComplex t₀ (A.indep ht₀) := by
        apply Geometry.SimplicialComplex.ext
        ext s
        change s ∈ A.faces ↔ s.Nonempty ∧ s ⊆ t₀
        constructor
        · intro hs
          have hx := centroid_mem_openSimplex_of_mem_faces A s hs
          have hxt : s.centroid ℝ id ∈ convexHull ℝ (t₀ : Set E) :=
            heq ▸ A.convexHull_subset_space hs (openSimplex_subset_convexHull s hx)
          exact ⟨A.nonempty_of_mem_faces hs,
            face_subset_of_mem_openSimplex_of_mem_convexHull A hs ht₀ hx hxt⟩
        · rintro ⟨hsne, hst⟩
          exact A.down_closed ht₀ hst hsne
      rw [hAsimplex]
      exact hK.isPLBall_derivedNeighborhood_triangle_subcomplex_surface (hAK ht₀) ht₀card
    · obtain ⟨t, s, ht, htcard, htt₀, -, hst, hscard, htrace, hinter, hball⟩ :=
        exists_isPLBall_eraseTriangleComplex_of_isGlueIso_planar A L hIso hL ht₀ ht₀card heq
      let A' := eraseTriangleComplex A t
      let L' := eraseTriangleComplex L (t.image φ)
      let _ : Finite A'.faces := (eraseTriangleComplex_faces_finite A t).to_subtype
      let _ : Finite L'.faces :=
        (eraseTriangleComplex_faces_finite L (t.image φ)).to_subtype
      have hA'K : A'.faces ⊆ K.faces :=
        (eraseTriangleComplex_faces_subset A t).trans hAK
      have hIso' : IsGlueIso A' L' φ ψ := hIso.eraseTriangleComplex ht
      have hL' : IsPLBall 2 L'.space := hball.of_isPLHomeomorphOn hIso'.isPLHomeomorphOn
      have ht₀' : t₀ ∈ A'.faces :=
        (mem_eraseTriangleComplex_triangle_iff A t
          (fun u hu => card_le_of_isPLBall A hA hu) ht₀card).mpr ⟨ht₀, htt₀.symm⟩
      have hlt : {u ∈ A'.faces | u.card = 3}.ncard < n := by
        rw [← hn]
        exact ncard_triangles_eraseTriangleComplex_lt A t ht htcard
          (fun u hu => card_le_of_isPLBall A hA hu)
      have hprev := ih _ hlt (A := A') (L := L') (hAK := hA'K)
        (hL := hL') (hIso := hIso') (ht₀ := ht₀') rfl
      exact hK.isPLBall_free_triangle_surface hA hAK ht htcard
        hst hscard htrace hinter hprev

open Classical in
theorem isPLBall_derivedNeighborhood_of_isGlueIso_planar_subcomplex_in_surface
    {K A : Geometry.SimplicialComplex ℝ E}
    {L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    [Finite K.faces] [Finite A.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hAK : A.faces ⊆ K.faces)
    {φ : E → EuclideanSpace ℝ (Fin 2)} {ψ : EuclideanSpace ℝ (Fin 2) → E}
    (hL : IsPLBall 2 L.space) (hIso : IsGlueIso A L φ ψ) :
    IsPLBall 2 (PiecewiseLinear.derivedNeighborhood K A).space := by
  classical
  have hA := hL.of_isPLHomeomorphOn hIso.symm.isPLHomeomorphOn
  obtain ⟨x, hx⟩ := hA.nonempty
  obtain ⟨s, hs, -⟩ := A.mem_space_iff.mp hx
  obtain ⟨t, ht, -, htc⟩ := exists_face_superset_card_eq_of_isPLBall A hA hs
  exact isPLBall_derivedNeighborhood_planar_subcomplex_surface_aux K A L hK hAK
    hL hIso ht htc

end

end IsCombinatorialManifoldWithBoundary

namespace IsCombinatorialManifoldWithBoundary

open Classical in
theorem exists_isSubdivision_disk_pair_with_derivedNeighborhood_endpoint_disk
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {Δ D₁ D₂ U : Set E}
    (hΔ : IsPLBall 2 Δ) (hD₁ : IsPLBall 2 D₁) (hD₂ : IsPLBall 2 D₂)
    (hΔD₁ : Δ ⊆ D₁) (hΔD₂ : Δ ⊆ D₂) (hD₁D₂ : D₁ ∩ D₂ = Δ)
    (hD₁K : D₁ ⊆ K.space) (hD₂K : D₂ ⊆ K.space) (hU : U ∈ 𝓝ˢ[K.space] Δ) :
    ∃ (R A A₁ A₂ : Geometry.SimplicialComplex ℝ E)
      (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
      (φ : E → EuclideanSpace ℝ (Fin 2)) (ψ : EuclideanSpace ℝ (Fin 2) → E),
      IsSubdivision R K ∧ R.faces.Finite ∧
      A.faces ⊆ R.faces ∧ A.faces.Finite ∧ A.space = Δ ∧
      A₁.faces ⊆ R.faces ∧ A₁.faces.Finite ∧ A₁.space = D₁ ∧
      A₂.faces ⊆ R.faces ∧ A₂.faces.Finite ∧ A₂.space = D₂ ∧
      A.faces ⊆ A₁.faces ∧ A.faces ⊆ A₂.faces ∧ A₁.space ∩ A₂.space = A.space ∧
      L.faces.Finite ∧ IsPLBall 2 L.space ∧ IsGlueIso A L φ ψ ∧
      IsPLBall 3 (PiecewiseLinear.derivedNeighborhood R A).space ∧
      Δ ⊆ (PiecewiseLinear.derivedNeighborhood R A).space ∧
      (PiecewiseLinear.derivedNeighborhood R A).space ⊆ K.space ∧
      (PiecewiseLinear.derivedNeighborhood R A).space ⊆ U ∧
      (∀ x ∈ Δ, (PiecewiseLinear.derivedNeighborhood R A).space ∈ 𝓝[K.space] x) ∧
      IsPLBall 2 (D₂ ∩ (PiecewiseLinear.derivedNeighborhood R A).space) := by
  classical
  obtain ⟨R, A, A₁, A₂, L, φ, ψ, hR, hRfin, hAR, hAfin, hAΔ,
      hA₁R, hA₁fin, hA₁D₁, hA₂R, hA₂fin, hA₂D₂, hAA₁, hAA₂, hmeet,
      hLfin, hL, hIso, hNball, hcontains, hNK, hNU, hnhds⟩ :=
    hK.exists_isSubdivision_disk_pair_with_derivedNeighborhood hΔ hD₁ hD₂
      hΔD₁ hΔD₂ hD₁D₂ hD₁K hD₂K hU
  let _ : Finite R.faces := hRfin.to_subtype
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite A₂.faces := hA₂fin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  have hA₂ball : IsPLBall 2 A₂.space := by
    rw [hA₂D₂]
    exact hD₂
  have htrace : IsPLBall 2 (A₂.space ∩ (PiecewiseLinear.derivedNeighborhood R A).space) := by
    have hA₂man := hA₂ball.isCombinatorialManifoldWithBoundary
    have hintrinsic :=
      hA₂man.isPLBall_derivedNeighborhood_of_isGlueIso_planar_subcomplex_in_surface hAA₂ hL hIso
    rw [inter_comm, derivedNeighborhood_space_inter_subcomplex R A A₂ hA₂R hAA₂]
    exact hintrinsic
  refine ⟨R, A, A₁, A₂, L, φ, ψ, hR, hRfin, hAR, hAfin, hAΔ,
    hA₁R, hA₁fin, hA₁D₁, hA₂R, hA₂fin, hA₂D₂, hAA₁, hAA₂, hmeet,
    hLfin, hL, hIso, hNball, hcontains, hNK, hNU, hnhds, ?_⟩
  rwa [← hA₂D₂]

end IsCombinatorialManifoldWithBoundary

end DifferentialGeometry.Topology.PiecewiseLinear
