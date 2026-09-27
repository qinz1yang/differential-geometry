/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryFacets
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactEdgeTraces
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTriangleEndpoints
import DifferentialGeometry.Topology.PiecewiseLinear.UpperLinkBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
private theorem triple_centroid_mem_dualCell (K : Geometry.SimplicialComplex ℝ E)
    {e s t : Finset E} (he : e ∈ K.faces) (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    (hes : e ⊆ s) (hst : s ⊆ t) :
    {e.centroid ℝ id, s.centroid ℝ id, t.centroid ℝ id} ∈ (dualCell K e he).faces := by
  have hflag : IsFlag K {e, s, t} := by
    refine ⟨?_, ?_⟩
    · intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl <;> assumption
    · intro r hr u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr hu
      rcases hr with rfl | rfl | rfl <;> rcases hu with rfl | rfl | rfl
      all_goals first | exact Or.inl subset_rfl | exact Or.inl hes | exact Or.inr hes |
        exact Or.inl hst | exact Or.inr hst | exact Or.inl (hes.trans hst) |
        exact Or.inr (hes.trans hst)
  have h := (mem_dualCell_faces_iff_of_flag he hflag (Finset.insert_nonempty _ _)).mpr
    (fun r hr => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl
      · exact subset_rfl
      · exact hes
      · exact hes.trans hst)
  simpa only [Finset.image_insert, Finset.image_singleton] using h

open Classical in
theorem pair_centroid_mem_boundaryComplex_dualCell_of_facet [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {e s t : Finset E}
    (he : e ∈ K.faces) (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    (hec : e.card = 2) (hsc : s.card = 3) (htc : t.card = 4)
    (hes : e ⊆ s) (hst : s ⊆ t) (hmax : ∀ r ∈ K.faces, r ⊆ t) :
    {e.centroid ℝ id, s.centroid ℝ id} ∈ (boundaryComplex 2 (dualCell K e he)).faces := by
  let A := dualCell K e he
  let P : Finset E := {e.centroid ℝ id, s.centroid ℝ id}
  let _ : Finite A.faces := (dualCell_faces_finite K he).to_subtype
  have hA : IsPLBall 2 A.space := hK.isPLBall_dualCell K he (k := 1) hec (by omega)
  have hcent : e.centroid ℝ id ≠ s.centroid ℝ id := by
    intro h
    have heq := injOn_faces_of_mem_openSimplex K
      (centroid_mem_openSimplex_of_mem_faces K) he hs h
    have hc := congrArg Finset.card heq
    rw [hec, hsc] at hc
    omega
  have hPc : P.card = 2 := Finset.card_pair hcent
  apply (hA.isCombinatorialManifoldWithBoundary.mem_boundaryComplex_iff_unique_coface A hPc).mpr
  refine ⟨t.centroid ℝ id, ?_⟩
  ext z
  change (z ∉ P ∧ insert z P ∈ A.faces) ↔ z = t.centroid ℝ id
  constructor
  · rintro ⟨hzP, hzA⟩
    obtain ⟨d, hd, hdne, hde, himage⟩ := (mem_dualCell_faces_iff K he).mp hzA
    have hzi : z ∈ d.image (fun r => r.centroid ℝ id) :=
      himage ▸ Finset.mem_insert_self _ _
    obtain ⟨r, hr, hctr⟩ := Finset.mem_image.mp hzi
    have hrK := hd.mem_faces hr
    have her := hde r hr
    have hrs : r ⊆ s ∨ s ⊆ r := subset_or_subset_of_centroid_mem_face K hrK hs
      (dualCell_faces_subset K he hzA) (by rw [hctr]; exact Finset.mem_insert_self _ _)
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
    have hre : r ≠ e := by
      intro h
      apply hzP
      rw [← hctr, h]
      exact Finset.mem_insert_self _ _
    have hrne : r ≠ s := by
      intro h
      apply hzP
      rw [← hctr, h]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hrt : r = t := by
      have hrt := hmax r hrK
      have hrc := Finset.card_le_card hrt
      have herc := Finset.card_le_card her
      rcases hrs with hrs | hsr
      · have hrsc := Finset.card_le_card hrs
        by_cases hc : r.card = 2
        · exact (hre (Finset.eq_of_subset_of_card_le her (by omega)).symm).elim
        · exact (hrne (Finset.eq_of_subset_of_card_le hrs (by omega))).elim
      · have hlt := Finset.card_lt_card
          (Finset.ssubset_iff_subset_ne.mpr ⟨hsr, hrne.symm⟩)
        exact Finset.eq_of_subset_of_card_le hrt (by omega)
    rw [← hctr, hrt]
  · rintro rfl
    constructor
    · intro hmem
      rcases Finset.mem_insert.mp hmem with h | h
      · have heq := injOn_faces_of_mem_openSimplex K
          (centroid_mem_openSimplex_of_mem_faces K) ht he h
        have hc := congrArg Finset.card heq
        rw [htc, hec] at hc
        omega
      · have heq := injOn_faces_of_mem_openSimplex K
          (centroid_mem_openSimplex_of_mem_faces K) ht hs (Finset.mem_singleton.mp h)
        have hc := congrArg Finset.card heq
        rw [htc, hsc] at hc
        omega
    · have h := triple_centroid_mem_dualCell K he hs ht hes hst
      have hperm : insert (t.centroid ℝ id) P =
          ({e.centroid ℝ id, s.centroid ℝ id, t.centroid ℝ id} : Finset E) := by
        ext z
        simp only [P, Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [hperm]
      exact h

open Classical in
theorem boundaryComplex_tetra_edge_trace_eq_pair [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {e s f t : Finset E}
    (he : e ∈ K.faces) (hs : s ∈ K.faces) (hf : f ∈ K.faces) (ht : t ∈ K.faces)
    (hec : e.card = 2) (hsc : s.card = 3) (hfc : f.card = 3) (htc : t.card = 4)
    (hes : e ⊆ s) (hef : e ⊆ f) (hst : s ⊆ t) (hft : f ⊆ t) (hsf : s ≠ f)
    (hmax : ∀ r ∈ K.faces, r ⊆ t) :
    (boundaryComplex 1 (upperLink (dualCell K e he) {e.centroid ℝ id})).space =
      {({e.centroid ℝ id, s.centroid ℝ id} : Finset E).centroid ℝ id,
        ({e.centroid ℝ id, f.centroid ℝ id} : Finset E).centroid ℝ id} := by
  let A := dualCell K e he
  let G := upperLink A {e.centroid ℝ id}
  let _ : Finite A.faces := (dualCell_faces_finite K he).to_subtype
  let _ : Finite G.faces := (upperLink_faces_finite _ _).to_subtype
  have hA : IsPLBall 2 A.space := hK.isPLBall_dualCell K he (k := 1) hec (by omega)
  have hAs := pair_centroid_mem_boundaryComplex_dualCell_of_facet K hK he hs ht
    hec hsc htc hes hst hmax
  have hAf := pair_centroid_mem_boundaryComplex_dualCell_of_facet K hK he hf ht
    hec hfc htc hef hft hmax
  have hvB : {e.centroid ℝ id} ∈ (boundaryComplex 2 A).faces :=
    (boundaryComplex 2 A).down_closed hAs (by simp) (Finset.singleton_nonempty _)
  have hG : IsPLBall 1 G.space :=
    hA.isCombinatorialManifoldWithBoundary.isPLBall_upperLink_of_mem_boundaryComplex A hvB
      (k := 0) (Finset.card_singleton _)
  have hmark (u : Finset E) (hu : u ∈ K.faces) (huc : u.card = 3)
      (hAu : {e.centroid ℝ id, u.centroid ℝ id} ∈ (boundaryComplex 2 A).faces) :
      ({e.centroid ℝ id, u.centroid ℝ id} : Finset E).centroid ℝ id ∈
        (boundaryComplex 1 G).space := by
    let P : Finset E := {e.centroid ℝ id, u.centroid ℝ id}
    have hcent : e.centroid ℝ id ≠ u.centroid ℝ id := by
      intro h
      have heq := injOn_faces_of_mem_openSimplex K
        (centroid_mem_openSimplex_of_mem_faces K) he hu h
      have hc := congrArg Finset.card heq
      rw [hec, huc] at hc
      omega
    have hlt : ({e.centroid ℝ id} : Finset E) ⊂ P := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨by simp [P], ?_⟩
      intro hp
      have hm : u.centroid ℝ id ∈ ({e.centroid ℝ id} : Finset E) :=
        hp.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      exact hcent (Finset.mem_singleton.mp hm).symm
    change _ ∈ (boundaryComplex 1 (upperLink A {e.centroid ℝ id})).space
    rw [boundaryComplex_upperLink_singleton A hA.isCombinatorialManifoldWithBoundary hvB]
    apply (upperLink (boundaryComplex 2 A) {e.centroid ℝ id}).subset_space
      (s := {P.centroid ℝ id}) ?_ (Finset.mem_singleton_self _)
    refine ⟨{P}, ?_, Finset.singleton_nonempty _, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro r hr
        rw [Finset.mem_singleton.mp hr]
        exact hAu
      · intro r hr q hq
        rw [Finset.mem_singleton.mp hr, Finset.mem_singleton.mp hq]
        exact Or.inl subset_rfl
    · intro r hr
      rw [Finset.mem_singleton.mp hr]
      exact hlt
    · simp only [Finset.image_singleton]
  have hpq : ({e.centroid ℝ id, s.centroid ℝ id} : Finset E).centroid ℝ id ≠
      ({e.centroid ℝ id, f.centroid ℝ id} : Finset E).centroid ℝ id := by
    intro h
    have hpair := injOn_faces_of_mem_openSimplex (barycentricSubdivision K)
      (centroid_mem_openSimplex_of_mem_faces _)
      (pair_centroid_mem_barycentricSubdivision_of_subset_or_subset K he hs (Or.inl hes))
      (pair_centroid_mem_barycentricSubdivision_of_subset_or_subset K he hf (Or.inl hef)) h
    have hm : s.centroid ℝ id ∈ ({e.centroid ℝ id, f.centroid ℝ id} : Finset E) :=
      hpair ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    rcases Finset.mem_insert.mp hm with h | h
    · have heq := injOn_faces_of_mem_openSimplex K
        (centroid_mem_openSimplex_of_mem_faces K) hs he h
      have hc := congrArg Finset.card heq
      rw [hsc, hec] at hc
      omega
    · exact hsf (injOn_faces_of_mem_openSimplex K
        (centroid_mem_openSimplex_of_mem_faces K) hs hf (Finset.mem_singleton.mp h))
  exact boundaryComplex_interval_eq_pair_of_subset G hG hpq
    (hmark s hs hsc hAs) (hmark f hf hfc hAf)

end DifferentialGeometry.Topology.PiecewiseLinear
