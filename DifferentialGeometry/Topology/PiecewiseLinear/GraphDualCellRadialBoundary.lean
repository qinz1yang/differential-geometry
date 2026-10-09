/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedCellCone
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRayEmbedding
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedWeights

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
private theorem barycentricCoordinate_centroid
    (K : Geometry.SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ K.faces) (z : E) :
    barycentricCoordinate K z (s.centroid ℝ id) = if z ∈ s then (s.card : ℝ)⁻¹ else 0 := by
  have hne := K.nonempty_of_mem_faces hs
  have hmem : s.centroid ℝ id ∈ convexHull ℝ (s : Set E) :=
    s.centroid_mem_convexHull hne
  rw [barycentricCoordinate_eq K hs hmem]
  by_cases hz : z ∈ s
  · rw [ite_eq_left hz, weights_centroid (K.indep hs) (Finset.Subset.refl s) hne hz,
      ite_eq_left hz]
  · simp only [ite_eq_right hz]

open Classical in
theorem centroid_mem_frontier_graphDualCell_of_mixed_face
    (M L : Geometry.SimplicialComplex ℝ E) {v : E} (hv : {v} ∈ M.faces)
    {s a : Finset E} (hs : s ∈ (dualCell M {v} hv).faces)
    (ha : a ∈ L.faces) (has : a.centroid ℝ id ∈ s)
    {w : E} (hws : w ∈ s) (hw : w ∉ (barycentricSubdivision L).vertices) :
    s.centroid ℝ id ∈ frontier (graphDualCell M L v).space := by
  have hsM := dualCell_faces_subset M hv hs
  have hne := (barycentricSubdivision M).nonempty_of_mem_faces hsM
  have hmem : s.centroid ℝ id ∈ convexHull ℝ (s : Set E) :=
    s.centroid_mem_convexHull hne
  have hxN : {s.centroid ℝ id} ∈ (derivedNeighborhood M L).faces :=
    (singleton_centroid_mem_derivedNeighborhood_iff M L hsM).mpr ⟨a, ha, has⟩
  have hxC : s.centroid ℝ id ∈ (graphDualCell M L v).space := by
    refine (graphDualCell M L v).convexHull_subset_space ⟨hxN, ?_⟩ (by simp)
    rw [Finset.coe_singleton, convexHull_singleton, singleton_subset_iff,
      closedStar_barycentricSubdivision_eq_dualCell M hv]
    exact (dualCell M {v} hv).convexHull_subset_space hs hmem
  have hpos : 0 < (s.card : ℝ)⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr (Finset.card_pos.mpr hne))
  have hnot : s.centroid ℝ id ∉ interior (derivedNeighborhood M L).space := by
    apply notMem_interior_derivedNeighborhood_of_barycentricCoordinate_le
      ((barycentricSubdivision M).convexHull_subset_space hsM hmem) hw
    · rw [barycentricCoordinate_centroid _ hsM, ite_eq_left hws]
      exact hpos
    · intro z _
      rw [barycentricCoordinate_centroid _ hsM, barycentricCoordinate_centroid _ hsM,
        ite_eq_left hws]
      split_ifs
      · exact le_rfl
      · exact hpos.le
  exact ⟨subset_closure hxC, fun h =>
    hnot (interior_mono (graphDualCell_space_subset M L v) h)⟩

open Classical in
theorem not_isRadiallyInjective_frontier_graphDualCell_of_edge_lt_face
    (M L : Geometry.SimplicialComplex ℝ E) (hLM : L.faces ⊆ M.faces)
    (hcard : ∀ a ∈ L.faces, a.card ≤ 2) {e t : Finset E} (he : e ∈ L.faces)
    (ht : t ∈ M.faces) (het : e ⊆ t) (hec : e.card = 2) (htc : 2 < t.card)
    {v : E} (hve : v ∈ e) :
    ¬ IsRadiallyInjective v (frontier (graphDualCell M L v).space) := by
  let c := e.centroid ℝ id
  let d := t.centroid ℝ id
  have hv : {v} ∈ M.faces := M.down_closed (hLM he)
    (Finset.singleton_subset_iff.mpr hve) (Finset.singleton_nonempty v)
  have hetne : e ≠ t := fun h => by have hc := congrArg Finset.card h; omega
  have hvne : ({v} : Finset E) ≠ e := fun h => by
    have hc := congrArg Finset.card h
    simp only [Finset.card_singleton, hec] at hc
    omega
  have hvtne : ({v} : Finset E) ≠ t := fun h => by
    have hc := congrArg Finset.card h
    simp only [Finset.card_singleton] at hc
    omega
  have hvc : v ≠ c := by
    simpa only [Finset.centroid_singleton, id_eq] using
      centroid_ne_centroid_of_ne M hv (hLM he) hvne
  have hvd : v ≠ d := by
    simpa only [Finset.centroid_singleton, id_eq] using
      centroid_ne_centroid_of_ne M hv ht hvtne
  have hcd : c ≠ d := centroid_ne_centroid_of_ne M (hLM he) ht hetne
  have hdL : d ∉ (barycentricSubdivision L).vertices := by
    intro hd
    obtain ⟨a, ha, had⟩ := exists_eq_centroid_of_singleton_mem_barycentricSubdivision L hd
    have hat : a = t := injOn_faces_of_mem_openSimplex M
      (centroid_mem_openSimplex_of_mem_faces M) (hLM ha) ht had
    have hac := hcard a ha
    rw [hat] at hac
    omega
  have hflag : IsFlag M {e, t} := by
    refine ⟨?_, ?_⟩
    · intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact hLM he
      · exact ht
    · intro a ha b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact Or.inl subset_rfl
      · exact Or.inl het
      · exact Or.inr het
      · exact Or.inl subset_rfl
  have hsub : ∀ a ∈ ({e, t} : Finset (Finset E)), ({v} : Finset E) ⊆ a := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact Finset.singleton_subset_iff.mpr hve
    · exact Finset.singleton_subset_iff.mpr (het hve)
  have hpair : {c, d} ∈ (dualCell M {v} hv).faces := by
    simpa only [Finset.image_insert, Finset.image_singleton] using
      (mem_dualCell_faces_iff_of_flag hv hflag (Finset.insert_nonempty e {t})).mpr hsub
  have hflag' := hflag.insert_of_subset hv hsub
  have hsub' : ∀ a ∈ (insert {v} {e, t} : Finset (Finset E)), ({v} : Finset E) ⊆ a := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact subset_rfl
    · exact hsub a ha
  have htriple : {v, c, d} ∈ (dualCell M {v} hv).faces := by
    simpa only [Finset.image_insert, Finset.image_singleton, Finset.centroid_singleton, id_eq]
      using (mem_dualCell_faces_iff_of_flag hv hflag'
        (Finset.insert_nonempty {v} {e, t})).mpr hsub'
  let x := ({v, c, d} : Finset E).centroid ℝ id
  let y := ({c, d} : Finset E).centroid ℝ id
  have hx : x ∈ frontier (graphDualCell M L v).space :=
    centroid_mem_frontier_graphDualCell_of_mixed_face M L hv htriple he
      (by simp [c]) (w := d) (by simp) hdL
  have hy : y ∈ frontier (graphDualCell M L v).space :=
    centroid_mem_frontier_graphDualCell_of_mixed_face M L hv hpair he
      (by simp [c]) (w := d) (by simp) hdL
  have hxc : x = (3 : ℝ)⁻¹ • v + (3 : ℝ)⁻¹ • c + (3 : ℝ)⁻¹ • d := by
    change ({v, c, d} : Finset E).centroid ℝ id = _
    rw [centroid_eq_sum _ (Finset.insert_nonempty v {c, d})]
    simp [hvc, hvd, hcd, add_assoc]
  have hyc : y = (2 : ℝ)⁻¹ • c + (2 : ℝ)⁻¹ • d := by
    change ({c, d} : Finset E).centroid ℝ id = _
    rw [centroid_eq_sum _ (Finset.insert_nonempty c {d})]
    simp [hcd]
  have hxy : x = v + (2 / 3 : ℝ) • (y - v) := by
    rw [hxc, hyc]
    module
  have hne : x ≠ y := by
    apply centroid_ne_centroid_of_ne (barycentricSubdivision M)
      (dualCell_faces_subset M hv htriple) (dualCell_faces_subset M hv hpair)
    intro h
    have hc := congrArg Finset.card h
    simp [hvc, hvd, hcd] at hc
  intro hrad
  exact hne (hrad y hy x hx (2 / 3) (by norm_num) hxy)

open Classical in
theorem not_exists_isConeBase_frontier_graphDualCell_of_edge_lt_face
    (M L : Geometry.SimplicialComplex ℝ E) (hLM : L.faces ⊆ M.faces)
    (hcard : ∀ a ∈ L.faces, a.card ≤ 2) {e t : Finset E} (he : e ∈ L.faces)
    (ht : t ∈ M.faces) (het : e ⊆ t) (hec : e.card = 2) (htc : 2 < t.card)
    {v : E} (hve : v ∈ e) :
    ¬ ∃ B : Geometry.SimplicialComplex ℝ E,
      IsConeBase v B ∧ B.space = frontier (graphDualCell M L v).space := by
  rintro ⟨B, hB, hBspace⟩
  apply not_isRadiallyInjective_frontier_graphDualCell_of_edge_lt_face
    M L hLM hcard he ht het hec htc hve
  rw [← hBspace]
  exact hB.radial

end DifferentialGeometry.Topology.PiecewiseLinear
